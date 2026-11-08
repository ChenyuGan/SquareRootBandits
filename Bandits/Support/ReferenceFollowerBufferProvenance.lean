/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

import Lean.Elab.Tactic.Omega

/-!
# Physical provenance of the reference follower's sparse buffer

The sparse buffer and local event order follow
`sources/zip4/manuscript/06_interruptions.tex:195-233,246-275,295-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,54-60`.
This module analyzes only the literal records and diagnostics in the computed
`ReferenceActivePhysicalHorizon.run`. A successful reset is recognized from
the actual reference-DOWN diagnostic constructor. Initial/replay buffers stay
as explicit seed data; suffix records are tied to the actual own entries.

The results here concern logging provenance and chronological buffer safety.
They do not identify sparse arrivals with the global queue trace, prove
message authenticity, establish no dagger for the whole run, or close a
manuscript regret assertion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferenceDownReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SparseCalendarReplay

namespace Bandits.Support.ReferenceFollowerBufferProvenance

abbrev Parameters := ReferenceActivePhysicalHorizon.Parameters
abbrev RateInput := ReferenceActivePhysicalHorizon.RateInput
abbrev BufferRecord (p : Parameters) :=
  SparseCalendarReplay.SparseCalendarRecord p.K

variable {p : Parameters} {rate : RateInput p}

/-- The only new sparse records attributed to one actual physical record:
the literal `logAt` list from its prepared ordinary unoccupied follower and
its actual own entry. Occupied and dagger choice states emit the empty list. -/
def logEmission (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    List (BufferRecord p) := by
  classical
  let prepared := record.output.preparation.followers.followers i
  match prepared.configuration with
  | .dagger => exact []
  | .ordinary state _ =>
      if hunoccupied : state.status = .unoccupied then
        exact ReferencePrelaunchFollower.logAt i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i))
      else exact []

/-- A reset is exactly an actual DOWN diagnostic whose outcome has the
accepted constructor. Rejection, skip, and every failure retain the buffer. -/
def acceptedDownReset (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ cut, (record.output.followers i).down = some cut ∧
    ∃ before after raw reply scan registers lastService,
      cut.outcome = .accepted before after raw reply scan registers lastService

noncomputable def bufferFoldStep (i : Fin (p.m - 1)) (buffer : List (BufferRecord p))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    List (BufferRecord p) := by
  classical
  exact if acceptedDownReset i record then [] else buffer ++ logEmission i record

/-- Fold the actual per-record emissions, clearing only at an accepted actual
DOWN diagnostic. This is the buffer equation's literal list analysis. -/
noncomputable def bufferFold (i : Fin (p.m - 1)) (seed : List (BufferRecord p))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) : List (BufferRecord p) := by
  classical
  exact records.foldl (bufferFoldStep i) seed

noncomputable def suffixFoldStep (i : Fin (p.m - 1))
    (seenAndSuffix : Bool × List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Bool × List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) := by
  classical
  exact if acceptedDownReset i record then (true, [])
    else (seenAndSuffix.1, seenAndSuffix.2 ++ [record])

/-- Records strictly after the last accepted DOWN, or all records when there
is no accepted DOWN. The reset record itself is intentionally excluded. -/
noncomputable def recordsAfterLastAcceptedDown (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) :
    Bool × List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) := by
  classical
  exact records.foldl (suffixFoldStep i) (false, [])

/-- Every nonempty actual emission is the one canonical log record, with
timestamp, arm, quantized own feedback, and this same row's thin coordinate. -/
theorem logEmission_member_fields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (saved : BufferRecord p) (hsaved : saved ∈ logEmission i record) :
    ∃ own, saved.calendarRound = record.input.time.val + 1 ∧
      saved.pilot = own.1 ∧ saved.observation = own.2.val ∧
      saved.thinScalar = (record.input.row.2 record.input.time).1
        ContinuousControlSlice.Label.thin ∧
      own = record.output.ownEntries (followerPlayer p.two_le_m i) := by
  classical
  let prepared := record.output.preparation.followers.followers i
  cases hconfiguration : prepared.configuration with
  | dagger => simp [logEmission, prepared, hconfiguration] at hsaved
  | ordinary state memory =>
      by_cases hstatus : state.status = .unoccupied
      · have hmem := (ReferencePrelaunchFollower.mem_logAt_iff i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i)) saved).mp (by
            simpa [logEmission, prepared, hconfiguration, hstatus] using hsaved)
        rcases hmem with ⟨_, rfl⟩
        exact ⟨record.output.ownEntries (followerPlayer p.two_le_m i), rfl, rfl, rfl,
          rfl, rfl⟩
      · simp [logEmission, prepared, hconfiguration, hstatus] at hsaved

/-- The emitted own value is the exact action/observation pair produced by
the same prepared round. -/
theorem round_ownEntry_eq_prepared (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.ownEntries (followerPlayer p.two_le_m i) =
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (followerPlayer p.two_le_m i)) := by
  rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  change (prepared.arms.actions (followerPlayer p.two_le_m i),
      ActualInitializationPhysicalStep.observationOfGrid p
        (prepared.feedback.feedback (followerPlayer p.two_le_m i))) =
    ((prepared.followers.followers i).arm,
      prepared.feedback.observations (followerPlayer p.two_le_m i))
  rw [prepared.action_follower, prepared.feedback.observations_eq]
  rfl

/-- The retained follower diagnostic is the literal finish of this record's
prepared follower and computed own feedback. -/
theorem roundRecord_follower_eq_finishFollower (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.followers i = ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) := by
  rw [record.output_eq]
  rfl

/-- Beginning-of-round `StartRound` and successful arm preparation preserve
the actual buffer. A dagger preparation has no ordinary choice state. -/
theorem prepared_choice_buffer_eq_input (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared :
      (record.output.preparation.followers.followers i).configuration =
        .ordinary choice memory) :
    ∃ prior priorMemory,
      record.input.state.followers i = .ordinary prior priorMemory ∧
      choice.buffer = prior.buffer := by
  rw [record.output_eq] at hprepared
  change (DeclaredFollowerLocalRound.prepare rate i
      record.input.row (record.input.state.activations i) record.input.time
      (record.input.active i) (record.input.state.followers i)).configuration =
      .ordinary choice memory at hprepared
  cases hinput : record.input.state.followers i with
  | dagger =>
      simp only [hinput, DeclaredFollowerLocalRound.prepare] at hprepared
      simp at hprepared
  | ordinary prior priorMemory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta record.input.time
          prior priorMemory with
      | error reason =>
          simp only [hinput, DeclaredFollowerLocalRound.prepare, hstart] at hprepared
          simp at hprepared
      | ok result =>
          rcases result with ⟨choiceState, choiceMemory⟩
          simp only [hinput, DeclaredFollowerLocalRound.prepare, hstart] at hprepared
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
              record.input.row (record.input.state.activations i) record.input.time
              choiceState with
          | failure => simp [hoff] at hprepared
          | noOffer =>
              cases harm : ActiveFollowerArmChoice.followerArmChoice choiceState
                  record.input.row record.input.time i none with
              | none => simp [hoff, harm] at hprepared
              | some arm =>
                  simp only [hoff, harm] at hprepared
                  injection hprepared with hchoice hmemory
                  rcases ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
                      prior choiceState priorMemory choiceMemory hstart with
                    ⟨_, _, _, _, _, hbuffer, _, _⟩
                  refine ⟨prior, priorMemory, rfl, ?_⟩
                  calc
                    choice.buffer = choiceState.buffer := by cases hchoice; rfl
                    _ = prior.buffer := hbuffer

          | offer offered =>
              cases harm : ActiveFollowerArmChoice.followerArmChoice choiceState
                  record.input.row record.input.time i (some offered) with
              | none => simp [hoff, harm] at hprepared
              | some arm =>
                  simp only [hoff, harm] at hprepared
                  injection hprepared with hchoice hmemory
                  rcases ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
                      prior choiceState priorMemory choiceMemory hstart with
                    ⟨_, _, _, _, _, hbuffer, _, _⟩
                  refine ⟨prior, priorMemory, rfl, ?_⟩
                  calc
                    choice.buffer = choiceState.buffer := by cases hchoice; rfl
                    _ = prior.buffer := hbuffer

/-- On the computed unoccupied prepared call, chronological local validity
forces checked logging to succeed. The logged buffer is exactly the carried
buffer plus this record's own `logAt`; the actual prepared arm and feedback
are the same tuple retained in `RoundRecord.ownEntries`. -/
theorem actualPreparedLogging_success (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared :
      (record.output.preparation.followers.followers i).configuration =
        .ordinary choice memory)
    (hvalid : localBufferValid choice)
    (hbefore : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1)
    (hunoccupied : choice.status = .unoccupied) :
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i)) choice = .ok logged ∧
      record.output.ownEntries (followerPlayer p.two_le_m i) =
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations
            (followerPlayer p.two_le_m i)) ∧
      logged.buffer = choice.buffer ++ logEmission i record ∧
      localBufferValid logged := by
  have hown := round_ownEntry_eq_prepared i record
  rcases ActiveFollowerLogging.checkedLogging_success_of_chronological
      i record.input.row (record.input.state.activations i) record.input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i)) choice
      hvalid hbefore hunoccupied with
    ⟨logged, hlogging, hbuffer, _, _, hloggedValid⟩
  refine ⟨logged, hlogging, hown, ?_, hloggedValid⟩
  rw [hbuffer]
  simp [logEmission, hprepared, hunoccupied]

/-- The successful prepared logging call is the actual `RoundOutput` DOWN
input diagnostic, before reference recovery runs. -/
theorem actualPrepared_downInput_buffer (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared :
      (record.output.preparation.followers.followers i).configuration =
        .ordinary choice memory)
    (hvalid : localBufferValid choice)
    (hbefore : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1)
    (hunoccupied : choice.status = .unoccupied) :
    ∃ logged,
      (record.output.followers i).downInput = some logged ∧
      logged.buffer = choice.buffer ++ logEmission i record ∧
      localBufferValid logged := by
  rcases actualPreparedLogging_success i record choice memory hprepared hvalid hbefore
      hunoccupied with ⟨logged, hlogging, hown, hbuffer, hloggedValid⟩
  have halign := record.output.preparation.follower_alignment i
  have hloggingPrepared :
      ActiveFollowerLogging.checkedLogging i
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
        choice = .ok logged := by
    rw [halign.1, halign.2.2.2, halign.2.2.1, ← hown]
    exact hlogging
  have hpreparedStep :
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary choice memory := by
    simpa [record.output_eq, ReferenceActivePhysicalStep.step] using hprepared
  have hloggingStep :
      ActiveFollowerLogging.checkedLogging i
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).row
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).activation
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).time
        (((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm,
          (ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (followerPlayer p.two_le_m i)) choice = .ok logged := by
    have h := hloggingPrepared
    rw [record.output_eq] at h
    simpa only [ReferenceActivePhysicalStep.step] using h
  have halignStep :=
    (ReferenceActivePhysicalStep.prepare record.input).follower_alignment i
  refine ⟨logged, ?_, hbuffer, hloggedValid⟩
  rw [record.output_eq]
  simp [ReferenceActivePhysicalStep.step,
    ReferenceActivePhysicalStep.PreparedRound.observeFollower,
    ReferenceActivePhysicalStep.finishFollower,
    ReferenceActivePhysicalStep.recordFollower, hpreparedStep, hloggingStep,
    hunoccupied, halignStep.2.1]
  cases hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).row
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).time
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (followerPlayer p.two_le_m i)) rate logged).outcome with
  | error failure => simp
  | ok postRecord =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i
          ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).row
          ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).time
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (followerPlayer p.two_le_m i)) choice memory postRecord with
      | error failure => simp [hfinish]
      | ok result => simp [hfinish]

/-- Strict timestamp chronology rules out repeated `(round, arm)` keys. -/
theorem pairwise_timestamp_keys_nodup {records : List (BufferRecord p)}
    (hchronological : records.Pairwise (fun a b => a.calendarRound < b.calendarRound)) :
    (records.map fun r => (r.calendarRound, r.pilot)).Nodup := by
  induction records with
  | nil => simp
  | cons head tail ih =>
      simp only [List.pairwise_cons] at hchronological
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨other, hother, hkey⟩ := List.mem_map.mp hmem
        have hlt := hchronological.1 other hother
        have hround := congrArg Prod.fst hkey
        omega
      · exact ih hchronological.2

/-- The typed replay seed itself satisfies the full sparse-buffer domain,
strict time order, and one-based source timestamp bounds. -/
theorem replay_buffer_valid {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    localBufferValid (ReferencePrelaunchFollower.replay eta i row alpha history hn) ∧
      (ReferencePrelaunchFollower.replay eta i row alpha history hn).buffer.Pairwise
        (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ (ReferencePrelaunchFollower.replay eta i row alpha history hn).buffer,
        saved.calendarRound ≤ n := by
  classical
  refine ⟨?_, ReferencePrelaunchFollower.replay_buffer_pairwise eta i row alpha history hn, ?_⟩
  · refine ⟨?_, pairwise_timestamp_keys_nodup
      (ReferencePrelaunchFollower.replay_buffer_pairwise eta i row alpha history hn), ?_⟩
    · intro saved hsaved
      obtain ⟨u, _, hround, _, _, _⟩ :=
        ReferencePrelaunchFollower.replay_buffer_fields eta i row alpha history hn saved hsaved
      constructor <;> omega
    · intro saved hsaved
      obtain ⟨u, _, _, _, hobs, _⟩ :=
        ReferencePrelaunchFollower.replay_buffer_fields eta i row alpha history hn saved hsaved
      obtain ⟨q, hq⟩ := (history u).2.property
      refine ⟨q.val, ?_, ?_⟩
      · exact Nat.le_of_lt_succ q.isLt
      · rw [hobs]
        exact hq
  · intro saved hsaved
    obtain ⟨u, _, hround, _, _, _⟩ :=
      ReferencePrelaunchFollower.replay_buffer_fields eta i row alpha history hn saved hsaved
    omega

/-- Every declared ordinary initialization seed has only typed chronological
replay entries. A fresh or forced launch starts empty; an existing follower
carries its actual replay buffer through `atLaunch`. -/
theorem initialization_ordinary_buffer_valid
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (i : ActiveRoundActions.Follower p.m) :
    localBufferValid (ReferenceInitializationRun.ordinary x b i) ∧
      (ReferenceInitializationRun.ordinary x b i).buffer.Pairwise
        (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ (ReferenceInitializationRun.ordinary x b i).buffer,
        saved.calendarRound ≤ ReferenceInitializationRun.elapsed p b.completed := by
  classical
  by_cases hforced : b.forcedFailure i
  · simp [ReferenceInitializationRun.ordinary, hforced,
      ReferencePrelaunchFollower.forcedAtLaunch, ReferencePrelaunchFollower.initial,
      ActiveFollowerLifecycle.localBufferValid]
  · cases hactivation : b.activation i with
    | none =>
        simp [ReferenceInitializationRun.ordinary, hforced, hactivation,
          ReferencePrelaunchFollower.initial, ActiveFollowerLifecycle.localBufferValid]
    | some activation =>
        have hvalid := replay_buffer_valid (eta := x.eta)
          (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row activation
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (ReferenceInitializationRun.elapsed_le_T p b.completed)
        simpa [ReferenceInitializationRun.ordinary, hforced, hactivation,
          ReferencePrelaunchFollower.atLaunch] using hvalid

/-- The exact follower replay chosen by an actual launched initialization
boundary is the seed buffer for the postlaunch run. Its prelaunch history is
seed data; only later physical emissions receive this module's recordwise
provenance. All original source, reward, carry, history, launch, and handoff
binders of `ofActualLaunchedBoundary` remain explicit. -/
theorem actualLaunchedBoundary_follower_buffer_seed
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
    ∃ state memory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary state memory ∧
      localBufferValid state ∧
      state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ state.buffer,
        saved.calendarRound ≤ BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h) := by
  rcases ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
      learnerSeed hlaunched i with
    ⟨state, memory, hconfiguration, hstate, _, _, _, _, _, _, _⟩
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let finished := ReferenceInitializationRun.finishBlock x b h
  have hvalid := initialization_ordinary_buffer_valid x finished
    (ActualReferenceInitializationBlock.refFollower i)
  rw [← hstate] at hvalid
  have hcompleted := (ReferenceInitializationRun.finishBlock_equations x b h).1
  have hblock : ReferenceInitializationRun.elapsed p finished.completed =
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) := by
    rw [hcompleted]
    simp [ReferenceInitializationRun.elapsed, ReferenceInitializationRun.nextBlock,
      BootstrapObservedFollower.blockStop]
  refine ⟨state, memory, hconfiguration, hvalid.1, hvalid.2.1, ?_⟩
  intro saved hsaved
  calc
    saved.calendarRound ≤ ReferenceInitializationRun.elapsed p finished.completed :=
      hvalid.2.2 saved hsaved
    _ = BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) := hblock

/-- The reference-only DOWN cut changes only the buffer at its actual
accepted constructor. Parser rejection and raw mismatch both keep the
pre-recovery logged buffer; skips and failures have no installed result. -/
theorem downTransition_buffer_alternatives
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    match ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state with
    | .accepted _ after _ _ _ _ _ => after.buffer = []
    | .decodeOrParseRejected _ after _ => after.buffer = state.buffer
    | .parsedButUnaccepted _ after _ _ => after.buffer = state.buffer
    | .skipped before _ => before.buffer = state.buffer
    | .inputFailure _ _ => True
    | .outputFailure _ _ => True := by
  classical
  unfold ActiveFollowerDownAcceptance.downTransition
  repeat' (first | split_ifs | simp_all)
  all_goals
    generalize hparsed : OrdinaryMessageCodec.parseDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (Option.map
        (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row t feedback rate state).2) = parsed
    cases parsed with
    | none => simp_all
    | some message =>
        simp only []
        split_ifs <;> try simp_all
        all_goals
          let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message t
            (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate message t state
              (by assumption)) row
          cases hrecover : ActiveFollowerDownAcceptance.checkedRecovery p rate message state
              scan.endpoint with
          | error failure => simp_all [scan]
          | ok recovered => simp_all [scan]

theorem referenceDownCut_buffer_alternatives
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    match (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).outcome with
    | .accepted _ after _ _ _ _ _ => after.buffer = []
    | .decodeOrParseRejected _ after _ => after.buffer = state.buffer
    | .parsedButUnaccepted _ after _ _ => after.buffer = state.buffer
    | .skipped before _ => before.buffer = state.buffer
    | .inputFailure _ _ => True
    | .outputFailure _ _ => True := by
  classical
  let cut := ReferenceDownReception.referenceDownCut p view i row t feedback rate state
  change match cut.outcome with
    | .accepted _ after _ _ _ _ _ => after.buffer = []
    | .decodeOrParseRejected _ after _ => after.buffer = state.buffer
    | .parsedButUnaccepted _ after _ _ => after.buffer = state.buffer
    | .skipped before _ => before.buffer = state.buffer
    | .inputFailure _ _ => True
    | .outputFailure _ _ => True
  by_cases hmismatch : ReferenceDownReception.rawMismatch cut
  · have hbranches :
        ActiveFollowerDownAcceptance.downSelected p i row t ∧
          state.status = .unoccupied ∧
          ActiveFollowerDownAcceptance.registerInputDomain p rate state ∧
          ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch ∧
          ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
      dsimp only [cut, ReferenceDownReception.rawMismatch] at hmismatch
      unfold ReferenceDownReception.referenceDownCut at hmismatch
      split_ifs at hmismatch
      all_goals simp_all
    rcases hbranches with ⟨hselected, hstatus, hregisters, hbatch, hbuffer⟩
    have hmismatch' : ReferenceDownReception.rawMismatch
        (ReferenceDownReception.referenceDownCut p view i row t feedback rate state) := by
      simpa only [cut] using hmismatch
    have hpreserved := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
      view i row t feedback rate state hselected hstatus hregisters hbatch hbuffer hmismatch'
    rw [hpreserved.1]
  · have hmatch : ¬ ReferenceDownReception.rawMismatch
        (ReferenceDownReception.referenceDownCut p view i row t feedback rate state) := by
      simpa only [cut] using hmismatch
    have hordinary := ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
      view i row t feedback rate state hmatch
    rw [hordinary]
    exact downTransition_buffer_alternatives i row t feedback state

/-- The real release and finish stages preserve whichever buffer the
successful service or DOWN stage supplied. -/
theorem releaseAndFinish_buffer_preserved (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState postState output : ReferencePrelaunchFollower.State p rate.eta)
    (memory outputMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation
      choiceState memory postState = .ok (output, outputMemory)) :
    output.buffer = postState.buffer := by
  classical
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState postState with
  | error reason => simp [hrelease] at hfinish
  | ok released =>
      cases hfinal : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error reason => simp [hrelease, hfinal] at hfinish
      | ok result =>
          rcases result with ⟨finished, finishedMemory⟩
          have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta t row
            released finished memory finishedMemory hfinal
          have hpair : (output, outputMemory) = (finished, finishedMemory) := by
            have hresult : finished = output ∧ finishedMemory = outputMemory := by
              simpa [hrelease, hfinal] using hfinish
            exact Prod.ext hresult.1.symm hresult.2.symm
          have hout : output = finished := congrArg Prod.fst hpair
          subst output
          rw [hframe]
          have hbuffer : released.buffer = postState.buffer := by
            unfold ActiveFollowerLifecycle.releaseAfterService at hrelease
            by_cases hpending : choiceState.status = .pending
            · by_cases hpreRegs : ActiveFollowerLifecycle.localStateDomainValid choiceState
              · cases hlast : choiceState.lastDown with
                | none => simp [hpending, hpreRegs, hlast] at hrelease
                | some M =>
                    by_cases htime : M.val.sigma ≤ t.val
                    · by_cases hpostRegs : ActiveFollowerLifecycle.localStateDomainValid postState
                      · let candidate := if ActiveFollowerLifecycle.releaseCondition rate.eta i
                            (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation M then
                            { postState with status := .released } else postState
                        have hguard : candidate.status = .unoccupied ∨
                            (∃ M', candidate.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1) := by
                          by_contra hguard
                          simp [hpending, hpreRegs, hlast, htime, hpostRegs, hguard,
                            candidate] at hrelease
                        have heq : candidate = released := by
                          simp [hpending, hpreRegs, hlast, htime, hpostRegs, hguard,
                            candidate] at hrelease
                          exact hrelease
                        rw [← heq]
                        by_cases hcondition : ActiveFollowerLifecycle.releaseCondition rate.eta i
                            (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation M
                        · simp [candidate, hcondition]
                        · simp [candidate, hcondition]
                      · simp [hpending, hpreRegs, hlast, htime, hpostRegs] at hrelease
                    · simp [hpending, hpreRegs, hlast, htime] at hrelease
              · simp [hpending, hpreRegs] at hrelease
            · simp [hpending] at hrelease
              exact (congrArg (fun state => state.buffer) hrelease).symm
          exact hbuffer

/-- An ordinary actual follower endpoint exposes both successful stages of
its literal record/DOWN and release/finish pipeline. -/
theorem finishFollower_ordinary_decompose
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (houtput : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation state memory post = .ok (next, nextMemory) := by
  cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm
      observation state).result with
  | error failure =>
      simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord] at houtput
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory post with
      | error failure =>
          simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord,
            hfinish] at houtput
      | ok result =>
          rcases result with ⟨finished, finishedMemory⟩
          have hpair : (finished, finishedMemory) = (next, nextMemory) := by
            have h := houtput
            simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord,
              hfinish] at h
            rcases h with ⟨hstate, hmemory⟩
            exact Prod.ext hstate hmemory
          have hfinish' : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post =
                .ok (next, nextMemory) := by
            rw [hfinish]
            exact congrArg Except.ok hpair
          exact ⟨post, rfl, hfinish'⟩

/-- An actual unoccupied prepared endpoint has exactly the successful logging
append, unless its actual reference DOWN diagnostic accepted and cleared it.
All inputs are fields of this record's prepared state and output. -/
theorem actualUnoccupiedEndpoint_buffer
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hunoccupied : choice.status = .unoccupied)
    (hvalid : localBufferValid choice)
    (hbefore : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1)
    (hnext : (record.output.followers i).configuration = .ordinary next nextMemory) :
    next.buffer = bufferFoldStep i choice.buffer record := by
  classical
  rcases actualPreparedLogging_success i record choice memory hprepared hvalid hbefore
      hunoccupied with ⟨logged, hlogging, hown, hloggedBuffer, hloggedValid⟩
  have halign := record.output.preparation.follower_alignment i
  have hloggingPrepared : ActiveFollowerLogging.checkedLogging
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) choice =
      .ok logged := by
    rw [halign.2.1, halign.1, halign.2.2.2, halign.2.2.1, ← hown]
    exact hlogging
  have hfinishFollower := roundRecord_follower_eq_finishFollower i record
  rw [hfinishFollower] at hnext
  rcases finishFollower_ordinary_decompose
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
      choice memory next nextMemory hprepared hnext with
    ⟨post, hrecordResult, hfinish⟩
  let cut := ReferenceDownReception.referenceDownCut p
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
    rate logged
  have hresultDown : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post := by
    simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied,
      hloggingPrepared, cut] using hrecordResult
  have hdownDiag : (record.output.followers i).down = some cut := by
    rw [roundRecord_follower_eq_finishFollower i record]
    simp [ReferenceActivePhysicalStep.finishFollower, hprepared,
      ReferenceActivePhysicalStep.recordFollower, hunoccupied, hloggingPrepared,
      cut, hresultDown, hfinish]
  have hbufferFinal := releaseAndFinish_buffer_preserved
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
    choice post next memory nextMemory hfinish
  have hcutBuffer := referenceDownCut_buffer_alternatives
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) logged
  cases houtcome : cut.outcome with
  | accepted before after raw reply scan registers lastService =>
      have hafterBuffer : after.buffer = [] := by
        simpa [cut, houtcome] using hcutBuffer
      have hafterPost : after = post := by
        simp only [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown
        exact Except.ok.inj hresultDown
      have hreset : acceptedDownReset i record := by
        exact ⟨cut, hdownDiag, before, after, raw, reply, scan, registers,
          lastService, houtcome⟩
      calc
        next.buffer = post.buffer := hbufferFinal
        _ = after.buffer := congrArg (fun state => state.buffer) hafterPost.symm
        _ = [] := hafterBuffer
        _ = bufferFoldStep i choice.buffer record := by
          simp [bufferFoldStep, hreset]
  | decodeOrParseRejected before after raw =>
      have hafterBuffer : after.buffer = logged.buffer := by
        simpa [cut, houtcome] using hcutBuffer
      have hafterPost : after = post := by
        simp only [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown
        exact Except.ok.inj hresultDown
      have hnotReset : ¬ acceptedDownReset i record := by
        rintro ⟨other, hother, obefore, oafter, oraw, oreply, oscan, oregisters,
          olastService, haccepted⟩
        have heq : other = cut := Option.some.inj (hother.symm.trans hdownDiag)
        subst other
        simp [houtcome] at haccepted
      calc
        next.buffer = post.buffer := hbufferFinal
        _ = after.buffer := congrArg (fun state => state.buffer) hafterPost.symm
        _ = logged.buffer := hafterBuffer
        _ = choice.buffer ++ logEmission i record := hloggedBuffer
        _ = bufferFoldStep i choice.buffer record := by
          simp [bufferFoldStep, hnotReset]
  | parsedButUnaccepted before after raw reply =>
      have hafterBuffer : after.buffer = logged.buffer := by
        simpa [cut, houtcome] using hcutBuffer
      have hafterPost : after = post := by
        simp only [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown
        exact Except.ok.inj hresultDown
      have hnotReset : ¬ acceptedDownReset i record := by
        rintro ⟨other, hother, obefore, oafter, oraw, oreply, oscan, oregisters,
          olastService, haccepted⟩
        have heq : other = cut := Option.some.inj (hother.symm.trans hdownDiag)
        subst other
        simp [houtcome] at haccepted
      calc
        next.buffer = post.buffer := hbufferFinal
        _ = after.buffer := congrArg (fun state => state.buffer) hafterPost.symm
        _ = logged.buffer := hafterBuffer
        _ = choice.buffer ++ logEmission i record := hloggedBuffer
        _ = bufferFoldStep i choice.buffer record := by
          simp [bufferFoldStep, hnotReset]
  | skipped before reason =>
      have hbeforeBuffer : before.buffer = logged.buffer := by
        simpa [cut, houtcome] using hcutBuffer
      have hbeforePost : before = post := by
        simp only [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown
        exact Except.ok.inj hresultDown
      have hnotReset : ¬ acceptedDownReset i record := by
        rintro ⟨other, hother, obefore, oafter, oraw, oreply, oscan, oregisters,
          olastService, haccepted⟩
        have heq : other = cut := Option.some.inj (hother.symm.trans hdownDiag)
        subst other
        simp [houtcome] at haccepted
      calc
        next.buffer = post.buffer := hbufferFinal
        _ = before.buffer := congrArg (fun state => state.buffer) hbeforePost.symm
        _ = logged.buffer := hbeforeBuffer
        _ = choice.buffer ++ logEmission i record := hloggedBuffer
        _ = bufferFoldStep i choice.buffer record := by
          simp [bufferFoldStep, hnotReset]
  | inputFailure before reason =>
      exact False.elim (by
        simp [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown)
  | outputFailure before reason =>
      exact False.elim (by
        simp [DeclaredFollowerLocalRound.consumeDownResult, houtcome] at hresultDown)

/-- Every ordinary endpoint of an actual record has the literal source
buffer transition. StartRound/preparation carry the preceding buffer; an
unoccupied endpoint uses checked logging and the actual DOWN outcome, while
an occupied endpoint uses checked service and has no DOWN reset. -/
theorem actualFollowerEndpoint_buffer
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary before beforeMemory)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hnext : (record.output.followers i).configuration = .ordinary next nextMemory)
    (hvalid : localBufferValid before)
    (hbefore : ∀ saved ∈ before.buffer,
      saved.calendarRound < record.input.time.val + 1) :
    next.buffer = bufferFoldStep i before.buffer record := by
  classical
  rcases prepared_choice_buffer_eq_input i record choice choiceMemory hprepared with
    ⟨prior, priorMemory, hprior, hchoiceBuffer⟩
  have hpriorBuffer : prior.buffer = before.buffer := by
    have hconfiguration :
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary prior priorMemory =
          DeclaredFollowerLocalRound.LocalConfiguration.ordinary before beforeMemory :=
      hprior.symm.trans hinput
    cases hconfiguration
    rfl
  have hchoiceBuffer : choice.buffer = before.buffer := hchoiceBuffer.trans hpriorBuffer
  have hvalidChoice : localBufferValid choice := by
    simpa [ActiveFollowerLifecycle.localBufferValid, hchoiceBuffer] using hvalid
  have hbeforeChoice : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1 := by
    intro saved hsaved
    rw [hchoiceBuffer] at hsaved
    exact hbefore saved hsaved
  have hfinishFollower := roundRecord_follower_eq_finishFollower i record
  have hnext' := hnext
  rw [hfinishFollower] at hnext'
  by_cases hstatus : choice.status = .unoccupied
  · have htransition := actualUnoccupiedEndpoint_buffer i record choice choiceMemory
      next nextMemory hprepared hstatus hvalidChoice hbeforeChoice hnext
    rw [hchoiceBuffer] at htransition
    exact htransition
  · rcases finishFollower_ordinary_decompose
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i)
        (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
        choice choiceMemory next nextMemory hprepared hnext' with
      ⟨post, hrecordResult, hfinish⟩
    cases hserviceResult : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) choice with
    | failure =>
        simp [ReferenceActivePhysicalStep.recordFollower, hstatus,
          DeclaredFollowerLocalRound.recordOrServiceThenDown, hserviceResult] at hrecordResult
    | success result =>
        have hpost : result.output = post := by
          simpa [ReferenceActivePhysicalStep.recordFollower, hstatus,
            DeclaredFollowerLocalRound.recordOrServiceThenDown, hserviceResult] using hrecordResult
        have hserviceBuffer : result.output.buffer = choice.buffer := by
          rw [result.queueUpdate]
          exact (ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
            rate.n choice result.arrival).2.2.1
        have hpostBuffer : post.buffer = before.buffer := by
          calc
            post.buffer = result.output.buffer := congrArg
              (fun state => state.buffer) hpost.symm
            _ = choice.buffer := hserviceBuffer
            _ = before.buffer := hchoiceBuffer
        have hbufferFinal := releaseAndFinish_buffer_preserved
          (record.output.preparation.followers.followers i).follower
          (record.output.preparation.followers.followers i).row
          (record.output.preparation.followers.followers i).time
          (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
          choice post next choiceMemory nextMemory hfinish
        have hdownDiag : (record.output.followers i).down = none := by
          rw [roundRecord_follower_eq_finishFollower i record]
          simp [ReferenceActivePhysicalStep.finishFollower, hprepared,
            ReferenceActivePhysicalStep.recordFollower, hstatus,
            DeclaredFollowerLocalRound.recordOrServiceThenDown, hserviceResult, hpost, hfinish]
        have hnotReset : ¬ acceptedDownReset i record := by
          rintro ⟨cut, hcut, beforeState, afterState, raw, reply, scan, registers,
            lastService, houtcome⟩
          rw [hdownDiag] at hcut
          cases hcut
        have hempty : logEmission i record = [] := by
          simp [logEmission, hprepared, hstatus]
        calc
          next.buffer = post.buffer := hbufferFinal
          _ = before.buffer := hpostBuffer
          _ = bufferFoldStep i before.buffer record := by
            simp [bufferFoldStep, hnotReset, hempty]

/-- A successful reset record's own current log is not retained. -/
theorem acceptedDownReset_fold_clears (i : Fin (p.m - 1))
    (seed : List (BufferRecord p))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hreset : acceptedDownReset i record) :
    bufferFold i seed (records ++ [record]) = [] := by
  classical
  simp [bufferFold, bufferFoldStep, List.foldl_append, hreset]

/-- General fold law pairing the physical buffer transition with the suffix
after the most recent accepted reset. The reset record clears both the seed
and every earlier emission; later emissions append in source order. -/
theorem bufferFold_suffix_from (i : Fin (p.m - 1))
    (initialSuffix : Bool × List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)))
    (baseSeed currentBuffer : List (BufferRecord p))
    (hstart : currentBuffer = if initialSuffix.1 then
      initialSuffix.2.flatMap (logEmission i)
      else baseSeed ++ initialSuffix.2.flatMap (logEmission i))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) :
    records.foldl (bufferFoldStep i) currentBuffer =
      let suffix := records.foldl (suffixFoldStep i) initialSuffix
      if suffix.1 then suffix.2.flatMap (logEmission i)
      else baseSeed ++ suffix.2.flatMap (logEmission i) := by
  classical
  induction records generalizing initialSuffix currentBuffer with
  | nil =>
      change currentBuffer = if initialSuffix.1 then
        initialSuffix.2.flatMap (logEmission i)
        else baseSeed ++ initialSuffix.2.flatMap (logEmission i)
      exact hstart
  | cons record records ih =>
      by_cases hreset : acceptedDownReset i record
      · simpa [List.foldl_cons, bufferFoldStep, suffixFoldStep, hreset] using
          ih (true, []) [] (by simp)
      · have hstart' : currentBuffer ++ logEmission i record =
            if initialSuffix.1 then
              (initialSuffix.2 ++ [record]).flatMap (logEmission i)
            else baseSeed ++ (initialSuffix.2 ++ [record]).flatMap (logEmission i) := by
          rw [hstart]
          by_cases hseen : initialSuffix.1
          · simp [hseen, List.flatMap_append]
          · simp [hseen, List.flatMap_append, List.append_assoc]
        simpa [List.foldl_cons, bufferFoldStep, suffixFoldStep, hreset] using
          ih (initialSuffix.1, initialSuffix.2 ++ [record])
            (currentBuffer ++ logEmission i record) hstart'

/-- The literal reset fold is exactly the seed plus emissions after the last
actual accepted DOWN, with the accepted DOWN's own emission discarded. -/
theorem bufferFold_eq_lastAcceptedDown_suffix (i : Fin (p.m - 1))
    (seed : List (BufferRecord p))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) :
    bufferFold i seed records =
      let suffix := recordsAfterLastAcceptedDown i records
      if suffix.1 then suffix.2.flatMap (logEmission i)
      else seed ++ suffix.2.flatMap (logEmission i) := by
  change records.foldl (bufferFoldStep i) seed =
    let suffix := records.foldl (suffixFoldStep i) (false, [])
    if suffix.1 then suffix.2.flatMap (logEmission i)
    else seed ++ suffix.2.flatMap (logEmission i)
  exact bufferFold_suffix_from i (false, []) seed seed (by simp) records

/-- A single physical round emits at most one sparse record, hence its own
emission is strictly pairwise in source timestamp. -/
theorem logEmission_pairwise (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (logEmission i record).Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
  classical
  let prepared := record.output.preparation.followers.followers i
  cases hconfiguration : prepared.configuration with
  | dagger => simp [logEmission, prepared, hconfiguration]
  | ordinary state memory =>
      by_cases hunoccupied : state.status = .unoccupied
      · by_cases htests : SparseCalendarReplay.loggingTestsPass
            (ReferencePrelaunchFollower.loggingRound i record.input.row
              (record.input.state.activations i) record.input.time
              (record.output.ownEntries (followerPlayer p.two_le_m i)))
        · simp [logEmission, prepared, hconfiguration, hunoccupied,
            ReferencePrelaunchFollower.logAt, htests]
        · simp [logEmission, prepared, hconfiguration, hunoccupied,
            ReferencePrelaunchFollower.logAt, htests]
      · simp [logEmission, prepared, hconfiguration, hunoccupied]

/-- Every emitted timestamp is the one-based source coordinate of that same
actual round record. -/
theorem logEmission_source_timestamp (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (saved : BufferRecord p) (hsaved : saved ∈ logEmission i record) :
    saved.calendarRound = record.input.time.val + 1 := by
  obtain ⟨_, htime, _, _, _, _⟩ := logEmission_member_fields i record saved hsaved
  exact htime

/-- Flattening a strictly ordered record list preserves strict timestamp
order when each record emits only at its own source coordinate. -/
theorem emissions_of_pairwise_records (i : Fin (p.m - 1))
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (htimes : List.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) records) :
    List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
      (List.flatMap (logEmission i) records) := by
  induction records with
  | nil => simp
  | cons record rest ih =>
      simp only [List.pairwise_cons] at htimes
      rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨logEmission_pairwise i record, ih htimes.2, ?_⟩
      intro earlier hearlier later hlater
      rcases List.mem_flatMap.mp hlater with ⟨laterRecord, hlaterRecord, hlaterEntry⟩
      have hsource := htimes.1 laterRecord hlaterRecord
      have hearlierTime := logEmission_source_timestamp i record earlier hearlier
      have hlaterTime := logEmission_source_timestamp i laterRecord later hlaterEntry
      omega

/-- The record suffix chosen by the actual accepted-DOWN reset fold is a
literal sublist of the processed physical records. -/
theorem suffixFold_second_sublist (i : Fin (p.m - 1))
    (initialSuffix : Bool × List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    (records.foldl (suffixFoldStep i) initialSuffix).2.Sublist
      (initialSuffix.2 ++ records) := by
  induction records generalizing initialSuffix with
  | nil => simp
  | cons record rest ih =>
      rw [List.foldl_cons]
      by_cases hreset : acceptedDownReset i record
      · have htail := ih (true, [])
        have hrest : rest.Sublist (initialSuffix.2 ++ record :: rest) := by
          exact (List.sublist_cons_self record rest).trans
            (List.sublist_append_right initialSuffix.2 (record :: rest))
        simpa [suffixFoldStep, hreset] using htail.trans hrest
      · have htail := ih (initialSuffix.1, initialSuffix.2 ++ [record])
        simpa [suffixFoldStep, hreset, List.append_assoc] using htail

/-- Consecutive zero-based calendar coordinates are strictly ordered. -/
theorem calendar_pairwise_lt (start count : ℕ) :
    (ReferenceActivePhysicalHorizon.calendar start count).Pairwise (fun a b => a < b) := by
  induction count generalizing start with
  | zero => simp [ReferenceActivePhysicalHorizon.calendar]
  | succ count ih =>
      simp only [ReferenceActivePhysicalHorizon.calendar, List.range'_succ,
        List.pairwise_cons]
      constructor
      · intro later hlater
        obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hlater
        omega
      · exact ih (start + 1)

/-- The exact computed execution records have strict source-time order. The
calendar equality is the project's `run_time_values` theorem, so this result
does not assume an externally supplied path. -/
theorem run_record_times_pairwise (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    List.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val)
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) := by
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan hmode
  have hcalendar := calendar_pairwise_lt start count
  have hmapped : List.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val)
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) := by
    exact List.pairwise_map.mp (htimes ▸ hcalendar)
  exact hmapped

/-- Flattening the actual per-round emissions preserves strict timestamp
order: each entry has its source round's one-based timestamp, and the run
calendar advances strictly. -/
theorem run_emissions_pairwise (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
      (List.flatMap (logEmission i)
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) := by
  exact emissions_of_pairwise_records i
    (run_record_times_pairwise initial rows selected rewards start count hspan hmode)

/-- Therefore the actual run's emitted list has no duplicate `(round, arm)`
keys. This is a consequence of strict chronological timestamps. -/
theorem run_emissions_keys_nodup (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    List.Nodup (List.map (fun saved => (saved.calendarRound, saved.pilot))
      (List.flatMap (logEmission i)
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records)) :=
  pairwise_timestamp_keys_nodup (run_emissions_pairwise i initial rows selected rewards
    start count hspan hmode)

/-- Every actual emitted timestamp is at or after the first source round in
the requested interval. -/
theorem run_emission_timestamp_lower (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (saved : BufferRecord p)
    (hsaved : saved ∈ List.flatMap (logEmission i)
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) :
    start + 1 ≤ saved.calendarRound := by
  rcases List.mem_flatMap.mp hsaved with ⟨record, hrecord, hentry⟩
  have htime := logEmission_source_timestamp i record saved hentry
  have htimeMem : record.input.time.val ∈
      ReferenceActivePhysicalHorizon.calendar start count := by
    rw [← ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
      start count hspan hmode]
    exact List.mem_map.mpr ⟨record, hrecord, rfl⟩
  have hstart := List.left_le_of_mem_range' (by
    simpa only [ReferenceActivePhysicalHorizon.calendar] using htimeMem)
  omega

/-- Every emitted timestamp is no later than the first source coordinate
after the actual run. -/
theorem run_emission_timestamp_upper (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (saved : BufferRecord p)
    (hsaved : saved ∈ List.flatMap (logEmission i)
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) :
    saved.calendarRound ≤ start + count := by
  rcases List.mem_flatMap.mp hsaved with ⟨record, hrecord, hentry⟩
  have htime := logEmission_source_timestamp i record saved hentry
  have htimeMem : record.input.time.val ∈
      ReferenceActivePhysicalHorizon.calendar start count := by
    rw [← ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
      start count hspan hmode]
    exact List.mem_map.mpr ⟨record, hrecord, rfl⟩
  obtain ⟨offset, hoffset, hvalue⟩ := List.mem_range'.mp (by
    simpa only [ReferenceActivePhysicalHorizon.calendar] using htimeMem)
  omega

/-- The emissions strictly after the most recent accepted actual DOWN remain
chronological, since their source records are a sublist of the actual run. -/
theorem run_lastDown_suffix_emissions_pairwise (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    let suffix := recordsAfterLastAcceptedDown i
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records
    List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
      (suffix.2.flatMap (logEmission i)) := by
  let records := (ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode).records
  have hrecords := run_record_times_pairwise initial rows selected rewards start count hspan hmode
  let suffix := recordsAfterLastAcceptedDown i records
  change List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
    (suffix.2.flatMap (logEmission i))
  apply emissions_of_pairwise_records i
  apply List.Pairwise.sublist
    (suffixFold_second_sublist i (false, []) records)
  exact hrecords

/-- With an explicitly typed seed at or before the run boundary, the literal
last-accepted-DOWN formula is strictly chronological. The reset record and
every earlier emission are omitted by `recordsAfterLastAcceptedDown`. -/
theorem run_bufferFold_pairwise (i : Fin (p.m - 1))
    (seed : List (BufferRecord p))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : seed.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hseedTime : ∀ saved ∈ seed, saved.calendarRound ≤ start) :
    List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
      (bufferFold i seed
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records) := by
  rw [bufferFold_eq_lastAcceptedDown_suffix]
  let records := (ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode).records
  let suffix := recordsAfterLastAcceptedDown i records
  have hsuffixPair : List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
      (suffix.2.flatMap (logEmission i)) := by
    simpa [records, suffix] using run_lastDown_suffix_emissions_pairwise i initial rows
      selected rewards start count hspan hmode
  change List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
    (if suffix.1 then suffix.2.flatMap (logEmission i)
      else seed ++ suffix.2.flatMap (logEmission i))
  cases hcondition : suffix.1 with
  | false =>
      change List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
        (seed ++ suffix.2.flatMap (logEmission i))
      rw [List.pairwise_append]
      refine ⟨hseed, hsuffixPair, ?_⟩
      intro earlier hearlier later hlater
      rcases List.mem_flatMap.mp hlater with ⟨record, hrecordSuffix, hentry⟩
      have hrecordRun : record ∈ records :=
        (suffixFold_second_sublist i (false, []) records).subset hrecordSuffix
      have hentryRun : later ∈ List.flatMap (logEmission i) records :=
        List.mem_flatMap.mpr ⟨record, hrecordRun, hentry⟩
      have hlower := run_emission_timestamp_lower i initial rows selected rewards
        start count hspan hmode later hentryRun
      have hearlierTime := hseedTime earlier hearlier
      omega
  | true =>
      change List.Pairwise (fun a b => a.calendarRound < b.calendarRound)
        (suffix.2.flatMap (logEmission i))
      exact hsuffixPair

/-- Every retained entry is either original seed data or an emission of an
actual processed record; resetting never creates a record. -/
theorem bufferFold_mem_origin (i : Fin (p.m - 1)) (seed : List (BufferRecord p))
    (records : List (RoundRecord (p := p) (rate := rate)))
    (saved : BufferRecord p) (hsaved : saved ∈ bufferFold i seed records) :
    saved ∈ seed ∨ ∃ record ∈ records, saved ∈ logEmission i record := by
  classical
  rw [bufferFold_eq_lastAcceptedDown_suffix] at hsaved
  let suffix := recordsAfterLastAcceptedDown i records
  have hsub := suffixFold_second_sublist i (false, []) records
  have hnew (h : saved ∈ suffix.2.flatMap (logEmission i)) :
      ∃ record ∈ records, saved ∈ logEmission i record := by
    obtain ⟨record, hrecord, hentry⟩ := List.mem_flatMap.mp h
    exact ⟨record, hsub.subset hrecord, hentry⟩
  change saved ∈ (if suffix.1 then suffix.2.flatMap (logEmission i)
    else seed ++ suffix.2.flatMap (logEmission i)) at hsaved
  cases hseen : suffix.1 with
  | true => exact Or.inr (hnew (by simpa [hseen] using hsaved))
  | false =>
      rcases List.mem_append.mp (by
        simpa only [hseen, Bool.false_eq_true, ite_false] using hsaved) with hold | hentry
      · exact Or.inl hold
      · exact Or.inr (hnew hentry)

/-- Timestamp and quantization domains of every newly emitted record follow
from the actual physical time and typed own feedback. -/
theorem logEmission_domains (i : Fin (p.m - 1))
    (record : RoundRecord (p := p) (rate := rate)) (saved : BufferRecord p)
    (hsaved : saved ∈ logEmission i record) :
    (1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
      ∃ q : ℕ, q ≤ D p ∧ saved.observation.val = (q : ℝ) / (D p : ℝ) := by
  obtain ⟨own, htime, _, hobs, _, _⟩ := logEmission_member_fields i record saved hsaved
  obtain ⟨q, hq⟩ := own.2.property
  refine ⟨⟨by omega, by have := record.input.time.isLt; omega⟩,
    q.val, Nat.le_of_lt_succ q.isLt, ?_⟩
  rw [hobs]
  exact hq

/-- Safety of the literal reset fold, from explicit chronological seed data.
No successful-run or no-dagger premise occurs in this list calculation. -/
theorem run_bufferFold_safety (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (hvalid : localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start) :
    let retained := bufferFold i seed.buffer
      (run initial rows selected rewards start count hspan hmode).records
    localBufferValid { seed with buffer := retained } ∧
      retained.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ retained, saved.calendarRound ≤ start + count := by
  let records := (run initial rows selected rewards start count hspan hmode).records
  have hretained := run_bufferFold_pairwise i seed.buffer initial rows selected rewards
    start count hspan hmode hpair htime
  refine ⟨⟨?_, pairwise_timestamp_keys_nodup hretained, ?_⟩, hretained, ?_⟩
  · intro saved hsaved
    rcases bufferFold_mem_origin i seed.buffer records saved hsaved with hold | hnew
    · exact hvalid.1 saved hold
    · obtain ⟨record, _, hentry⟩ := hnew
      exact (logEmission_domains i record saved hentry).1
  · intro saved hsaved
    rcases bufferFold_mem_origin i seed.buffer records saved hsaved with hold | hnew
    · exact hvalid.2.2 saved hold
    · obtain ⟨record, _, hentry⟩ := hnew
      exact (logEmission_domains i record saved hentry).2
  · intro saved hsaved
    rcases bufferFold_mem_origin i seed.buffer records saved hsaved with hold | hnew
    · exact (htime saved hold).trans (Nat.le_add_right start count)
    · obtain ⟨record, hrecord, hentry⟩ := hnew
      exact run_emission_timestamp_upper i initial rows selected rewards start count
        hspan hmode saved (List.mem_flatMap.mpr ⟨record, hrecord, hentry⟩)

/-- At every ordinary endpoint of the computed horizon, the actual buffer is
exactly the carried seed and chronological eligible emissions, cleared by
actual accepted DOWN diagnostics. Dagger absorption excludes a dagger
predecessor; failures remain branches of the computed execution. -/
theorem run_buffer_provenance (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (next : ReferencePrelaunchFollower.State p rate.eta) (nextMemory : LocalMemory p)
    (hnext : (run initial rows selected rewards start count hspan hmode).finalState.followers i =
      .ordinary next nextMemory) :
    next.buffer = bufferFold i seed.buffer
      (run initial rows selected rewards start count hspan hmode).records := by
  induction count generalizing next nextMemory with
  | zero =>
      rw [run_zero_final] at hnext
      rw [run_zero_records]
      have heq := hseed.symm.trans hnext
      cases heq
      rfl
  | succ count ih =>
      let priorRun := run initial rows selected rewards start count (by omega) hmode
      let entry : CalendarEntry p start := ⟨start + count, by omega, by omega⟩
      let input := roundInputAt initial rows selected rewards start hmode priorRun entry
      let record : RoundRecord (p := p) (rate := rate) := ⟨input, step input, rfl⟩
      have hfinal : record.output.next.followers i = .ordinary next nextMemory := by
        rw [run_successor_step] at hnext
        change (step input).next.followers i = .ordinary next nextMemory at hnext
        exact hnext
      have hrecordNext : (record.output.followers i).configuration =
          .ordinary next nextMemory := hfinal
      have hprior : ∃ before beforeMemory,
          priorRun.finalState.followers i = .ordinary before beforeMemory := by
        cases hc : priorRun.finalState.followers i with
        | ordinary before beforeMemory => exact ⟨before, beforeMemory, rfl⟩
        | dagger =>
            have hd := step_follower_dagger input i hc
            rw [hfinal] at hd
            cases hd
      obtain ⟨before, beforeMemory, hbefore⟩ := hprior
      have hbuffer := ih (by omega) before beforeMemory hbefore
      have hsafe := run_bufferFold_safety i seed initial rows selected rewards start count
        (by omega) hmode hvalid hpair htime
      have hbeforeValid : localBufferValid before := by
        simpa only [localBufferValid, hbuffer] using hsafe.1
      have hbeforeTime : ∀ saved ∈ before.buffer,
          saved.calendarRound < record.input.time.val + 1 := by
        intro saved hsaved
        rw [hbuffer] at hsaved
        have := hsafe.2.2 saved hsaved
        change saved.calendarRound < start + count + 1
        omega
      have hchoice : ∃ choice choiceMemory,
          (record.output.preparation.followers.followers i).configuration =
            .ordinary choice choiceMemory := by
        cases hc : (record.output.preparation.followers.followers i).configuration with
        | ordinary choice choiceMemory => exact ⟨choice, choiceMemory, rfl⟩
        | dagger =>
            have hd := (finishFollower_dagger
              record.output.preparation.coordinator.downView
              (record.output.preparation.followers.followers i)
              (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
              hc).1
            rw [← roundRecord_follower_eq_finishFollower i record, hrecordNext] at hd
            cases hd
      obtain ⟨choice, choiceMemory, hchoice⟩ := hchoice
      have htransition := actualFollowerEndpoint_buffer i record before beforeMemory
        choice choiceMemory next nextMemory hbefore hchoice hrecordNext hbeforeValid hbeforeTime
      rw [run_successor_step]
      change next.buffer = bufferFold i seed.buffer (priorRun.records ++ [record])
      rw [hbuffer] at htransition
      simpa only [bufferFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
        using htransition

/-- Ordinary endpoints inherit strict chronology, checked sparse domains,
unique keys, and timestamps strictly before the next source round. The
statement applies separately to every prefix length, including zero. -/
theorem run_buffer_chronological (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (seed : ReferencePrelaunchFollower.State p rate.eta) (seedMemory : LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (next : ReferencePrelaunchFollower.State p rate.eta) (nextMemory : LocalMemory p)
    (hnext : (run initial rows selected rewards start count hspan hmode).finalState.followers i =
      .ordinary next nextMemory) :
    localBufferValid next ∧
      next.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ next.buffer, saved.calendarRound < start + count + 1 := by
  have hb := run_buffer_provenance i initial rows selected rewards start count hspan hmode
    seed seedMemory hseed hvalid hpair htime next nextMemory hnext
  have hs := run_bufferFold_safety i seed initial rows selected rewards start count hspan
    hmode hvalid hpair htime
  refine ⟨by simpa only [localBufferValid, hb] using hs.1, hb ▸ hs.2.1, ?_⟩
  intro saved hsaved
  rw [hb] at hsaved
  exact Nat.lt_succ_of_le (hs.2.2 saved hsaved)

/-- At the next actual unoccupied CHOICE, chronological premises are derived
from the computed prefix. The pre-recovery DOWN input is the retained buffer
plus the current physical emission, and neither logging-domain error can
occur. Later DOWN/release/finish failures are unrestricted. -/
theorem run_logging_ne_error (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (seed : ReferencePrelaunchFollower.State p rate.eta) (seedMemory : LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (choice : ReferencePrelaunchFollower.State p rate.eta) (choiceMemory : LocalMemory p) :
    let priorRun := run initial rows selected rewards start count (by omega) hmode
    let input := roundInputAt initial rows selected rewards start hmode priorRun
      ⟨start + count, by omega, by omega⟩
    let record : RoundRecord (p := p) (rate := rate) := ⟨input, step input, rfl⟩
    (record.output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory →
    choice.status = .unoccupied →
    (∃ logged, (record.output.followers i).downInput = some logged ∧
      logged.buffer = bufferFold i seed.buffer priorRun.records ++ logEmission i record ∧
      localBufferValid logged) ∧
    ∀ reason, ActiveFollowerLogging.checkedLogging i input.row
      (input.state.activations i) input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i)) choice ≠ .error reason := by
  intro priorRun input record hprepared hunoccupied
  obtain ⟨prior, priorMemory, hprior, hchoiceBuffer⟩ :=
    prepared_choice_buffer_eq_input i record choice choiceMemory hprepared
  have hchrono := run_buffer_chronological i initial rows selected rewards start count
    (by omega) hmode seed seedMemory hseed hvalid hpair htime prior priorMemory hprior
  have hb := run_buffer_provenance i initial rows selected rewards start count (by omega)
    hmode seed seedMemory hseed hvalid hpair htime prior priorMemory hprior
  have hchoiceValid : localBufferValid choice := by
    simpa only [localBufferValid, hchoiceBuffer] using hchrono.1
  have hchoiceTime : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1 := by
    intro saved hsaved
    rw [hchoiceBuffer] at hsaved
    exact hchrono.2.2 saved hsaved
  obtain ⟨logged, hdiag, hlogged, hloggedValid⟩ := actualPrepared_downInput_buffer
    i record choice choiceMemory hprepared hchoiceValid hchoiceTime hunoccupied
  obtain ⟨logged', hlogging, _, _, _⟩ := actualPreparedLogging_success
    i record choice choiceMemory hprepared hchoiceValid hchoiceTime hunoccupied
  refine ⟨⟨logged, hdiag, ?_, hloggedValid⟩, ?_⟩
  · rw [hlogged, hchoiceBuffer, hb]
  · intro reason herror
    rw [hlogging] at herror
    cases herror

end Bandits.Support.ReferenceFollowerBufferProvenance

end
