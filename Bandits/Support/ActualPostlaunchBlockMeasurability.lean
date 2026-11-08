/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchStepMeasurability
public import Bandits.Support.ActualCompletePhysicalHistory

/-!
# Borel readouts of one actual mixed postlaunch block

This module composes the existing actual mixed-step code along the existing
within-block fold. Its root varies the original source, whole reward table,
and same cursor-indexed postlaunch state together.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.ActualCompletePhysicalHistory

namespace Bandits.Support.ActualPostlaunchBlockMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := ActualPostlaunchPhysicalStep.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualPostlaunchPhysicalStep.GridRewardTable p

variable {p : Parameters} {rate : RateInput p}
  {block : Fin (n_boot p)}

/-- The ordinary joint domain at one cursor, with P's original storage Borel
space and the full source and reward coordinates. -/
abbrev BlockInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (cursor : Nat) :=
  SourceInput p × (GridRewardTable p ×
    ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor)

@[instance_reducible] instance blockInputMeasurableSpace (cursor : Nat) :
    MeasurableSpace (BlockInput p rate block cursor) :=
  MeasurableSpace.prod
    (ActualInitializationRoundMeasurability.roundSourceMeasurableSpace p)
    (MeasurableSpace.prod
      (ActualInitializationRoundMeasurability.roundRewardMeasurableSpace p)
      (inferInstance : MeasurableSpace
        (ActualPostlaunchPhysicalStep.PostlaunchState
          (p := p) (rate := rate) block cursor)))

/-- Pack the same source, whole reward table, and state into M's original
physical-input carrier. The strict cursor bound is only its typing field. -/
def packInput (cursor : Nat) (hcursor : cursor < blockLength p block)
    (x : BlockInput p rate block cursor) :
    ActualPostlaunchPhysicalStep.PhysicalInput (p := p) (rate := rate) block cursor :=
  ⟨x.1, x.2.1, x.2.2, hcursor⟩

theorem measurable_packInput (cursor : Nat)
    (hcursor : cursor < blockLength p block) :
    Measurable (packInput (p := p) (rate := rate) (block := block) cursor hcursor) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x : BlockInput p rate block cursor =>
    (x.1, (x.2.1,
      ActualPostlaunchPreparationMeasurability.encodeState x.2.2)))
  exact measurable_fst.prodMk
    (measurable_snd.fst.prodMk
      (ActualPostlaunchPreparationMeasurability.measurable_encodeState.comp
        measurable_snd.snd))

/-- The next joint domain is obtained by applying S's actual step to the
packed input and retaining its literal `nextState`. -/
def advanceInput (cursor : Nat) (hcursor : cursor < blockLength p block)
    (x : BlockInput p rate block cursor) : BlockInput p rate block (cursor + 1) :=
  (x.1, (x.2.1,
    (ActualPostlaunchPhysicalStep.step
      (packInput (p := p) (rate := rate) (block := block) cursor hcursor x)).nextState))

theorem measurable_advanceInput (cursor : Nat)
    (hcursor : cursor < blockLength p block) :
    Measurable (advanceInput (p := p) (rate := rate) (block := block) cursor hcursor) :=
  measurable_fst.prodMk
    (measurable_snd.fst.prodMk
      (ActualPostlaunchStepMeasurability.measurable_nextState.comp
        (measurable_packInput (p := p) (rate := rate) (block := block)
          cursor hcursor)))

/-- Every record retained by H's block trace has the fixed trace block. -/
theorem MixedBlockTrace.record_block
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    ∀ record ∈ trace.records, record.block = block := by
  induction trace with
  | done state =>
      simp [ActualCompletePhysicalHistory.MixedBlockTrace.records]
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      intro record hrecord
      simp only [ActualCompletePhysicalHistory.MixedBlockTrace.records,
        List.mem_cons] at hrecord
      rcases hrecord with hhead | htail
      · subst record
        rfl
      · exact ih record htail

/-- Read the actual S code from each exact input retained by H's records.
The proof-indexed map only transports the code to the fixed block index. -/
def recordStepCode {source : SourceInput p} {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hblock : record.block = block) : ActualPostlaunchStepMeasurability.StepCode
      p rate block :=
  hblock ▸ ActualPostlaunchStepMeasurability.stepCode record.input

/-- The full chronological actual step-code list, read directly from H's
retained records. -/
def traceStepCodes {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    List (ActualPostlaunchStepMeasurability.StepCode p rate block) :=
  trace.records.pmap
    (fun record hblock => recordStepCode (p := p) (rate := rate) (block := block)
      record hblock)
    (MixedBlockTrace.record_block trace)

/-- Length/index coordinates for any finite history. The `Unit ⊕ α` tag
preserves the distinction between an absent position and an actual round. -/
def roundListCoordinates {α : Type*} (rounds : List α) :
    ℕ × (ℕ → Unit ⊕ α) :=
  (rounds.length, fun n =>
    match rounds[n]? with
    | none => Sum.inl ()
    | some round => Sum.inr round)

/-- Length and every indexed code, with an explicit absent-position tag. -/
def stepCodeListCoordinates (codes :
    List (ActualPostlaunchStepMeasurability.StepCode p rate block)) :
    ℕ × (ℕ → Unit ⊕ ActualPostlaunchStepMeasurability.StepCode p rate block) :=
  roundListCoordinates codes

theorem stepCodeListCoordinates_eq_roundListCoordinates (codes :
    List (ActualPostlaunchStepMeasurability.StepCode p rate block)) :
    stepCodeListCoordinates (p := p) (rate := rate) (block := block) codes =
      roundListCoordinates codes := by
  rfl

/-- Apply a literal round readout to each present indexed history position;
absent positions retain their left `Sum` tag. -/
def mapRoundCoordinates {α β : Type*} (read : α → β)
    (coordinates : ℕ × (ℕ → Unit ⊕ α)) : ℕ × (ℕ → Unit ⊕ β) :=
  (coordinates.1, fun n =>
    (coordinates.2 n).elim Sum.inl (fun round => Sum.inr (read round)))

theorem mapRoundCoordinates_roundListCoordinates {α β : Type*}
    (read : α → β) (rounds : List α) :
    mapRoundCoordinates read (roundListCoordinates rounds) =
      roundListCoordinates (rounds.map read) := by
  apply Prod.ext
  · simp [mapRoundCoordinates, roundListCoordinates]
  · funext n
    cases hget : rounds[n]? with
    | none => simp [mapRoundCoordinates, roundListCoordinates, hget]
    | some round => simp [mapRoundCoordinates, roundListCoordinates, hget]

theorem measurable_mapRoundCoordinates {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (read : α → β)
    (hread : Measurable read) :
    Measurable (mapRoundCoordinates read :
      (ℕ × (ℕ → Unit ⊕ α)) → ℕ × (ℕ → Unit ⊕ β)) := by
  have htag : Measurable (fun value : Unit ⊕ α =>
      value.elim Sum.inl (fun round => Sum.inr (read round))) :=
    Measurable.sumElim measurable_inl (measurable_inr.comp hread)
  have hstream : Measurable (fun coordinates : ℕ × (ℕ → Unit ⊕ α) =>
      fun n => (coordinates.2 n).elim Sum.inl (fun round => Sum.inr (read round))) := by
    apply measurable_pi_iff.mpr
    intro n
    exact htag.comp ((measurable_pi_apply n).comp measurable_snd)
  exact measurable_fst.prodMk hstream

/-- The simultaneous actual actions are a projection of each full S code. -/
def stepCodeActions
    (code : ActualPostlaunchStepMeasurability.StepCode p rate block) :
    FiniteBanditModel.ActionProfile p.m p.K :=
  code.1.2.1

/-- The whole collision-filtered grid feedback vector is a projection of each
full S code. -/
def stepCodeFeedback
    (code : ActualPostlaunchStepMeasurability.StepCode p rate block) :
    Fin p.m → Fin (D p + 1) :=
  code.1.2.2

theorem measurable_stepCodeActions : Measurable
    (stepCodeActions (p := p) (rate := rate) (block := block)) :=
  measurable_fst.comp (measurable_snd.comp measurable_fst)

theorem measurable_stepCodeFeedback : Measurable
    (stepCodeFeedback (p := p) (rate := rate) (block := block)) :=
  measurable_snd.comp (measurable_snd.comp measurable_fst)

private theorem measurable_stepCodeListCoordinates_cons
    {Ω : Type*} [MeasurableSpace Ω]
    (head : Ω → ActualPostlaunchStepMeasurability.StepCode p rate block)
    (tail : Ω → List (ActualPostlaunchStepMeasurability.StepCode p rate block))
    (hhead : Measurable head)
    (htail : Measurable (fun ω => stepCodeListCoordinates (p := p) (rate := rate)
      (block := block) (tail ω))) :
    Measurable (fun ω => stepCodeListCoordinates (p := p) (rate := rate)
      (block := block) (head ω :: tail ω)) := by
  have hlength : Measurable (fun ω => (head ω :: tail ω).length) := by
    change Measurable (fun ω => Nat.succ (tail ω).length)
    exact (measurable_of_countable Nat.succ).comp (measurable_fst.comp htail)
  have hstream : Measurable (fun ω =>
      (stepCodeListCoordinates (p := p) (rate := rate) (block := block)
        (head ω :: tail ω)).2) := by
    apply measurable_pi_iff.mpr
    intro n
    cases n with
    | zero =>
        simp only [stepCodeListCoordinates, List.getElem?_cons_zero]
        exact measurable_inr.comp hhead
    | succ n =>
        simp only [stepCodeListCoordinates, List.getElem?_cons_succ]
        exact (measurable_pi_apply n).comp (measurable_snd.comp htail)
  exact hlength.prodMk hstream

/-- The same-record code reconstructs the actual step result; H's retained
equation identifies that result with the record's stored `RoundResult`. -/
theorem recordStepCode_reconstructs
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hblock : record.block = block) :
    (recordStepCode (p := p) (rate := rate) (block := block) record hblock).1.2.1 =
        ActualPostlaunchPhysicalStep.actionProfile record.result.prepared ∧
      (recordStepCode (p := p) (rate := rate) (block := block) record hblock).1.2.2 =
        ActualPostlaunchPhysicalStep.physicalFeedback record.result.prepared := by
  cases hblock
  change (ActualPostlaunchStepMeasurability.stepCode record.input).1.2.1 =
      ActualPostlaunchPhysicalStep.actionProfile record.result.prepared ∧
    (ActualPostlaunchStepMeasurability.stepCode record.input).1.2.2 =
      ActualPostlaunchPhysicalStep.physicalFeedback record.result.prepared
  rw [record.result_eq]
  rcases ActualPostlaunchStepMeasurability.stepCode_reconstructs record.input with
    ⟨_, _, hactions, hfeedback, _, _, _⟩
  exact ⟨hactions, hfeedback⟩

/-- Full reconstruction of the exact H record from its retained S code. This
includes prepared coordinator/follower data, simultaneous actions and own
feedback, the complete coordinator observation, every follower outcome, and
the successor in P's same storage encoding. -/
theorem recordStepCode_eq_cast
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hblock : record.block = block) :
    recordStepCode (p := p) (rate := rate) (block := block) record hblock =
      hblock ▸ ActualPostlaunchStepMeasurability.stepCode record.input := by
  rfl

/-- At the record's native block index, S reconstructs every data field from
the retained input's literal code, and H's record equation identifies the
retained result with that same step. `recordStepCode_eq_cast` states the exact
proof-indexed transport to the fixed block. -/
theorem recordStepCode_reconstructs_full
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    (let code := ActualPostlaunchStepMeasurability.stepCode record.input
    OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode
        (ActualPostlaunchPreparationMeasurability.coordinatorInput record.input)
        code.1.1.1.2 rfl =
          (ActualPostlaunchPhysicalStep.step record.input).prepared.coordinator ∧
      (∀ i, ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
        (rate := rate) i record.input.source record.input.time (code.1.1.2 i) =
          some ((ActualPostlaunchPhysicalStep.step record.input).prepared.followers i)) ∧
      code.1.2.1 = ActualPostlaunchPhysicalStep.actionProfile
        (ActualPostlaunchPhysicalStep.step record.input).prepared ∧
      code.1.2.2 = ActualPostlaunchPhysicalStep.physicalFeedback
        (ActualPostlaunchPhysicalStep.step record.input).prepared ∧
      ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation code.2.1 =
        (ActualPostlaunchPhysicalStep.step record.input).coordinatorObservation ∧
      (∀ i, ActualPostlaunchFollowerMeasurability.decodeLocalCode record.input.source
        record.input.time i (code.2.2 i) =
          some ((ActualPostlaunchPhysicalStep.step record.input).followers i)) ∧
      ActualPostlaunchPreparationMeasurability.decodeState
        ⟨ActualPostlaunchStepMeasurability.successorCoordinates code,
          ⟨(ActualPostlaunchPhysicalStep.step record.input).nextState,
            ActualPostlaunchStepMeasurability.encode_nextState record.input⟩⟩ =
        (ActualPostlaunchPhysicalStep.step record.input).nextState) ∧
      record.result = ActualPostlaunchPhysicalStep.step record.input := by
  exact ⟨ActualPostlaunchStepMeasurability.stepCode_reconstructs record.input,
    record.result_eq⟩

/-- On a trace constructor, the pmap readout adds precisely the S code of its
retained input before the code list of its actual successor trace. -/
theorem traceStepCodes_cons
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hstate : input.state = state) (hsource : input.source = source)
    (hrewards : input.rewards = rewards)
    (result : ActualPostlaunchPhysicalStep.RoundResult input)
    (result_eq : result = ActualPostlaunchPhysicalStep.step input)
    (tail : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block (cursor + 1) result.nextState stop)
    (hlt : cursor < stop) :
    traceStepCodes (ActualCompletePhysicalHistory.MixedBlockTrace.step
      state input hstate hsource hrewards result result_eq tail hlt) =
      ActualPostlaunchStepMeasurability.stepCode input :: traceStepCodes tail := by
  simp [traceStepCodes, ActualCompletePhysicalHistory.MixedBlockTrace.records,
    recordStepCode]

/-- Mapping the full-code list to simultaneous actions agrees record by
record with H's retained `RoundResult.prepared` projections. -/
theorem MixedBlockTrace.stepCodes_actions
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    (traceStepCodes trace).map (stepCodeActions (p := p) (rate := rate)
      (block := block)) =
      trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions := by
  induction trace with
  | done state => rfl
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      rw [traceStepCodes_cons input hstate hsource hrewards result result_eq tail hlt]
      simp only [List.map_cons,
        ActualCompletePhysicalHistory.MixedBlockTrace.records]
      have hhead : stepCodeActions (ActualPostlaunchStepMeasurability.stepCode input) =
          ActualCompletePhysicalHistory.MixedRoundRecord.actions
            ⟨block, cursor, input, hsource, hrewards, result, result_eq⟩ := by
        change (ActualPostlaunchStepMeasurability.stepCode input).1.2.1 =
          ActualPostlaunchPhysicalStep.actionProfile result.prepared
        rw [result_eq]
        rcases ActualPostlaunchStepMeasurability.stepCode_reconstructs input with
          ⟨_, _, hactions, _, _, _, _⟩
        exact hactions
      rw [hhead, ih]

/-- Mapping the full-code list to simultaneous grid feedback agrees record
by record with H's retained actual collision-filtered feedback. -/
theorem MixedBlockTrace.stepCodes_feedback
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    (traceStepCodes trace).map (stepCodeFeedback (p := p) (rate := rate)
      (block := block)) =
      trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback := by
  induction trace with
  | done state => rfl
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      rw [traceStepCodes_cons input hstate hsource hrewards result result_eq tail hlt]
      simp only [List.map_cons,
        ActualCompletePhysicalHistory.MixedBlockTrace.records]
      have hhead : stepCodeFeedback (ActualPostlaunchStepMeasurability.stepCode input) =
          ActualCompletePhysicalHistory.MixedRoundRecord.feedback
            ⟨block, cursor, input, hsource, hrewards, result, result_eq⟩ := by
        change (ActualPostlaunchStepMeasurability.stepCode input).1.2.2 =
          ActualPostlaunchPhysicalStep.physicalFeedback result.prepared
        rw [result_eq]
        rcases ActualPostlaunchStepMeasurability.stepCode_reconstructs input with
          ⟨_, _, _, hfeedback, _, _, _⟩
        exact hfeedback
      rw [hhead, ih]

/-- Length/index observations of the actual action history derived from the
same full code list. -/
def MixedBlockTrace.actionCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    ℕ × (ℕ → Unit ⊕ FiniteBanditModel.ActionProfile p.m p.K) :=
  mapRoundCoordinates (stepCodeActions (p := p) (rate := rate) (block := block))
    (roundListCoordinates (traceStepCodes trace))

/-- Length/index observations of the whole simultaneous own-feedback grid
history derived from the same full code list. -/
def MixedBlockTrace.feedbackCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    ℕ × (ℕ → Unit ⊕ (Fin p.m → Fin (D p + 1))) :=
  mapRoundCoordinates (stepCodeFeedback (p := p) (rate := rate) (block := block))
    (roundListCoordinates (traceStepCodes trace))

theorem MixedBlockTrace.actionCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    MixedBlockTrace.actionCoordinates trace = roundListCoordinates
      (trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions) := by
  unfold MixedBlockTrace.actionCoordinates
  rw [mapRoundCoordinates_roundListCoordinates, MixedBlockTrace.stepCodes_actions trace]

theorem MixedBlockTrace.feedbackCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    MixedBlockTrace.feedbackCoordinates trace = roundListCoordinates
      (trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback) := by
  unfold MixedBlockTrace.feedbackCoordinates
  rw [mapRoundCoordinates_roundListCoordinates, MixedBlockTrace.stepCodes_feedback trace]

/-- Each player's arm history remains a projection of the action coordinates
derived from the full actual step codes. -/
def MixedBlockTrace.playerArmCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    ℕ × (ℕ → Unit ⊕ Fin p.K) :=
  mapRoundCoordinates (fun actions : FiniteBanditModel.ActionProfile p.m p.K =>
      actions player) (MixedBlockTrace.actionCoordinates trace)

/-- Each player's own grid-feedback history remains a projection of the same
full actual step codes. -/
def MixedBlockTrace.playerGridFeedbackCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    ℕ × (ℕ → Unit ⊕ Fin (D p + 1)) :=
  mapRoundCoordinates (fun feedback : Fin p.m → Fin (D p + 1) => feedback player)
    (MixedBlockTrace.feedbackCoordinates trace)

/-- Each player's own quantized observation history is also read from its
feedback entries; the grid-to-real conversion is the literal source scaling. -/
def MixedBlockTrace.playerQuantizedObservationCoordinates
    {source : SourceInput p} {rewards : GridRewardTable p} {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    ℕ × (ℕ → Unit ⊕ ℝ) :=
  mapRoundCoordinates (fun feedback : Fin p.m → Fin (D p + 1) =>
      ((feedback player).val : ℝ) / (D p : ℝ))
    (MixedBlockTrace.feedbackCoordinates trace)

theorem MixedBlockTrace.playerArmCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    MixedBlockTrace.playerArmCoordinates trace player = roundListCoordinates
      ((trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions).map
        (fun actions => actions player)) := by
  unfold MixedBlockTrace.playerArmCoordinates
  rw [MixedBlockTrace.actionCoordinates_eq_records trace,
    mapRoundCoordinates_roundListCoordinates]

theorem MixedBlockTrace.playerGridFeedbackCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    MixedBlockTrace.playerGridFeedbackCoordinates trace player = roundListCoordinates
      ((trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback).map
        (fun feedback => feedback player)) := by
  unfold MixedBlockTrace.playerGridFeedbackCoordinates
  rw [MixedBlockTrace.feedbackCoordinates_eq_records trace,
    mapRoundCoordinates_roundListCoordinates]

theorem MixedBlockTrace.playerQuantizedObservationCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) (player : Fin p.m) :
    MixedBlockTrace.playerQuantizedObservationCoordinates trace player = roundListCoordinates
      ((trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback).map
        (fun feedback => ((feedback player).val : ℝ) / (D p : ℝ))) := by
  unfold MixedBlockTrace.playerQuantizedObservationCoordinates
  rw [MixedBlockTrace.feedbackCoordinates_eq_records trace,
    mapRoundCoordinates_roundListCoordinates]

/-- The actual time values are read from H's exact retained records. -/
def MixedBlockTrace.timeValues {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) : List Nat :=
  (trace.records.map ActualCompletePhysicalHistory.MixedRoundRecord.time).map Fin.val

theorem MixedBlockTrace.timeValues_eq_consecutive
    (source : SourceInput p) (rewards : GridRewardTable p)
    (cursor stop : Nat)
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor)
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    MixedBlockTrace.timeValues trace = ActualInitializationHorizon.consecutiveNat
      (blockStart p block + cursor) (stop - cursor) :=
  ActualCompletePhysicalHistory.MixedBlockTrace.times_values
    p rate source rewards block cursor stop state trace

/-- A finite time-value history is a constant length/index readout on this
fixed block/cursor domain, including an empty endpoint history. -/
theorem measurable_foldMixedBlockAux_timeValueCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      roundListCoordinates
        (MixedBlockTrace.timeValues
          (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
            block cursor x.2.2 hcursor))) := by
  have heq : (fun x : BlockInput p rate block cursor =>
      roundListCoordinates
        (MixedBlockTrace.timeValues
          (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
            block cursor x.2.2 hcursor))) = fun _ =>
        roundListCoordinates (ActualInitializationHorizon.consecutiveNat
          (blockStart p block + cursor) (blockLength p block - cursor)) := by
    funext x
    exact congrArg roundListCoordinates
      (MixedBlockTrace.timeValues_eq_consecutive x.1 x.2.1 cursor
        (blockLength p block) x.2.2
        (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor))
  rw [heq]
  exact measurable_const

theorem MixedBlockTrace.stepCodes_length
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    (traceStepCodes trace).length = stop - cursor := by
  induction trace with
  | done state => simp [traceStepCodes, ActualCompletePhysicalHistory.MixedBlockTrace.records]
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      rw [traceStepCodes_cons input hstate hsource hrewards result result_eq tail hlt]
      simp only [List.length_cons, ih]
      omega

/-- The record chronology has exactly one retained item per original cursor
before the clipped block endpoint. -/
theorem MixedBlockTrace.record_count
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block cursor state stop) :
    trace.records.length = stop - cursor := by
  induction trace with
  | done state => simp [ActualCompletePhysicalHistory.MixedBlockTrace.records]
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      simp only [ActualCompletePhysicalHistory.MixedBlockTrace.records, List.length_cons, ih]
      omega

/-- H's final-state readout follows the tail whose initial state is the
recorded actual result's full successor. -/
theorem MixedBlockTrace.finalState_encode_eq_tail
    {source : SourceInput p} {rewards : GridRewardTable p}
    {cursor stop : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hstate : input.state = state) (hsource : input.source = source)
    (hrewards : input.rewards = rewards)
    (result : ActualPostlaunchPhysicalStep.RoundResult input)
    (result_eq : result = ActualPostlaunchPhysicalStep.step input)
    (tail : ActualCompletePhysicalHistory.MixedBlockTrace
      p rate source rewards block (cursor + 1) result.nextState stop)
    (hlt : cursor < stop) :
    ActualPostlaunchPreparationMeasurability.encodeState
      (ActualCompletePhysicalHistory.MixedBlockTrace.finalState
        (ActualCompletePhysicalHistory.MixedBlockTrace.step state input hstate
          hsource hrewards result result_eq tail hlt)) =
    ActualPostlaunchPreparationMeasurability.encodeState tail.finalState := rfl

/-- The same S code that enters H's next cursor stores exactly the encoded
successor state, including every original coordinator, bank and follower field. -/
theorem step_successor_encode_eq_code
    {cursor : Nat}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor) :
    ActualPostlaunchPreparationMeasurability.encodeState
        (ActualPostlaunchPhysicalStep.step input).nextState =
      ActualPostlaunchStepMeasurability.successorCoordinates
        (ActualPostlaunchStepMeasurability.stepCode input) :=
  ActualPostlaunchStepMeasurability.encode_nextState input

/-- The full fold readouts at one cursor: its unchanged or actual terminal
state and the full chronological S code list of H's own records. -/
private theorem measurable_foldOutputs_aux (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      (ActualCompletePhysicalHistory.MixedBlockTrace.finalState
        (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor),
      stepCodeListCoordinates (p := p) (rate := rate) (block := block)
        (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
          x.1 x.2.1 block cursor x.2.2 hcursor)))) := by
  have hmain : ∀ (n c : Nat) (hmeasure : blockLength p block - c = n)
      (hc : c ≤ blockLength p block),
      Measurable (fun x : BlockInput p rate block c =>
        (ActualCompletePhysicalHistory.MixedBlockTrace.finalState
          (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
            block c x.2.2 hc),
         stepCodeListCoordinates (p := p) (rate := rate) (block := block)
          (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
            x.1 x.2.1 block c x.2.2 hc)))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hmeasure hc
        by_cases hdone : c = blockLength p block
        · subst c
          have hstate : Measurable (fun x : BlockInput p rate block
              (blockLength p block) => x.2.2) := measurable_snd.snd
          have hcodes : Measurable (fun _ : BlockInput p rate block
              (blockLength p block) => stepCodeListCoordinates
                (p := p) (rate := rate) (block := block) []) := measurable_const
          have hfold (x : BlockInput p rate block (blockLength p block)) :
              ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                block (blockLength p block) x.2.2 hc = .done x.2.2 := by
            simp [ActualCompletePhysicalHistory.foldMixedBlockAux]
          have hpair : (fun x : BlockInput p rate block (blockLength p block) =>
              (ActualCompletePhysicalHistory.MixedBlockTrace.finalState
                (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                  block (blockLength p block) x.2.2 hc),
               stepCodeListCoordinates (p := p) (rate := rate) (block := block)
                (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                  x.1 x.2.1 block (blockLength p block) x.2.2 hc)))) =
              fun x => (x.2.2, stepCodeListCoordinates
                (p := p) (rate := rate) (block := block) []) := by
            funext x
            rw [hfold x]
            rfl
          rw [hpair]
          exact hstate.prodMk hcodes
        · have hlt : c < blockLength p block := by omega
          let hnext : c + 1 ≤ blockLength p block := by omega
          let pack := packInput (p := p) (rate := rate) (block := block) c hlt
          let advance := advanceInput (p := p) (rate := rate) (block := block) c hlt
          have hadvance : Measurable advance :=
            measurable_advanceInput (p := p) (rate := rate) (block := block) c hlt
          have hdecrease : blockLength p block - (c + 1) < n := by omega
          have htail := ih (blockLength p block - (c + 1)) hdecrease
            (c + 1) rfl hnext
          have htrace (x : BlockInput p rate block c) :
              ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                  block c x.2.2 hc =
                .step x.2.2 (pack x) rfl rfl rfl (ActualPostlaunchPhysicalStep.step (pack x))
                  rfl
                  (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                    block (c + 1) (ActualPostlaunchPhysicalStep.step (pack x)).nextState
                    hnext)
                  hlt := by
            conv_lhs =>
              rw [ActualCompletePhysicalHistory.foldMixedBlockAux.eq_1]
            simp only [dif_neg hdone]
            rfl
          have htraceCodes (x : BlockInput p rate block c) :
              traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                x.1 x.2.1 block c x.2.2 hc) =
                ActualPostlaunchStepMeasurability.stepCode (pack x) ::
                  traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                    x.1 x.2.1 block (c + 1)
                    (ActualPostlaunchPhysicalStep.step (pack x)).nextState hnext) := by
            rw [htrace]
            simp [traceStepCodes, ActualCompletePhysicalHistory.MixedBlockTrace.records,
              recordStepCode]
          have htailComposed : Measurable (fun x : BlockInput p rate block c =>
              (ActualCompletePhysicalHistory.MixedBlockTrace.finalState
                (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                  (advance x).1 (advance x).2.1 block (c + 1) (advance x).2.2 hnext),
               stepCodeListCoordinates (p := p) (rate := rate) (block := block)
                (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                  (advance x).1 (advance x).2.1 block (c + 1) (advance x).2.2 hnext)))) :=
            htail.comp hadvance
          have hfinal : Measurable (fun x : BlockInput p rate block c =>
              ActualCompletePhysicalHistory.MixedBlockTrace.finalState
                (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                  block c x.2.2 hc)) := by
            have heq : (fun x : BlockInput p rate block c =>
                ActualCompletePhysicalHistory.MixedBlockTrace.finalState
                  (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
                    block c x.2.2 hc)) = fun x =>
                ActualCompletePhysicalHistory.MixedBlockTrace.finalState
                  (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                    (advance x).1 (advance x).2.1 block (c + 1) (advance x).2.2 hnext) := by
              funext x
              rw [htrace]
              rfl
            rw [heq]
            exact measurable_fst.comp htailComposed
          have hhead : Measurable (fun x : BlockInput p rate block c =>
              ActualPostlaunchStepMeasurability.stepCode (pack x)) :=
            ActualPostlaunchStepMeasurability.measurable_stepCode.comp
              (measurable_packInput (p := p) (rate := rate) (block := block) c hlt)
          have hcodes : Measurable (fun x : BlockInput p rate block c =>
              stepCodeListCoordinates (p := p) (rate := rate) (block := block)
                (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                  x.1 x.2.1 block c x.2.2 hc))) := by
            have hcodesEq : (fun x : BlockInput p rate block c =>
                stepCodeListCoordinates (p := p) (rate := rate) (block := block)
                  (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                    x.1 x.2.1 block c x.2.2 hc))) = fun x =>
                stepCodeListCoordinates (p := p) (rate := rate) (block := block)
                  (ActualPostlaunchStepMeasurability.stepCode (pack x) ::
                    traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
                      x.1 x.2.1 block (c + 1)
                      (ActualPostlaunchPhysicalStep.step (pack x)).nextState hnext)) := by
              funext x
              rw [htraceCodes]
            rw [hcodesEq]
            exact measurable_stepCodeListCoordinates_cons (p := p) (rate := rate)
              (block := block) (fun x => ActualPostlaunchStepMeasurability.stepCode (pack x))
              (fun x => traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux
                p rate x.1 x.2.1 block (c + 1)
                (ActualPostlaunchPhysicalStep.step (pack x)).nextState hnext))
              hhead (measurable_snd.comp htailComposed)
          exact hfinal.prodMk hcodes
  exact hmain (blockLength p block - cursor) cursor rfl hcursor

theorem measurable_foldMixedBlockAux_finalState (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
        block cursor x.2.2 hcursor).finalState) :=
  (measurable_foldOutputs_aux (p := p) (rate := rate) (block := block)
    cursor hcursor).fst

theorem measurable_foldMixedBlockAux_stepCodeCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      stepCodeListCoordinates (p := p) (rate := rate) (block := block)
        (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlockAux p rate
          x.1 x.2.1 block cursor x.2.2 hcursor))) :=
  (measurable_foldOutputs_aux (p := p) (rate := rate) (block := block)
    cursor hcursor).snd


/-- The encoded final state of the actual fold is Borel in P's original
cursor-indexed storage spaces. -/
theorem measurable_foldMixedBlockAux_finalStateCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      ActualPostlaunchPreparationMeasurability.encodeState
        ((ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor).finalState)) :=
  ActualPostlaunchPreparationMeasurability.measurable_encodeState.comp
    (measurable_foldMixedBlockAux_finalState (p := p) (rate := rate) (block := block)
      cursor hcursor)

/-- The full simultaneous action history is Borel as a projection of the
same chronological actual S code list. -/
theorem measurable_foldMixedBlockAux_actionCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      MixedBlockTrace.actionCoordinates (ActualCompletePhysicalHistory.foldMixedBlockAux
        p rate x.1 x.2.1 block cursor x.2.2 hcursor)) := by
  have hcodes : Measurable (fun x : BlockInput p rate block cursor =>
      roundListCoordinates (traceStepCodes
        (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor))) := by
    simpa [stepCodeListCoordinates, roundListCoordinates] using
      measurable_foldMixedBlockAux_stepCodeCoordinates
        (p := p) (rate := rate) (block := block) cursor hcursor
  exact (measurable_mapRoundCoordinates
    (stepCodeActions (p := p) (rate := rate) (block := block))
    (measurable_stepCodeActions (p := p) (rate := rate) (block := block))).comp hcodes

/-- The full collision-filtered grid feedback history is Borel as a
projection of the same chronological actual S code list. -/
theorem measurable_foldMixedBlockAux_feedbackCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) :
    Measurable (fun x : BlockInput p rate block cursor =>
      MixedBlockTrace.feedbackCoordinates (ActualCompletePhysicalHistory.foldMixedBlockAux
        p rate x.1 x.2.1 block cursor x.2.2 hcursor)) := by
  have hcodes : Measurable (fun x : BlockInput p rate block cursor =>
      roundListCoordinates (traceStepCodes
        (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor))) := by
    simpa [stepCodeListCoordinates, roundListCoordinates] using
      measurable_foldMixedBlockAux_stepCodeCoordinates
        (p := p) (rate := rate) (block := block) cursor hcursor
  exact (measurable_mapRoundCoordinates
    (stepCodeFeedback (p := p) (rate := rate) (block := block))
    (measurable_stepCodeFeedback (p := p) (rate := rate) (block := block))).comp hcodes

/-- Every player's chronological arm history is Borel from the same full
actual code readout. -/
theorem measurable_foldMixedBlockAux_playerArmCoordinates (cursor : Nat)
    (hcursor : cursor ≤ blockLength p block) (player : Fin p.m) :
    Measurable (fun x : BlockInput p rate block cursor =>
      MixedBlockTrace.playerArmCoordinates (ActualCompletePhysicalHistory.foldMixedBlockAux
        p rate x.1 x.2.1 block cursor x.2.2 hcursor) player) := by
  have hread : Measurable
      (fun actions : FiniteBanditModel.ActionProfile p.m p.K => actions player) :=
    measurable_pi_apply player
  exact (measurable_mapRoundCoordinates _ hread).comp
    (measurable_foldMixedBlockAux_actionCoordinates
      (p := p) (rate := rate) (block := block) cursor hcursor)

/-- Every player's own chronological grid-feedback history is Borel from the
same full actual code readout. -/
theorem measurable_foldMixedBlockAux_playerGridFeedbackCoordinates
    (cursor : Nat) (hcursor : cursor ≤ blockLength p block) (player : Fin p.m) :
    Measurable (fun x : BlockInput p rate block cursor =>
      MixedBlockTrace.playerGridFeedbackCoordinates (ActualCompletePhysicalHistory.foldMixedBlockAux
        p rate x.1 x.2.1 block cursor x.2.2 hcursor) player) := by
  have hread : Measurable (fun feedback : Fin p.m → Fin (D p + 1) =>
      feedback player) := measurable_pi_apply player
  exact (measurable_mapRoundCoordinates _ hread).comp
    (measurable_foldMixedBlockAux_feedbackCoordinates
      (p := p) (rate := rate) (block := block) cursor hcursor)

/-- Every player's own real-valued quantized observation history is Borel
from that player's actual grid-feedback coordinates. -/
theorem measurable_foldMixedBlockAux_playerQuantizedObservationCoordinates
    (cursor : Nat) (hcursor : cursor ≤ blockLength p block) (player : Fin p.m) :
    Measurable (fun x : BlockInput p rate block cursor =>
      MixedBlockTrace.playerQuantizedObservationCoordinates
        (ActualCompletePhysicalHistory.foldMixedBlockAux p rate x.1 x.2.1
          block cursor x.2.2 hcursor) player) := by
  have hread : Measurable (fun feedback : Fin p.m → Fin (D p + 1) =>
      ((feedback player).val : ℝ) / (D p : ℝ)) :=
    (measurable_of_countable (fun grid : Fin (D p + 1) =>
      ((grid.val : ℝ) / (D p : ℝ)))).comp (measurable_pi_apply player)
  exact (measurable_mapRoundCoordinates _ hread).comp
    (measurable_foldMixedBlockAux_feedbackCoordinates
      (p := p) (rate := rate) (block := block) cursor hcursor)

/-- The cursor-zero specialization of the actual H fold has the same final
state and code readouts as the general auxiliary fold. -/
theorem measurable_foldMixedBlock_finalState :
    Measurable (fun x : BlockInput p rate block 0 =>
      (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block x.2.2).finalState) := by
  simpa [ActualCompletePhysicalHistory.foldMixedBlock] using
    (measurable_foldMixedBlockAux_finalState (p := p) (rate := rate)
      (block := block) 0 (Nat.zero_le _))

theorem measurable_foldMixedBlock_stepCodeCoordinates :
    Measurable (fun x : BlockInput p rate block 0 =>
      stepCodeListCoordinates (p := p) (rate := rate) (block := block)
        (traceStepCodes
          (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block x.2.2))) := by
  simpa [ActualCompletePhysicalHistory.foldMixedBlock] using
    (measurable_foldMixedBlockAux_stepCodeCoordinates (p := p) (rate := rate)
      (block := block) 0 (Nat.zero_le _))

/-- H's launch-input fold and ordinary zero-cursor fold have exactly the
same dependent trace when their source, rewards, and state are taken from that
same launch input. -/
theorem foldMixedBlockFromInput_eq_foldMixedBlock
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0) :
    ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate input.source
      input.rewards block input rfl rfl =
    ActualCompletePhysicalHistory.foldMixedBlock p rate input.source
      input.rewards block input.state := by
  cases input with
  | mk source rewards state hcursor =>
      have hpositive : 0 < blockLength p block := hcursor
      have hzero : ¬ (0 = blockLength p block) := by omega
      unfold ActualCompletePhysicalHistory.foldMixedBlock
      conv_rhs =>
        rw [ActualCompletePhysicalHistory.foldMixedBlockAux.eq_1]
      simp only [dif_neg hzero]
      unfold ActualCompletePhysicalHistory.foldMixedBlockFromInput
      rfl

/-- The source-initialized launch input's own source, reward table and
cursor-zero state are not replaced by a compatible ordinary initial state. -/
theorem measurable_foldMixedBlockFromInput_finalState :
    Measurable (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block 0 =>
      (ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate input.source
        input.rewards block input rfl rfl).finalState) := by
  have hjoint : Measurable (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0 => (input.source, (input.rewards, input.state))) :=
    ActualPostlaunchPreparationMeasurability.measurable_inputSource.prodMk
      (ActualPostlaunchPreparationMeasurability.measurable_inputRewards.prodMk
        ActualPostlaunchPreparationMeasurability.measurable_inputState)
  have hordinary := (measurable_foldMixedBlock_finalState
    (p := p) (rate := rate) (block := block)).comp hjoint
  have heq : (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0 =>
        (ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate input.source
          input.rewards block input rfl rfl).finalState) = fun input =>
        (ActualCompletePhysicalHistory.foldMixedBlock p rate input.source
          input.rewards block input.state).finalState := by
    funext input
    exact congrArg ActualCompletePhysicalHistory.MixedBlockTrace.finalState
      (foldMixedBlockFromInput_eq_foldMixedBlock input)
  rw [heq]
  exact hordinary

theorem measurable_foldMixedBlockFromInput_stepCodeCoordinates :
    Measurable (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block 0 =>
      stepCodeListCoordinates (p := p) (rate := rate) (block := block)
        (traceStepCodes
          (ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate input.source
            input.rewards block input rfl rfl))) := by
  have hjoint : Measurable (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0 => (input.source, (input.rewards, input.state))) :=
    ActualPostlaunchPreparationMeasurability.measurable_inputSource.prodMk
      (ActualPostlaunchPreparationMeasurability.measurable_inputRewards.prodMk
        ActualPostlaunchPreparationMeasurability.measurable_inputState)
  have hordinary := (measurable_foldMixedBlock_stepCodeCoordinates
    (p := p) (rate := rate) (block := block)).comp hjoint
  have heq : (fun input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0 =>
        stepCodeListCoordinates (p := p) (rate := rate) (block := block)
          (traceStepCodes
            (ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate input.source
              input.rewards block input rfl rfl))) = fun input =>
        stepCodeListCoordinates (p := p) (rate := rate) (block := block)
          (traceStepCodes (ActualCompletePhysicalHistory.foldMixedBlock p rate
            input.source input.rewards block input.state)) := by
    funext input
    rw [foldMixedBlockFromInput_eq_foldMixedBlock]
  rw [heq]
  exact hordinary


end Bandits.Support.ActualPostlaunchBlockMeasurability

end
