/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchBlockMeasurability
public import Bandits.Support.ActualPostlaunchBoundaryMeasurability

/-!
# Borel observations of an actual postlaunch suffix

This module composes the admitted actual mixed-block fold and actual
cross-successor boundary along `ActualCompletePhysicalHistory`'s recursive
postlaunch suffix. All observations retain the original block-indexed code
fibres and the preparation module's state encoding.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

The root varies the original source, whole reward table, and existing
cursor-zero state jointly. It does not construct a source-initialized launch
or a probability/history theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualCompletePhysicalHistory
open Bandits.Support.ActualPostlaunchBlockMeasurability
open Bandits.Support.ActualPostlaunchBoundaryMeasurability
open Bandits.Support.ActualPostlaunchPreparationMeasurability
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.ActualInitializationFollowerBoundaryMeasurability
open Bandits.Support.ActualInitializationBlockMeasurability

namespace Bandits.Support.ActualPostlaunchSuffixMeasurability

abbrev Parameters := ActualPostlaunchBlockMeasurability.Parameters
abbrev RateInput := ActualPostlaunchBlockMeasurability.RateInput
abbrev SourceInput (p : Parameters) := ActualPostlaunchBlockMeasurability.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualPostlaunchBlockMeasurability.GridRewardTable p

variable {p : Parameters} {rate : RateInput p}

abbrev StepCodeObservation (p : Parameters) (rate : RateInput p) :=
  Sigma fun block : Fin (n_boot p) =>
    ActualPostlaunchStepMeasurability.StepCode p rate block

abbrev BoundaryPayload (p : Parameters) (rate : RateInput p) :=
  (Fin (p.m - 1) → ActualInitializationFollowerBoundaryMeasurability.BoundaryOutputCode
    p rate) ×
  (Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate)

instance boundaryPayloadMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (BoundaryPayload p rate) :=
  MeasurableSpace.prod
    (inferInstance : MeasurableSpace
      (Fin (p.m - 1) →
        ActualInitializationFollowerBoundaryMeasurability.BoundaryOutputCode p rate))
    (inferInstance : MeasurableSpace
      (Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate))

abbrev BoundaryObservation (p : Parameters) (rate : RateInput p) :=
  Sigma fun _block : Fin (n_boot p) => BoundaryPayload p rate

abbrev CrossBoundaryFiber (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  Sigma fun next : Fin (n_boot p) =>
    BoundaryPayload p rate × ActualPostlaunchPreparationMeasurability.StateCoordinates
      p rate next

abbrev CrossBoundaryObservation (p : Parameters) (rate : RateInput p) :=
  Sigma fun block : Fin (n_boot p) => CrossBoundaryFiber p rate block

abbrev TerminalObservation (p : Parameters) (rate : RateInput p) :=
  Sigma fun block : Fin (n_boot p) =>
    BoundaryPayload p rate × ActualPostlaunchPreparationMeasurability.StateCoordinates
      p rate block

abbrev LengthIndexObservation (α : Type*) := ℕ × (ℕ → Unit ⊕ α)

instance stepCodeObservationMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (StepCodeObservation p rate) := by
  letI : ∀ block : Fin (n_boot p),
      MeasurableSpace (ActualPostlaunchStepMeasurability.StepCode p rate block) :=
    fun _ => inferInstance
  exact Sigma.instMeasurableSpace

instance boundaryObservationMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (BoundaryObservation p rate) := by
  letI : ∀ block : Fin (n_boot p), MeasurableSpace (BoundaryPayload p rate) :=
    fun _ => inferInstance
  exact Sigma.instMeasurableSpace

instance crossBoundaryObservationMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (CrossBoundaryObservation p rate) := by
  letI : ∀ block : Fin (n_boot p),
      MeasurableSpace (CrossBoundaryFiber p rate block) := fun _ => by
    letI : ∀ next : Fin (n_boot p),
        MeasurableSpace (BoundaryPayload p rate ×
          ActualPostlaunchPreparationMeasurability.StateCoordinates p rate next) :=
      fun _ => inferInstance
    exact Sigma.instMeasurableSpace
  exact Sigma.instMeasurableSpace

instance terminalObservationMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (TerminalObservation p rate) := by
  letI : ∀ block : Fin (n_boot p),
      MeasurableSpace (BoundaryPayload p rate ×
        ActualPostlaunchPreparationMeasurability.StateCoordinates p rate block) :=
    fun _ => inferInstance
  exact Sigma.instMeasurableSpace

private theorem measurable_sigmaMk_local {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem measurable_of_sigma_sections_local {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

/-- Concatenate a fixed-length block coordinate stream with a later stream.
The first stream's length is checked by the list reconstruction theorem; its
indexed entries are never padded with round records. -/
def appendFixedRoundCoordinates {α : Type*} (blockLength : ℕ)
    (left right : LengthIndexObservation α) : LengthIndexObservation α :=
  (blockLength + right.1, fun n =>
    if n < blockLength then left.2 n else right.2 (n - blockLength))

theorem measurable_appendFixedRoundCoordinates {α : Type*}
    [MeasurableSpace α] (blockLength : ℕ) :
    Measurable (fun pair : LengthIndexObservation α × LengthIndexObservation α =>
      appendFixedRoundCoordinates blockLength pair.1 pair.2) := by
  have hstream : Measurable (fun pair : LengthIndexObservation α ×
      LengthIndexObservation α => fun n =>
        if n < blockLength then pair.1.2 n else pair.2.2 (n - blockLength)) := by
    apply measurable_pi_iff.mpr
    intro n
    by_cases hn : n < blockLength
    · simp only [if_pos hn]
      exact (measurable_pi_apply n).comp
        (measurable_snd.comp measurable_fst)
    · simp only [if_neg hn]
      exact (measurable_pi_apply (n - blockLength)).comp
        (measurable_snd.comp measurable_snd)
  have hlen : Measurable (fun pair : LengthIndexObservation α ×
      LengthIndexObservation α => blockLength + pair.2.1) :=
    (measurable_of_countable fun pair : ℕ × ℕ => blockLength + pair.2).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  exact hlen.prodMk hstream

private theorem roundListCoordinates_cons {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (head : Ω → α) (tail : Ω → List α)
    (hhead : Measurable head)
    (htail : Measurable (fun ω =>
      ActualPostlaunchBlockMeasurability.roundListCoordinates (tail ω))) :
    Measurable (fun ω =>
      ActualPostlaunchBlockMeasurability.roundListCoordinates (head ω :: tail ω)) := by
  have hlength : Measurable (fun ω => (head ω :: tail ω).length) := by
    change Measurable (fun ω => Nat.succ (tail ω).length)
    exact (measurable_of_countable Nat.succ).comp
      (measurable_fst.comp htail)
  have hstream : Measurable (fun ω =>
      (ActualPostlaunchBlockMeasurability.roundListCoordinates
        (head ω :: tail ω)).2) := by
    apply measurable_pi_iff.mpr
    intro n
    cases n with
    | zero =>
        simp only [ActualPostlaunchBlockMeasurability.roundListCoordinates,
          List.getElem?_cons_zero]
        exact measurable_inr.comp hhead
    | succ n =>
        simp only [ActualPostlaunchBlockMeasurability.roundListCoordinates,
          List.getElem?_cons_succ]
        exact (measurable_pi_apply n).comp (measurable_snd.comp htail)
  exact hlength.prodMk hstream

private theorem appendFixedRoundCoordinates_roundListAppend {α : Type*}
    [MeasurableSpace α] (blockLength : ℕ) (left right : List α)
    (hlen : left.length = blockLength) :
    appendFixedRoundCoordinates blockLength
      (ActualPostlaunchBlockMeasurability.roundListCoordinates left)
      (ActualPostlaunchBlockMeasurability.roundListCoordinates right) =
    ActualPostlaunchBlockMeasurability.roundListCoordinates (left ++ right) := by
  apply Prod.ext
  · simp [appendFixedRoundCoordinates,
      ActualPostlaunchBlockMeasurability.roundListCoordinates, hlen]
  · funext n
    by_cases hn : n < blockLength
    · simp [appendFixedRoundCoordinates,
        ActualPostlaunchBlockMeasurability.roundListCoordinates, hn, hlen,
        List.getElem?_append_left]
    · have hle : blockLength ≤ n := Nat.le_of_not_gt hn
      have hright : left.length ≤ n := by rw [hlen]; exact hle
      simp only [appendFixedRoundCoordinates, if_neg hn,
        ActualPostlaunchBlockMeasurability.roundListCoordinates]
      rw [List.getElem?_append_right hright, hlen]

private theorem measurable_sigmaObservationActions :
    Measurable (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeActions code.2) := by
  apply measurable_of_sigma_sections_local
  intro block
  exact ActualPostlaunchBlockMeasurability.measurable_stepCodeActions

private theorem measurable_sigmaObservationFeedback :
    Measurable (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2) := by
  apply measurable_of_sigma_sections_local
  intro block
  exact ActualPostlaunchBlockMeasurability.measurable_stepCodeFeedback

/-- The literal actual full step code attached to a retained H record, tagged
by that record's own block. -/
def recordStepCodeObservation {source : SourceInput p} {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    StepCodeObservation p rate :=
  ⟨record.block, ActualPostlaunchStepMeasurability.stepCode record.input⟩

theorem recordStepCodeObservation_code {source : SourceInput p}
    {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    (recordStepCodeObservation record).2 =
      ActualPostlaunchStepMeasurability.stepCode record.input := rfl

/-- B's existing S decoder reconstructs every retained preparation,
diagnostic/observation code, result projection, and successor from the exact
record input. -/
theorem recordStepCodeObservation_reconstructs_full {source : SourceInput p}
    {rewards : GridRewardTable p}
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
      record.result = ActualPostlaunchPhysicalStep.step record.input :=
  ActualPostlaunchBlockMeasurability.recordStepCode_reconstructs_full record

/-- The D boundary outputs and their literal follower-carry readouts at one
actual completed boundary. -/
def boundaryPayload (source : SourceInput p) {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block)) : BoundaryPayload p rate :=
  let outputs := ActualPostlaunchBoundaryMeasurability.boundaryOutputCode
    (source, state)
  (outputs, fun i => ActualPostlaunchBoundaryMeasurability.boundaryCarryCode
    (outputs i))

/-- A retained H boundary code, tagged by its actual block. -/
def boundaryRecordObservation (source : SourceInput p)
    (record : ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate) :
    BoundaryObservation p rate :=
  ⟨record.block, boundaryPayload source record.state⟩

/-- The terminal code retains the final D boundary output/carry and P storage
coordinates of that same actual terminal state. -/
def terminalBoundaryRecordObservation (source : SourceInput p)
    (record : ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate) :
    TerminalObservation p rate :=
  ⟨record.block, (boundaryPayload source record.state,
    ActualPostlaunchPreparationMeasurability.encodeState record.state)⟩

/-- A retained successor record stores D's boundary/carry codes and P's
existing encoding of H's actual successor state. -/
def crossBoundaryRecordObservation {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.PostlaunchCrossBoundaryRecord p rate source) :
    CrossBoundaryObservation p rate :=
  ⟨record.block, ⟨record.next,
    (boundaryPayload source record.state,
      ActualPostlaunchPreparationMeasurability.encodeState record.successorState)⟩⟩

/-- H's actual current-block trace, read as tagged S codes in chronological
order. -/
def mixedBlockStepCodeCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)} {cursor : ℕ}
    {state : PostlaunchState (p := p) (rate := rate) block cursor}
    {stop : ℕ}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block cursor state stop) : LengthIndexObservation (StepCodeObservation p rate) :=
  ActualPostlaunchBlockMeasurability.mapRoundCoordinates
    (fun code : ActualPostlaunchStepMeasurability.StepCode p rate block =>
      (⟨block, code⟩ : StepCodeObservation p rate))
    (ActualPostlaunchBlockMeasurability.stepCodeListCoordinates
      (ActualPostlaunchBlockMeasurability.traceStepCodes trace))

/-- Every H record's S code is exactly its tagged list entry. -/
private theorem traceStepCodeObservations_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)} {cursor stop : ℕ}
    {state : PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block cursor state stop) :
    (ActualPostlaunchBlockMeasurability.traceStepCodes trace).map
      (fun code : ActualPostlaunchStepMeasurability.StepCode p rate block =>
        (⟨block, code⟩ : StepCodeObservation p rate)) =
    trace.records.map recordStepCodeObservation := by
  induction trace with
  | done state => rfl
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      rw [ActualPostlaunchBlockMeasurability.traceStepCodes_cons
        input hstate hsource hrewards result result_eq tail hlt]
      simp [recordStepCodeObservation,
        ActualCompletePhysicalHistory.MixedBlockTrace.records]
      exact ih

theorem mixedBlockStepCodeCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)} {cursor stop : ℕ}
    {state : PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block cursor state stop) :
    mixedBlockStepCodeCoordinates trace =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (trace.records.map recordStepCodeObservation) := by
  unfold mixedBlockStepCodeCoordinates
  rw [ActualPostlaunchBlockMeasurability.stepCodeListCoordinates_eq_roundListCoordinates,
    ActualPostlaunchBlockMeasurability.mapRoundCoordinates_roundListCoordinates,
    traceStepCodeObservations_eq_records]

def postlaunchSuffixStepCodeCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : LengthIndexObservation (StepCodeObservation p rate) :=
  match suffix with
  | .final trace _ => mixedBlockStepCodeCoordinates trace
  | .successor trace _ _ _ tail =>
      appendFixedRoundCoordinates (BootstrapObservedFollower.blockLength p block)
        (mixedBlockStepCodeCoordinates trace) (postlaunchSuffixStepCodeCoordinates tail)

def postlaunchSuffixBoundaryCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : LengthIndexObservation (BoundaryObservation p rate) :=
  match suffix with
  | .final trace _ =>
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        [⟨block, boundaryPayload source trace.finalState⟩]
  | .successor trace _ _ _ tail =>
      appendFixedRoundCoordinates 1
        (ActualPostlaunchBlockMeasurability.roundListCoordinates
          [⟨block, boundaryPayload source trace.finalState⟩])
        (postlaunchSuffixBoundaryCoordinates tail)

def postlaunchSuffixCrossBoundaryCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : LengthIndexObservation (CrossBoundaryObservation p rate) :=
  match suffix with
  | .final _ _ =>
      ActualPostlaunchBlockMeasurability.roundListCoordinates []
  | .successor trace hasNext next next_eq tail =>
      appendFixedRoundCoordinates 1
        (ActualPostlaunchBlockMeasurability.roundListCoordinates
          [crossBoundaryRecordObservation
            (ActualCompletePhysicalHistory.postlaunchCrossBoundaryRecord
              trace hasNext next next_eq)])
        (postlaunchSuffixCrossBoundaryCoordinates tail)

def postlaunchSuffixTerminalObservation {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : TerminalObservation p rate :=
  match suffix with
  | .final trace _ =>
      terminalBoundaryRecordObservation source
        (ActualCompletePhysicalHistory.postlaunchBoundaryRecord trace)
  | .successor _ _ _ _ tail => postlaunchSuffixTerminalObservation tail

abbrev SuffixCoreObservation (p : Parameters) (rate : RateInput p) :=
  LengthIndexObservation (StepCodeObservation p rate) ×
    (LengthIndexObservation (BoundaryObservation p rate) ×
      (LengthIndexObservation (CrossBoundaryObservation p rate) ×
        TerminalObservation p rate))

def postlaunchSuffixCoreObservation {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : SuffixCoreObservation p rate :=
  (postlaunchSuffixStepCodeCoordinates suffix,
    (postlaunchSuffixBoundaryCoordinates suffix,
      (postlaunchSuffixCrossBoundaryCoordinates suffix,
        postlaunchSuffixTerminalObservation suffix)))

private theorem boundaryPayload_reconstructs {source : SourceInput p}
    {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block)) (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
        ((boundaryPayload source state).1 i) =
        ActualPostlaunchPhysicalStep.boundaryOutput state i ∧
      (boundaryPayload source state).2 i =
        ActualInitializationBlockMeasurability.followerCarryCodeOf
          (ActualPostlaunchPhysicalStep.boundaryCarry state i) := by
  constructor
  · exact ActualPostlaunchBoundaryMeasurability.boundaryOutputCode_reconstructs
      (source, state) i
  · exact ActualPostlaunchBoundaryMeasurability.boundaryCarryCode_eq_actual
      (source, state) i

/-- The boundary code decodes to the exact retained H outputs and to the
actual follower carry computed from the same source/state input. -/
theorem boundaryRecordObservation_reconstructs (source : SourceInput p)
    (record : ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate)
    (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
        ((boundaryRecordObservation source record).2.1 i) = record.outputs i ∧
      (boundaryRecordObservation source record).2.2 i =
        ActualInitializationBlockMeasurability.followerCarryCodeOf
          (ActualPostlaunchPhysicalStep.boundaryCarry record.state i) := by
  have h := boundaryPayload_reconstructs (source := source) record.state i
  constructor
  · calc
      ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
          (((boundaryRecordObservation source record).2.1) i) =
          ActualPostlaunchPhysicalStep.boundaryOutput record.state i := h.1
      _ = record.outputs i := (record.outputs_eq i).symm
  · exact h.2

/-- The final code reconstructs both D's actual outputs/carries and the
terminal state through P's existing storage decoder. -/
theorem terminalBoundaryRecordObservation_reconstructs (source : SourceInput p)
    (record : ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate)
    (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
        ((terminalBoundaryRecordObservation source record).2.1.1 i) = record.outputs i ∧
      (terminalBoundaryRecordObservation source record).2.1.2 i =
        ActualInitializationBlockMeasurability.followerCarryCodeOf
          (ActualPostlaunchPhysicalStep.boundaryCarry record.state i) ∧
      ActualPostlaunchPreparationMeasurability.decodeState
        ⟨(terminalBoundaryRecordObservation source record).2.2,
          ⟨record.state, rfl⟩⟩ = record.state := by
  refine ⟨(boundaryRecordObservation_reconstructs source record i).1,
    (boundaryRecordObservation_reconstructs source record i).2, ?_⟩
  exact ActualPostlaunchPreparationMeasurability.decode_encodeState record.state

/-- D's successor storage coordinates are exactly P's encoding of the
retained H successor state, from the same original source and boundary state. -/
theorem crossBoundaryRecordObservation_successorCoordinates_eq {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.PostlaunchCrossBoundaryRecord p rate source) :
    (crossBoundaryRecordObservation record).2.2.2 =
      ActualPostlaunchBoundaryMeasurability.successorBoundaryCoordinates
        record.hasNext record.next_eq (source, record.state) := by
  change ActualPostlaunchPreparationMeasurability.encodeState record.successorState = _
  rw [record.crossSuccessorBoundary_eq]
  exact ActualPostlaunchBoundaryMeasurability.encode_crossSuccessorBoundary
    record.hasNext record.next_eq (source, record.state)

/-- P decodes the successor coordinates to H's retained state, and D's
same-input decoder identifies that state with the actual cross-boundary map. -/
theorem crossBoundaryRecordObservation_reconstructs {source : SourceInput p}
    (record : ActualCompletePhysicalHistory.PostlaunchCrossBoundaryRecord p rate source)
    (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
      (((boundaryPayload source record.state).1) i) =
        ActualPostlaunchPhysicalStep.boundaryOutput record.state i ∧
    (boundaryPayload source record.state).2 i =
      ActualInitializationBlockMeasurability.followerCarryCodeOf
        (ActualPostlaunchPhysicalStep.boundaryCarry record.state i) ∧
    ActualPostlaunchPreparationMeasurability.decodeState
      ⟨(crossBoundaryRecordObservation record).2.2.2,
        ⟨record.successorState, rfl⟩⟩ = record.successorState ∧
    record.successorState = ActualPostlaunchPhysicalStep.crossSuccessorBoundary
      record.hasNext record.next_eq source record.state := by
  refine ⟨(boundaryPayload_reconstructs record.state i).1,
    (boundaryPayload_reconstructs record.state i).2, ?_,
    record.crossSuccessorBoundary_eq⟩
  exact ActualPostlaunchPreparationMeasurability.decode_encodeState
    record.successorState

private theorem measurable_boundaryPayload_local {block : Fin (n_boot p)} :
    Measurable (fun input :
      SourceInput p × PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) =>
      boundaryPayload input.1 input.2) := by
  have houtputs := ActualPostlaunchBoundaryMeasurability.measurable_boundaryOutputCode
    (p := p) (rate := rate) (block := block)
  have hcarry : Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) =>
      fun i : Fin (p.m - 1) =>
        ActualPostlaunchBoundaryMeasurability.boundaryCarryCode
          (ActualPostlaunchBoundaryMeasurability.boundaryOutputCode input i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ActualPostlaunchBoundaryMeasurability.measurable_boundaryCarryCode.comp
      ((measurable_pi_apply i).comp houtputs)
  exact houtputs.prodMk hcarry

private theorem measurable_sigmaMk_stepCode (block : Fin (n_boot p)) :
    Measurable (fun code : ActualPostlaunchStepMeasurability.StepCode p rate block =>
      (⟨block, code⟩ : StepCodeObservation p rate)) :=
  measurable_sigmaMk_local block

private theorem measurable_mixedBlockStepCodeCoordinates {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      mixedBlockStepCodeCoordinates
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block x.2.2)) := by
  exact (ActualPostlaunchBlockMeasurability.measurable_mapRoundCoordinates
      (fun code : ActualPostlaunchStepMeasurability.StepCode p rate block =>
        (⟨block, code⟩ : StepCodeObservation p rate))
      (measurable_sigmaMk_stepCode (p := p) (rate := rate) block)).comp
    (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_stepCodeCoordinates
      (p := p) (rate := rate) (block := block))

private theorem measurable_mixedBlockBoundaryObservation {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      (⟨block, boundaryPayload x.1
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
          x.2.2).finalState⟩ : BoundaryObservation p rate)) := by
  have hinput : Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput
      p rate block 0 => (x.1,
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
          x.2.2).finalState)) :=
    measurable_fst.prodMk
      (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_finalState
        (p := p) (rate := rate) (block := block))
  exact (measurable_sigmaMk_local (β := fun _ : Fin (n_boot p) =>
      BoundaryPayload p rate) block).comp
    ((measurable_boundaryPayload_local (p := p) (rate := rate)
      (block := block)).comp hinput)

private theorem measurable_mixedBlockTerminalObservation {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      (⟨block,
        (boundaryPayload x.1
          (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
            x.2.2).finalState,
         ActualPostlaunchPreparationMeasurability.encodeState
          ((ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
            x.2.2).finalState))⟩ : TerminalObservation p rate)) := by
  have hinput : Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput
      p rate block 0 => (x.1,
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
          x.2.2).finalState)) :=
    measurable_fst.prodMk
      (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_finalState
        (p := p) (rate := rate) (block := block))
  have hpayload := (measurable_boundaryPayload_local (p := p) (rate := rate)
    (block := block)).comp hinput
  have hstate :=
    (ActualPostlaunchPreparationMeasurability.measurable_encodeState
      (p := p) (rate := rate) (block := block)
      (cursor := BootstrapObservedFollower.blockLength p block)).comp
      (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_finalState
        (p := p) (rate := rate) (block := block))
  exact (measurable_sigmaMk_local
      (β := fun b : Fin (n_boot p) =>
        BoundaryPayload p rate ×
          ActualPostlaunchPreparationMeasurability.StateCoordinates p rate b)
      block).comp (hpayload.prodMk hstate)

private theorem measurable_mixedBlockCrossBoundaryObservation
    {block next : Fin (n_boot p)} (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext) :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      (⟨block, ⟨next,
        (boundaryPayload x.1
          (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
            x.2.2).finalState,
         ActualPostlaunchPreparationMeasurability.encodeState
          (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq x.1
            (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
              x.2.2).finalState))⟩⟩ : CrossBoundaryObservation p rate)) := by
  have hinput : Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput
      p rate block 0 => (x.1,
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
          x.2.2).finalState)) :=
    measurable_fst.prodMk
      (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_finalState
        (p := p) (rate := rate) (block := block))
  have hpayload := (measurable_boundaryPayload_local (p := p) (rate := rate)
    (block := block)).comp hinput
  have hcross :=
    (ActualPostlaunchBoundaryMeasurability.measurable_crossSuccessorBoundary
      (p := p) (rate := rate) (block := block) hnext hnext_eq).comp hinput
  have hstate :=
    (ActualPostlaunchPreparationMeasurability.measurable_encodeState
      (p := p) (rate := rate) (block := next) (cursor := 0)).comp hcross
  have hnextSigma :=
    (measurable_sigmaMk_local (β := fun next : Fin (n_boot p) =>
      BoundaryPayload p rate ×
        ActualPostlaunchPreparationMeasurability.StateCoordinates p rate next)
      next).comp (hpayload.prodMk hstate)
  exact (measurable_sigmaMk_local
      (β := fun b : Fin (n_boot p) => CrossBoundaryFiber p rate b)
      block).comp hnextSigma

private theorem measurable_successorBlockInput {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext) :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      ((x.1, (x.2.1,
        ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq x.1
          (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
            x.2.2).finalState)) :
        ActualPostlaunchBlockMeasurability.BlockInput p rate next 0)) := by
  have hcrossInput : Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput
      p rate block 0 => (x.1,
        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1 block
          x.2.2).finalState)) :=
    measurable_fst.prodMk
      (ActualPostlaunchBlockMeasurability.measurable_foldMixedBlock_finalState
        (p := p) (rate := rate) (block := block))
  have hcross :=
    (ActualPostlaunchBoundaryMeasurability.measurable_crossSuccessorBoundary
      (p := p) (rate := rate) (block := block) hnext hnext_eq).comp
      hcrossInput
  exact measurable_fst.prodMk (measurable_snd.fst.prodMk hcross)

theorem postlaunchSuffix_stepCodeCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixStepCodeCoordinates suffix =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (suffix.records.map recordStepCodeObservation) := by
  induction suffix with
  | final trace last =>
      exact mixedBlockStepCodeCoordinates_eq_records trace
  | @successor block state trace hasNext next next_eq tail ih =>
      have hlen : trace.records.length =
          BootstrapObservedFollower.blockLength p block := by
        simpa using
          (ActualPostlaunchBlockMeasurability.MixedBlockTrace.record_count trace)
      change appendFixedRoundCoordinates
          (BootstrapObservedFollower.blockLength p block)
          (mixedBlockStepCodeCoordinates trace)
          (postlaunchSuffixStepCodeCoordinates tail) = _
      rw [mixedBlockStepCodeCoordinates_eq_records trace, ih]
      simp only [ActualCompletePhysicalHistory.PostlaunchSuffix.records,
        List.map_append]
      have hlenMap :
          (trace.records.map recordStepCodeObservation).length =
            BootstrapObservedFollower.blockLength p block := by
        simpa using hlen
      exact appendFixedRoundCoordinates_roundListAppend _ _ _ hlenMap

theorem postlaunchSuffix_boundaryCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixBoundaryCoordinates suffix =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (suffix.boundaries.map (boundaryRecordObservation source)) := by
  induction suffix with
  | final trace last => rfl
  | @successor block state trace hasNext next next_eq tail ih =>
      change appendFixedRoundCoordinates 1
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            [⟨block, boundaryPayload source trace.finalState⟩])
          (postlaunchSuffixBoundaryCoordinates tail) = _
      rw [ih]
      change appendFixedRoundCoordinates 1
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            [⟨block, boundaryPayload source trace.finalState⟩])
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            (tail.boundaries.map (boundaryRecordObservation source))) =
        ActualPostlaunchBlockMeasurability.roundListCoordinates
          (boundaryRecordObservation source
            (ActualCompletePhysicalHistory.postlaunchBoundaryRecord trace) ::
            tail.boundaries.map (boundaryRecordObservation source))
      exact appendFixedRoundCoordinates_roundListAppend _ _ _ rfl

theorem postlaunchSuffix_crossBoundaryCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixCrossBoundaryCoordinates suffix =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (suffix.crossBoundaryRecords.map crossBoundaryRecordObservation) := by
  induction suffix with
  | final trace last => rfl
  | @successor block state trace hasNext next next_eq tail ih =>
      change appendFixedRoundCoordinates 1
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            [crossBoundaryRecordObservation
              (ActualCompletePhysicalHistory.postlaunchCrossBoundaryRecord
                trace hasNext next next_eq)])
          (postlaunchSuffixCrossBoundaryCoordinates tail) = _
      rw [ih]
      change appendFixedRoundCoordinates 1
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            [crossBoundaryRecordObservation
              (ActualCompletePhysicalHistory.postlaunchCrossBoundaryRecord
                trace hasNext next next_eq)])
          (ActualPostlaunchBlockMeasurability.roundListCoordinates
            (tail.crossBoundaryRecords.map crossBoundaryRecordObservation)) =
        ActualPostlaunchBlockMeasurability.roundListCoordinates
          (crossBoundaryRecordObservation
            (ActualCompletePhysicalHistory.postlaunchCrossBoundaryRecord
              trace hasNext next next_eq) ::
            tail.crossBoundaryRecords.map crossBoundaryRecordObservation)
      exact appendFixedRoundCoordinates_roundListAppend _ _ _ rfl

def postlaunchSuffixTerminalBoundaryRecord {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) : ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate :=
  match suffix with
  | .final trace _ => ActualCompletePhysicalHistory.postlaunchBoundaryRecord trace
  | .successor _ _ _ _ tail => postlaunchSuffixTerminalBoundaryRecord tail

theorem postlaunchSuffix_terminalObservation_eq_record {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixTerminalObservation suffix =
      terminalBoundaryRecordObservation source
        (postlaunchSuffixTerminalBoundaryRecord suffix) := by
  induction suffix with
  | final trace last => rfl
  | @successor block state trace hasNext next next_eq tail ih => exact ih

private theorem runPostlaunchSuffixFromTrace_final
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : PostlaunchState (p := p) (rate := rate) block 0)
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block 0 state (BootstrapObservedFollower.blockLength p block))
    (hlast : block.val + 1 = n_boot p) :
    ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace p rate source rewards
      block state trace = .final trace hlast := by
  unfold ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace
  simp [hlast]

private theorem runPostlaunchSuffixFromTrace_successor
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : PostlaunchState (p := p) (rate := rate) block 0)
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block 0 state (BootstrapObservedFollower.blockLength p block))
    (hnext : block.val + 1 < n_boot p) :
    ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace p rate source rewards
      block state trace =
      .successor trace hnext (ActualInitializationRun.successorBlock p block hnext) rfl
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate source rewards
          (ActualInitializationRun.successorBlock p block hnext)
          (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext rfl source
            trace.finalState)) := by
  unfold ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace
  have hlast : ¬ block.val + 1 = n_boot p := by omega
  simp [hlast]
  rfl

private theorem measurable_runPostlaunchSuffixCoreObservation_aux
    (n : ℕ) : ∀ (block : Fin (n_boot p)), n_boot p - block.val = n →
      Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput
          p rate block 0 =>
        postlaunchSuffixCoreObservation
          (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
            block x.2.2)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro block hmeasure
      by_cases hnext : block.val + 1 < n_boot p
      · let next := ActualInitializationRun.successorBlock p block hnext
        have hnext_eq : next = ActualInitializationRun.successorBlock p block hnext := rfl
        have hdecrease : n_boot p - next.val < n := by
          have hval : next.val = block.val + 1 := rfl
          rw [hval]
          omega
        have hnextInput : Measurable (fun x :
            ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              ((x.1, (x.2.1,
                ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq x.1
                  (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                    block x.2.2).finalState)) :
                ActualPostlaunchBlockMeasurability.BlockInput p rate next 0)) :=
          measurable_successorBlockInput (p := p) (rate := rate) hnext hnext_eq
        have htail :=
          (ih (n_boot p - next.val) hdecrease next rfl).comp hnextInput
        have htraceCode :=
          measurable_mixedBlockStepCodeCoordinates (p := p) (rate := rate)
            (block := block)
        have htraceBoundary :=
          measurable_mixedBlockBoundaryObservation (p := p) (rate := rate)
            (block := block)
        have htraceCross :=
          measurable_mixedBlockCrossBoundaryObservation (p := p) (rate := rate)
            hnext hnext_eq
        have htraceBoundaryList := roundListCoordinates_cons
          (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
            (⟨block, boundaryPayload x.1
              (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                block x.2.2).finalState⟩ : BoundaryObservation p rate))
          (fun _ => ([] : List (BoundaryObservation p rate)))
          htraceBoundary measurable_const
        have htraceCrossList := roundListCoordinates_cons
          (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
            (⟨block, ⟨next,
              (boundaryPayload x.1
                (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                  block x.2.2).finalState,
               ActualPostlaunchPreparationMeasurability.encodeState
                (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq x.1
                  (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                    block x.2.2).finalState))⟩⟩ : CrossBoundaryObservation p rate))
          (fun _ => ([] : List (CrossBoundaryObservation p rate)))
          htraceCross measurable_const
        have htailCode := measurable_fst.comp htail
        have htailBoundaryCore := measurable_snd.comp htail
        have htailBoundary := measurable_fst.comp htailBoundaryCore
        have htailCrossTerminal := measurable_snd.comp htailBoundaryCore
        have htailCross := measurable_fst.comp htailCrossTerminal
        have htailTerminal := measurable_snd.comp htailCrossTerminal
        have hcode : Measurable (fun x :
            ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              appendFixedRoundCoordinates (BootstrapObservedFollower.blockLength p block)
                (mixedBlockStepCodeCoordinates
                  (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                    block x.2.2))
                ((postlaunchSuffixCoreObservation
                  (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                    (x.1) (x.2.1) next
                    (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq
                      x.1 (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                        x.2.1 block x.2.2).finalState))).1)) := by
          exact (measurable_appendFixedRoundCoordinates
            (α := StepCodeObservation p rate)
            (BootstrapObservedFollower.blockLength p block)).comp
            (htraceCode.prodMk htailCode)
        have hboundary : Measurable (fun x :
            ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              appendFixedRoundCoordinates 1
                (ActualPostlaunchBlockMeasurability.roundListCoordinates
                  [⟨block, boundaryPayload x.1
                    (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                      x.2.1 block x.2.2).finalState⟩])
                ((postlaunchSuffixCoreObservation
                  (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                    x.1 x.2.1 next
                    (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq
                      x.1 (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                        x.2.1 block x.2.2).finalState))).2.1)) := by
          exact (measurable_appendFixedRoundCoordinates
            (α := BoundaryObservation p rate) 1).comp
            (htraceBoundaryList.prodMk htailBoundary)
        have hcross : Measurable (fun x :
            ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              appendFixedRoundCoordinates 1
                (ActualPostlaunchBlockMeasurability.roundListCoordinates
                  [⟨block, ⟨next,
                    (boundaryPayload x.1
                      (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                        x.2.1 block x.2.2).finalState,
                     ActualPostlaunchPreparationMeasurability.encodeState
                      (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext
                        hnext_eq x.1
                        (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                          x.2.1 block x.2.2).finalState))⟩⟩])
                ((postlaunchSuffixCoreObservation
                  (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                    x.1 x.2.1 next
                    (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq
                      x.1 (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                        x.2.1 block x.2.2).finalState))).2.2.1)) := by
          exact (measurable_appendFixedRoundCoordinates
            (α := CrossBoundaryObservation p rate) 1).comp
            (htraceCrossList.prodMk htailCross)
        have hterminal : Measurable (fun x :
            ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              (postlaunchSuffixCoreObservation
                (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                  x.1 x.2.1 next
                  (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext hnext_eq
                    x.1 (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1
                      x.2.1 block x.2.2).finalState))).2.2.2) := htailTerminal
        have hshape (x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0) :
            ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
                block x.2.2 =
              .successor
                (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                  block x.2.2)
                hnext next hnext_eq
                (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
                  next (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext
                    hnext_eq x.1
                    (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                      block x.2.2).finalState)) := by
          change ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace p rate
              x.1 x.2.1 block x.2.2
              (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                block x.2.2) = _
          exact runPostlaunchSuffixFromTrace_successor x.1 x.2.1 block x.2.2
            (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
              block x.2.2) hnext
        have hcoreShape :
            (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              postlaunchSuffixCoreObservation
                (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                  x.1 x.2.1 block x.2.2)) =
            (fun x => postlaunchSuffixCoreObservation
              (.successor
                (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                  block x.2.2)
                hnext next hnext_eq
                (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
                  next (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext
                    hnext_eq x.1
                    (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                      block x.2.2).finalState)))) := by
          funext x
          exact congrArg postlaunchSuffixCoreObservation (hshape x)
        rw [hcoreShape]
        simp only [postlaunchSuffixCoreObservation,
          postlaunchSuffixStepCodeCoordinates,
          postlaunchSuffixBoundaryCoordinates,
          postlaunchSuffixCrossBoundaryCoordinates,
          postlaunchSuffixTerminalObservation]
        exact hcode.prodMk (hboundary.prodMk (hcross.prodMk hterminal))
      · have hlast : block.val + 1 = n_boot p := by omega
        have htraceCode :=
          measurable_mixedBlockStepCodeCoordinates (p := p) (rate := rate)
            (block := block)
        have htraceBoundary :=
          measurable_mixedBlockBoundaryObservation (p := p) (rate := rate)
            (block := block)
        have htraceBoundaryList := roundListCoordinates_cons
          (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
            (⟨block, boundaryPayload x.1
              (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                block x.2.2).finalState⟩ : BoundaryObservation p rate))
          (fun _ => ([] : List (BoundaryObservation p rate)))
          htraceBoundary measurable_const
        have hterminal :=
          measurable_mixedBlockTerminalObservation (p := p) (rate := rate)
            (block := block)
        have hshape (x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0) :
            ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
                block x.2.2 =
              .final
                (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                  block x.2.2) hlast := by
          change ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace p rate
              x.1 x.2.1 block x.2.2
              (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                block x.2.2) = _
          exact runPostlaunchSuffixFromTrace_final x.1 x.2.1 block x.2.2
            (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
              block x.2.2) hlast
        have hcoreShape :
            (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
              postlaunchSuffixCoreObservation
                (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
                  x.1 x.2.1 block x.2.2)) =
            (fun x => postlaunchSuffixCoreObservation
              (.final
                (ActualCompletePhysicalHistory.foldMixedBlock p rate x.1 x.2.1
                  block x.2.2) hlast)) := by
          funext x
          exact congrArg postlaunchSuffixCoreObservation (hshape x)
        rw [hcoreShape]
        simp only [postlaunchSuffixCoreObservation,
          postlaunchSuffixStepCodeCoordinates,
          postlaunchSuffixBoundaryCoordinates,
          postlaunchSuffixCrossBoundaryCoordinates,
          postlaunchSuffixTerminalObservation]
        exact htraceCode.prodMk
          (htraceBoundaryList.prodMk (measurable_const.prodMk hterminal))

theorem measurable_runPostlaunchSuffixCoreObservation
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixCoreObservation
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  measurable_runPostlaunchSuffixCoreObservation_aux
    (p := p) (rate := rate) (n_boot p - block.val) block rfl

theorem measurable_runPostlaunchSuffix_stepCodeCoordinates
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixStepCodeCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (measurable_runPostlaunchSuffixCoreObservation (p := p) (rate := rate)
    (block := block)).fst

theorem measurable_runPostlaunchSuffix_boundaryCoordinates
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixBoundaryCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (measurable_runPostlaunchSuffixCoreObservation (p := p) (rate := rate)
    (block := block)).snd.fst

theorem measurable_runPostlaunchSuffix_crossBoundaryCoordinates
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixCrossBoundaryCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (measurable_runPostlaunchSuffixCoreObservation (p := p) (rate := rate)
    (block := block)).snd.snd.fst

theorem measurable_runPostlaunchSuffix_terminalObservation
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixTerminalObservation
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (measurable_runPostlaunchSuffixCoreObservation (p := p) (rate := rate)
    (block := block)).snd.snd.snd

private theorem recordCodeActions_eq {source : SourceInput p}
    {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    ActualPostlaunchBlockMeasurability.stepCodeActions
        (recordStepCodeObservation record).2 = record.actions := by
  have hfull := ActualPostlaunchBlockMeasurability.recordStepCode_reconstructs_full record
  change ActualPostlaunchBlockMeasurability.stepCodeActions
      (ActualPostlaunchStepMeasurability.stepCode record.input) =
    ActualPostlaunchPhysicalStep.actionProfile record.result.prepared
  rw [record.result_eq]
  exact hfull.1.2.2.1

private theorem recordCodeFeedback_eq {source : SourceInput p}
    {rewards : GridRewardTable p}
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards) :
    ActualPostlaunchBlockMeasurability.stepCodeFeedback
        (recordStepCodeObservation record).2 = record.feedback := by
  have hfull := ActualPostlaunchBlockMeasurability.recordStepCode_reconstructs_full record
  change ActualPostlaunchBlockMeasurability.stepCodeFeedback
      (ActualPostlaunchStepMeasurability.stepCode record.input) =
    ActualPostlaunchPhysicalStep.physicalFeedback record.result.prepared
  rw [record.result_eq]
  exact hfull.1.2.2.2.1

/-- Whole action history read from the tagged S codes, with absent positions
retaining B's explicit `Unit` tag. -/
def postlaunchSuffixActionCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    LengthIndexObservation (FiniteBanditModel.ActionProfile p.m p.K) :=
  ActualPostlaunchBlockMeasurability.mapRoundCoordinates
    (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeActions code.2)
    (postlaunchSuffixStepCodeCoordinates suffix)

/-- Whole simultaneous grid feedback history read from the same tagged S
codes. -/
def postlaunchSuffixFeedbackCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    LengthIndexObservation (Fin p.m → Fin (D p + 1)) :=
  ActualPostlaunchBlockMeasurability.mapRoundCoordinates
    (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2)
    (postlaunchSuffixStepCodeCoordinates suffix)

/-- The chronological arm coordinates for one player are read from the
simultaneous actual action profile. -/
def postlaunchSuffixPlayerArmCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) (player : Fin p.m) : LengthIndexObservation (Fin p.K) :=
  ActualPostlaunchBlockMeasurability.mapRoundCoordinates
    (fun actions : FiniteBanditModel.ActionProfile p.m p.K => actions player)
    (postlaunchSuffixActionCoordinates suffix)

/-- The chronological real-valued quantized feedback for one player is the
literal grid-to-real scaling of the same retained own-feedback coordinate. -/
def postlaunchSuffixPlayerQuantizedFeedbackCoordinates {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) (player : Fin p.m) : LengthIndexObservation ℝ :=
  ActualPostlaunchBlockMeasurability.mapRoundCoordinates
    (fun feedback : Fin p.m → Fin (D p + 1) =>
      ((feedback player).val : ℝ) / (D p : ℝ))
    (postlaunchSuffixFeedbackCoordinates suffix)

theorem postlaunchSuffix_actionCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixActionCoordinates suffix =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions) := by
  unfold postlaunchSuffixActionCoordinates
  rw [postlaunchSuffix_stepCodeCoordinates_eq_records,
    ActualPostlaunchBlockMeasurability.mapRoundCoordinates_roundListCoordinates]
  have hmap :
      (suffix.records.map recordStepCodeObservation).map
          (fun code : StepCodeObservation p rate =>
            ActualPostlaunchBlockMeasurability.stepCodeActions code.2) =
        suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions := by
    induction suffix.records with
    | nil => rfl
    | cons record records ih =>
        change ActualPostlaunchBlockMeasurability.stepCodeActions
            (recordStepCodeObservation record).2 ::
            ((records.map recordStepCodeObservation).map
              (fun code : StepCodeObservation p rate =>
                ActualPostlaunchBlockMeasurability.stepCodeActions code.2)) =
          record.actions :: records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions
        rw [recordCodeActions_eq, ih]
  rw [hmap]

theorem postlaunchSuffix_feedbackCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) :
    postlaunchSuffixFeedbackCoordinates suffix =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        (suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback) := by
  unfold postlaunchSuffixFeedbackCoordinates
  rw [postlaunchSuffix_stepCodeCoordinates_eq_records,
    ActualPostlaunchBlockMeasurability.mapRoundCoordinates_roundListCoordinates]
  have hmap :
      (suffix.records.map recordStepCodeObservation).map
          (fun code : StepCodeObservation p rate =>
            ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2) =
        suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback := by
    induction suffix.records with
    | nil => rfl
    | cons record records ih =>
        change ActualPostlaunchBlockMeasurability.stepCodeFeedback
            (recordStepCodeObservation record).2 ::
            ((records.map recordStepCodeObservation).map
              (fun code : StepCodeObservation p rate =>
                ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2)) =
          record.feedback :: records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback
        rw [recordCodeFeedback_eq, ih]
  rw [hmap]

theorem postlaunchSuffix_playerArmCoordinates_eq_records {source : SourceInput p}
    {rewards : GridRewardTable p} {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) (player : Fin p.m) :
    postlaunchSuffixPlayerArmCoordinates suffix player =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        ((suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.actions).map
          (fun actions => actions player)) := by
  unfold postlaunchSuffixPlayerArmCoordinates
  rw [postlaunchSuffix_actionCoordinates_eq_records,
    ActualPostlaunchBlockMeasurability.mapRoundCoordinates_roundListCoordinates]

theorem postlaunchSuffix_playerQuantizedFeedbackCoordinates_eq_records
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      block state) (player : Fin p.m) :
    postlaunchSuffixPlayerQuantizedFeedbackCoordinates suffix player =
      ActualPostlaunchBlockMeasurability.roundListCoordinates
        ((suffix.records.map ActualCompletePhysicalHistory.MixedRoundRecord.feedback).map
          (fun feedback => ((feedback player).val : ℝ) / (D p : ℝ))) := by
  unfold postlaunchSuffixPlayerQuantizedFeedbackCoordinates
  rw [postlaunchSuffix_feedbackCoordinates_eq_records,
    ActualPostlaunchBlockMeasurability.mapRoundCoordinates_roundListCoordinates]

theorem measurable_runPostlaunchSuffix_actionCoordinates
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixActionCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (ActualPostlaunchBlockMeasurability.measurable_mapRoundCoordinates
    (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeActions code.2)
    measurable_sigmaObservationActions).comp
      (measurable_runPostlaunchSuffix_stepCodeCoordinates (p := p) (rate := rate)
        (block := block))

theorem measurable_runPostlaunchSuffix_feedbackCoordinates
    {block : Fin (n_boot p)} :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixFeedbackCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2)) :=
  (ActualPostlaunchBlockMeasurability.measurable_mapRoundCoordinates
    (fun code : StepCodeObservation p rate =>
      ActualPostlaunchBlockMeasurability.stepCodeFeedback code.2)
    measurable_sigmaObservationFeedback).comp
      (measurable_runPostlaunchSuffix_stepCodeCoordinates (p := p) (rate := rate)
        (block := block))

theorem measurable_runPostlaunchSuffix_playerArmCoordinates
    {block : Fin (n_boot p)} (player : Fin p.m) :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixPlayerArmCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2) player) := by
  have hread : Measurable
      (fun actions : FiniteBanditModel.ActionProfile p.m p.K => actions player) :=
    measurable_pi_apply player
  exact (ActualPostlaunchBlockMeasurability.measurable_mapRoundCoordinates _ hread).comp
    (measurable_runPostlaunchSuffix_actionCoordinates (p := p) (rate := rate)
      (block := block))

theorem measurable_runPostlaunchSuffix_playerQuantizedFeedbackCoordinates
    {block : Fin (n_boot p)} (player : Fin p.m) :
    Measurable (fun x : ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 =>
      postlaunchSuffixPlayerQuantizedFeedbackCoordinates
        (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate x.1 x.2.1
          block x.2.2) player) := by
  have hread : Measurable (fun feedback : Fin p.m → Fin (D p + 1) =>
      ((feedback player).val : ℝ) / (D p : ℝ)) :=
    (measurable_of_countable fun grid : Fin (D p + 1) =>
      ((grid.val : ℝ) / (D p : ℝ))).comp (measurable_pi_apply player)
  exact (ActualPostlaunchBlockMeasurability.measurable_mapRoundCoordinates _ hread).comp
    (measurable_runPostlaunchSuffix_feedbackCoordinates (p := p) (rate := rate)
      (block := block))

end Bandits.Support.ActualPostlaunchSuffixMeasurability

end
