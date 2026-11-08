/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockFoldExact
public import Bandits.Support.ActualInitializationCombinedBoundaryMeasurability

/-!
# Joint source-and-carry measurability of one actual block handoff

For the original whole source, fixed whole grid rewards, and existing
fixed-constant block carry, this module composes the accepted physical block
code with the completed-boundary observation. The physical code remains in
the returned product alongside the observation, so its complete round codes
and own-entry histories remain available to a later recursion.

The endpoint restrictions are produced from the actual fold invariant and
its final-state identities. They are never supplied as input hypotheses.
The handoff decoder is identified with the existing `R.combinedBoundaryHandoff`
on that same physical `R.foldBlock`. A continuing carry is exposed only on
the actual no-launch, real-successor subtype; the sum-tagged observation keeps
launch and terminal exhaustion distinct on every endpoint.

This is a one-block internal composition. It does not assert runFrom,
whole-horizon, probability, locality, chronological-law, or regret closure.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`, and
`sources/zip4/manuscript/06_interruptions.tex:235-297`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationBlockFoldMeasurability
open Bandits.Support.ActualInitializationBlockFoldExact
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability

namespace Bandits.Support.ActualInitializationBlockHandoffMeasurability

abbrev Parameters := ActualInitializationCombinedBoundaryMeasurability.Parameters
abbrev RateInput := ActualInitializationCombinedBoundaryMeasurability.RateInput

variable {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
  {C_star C_h : ℝ}

/-- Reindex the actual `R.foldBlock` result by the two equalities carried by
the existing `BlockInput`. This keeps the shared constants fixed in the
handoff interface while retaining the original source and carry. -/
def actualBlockFoldOfInput
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    BlockFoldOutput p rate block input.1 rewards C_star C_h 0 := by
  rcases input with ⟨source, ⟨carry, hC_star, hC_h⟩⟩
  cases hC_star
  cases hC_h
  exact ActualInitializationRun.foldBlock p rate block source rewards carry

/-- The endpoint base is assembled from E's physical code and the same
original source. Its phase and full follower codes are the final-state fields
of the accepted physical fold code; the complete round-code list remains in
that code for the composition below. -/
def physicalBlockEndpointBaseOfInput
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    ActualInitializationCombinedBoundaryMeasurability.EndpointBase p rate block :=
  (input.1,
    ((ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput
      (C_star := C_star) (C_h := C_h) rewards input).phase,
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput
        (C_star := C_star) (C_h := C_h) rewards input).followers))

/-- Every endpoint coordinate restriction follows from the actual completed
fold invariant and E's proved final-state identities. -/
theorem physicalBlockEndpointBase_valid
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    ActualInitializationCombinedBoundaryMeasurability.endpointCoordinatesValid
      p rate block C_star C_h (physicalBlockEndpointBaseOfInput rewards input) := by
  rcases input with ⟨source, ⟨carry, hC_star, hC_h⟩⟩
  cases hC_star
  cases hC_h
  let foldInput : ActualInitializationBlockMeasurability.BlockInput
      p rate block carry.C_star carry.C_h := (source, ⟨carry, rfl, rfl⟩)
  let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
  have hphysical :=
    ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput
      rewards foldInput
  have hfinal :=
    ActualInitializationBlockFoldExact.actualBlockFoldCodeOfInput_final_states
      rewards foldInput
  have hphase :
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards foldInput).phase =
        ActualInitializationBlockMeasurability.continuationCodeOf folded.phase := by
    calc
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards foldInput).phase =
          (ActualInitializationBlockFoldMeasurability.actualBlockFoldCodeOfInput
            rewards foldInput).phase :=
        congrArg ActualInitializationBlockMeasurability.BlockFoldCode.phase hphysical
      _ = ActualInitializationBlockMeasurability.continuationCodeOf folded.phase := by
        simpa [ActualInitializationBlockFoldMeasurability.actualBlockFoldCodeOfInput,
          folded] using
          hfinal.1
  have hfollowers : ∀ i,
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards foldInput).followers i =
        ActualInitializationRoundMeasurability.followerCodeOfState p rate block
          (folded.followers i) := by
    intro i
    calc
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards foldInput).followers i =
          (ActualInitializationBlockFoldMeasurability.actualBlockFoldCodeOfInput
            rewards foldInput).followers i :=
        congrArg (fun code => code.followers i) hphysical
      _ = ActualInitializationRoundMeasurability.followerCodeOfState p rate block
          (folded.followers i) := by
        simpa [ActualInitializationBlockFoldMeasurability.actualBlockFoldCodeOfInput,
          folded] using
          hfinal.2 i
  change
    ActualInitializationCombinedBoundaryMeasurability.endpointPhaseValid p block
        carry.C_star carry.C_h source
          (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput
            rewards foldInput).phase ∧
      (∀ i, ActualInitializationRun.followerAtCursor p rate block
        (BootstrapObservedFollower.blockLength p block)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
          ((ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput
            rewards foldInput).followers i)))
  constructor
  · rw [hphase]
    exact ActualInitializationCombinedBoundaryMeasurability.endpointPhaseValid_of_blockFold
      folded
  · intro i
    rw [hfollowers i]
    simpa only [ActualInitializationRoundMeasurability.followerStateOfCode_encode] using
      ActualInitializationRun.blockFold_follower_complete folded i

/-- The actual physical endpoint input, with its validity proof constructed
from the actual fold rather than supplied by the caller. -/
def physicalBlockEndpointInputOfInput
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    ActualInitializationCombinedBoundaryMeasurability.BoundaryEndpointInput
      p rate block C_star C_h :=
  ⟨physicalBlockEndpointBaseOfInput rewards input,
    physicalBlockEndpointBase_valid rewards input⟩

/-- The endpoint assembled from E's code is exactly C's endpoint encoding of
the same original `R.foldBlock`, including the actual phase and every actual
follower state. -/
theorem physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    physicalBlockEndpointInputOfInput rewards input =
      ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold
        (actualBlockFoldOfInput rewards input) := by
  rcases input with ⟨source, ⟨carry, hC_star, hC_h⟩⟩
  cases hC_star
  cases hC_h
  apply Subtype.ext
  rfl

/-- The endpoint map is Borel jointly in the original source and the
existing fixed-constant carry. Its codomain uses C's existing product/subtype
measurable structure. -/
theorem measurable_physicalBlockEndpointInputOfInput
    (rewards : GridRewardTable p) :
    Measurable (physicalBlockEndpointInputOfInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) := by
  apply measurable_comap_iff.mpr
  change Measurable (physicalBlockEndpointBaseOfInput
    (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
    rewards)
  have hcode :=
    ActualInitializationBlockFoldExact.measurable_physicalBlockFoldCodeOfInput
      (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
      rewards
  have hcoordinates :=
    (ActualInitializationBlockFoldMeasurability.measurable_blockFoldCodeCoordinates
      (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)).comp hcode
  have hphase : Measurable (fun input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h =>
        (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).phase) :=
    measurable_fst.comp hcoordinates
  have hfollowers : Measurable
      (fun input : ActualInitializationBlockMeasurability.BlockInput
        p rate block C_star C_h =>
          (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).followers) :=
    measurable_fst.comp (measurable_snd.comp hcoordinates)
  change Measurable (fun input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h =>
        (input.1,
          ((ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).phase,
            (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput
              rewards input).followers)))
  exact measurable_fst.prodMk (hphase.prodMk hfollowers)

/-- The product retains E's complete physical fold code beside C's complete
boundary observation. In particular, the original ordered round-code list
and the whole source are still present for a later block recursion. -/
def actualBlockHandoffCompositionOfInput
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :=
  (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input,
    ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservationOfInput
      rate block C_star C_h (physicalBlockEndpointInputOfInput rewards input))

/-- The full source-and-carry handoff composition is Borel for each fixed
whole reward grid. -/
theorem measurable_actualBlockHandoffCompositionOfInput
    (rewards : GridRewardTable p) :
    Measurable (actualBlockHandoffCompositionOfInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) := by
  exact
    (ActualInitializationBlockFoldExact.measurable_physicalBlockFoldCodeOfInput
      (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
      rewards).prodMk
      ((ActualInitializationCombinedBoundaryMeasurability.measurable_combinedBoundaryObservationOfInput
        rate block C_star C_h).comp
        (measurable_physicalBlockEndpointInputOfInput rewards))

/-- The retained full round code in the composition is exactly E's admitted
physical code, not a newly run numerical decoder. -/
theorem actualBlockHandoffComposition_code
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    (actualBlockHandoffCompositionOfInput rewards input).1 =
      ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input := rfl

/-- The composed observation retains the exact original whole source,
including the private coordinates and original selected-row coordinate. -/
theorem actualBlockHandoffComposition_source
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    (actualBlockHandoffCompositionOfInput rewards input).2.originalSource = input.1 := rfl

/-- The composition's round-code list is E's complete ordered physical
encoding of the same `R.foldBlock` records. It retains every stored round
payload and does not filter error or exceptional tags. -/
theorem actualBlockHandoffComposition_rounds_eq_physicalRoundCodes
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    (actualBlockHandoffCompositionOfInput rewards input).1.rounds =
      ActualInitializationBlockFoldExact.physicalRoundCodes C_star C_h
        (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records
        (ActualInitializationBlockFoldExact.foldBlock_records_block
          input.1 rewards input.2.1) := by
  change
    (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).rounds = _
  rfl

/-- Simultaneous action and whole-grid feedback histories in the returned
physical code are those of the same original physical records. -/
theorem actualBlockHandoffComposition_actions_feedback
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    (actualBlockHandoffCompositionOfInput rewards input).1.actions =
        (PhysicalRoundRecord.actions
          (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records).map
          Sum.inr ∧
      (actualBlockHandoffCompositionOfInput rewards input).1.feedback =
        (PhysicalRoundRecord.feedback
          (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records).map
          Sum.inr := by
  change
    (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).actions = _ ∧
      (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).feedback = _
  rw [ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput]
  exact ActualInitializationBlockFoldExact.actualBlockFoldCodeOfInput_actions_feedback
    rewards input

/-- The same physical code exposes E's full own-entry histories, including
the complete stored round outputs used by subsequent recursion. -/
theorem actualBlockHandoffComposition_own_entries
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) (player : Fin p.m) :
    ((actualBlockHandoffCompositionOfInput rewards input).1.rounds.map
      (fun code => ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
        rate block code player)) =
      (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records.map
        (fun record => Sum.inr (record.result.actions player, record.result.feedback player)) := by
  change
    (ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput rewards input).rounds.map
      (fun code => ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
        rate block code player) = _
  rw [ActualInitializationBlockFoldExact.physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput]
  exact ActualInitializationBlockFoldExact.actualBlockFoldCodeOfInput_own_entries
    rewards input player

/-- Decoding the composed observation recovers the existing actual boundary
handoff on the same reindexed `R.foldBlock`, with source and constants taken
from the original input. -/
theorem actualBlockHandoffComposition_reconstructs_actual
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
        (actualBlockHandoffCompositionOfInput rewards input).2 =
      ActualInitializationRun.combinedBoundaryHandoff p rate block input.1 rewards
        C_star C_h (actualBlockFoldOfInput rewards input) := by
  let folded := actualBlockFoldOfInput rewards input
  let physicalObservation :=
    ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservationOfInput
      rate block C_star C_h (physicalBlockEndpointInputOfInput rewards input)
  let foldObservation :=
    ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservationOfInput
      rate block C_star C_h
        (ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold folded)
  have hendpoint := physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold
    rewards input
  have hobservations : physicalObservation = foldObservation :=
    congrArg (ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservationOfInput
      rate block C_star C_h) hendpoint
  change ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
    physicalObservation = _
  have hdecoded :
      ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
          physicalObservation =
        ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
          foldObservation := by
    apply ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoff_ext_of_fields
    · change physicalObservation.originalSource = foldObservation.originalSource
      exact congrArg
        ActualInitializationCombinedBoundaryMeasurability.CombinedBoundaryObservation.originalSource
        hobservations
    · change
        (fun i => ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate (physicalObservation.uncheckedBoundaryOutputs i)) =
        (fun i => ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate (foldObservation.uncheckedBoundaryOutputs i))
      exact congrArg (fun observation => fun i =>
        ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
          (observation.uncheckedBoundaryOutputs i)) hobservations
    · change physicalObservation.selectedRow = foldObservation.selectedRow
      exact congrArg
        ActualInitializationCombinedBoundaryMeasurability.CombinedBoundaryObservation.selectedRow
        hobservations
    · change physicalObservation.selectedTarget = foldObservation.selectedTarget
      exact congrArg
        ActualInitializationCombinedBoundaryMeasurability.CombinedBoundaryObservation.selectedTarget
        hobservations
    · change
        ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
          physicalObservation =
        ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
          foldObservation
      exact congrArg
        ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
        hobservations
  exact hdecoded.trans
    (ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservation_reconstructs_actual
      folded)

/-- The next-carry component of the composed full observation is C's actual
sum-tagged carry-or-absence observation on every path. -/
theorem actualBlockHandoffComposition_nextCarry
    (rewards : GridRewardTable p)
    (input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    (actualBlockHandoffCompositionOfInput rewards input).2.nextCarry =
      ActualInitializationCombinedBoundaryMeasurability.endpointNextCarryObservation
        rate block C_star C_h (physicalBlockEndpointInputOfInput rewards input) := rfl

/-- The full sum-tagged next-carry observation remains Borel after composing
with the actual source-and-carry endpoint map. Launch and terminal exhaustion
are the absent tag, and only an actual continuing successor carries a code. -/
theorem measurable_actualBlockHandoffComposition_nextCarry
    (rewards : GridRewardTable p) :
    Measurable (fun input : ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h =>
        ActualInitializationCombinedBoundaryMeasurability.endpointNextCarryObservation
          rate block C_star C_h (physicalBlockEndpointInputOfInput rewards input)) :=
  (ActualInitializationCombinedBoundaryMeasurability.measurable_endpointNextCarryObservation
    rate block C_star C_h).comp (measurable_physicalBlockEndpointInputOfInput rewards)

/-- The no-launch slice of the actual source-and-carry block input. -/
def actualBlockPrelaunchSet (rewards : GridRewardTable p) :
    Set (ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h) :=
  {input | physicalBlockEndpointInputOfInput rewards input ∈
    ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet
      p rate block C_star C_h}

/-- A prelaunch input inherits the original block-input measurable structure
through its subtype coercion. -/
abbrev ActualBlockPrelaunchInput (rewards : GridRewardTable p) :=
  {input : ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h //
    input ∈ actualBlockPrelaunchSet rewards}

instance actualBlockPrelaunchInputMeasurableSpace (rewards : GridRewardTable p) :
    MeasurableSpace (ActualBlockPrelaunchInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) :=
  MeasurableSpace.comap Subtype.val inferInstance

theorem measurableSet_actualBlockPrelaunchSet (rewards : GridRewardTable p) :
    MeasurableSet (actualBlockPrelaunchSet (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) := by
  change MeasurableSet ((physicalBlockEndpointInputOfInput rewards) ⁻¹'
    ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet
      p rate block C_star C_h)
  exact measurableSet_preimage (measurable_physicalBlockEndpointInputOfInput rewards)
    (ActualInitializationCombinedBoundaryMeasurability.measurableSet_endpointPrelaunchSet
      rate block C_star C_h)

/-- The actual no-launch endpoint, packaged in C's existing prelaunch subtype. -/
def actualPrelaunchEndpointInputOfInput (rewards : GridRewardTable p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    ActualInitializationCombinedBoundaryMeasurability.PrelaunchEndpointInput
      p rate block C_star C_h :=
  ⟨physicalBlockEndpointInputOfInput rewards input.1, input.2⟩

/-- The prelaunch endpoint lift is measurable on the actual no-launch slice. -/
theorem measurable_actualPrelaunchEndpointInputOfInput (rewards : GridRewardTable p) :
    Measurable (actualPrelaunchEndpointInputOfInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun input : ActualBlockPrelaunchInput
    (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h) rewards =>
      physicalBlockEndpointInputOfInput rewards input.1)
  exact (measurable_physicalBlockEndpointInputOfInput rewards).comp measurable_subtype_coe

/-- The next block's actual carry, valued in the existing fixed-constant
`BlockCarry` subtype. Its domain is precisely the actual no-launch slice; a
real successor is supplied separately. -/
def actualEndpointNextCarryOfInput (rewards : GridRewardTable p)
    (hnext : block.val + 1 < n_boot p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    ActualInitializationBlockMeasurability.FixedConstantsBlockCarry p rate
      (ActualInitializationRun.successorBlock p block hnext) C_star C_h :=
  ActualInitializationCombinedBoundaryMeasurability.endpointNextCarry
    rate block C_star C_h (actualPrelaunchEndpointInputOfInput rewards input) hnext

/-- The actual continuing carry is Borel jointly in source and incoming carry
on the no-launch slice, into the same fixed-constant successor carry space. -/
theorem measurable_actualEndpointNextCarryOfInput (rewards : GridRewardTable p)
    (hnext : block.val + 1 < n_boot p) :
    Measurable (actualEndpointNextCarryOfInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards hnext) :=
  (ActualInitializationCombinedBoundaryMeasurability.measurable_endpointNextCarry
    rate block C_star C_h hnext).comp
      (measurable_actualPrelaunchEndpointInputOfInput rewards)

/-- On the actual no-launch, real-successor slice, R's `continueNext` payload
is exactly the composed measurable carry, including both fixed constants. -/
theorem actualEndpointNextCarryOfInput_eq_actual_continueNext
    (rewards : GridRewardTable p)
    (hnext : block.val + 1 < n_boot p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    match (ActualInitializationRun.combinedBoundaryHandoff p rate block input.1.1 rewards
      C_star C_h (actualBlockFoldOfInput rewards input.1)).disposition with
    | .continueNext next carry =>
        next = ActualInitializationRun.successorBlock p block hnext ∧
          HEq carry (actualEndpointNextCarryOfInput rewards hnext input).1 ∧
            carry.C_star = C_star ∧ carry.C_h = C_h
    | .launched _ _ => False
    | .exhausted _ => False := by
  have hpre :
      (ActualInitializationBlockMeasurability.continuationCodeOf
        (actualBlockFoldOfInput rewards input.1).phase).2.2.2.2 = none := by
    have htag := input.2
    change (physicalBlockEndpointInputOfInput rewards input.1).1.2.1.2.2.2.2 = none at htag
    rw [physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold] at htag
    simpa [ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold] using htag
  have hinput :
      actualPrelaunchEndpointInputOfInput rewards input =
        ⟨ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold
          (actualBlockFoldOfInput rewards input.1), hpre⟩ := by
    apply Subtype.ext
    exact physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold rewards input.1
  have hactual :=
    ActualInitializationCombinedBoundaryMeasurability.endpointNextCarry_eq_actual_continueNext
      (actualBlockFoldOfInput rewards input.1) hpre hnext
  cases hdisp : (ActualInitializationRun.combinedBoundaryHandoff p rate block input.1.1
      rewards C_star C_h (actualBlockFoldOfInput rewards input.1)).disposition with
  | continueNext next carry =>
      simp only [hdisp] at hactual ⊢
      simpa [actualEndpointNextCarryOfInput, hinput] using hactual
  | launched launch seed =>
      simp only [hdisp] at hactual ⊢
  | exhausted live =>
      simp only [hdisp] at hactual ⊢

end Bandits.Support.ActualInitializationBlockHandoffMeasurability

end
