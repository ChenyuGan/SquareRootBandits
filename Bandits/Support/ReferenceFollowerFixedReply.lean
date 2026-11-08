/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

/-!
# Fixed follower replies on actual active runs

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-72,108-110`,
`sources/zip4/manuscript/06_interruptions.tex:168-177,248-261,270-295,302-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108`.

The projections in this module are from the canonical active physical
`ReferenceActivePhysicalHorizon.run`, its retained `RoundRecord`s, and the
literal checked local operations. They do not replace a physical trace with a
supplied history. The endpoint claims below concern reply-register values;
they do not identify them with global queue totals or prove stale-batch
correctness or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceUpReception

namespace Bandits.Support.ReferenceFollowerFixedReply

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

section RoundAPI

variable {p : Parameters} {rate : RateInput p}

/-- The actual choice-time follower preparation retained by a physical round.
The configuration is already after `startRound` and UP-offer/arm validation.
-/
def actualChoice (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : DeclaredFollowerLocalRound.PreparedRound p rate :=
  record.output.preparation.followers.followers i

/-- The actual sender word computed by the physical round's selected sender
adapter. Nonselected follower preparations are not given an UP word premise.
-/
def actualUpExpected (record : RoundRecord (p := p) (rate := rate)) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  ReferenceActivePhysicalStep.upExpected record.output.preparation

/-- Alignment for a follower preparation is derived from its actual PREPARE
call, with no separately supplied row, identity, or time relation. -/
theorem actualChoice_alignment (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    (actualChoice record i).row = record.input.row ∧
      (actualChoice record i).follower = i ∧
      (actualChoice record i).time = record.input.time := by
  rcases record.output.preparation.follower_alignment i with ⟨hrow, hi, htime, _⟩
  exact ⟨hrow, hi, htime⟩

/-- The actual choice-time current UP word is absent for an occupied ordinary
choice configuration. This includes invalid checked-offer inputs, which take
the existing failure path and also produce no word. -/
theorem currentOfferWord_eq_none_of_occupiedChoice
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (actualChoice record i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
      (actualChoice record i) (actualChoice_alignment record i).1
      (actualChoice_alignment record i).2.1
      (actualChoice_alignment record i).2.2 = none := by
  have hnonoffer :
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (actualChoice record i).follower (actualChoice record i).row
        (actualChoice record i).activation (actualChoice record i).time state =
        .failure ∨
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (actualChoice record i).follower (actualChoice record i).row
        (actualChoice record i).activation (actualChoice record i).time state =
        .noOffer := by
    by_cases hdomain : ActiveFollowerQueueOperation.stateInputDomain state
    · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound
          (actualChoice record i).follower (actualChoice record i).row
          (actualChoice record i).activation (actualChoice record i).time ∧
          state.status = .unoccupied) := by
        rintro ⟨_, hstatus⟩
        exact hoccupied hstatus
      exact Or.inr (ActiveFollowerQueueOperation.checkedUpOffer_noOffer
        rate.eta (actualChoice record i).follower (actualChoice record i).row
        (actualChoice record i).activation (actualChoice record i).time state
        hdomain hnot)
    · have hfailure : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          (actualChoice record i).follower (actualChoice record i).row
          (actualChoice record i).activation (actualChoice record i).time state =
          .failure := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain]
      exact Or.inl hfailure
  exact ReferenceUpReception.currentOfferWord_eq_none_of_checked_nonoffer
    rate record.input.row i record.input.time (actualChoice record i)
    (actualChoice_alignment record i).1 (actualChoice_alignment record i).2.1
    (actualChoice_alignment record i).2.2 state memory hconfiguration hnonoffer

/-- An actual selected sender's expected word is the canonical encoding of
the exact checked offer retained by its choice-time state. -/
theorem actualUpExpected_eq_encoded_offer
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hselected : ReferenceActivePhysicalStep.upSenderIndex record.input = i)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (actualChoice record i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice record i).follower (actualChoice record i).row
      (actualChoice record i).activation (actualChoice record i).time state =
        .offer offered) :
    actualUpExpected record = some ((OrdinaryMessageCodec.wordEquivFlat
      (CoordinatorCollectionLedger.codecParams p rate.eta.val))
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) := by
  have hword := ReferenceUpReception.currentOfferWord_eq_encoded_offer
    rate record.input.row i record.input.time (actualChoice record i)
    (actualChoice_alignment record i).1 (actualChoice_alignment record i).2.1
    (actualChoice_alignment record i).2.2 state memory hconfiguration offered hoff
  cases hselected
  change ReferenceUpReception.currentOfferWord rate record.input.row
      (ReferenceActivePhysicalStep.upSenderIndex record.input) record.input.time
      (actualChoice record (ReferenceActivePhysicalStep.upSenderIndex record.input))
      (actualChoice_alignment record (ReferenceActivePhysicalStep.upSenderIndex record.input)).1
      (actualChoice_alignment record (ReferenceActivePhysicalStep.upSenderIndex record.input)).2.1
      (actualChoice_alignment record (ReferenceActivePhysicalStep.upSenderIndex record.input)).2.2 = _
  exact hword

/-- Replay's actual zero registers make the successful active UP offer the
distinguished `(0,0,0,0)` placeholder. Its decoder buffer and other replay
fields remain those of the supplied replay state. -/
theorem replay_checked_offer_is_placeholder
    {n : ℕ} (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p)
    (history : ReferencePrelaunchFollower.LocalHistory p n) (hn : n ≤ p.T)
    (time : Fin p.T) (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time
      (ReferencePrelaunchFollower.replay rate.eta i row activation history hn) =
        .offer offered) :
    offered.val = OrdinaryMessageCodec.upPlaceholder :=
  ActiveFollowerQueueOperation.checkedUpOffer_replay_placeholder
    rate.eta i row activation history hn time offered hoff

/-- Every coordinate in the physical calendar interval has a corresponding
actual retained record in the canonical run. The record is obtained from
`run_time_values`, not supplied as a trace element. -/
theorem run_actual_record_at_time
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : Fin count) :
    ∃ record,
      record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records ∧
      record.input.time.val = start + offset.val := by
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
    rewards start count hspan hmode
  have hcalendar : start + offset.val ∈
      ReferenceActivePhysicalHorizon.calendar start count := by
    rw [ReferenceActivePhysicalHorizon.calendar]
    apply List.mem_range'.mpr
    exact ⟨offset.val, offset.isLt, by simp⟩
  have hmem : start + offset.val ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.map (fun record => record.input.time.val) := by
    rw [htimes]
    exact hcalendar
  rcases List.mem_map.mp hmem with ⟨record, hrecord, htime⟩
  exact ⟨record, hrecord, htime⟩

/-- The four literal zero reply registers make any successful checked offer
equal to the source's distinguished placeholder. -/
theorem checked_offer_is_placeholder_of_zero_registers
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstart : ReferencePrelaunchFollower.acceptedStart state = 0)
    (hS : state.S = 0) (hdelta : state.delta = 0) (hbacklog : state.backlog = 0)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
      .offer offered) :
    offered.val = OrdinaryMessageCodec.upPlaceholder := by
  have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields
    rate.eta i row activation time state offered hoff
  calc
    offered.val = ActiveFollowerQueueOperation.upOfferFields state := hfields
    _ = OrdinaryMessageCodec.upPlaceholder := by
      ext <;> simp [ActiveFollowerQueueOperation.upOfferFields, hstart, hS,
        hdelta, hbacklog, OrdinaryMessageCodec.upPlaceholder]

/-- If two actual choice snapshots offer UP using the same four reply
registers, their offered records and flattened current words agree. This
statement uses only the two actual checked offers and sender alignments.
-/
theorem actualUpExpected_eq_of_same_reply_registers
    (left right : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hleftSelected : ReferenceActivePhysicalStep.upSenderIndex left.input = i)
    (hrightSelected : ReferenceActivePhysicalStep.upSenderIndex right.input = i)
    (leftState rightState : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hleftConfiguration : (actualChoice left i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary leftState leftMemory)
    (hrightConfiguration : (actualChoice right i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary rightState rightMemory)
    (hregisters :
      ReferencePrelaunchFollower.acceptedStart leftState =
          ReferencePrelaunchFollower.acceptedStart rightState ∧
        leftState.S = rightState.S ∧ leftState.delta = rightState.delta ∧
        leftState.backlog = rightState.backlog)
    (leftOffer rightOffer : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hleftOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice left i).follower (actualChoice left i).row
      (actualChoice left i).activation (actualChoice left i).time leftState =
        .offer leftOffer)
    (hrightOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice right i).follower (actualChoice right i).row
      (actualChoice right i).activation (actualChoice right i).time rightState =
        .offer rightOffer) :
    leftOffer = rightOffer ∧ actualUpExpected left = actualUpExpected right := by
  have hleftFields := ReferenceUpReception.checkedPreparedOffer_field_equations
    rate left.input.row i left.input.time (actualChoice left i)
    (actualChoice_alignment left i).1 (actualChoice_alignment left i).2.1
    (actualChoice_alignment left i).2.2 leftState leftMemory hleftConfiguration
    leftOffer hleftOffer
  have hrightFields := ReferenceUpReception.checkedPreparedOffer_field_equations
    rate right.input.row i right.input.time (actualChoice right i)
    (actualChoice_alignment right i).1 (actualChoice_alignment right i).2.1
    (actualChoice_alignment right i).2.2 rightState rightMemory hrightConfiguration
    rightOffer hrightOffer
  have hoffers : leftOffer = rightOffer := by
    apply Subtype.ext
    apply OrdinaryMessageCodec.UpFields.ext
    · exact hleftFields.1.trans (hregisters.1.trans hrightFields.1.symm)
    · exact hleftFields.2.1.trans (hregisters.2.1.trans hrightFields.2.1.symm)
    · exact hleftFields.2.2.1.trans (hregisters.2.2.1.trans hrightFields.2.2.1.symm)
    · exact hleftFields.2.2.2.trans (hregisters.2.2.2.trans hrightFields.2.2.2.symm)
  constructor
  · exact hoffers
  · rw [actualUpExpected_eq_encoded_offer left i hleftSelected leftState leftMemory
      hleftConfiguration leftOffer hleftOffer,
      actualUpExpected_eq_encoded_offer right i hrightSelected rightState rightMemory
        hrightConfiguration rightOffer hrightOffer, hoffers]

/-- The selected senders' actual aligned `currentOfferWord` values agree
whenever their four literal reply registers agree. This is the word-level
form consumed by the stale-batch argument; no claim is made about slots that
do not actually select this follower. -/
theorem currentOfferWord_eq_of_same_reply_registers
    (left right : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (leftState rightState : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hleftConfiguration : (actualChoice left i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary leftState leftMemory)
    (hrightConfiguration : (actualChoice right i).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary rightState rightMemory)
    (hregisters :
      ReferencePrelaunchFollower.acceptedStart leftState =
          ReferencePrelaunchFollower.acceptedStart rightState ∧
        leftState.S = rightState.S ∧ leftState.delta = rightState.delta ∧
        leftState.backlog = rightState.backlog)
    (leftOffer rightOffer : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hleftOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice left i).follower (actualChoice left i).row
      (actualChoice left i).activation (actualChoice left i).time leftState =
        .offer leftOffer)
    (hrightOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice right i).follower (actualChoice right i).row
      (actualChoice right i).activation (actualChoice right i).time rightState =
        .offer rightOffer) :
    ReferenceUpReception.currentOfferWord rate left.input.row i left.input.time
      (actualChoice left i) (actualChoice_alignment left i).1
      (actualChoice_alignment left i).2.1 (actualChoice_alignment left i).2.2 =
    ReferenceUpReception.currentOfferWord rate right.input.row i right.input.time
      (actualChoice right i) (actualChoice_alignment right i).1
      (actualChoice_alignment right i).2.1 (actualChoice_alignment right i).2.2 := by
  have hleftFields := ReferenceUpReception.checkedPreparedOffer_field_equations
    rate left.input.row i left.input.time (actualChoice left i)
    (actualChoice_alignment left i).1 (actualChoice_alignment left i).2.1
    (actualChoice_alignment left i).2.2 leftState leftMemory hleftConfiguration
    leftOffer hleftOffer
  have hrightFields := ReferenceUpReception.checkedPreparedOffer_field_equations
    rate right.input.row i right.input.time (actualChoice right i)
    (actualChoice_alignment right i).1 (actualChoice_alignment right i).2.1
    (actualChoice_alignment right i).2.2 rightState rightMemory hrightConfiguration
    rightOffer hrightOffer
  have hoffers : leftOffer = rightOffer := by
    apply Subtype.ext
    apply OrdinaryMessageCodec.UpFields.ext
    · exact hleftFields.1.trans (hregisters.1.trans hrightFields.1.symm)
    · exact hleftFields.2.1.trans (hregisters.2.1.trans hrightFields.2.1.symm)
    · exact hleftFields.2.2.1.trans (hregisters.2.2.1.trans hrightFields.2.2.1.symm)
    · exact hleftFields.2.2.2.trans (hregisters.2.2.2.trans hrightFields.2.2.2.symm)
  rw [ReferenceUpReception.currentOfferWord_eq_encoded_offer
      rate left.input.row i left.input.time (actualChoice left i)
      (actualChoice_alignment left i).1 (actualChoice_alignment left i).2.1
      (actualChoice_alignment left i).2.2 leftState leftMemory hleftConfiguration
      leftOffer hleftOffer,
    ReferenceUpReception.currentOfferWord_eq_encoded_offer
      rate right.input.row i right.input.time (actualChoice right i)
      (actualChoice_alignment right i).1 (actualChoice_alignment right i).2.1
      (actualChoice_alignment right i).2.2 rightState rightMemory hrightConfiguration
      rightOffer hrightOffer,
    hoffers]

end RoundAPI

section ActualLaunchSeed

variable {p : Parameters}
variable
  (source : Bandits.Support.BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
  (rate : ActualInitializationLaunchState.RateInput p) (C_star C_h : ℝ)
  (b : ReferenceInitializationRun.Boundary p)
  (h : b.completed < Bandits.Support.BootstrapDimensions.n_boot p)
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
    Bandits.Support.BootstrapAllCandidateController.cleanPrefix
      (ReferenceInitializationRun.physical
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        b h)
      source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
      (Bandits.Support.ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
  (hforce : ∀ i, ReferenceInitializationRun.forced
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    b h i = false)
  (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
  (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
  (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
    (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual)).disposition = .launched launch learnerSeed)

include source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
  learnerSeed hlaunched

/-- The actual launched boundary stores the whole ordinary replay state and
its carried proposal memory. Its reply fields are zero and the status is
unoccupied. `ordinary_registers` expands the canonical `ordinary` definition
into its forced-at-launch, initial, or accepted replay branches; no state
fields, buffer, decoder batch, or memory are reconstructed or discarded.
-/
theorem ofActualLaunchedBoundary_replaySeed (i : Fin (p.m - 1)) :
    ∃ state memory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary state memory ∧
      state = ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        (ActualReferenceInitializationBlock.refFollower i) ∧
      state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
      state.status = .unoccupied ∧ state.initializationFailure = false := by
  rcases ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
      learnerSeed hlaunched i with
    ⟨state, memory, hconfiguration, hstate, _, _, _, _, _, _, hfailure⟩
  have hregisters := ReferenceInitializationRun.ordinary_registers
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    (ReferenceInitializationRun.finishBlock
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h)
    (ActualReferenceInitializationBlock.refFollower i)
  rw [← hstate] at hregisters
  rcases hregisters with ⟨hlast, hstart, hS, hdelta, hbacklog, hstatus⟩
  exact ⟨state, memory, hconfiguration, hstate, hlast, hstart, hS, hdelta,
    hbacklog, hstatus, hfailure⟩

/-- The actual launch boundary supplies the physical horizon's all-active mode
at the exact computed block stop. A nonempty postlaunch run additionally uses
the explicit bound that this stop is a real calendar coordinate. -/
theorem ofActualLaunchedBoundary_allActiveAtBlockStop
    (hstop : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) < p.T) :
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) := by
  change ∀ i, ((ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).activations i).val ≤
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1
  exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activeAtTime source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    ⟨BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h), hstop⟩
    (Nat.le_refl _)

end ActualLaunchSeed

end Bandits.Support.ReferenceFollowerFixedReply

end
