/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapAllCandidateController
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapWeightPotential
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.ReferencePrelaunchFollower

import Lean.Elab.Tactic.Omega

/-!
# Observation-parametric bootstrap follower

This module implements one uninformed follower's local startup block, using
its original labelled private scalars, its own row observations, and the
existing all-candidate registers. It does not generate observations or assert
that supplied observations came from physical play.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,55-113` and
`sources/zip4/manuscript/appendix_b_communication.tex:101-165`.

## Main definitions
- `StartupState`: the current numerator vector and a checked local block
  cursor, with inactive and active cases kept disjoint.
- `beginBlock`, `choose`, and `observe`: local startup operations.
- `finishBlock`: the clipped block update and continuation/declaration result.

## Main results
- The existing all-candidate `advance` is exactly specialized by a supplied
  accepted physical observation.
- Gain is bounded by the checked processed prefix and then by `B_boot`.
- The literal held-arm floor update preserves every numerator lower bound.

This is an internal operator only. It proves no probability, generated
physical provenance, coupling, initialization, or source-facing closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.BootstrapPhysicalBlock
open Classical

namespace Bandits.Support.BootstrapObservedFollower

variable {p : Parameters} {s : Fin (n_boot p)}

/-- The zero-based first offset of source block `s`. -/
def blockStart (p : Parameters) (s : Fin (n_boot p)) : ℕ :=
  s.val * B_boot p

/-- The clipped exclusive endpoint of source block `s`. -/
def blockStop (p : Parameters) (s : Fin (n_boot p)) : ℕ :=
  min p.T ((s.val + 1) * B_boot p)

/-- The actual clipped number of calendar rounds in source block `s`. -/
def blockLength (p : Parameters) (s : Fin (n_boot p)) : ℕ :=
  blockStop p s - blockStart p s

theorem blockLength_eq_calendarBlock_card (p : Parameters)
    (s : Fin (n_boot p)) :
    blockLength p s = (calendarBlock p s).card := by
  simp [blockLength, blockStop, blockStart, calendarBlock_card]

/-- The shortened final block is included in the same clipped length. -/
theorem blockLength_le_B_boot (p : Parameters) (s : Fin (n_boot p)) :
    blockLength p s ≤ B_boot p := by
  rw [blockLength_eq_calendarBlock_card]
  exact calendarBlock_card_le_B_boot p s

theorem blockStart_lt_blockStop (p : Parameters) (s : Fin (n_boot p)) :
    blockStart p s < blockStop p s := by
  have hnonempty := Finset.card_pos.mpr (calendarBlock_nonempty p s)
  rw [← blockLength_eq_calendarBlock_card, blockLength] at hnonempty
  omega

/-- The source round immediately following the actual clipped block endpoint.
Its value is `T + 1` at the horizon. -/
def nextActivationRound (p : Parameters) (s : Fin (n_boot p)) :
    Activation p := by
  refine ⟨blockStop p s + 1, ?_⟩
  constructor
  · have h := blockStart_lt_blockStop p s
    unfold blockStart at h
    omega
  · have hstop : blockStop p s ≤ p.T := Nat.min_le_left _ _
    omega

theorem finalBlock_endpoint_eq_T (p : Parameters) (s : Fin (n_boot p))
    (hlast : s.val + 1 = n_boot p) :
    blockStop p s = p.T := by
  have hceil := n_boot_real_lower_bound p
  have hmulReal : (p.T : ℝ) ≤ (n_boot p : ℝ) * (B_boot p : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).1 hceil
  have hmul : p.T ≤ n_boot p * B_boot p := by exact_mod_cast hmulReal
  unfold blockStop
  rw [hlast]
  exact min_eq_left hmul

theorem nextActivationRound_final_eq_T_succ (p : Parameters)
    (s : Fin (n_boot p)) (hlast : s.val + 1 = n_boot p) :
    (nextActivationRound p s).val = p.T + 1 := by
  change blockStop p s + 1 = p.T + 1
  rw [finalBlock_endpoint_eq_T p s hlast]

theorem nextActivationRound_nonlast_eq_nextStart (p : Parameters)
    (s : Fin (n_boot p)) (hnext : s.val + 1 < n_boot p) :
    (nextActivationRound p s).val = (s.val + 1) * B_boot p + 1 := by
  have hcard := calendarBlock_card_eq_B_boot_of_nonlast p s hnext
  rw [← blockLength_eq_calendarBlock_card] at hcard
  have hstop : blockStop p s = (s.val + 1) * B_boot p := by
    have hlength :
        min p.T ((s.val + 1) * B_boot p) - s.val * B_boot p = B_boot p := by
      simpa [blockLength, blockStop, blockStart] using hcard
    have hstart := blockStart_lt_blockStop p s
    unfold blockStart blockStop at hstart
    have hsum :
        min p.T ((s.val + 1) * B_boot p) = s.val * B_boot p + B_boot p := by
      omega
    simpa [blockStop, Nat.add_mul, one_mul] using hsum
  simp [nextActivationRound, hstop]

/-- Active blocks retain the held arm, private ID, complete stay gain, and the
accepted candidate registers. The inactive branch has no held arm or ID. -/
inductive StartupBlockCase (p : Parameters) where
  | inactive
  | active (heldArm : Fin p.K) (privateID : Fin (A_id p))
      (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)

/-- Literal gain carried by a block case; the inactive value is definitionally
zero. -/
def StartupBlockCase.gain {p : Parameters} :
    StartupBlockCase p → ℕ
  | .inactive => 0
  | .active _ _ gain _ => gain

theorem StartupBlockCase.inactive_gain :
    StartupBlockCase.gain (.inactive : StartupBlockCase p) = 0 := rfl

/-- One follower's startup state. `processed` is a prefix cursor, not a
physical-history claim. The carried gain invariant is established by
`beginBlock` and preserved by each successful `observe`. -/
structure StartupState (p : Parameters) (s : Fin (n_boot p)) where
  numerators : Fin p.K → ℕ
  numerators_lower_bound :
    ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a
  processed : Fin (blockLength p s + 1)
  blockCase : StartupBlockCase p
  gain_le_processed : blockCase.gain ≤ processed.val

/-- The accepted all-one constructor for one follower's initial numerators. -/
def initialNumerators (p : Parameters) : Fin p.K → ℕ :=
  BootstrapWeightPotential.initial p.K (b_N p)

theorem initialNumerators_weight_eq_one (p : Parameters) (a : Fin p.K) :
    BootstrapWeightPotential.weight (b_N p) (initialNumerators p) a = 1 := by
  exact BootstrapWeightPotential.weight_initial a

theorem initialNumerators_lower_bound (p : Parameters) :
    ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) (initialNumerators p) a := by
  intro a
  rw [initialNumerators_weight_eq_one]

/-- The empty cursor is valid for every nonempty clipped source block. -/
theorem zero_cursor_lt (p : Parameters) (s : Fin (n_boot p)) :
    0 < blockLength p s + 1 := Nat.zero_lt_succ _

/-- Start one actual source block from the follower's own numerator vector and
its original coin/held-arm/private-ID scalar triple, in source order. No row
coordinate is read here. -/
noncomputable def beginBlock (p : Parameters) (s : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (hweights : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (scalars : PrivateSourceStreams.BlockScalars) : StartupState p s := by
  let active := PrivateSourceStreams.activityScalarDraw p scalars.1
  if hactive : active = true then
    let held := PrivateSourceStreams.heldArmScalarDraw p numerators hweights scalars.2.1
    let privateID := PrivateSourceStreams.privateIDScalarDraw p scalars.2.2
    exact
      { numerators := numerators
        numerators_lower_bound := hweights
        processed := ⟨0, zero_cursor_lt p s⟩
        blockCase := .active held privateID 0
          (BootstrapAllCandidateController.initialRegisters p)
        gain_le_processed := by simp [StartupBlockCase.gain] }
  else
    exact
      { numerators := numerators
        numerators_lower_bound := hweights
        processed := ⟨0, zero_cursor_lt p s⟩
        blockCase := .inactive
        gain_le_processed := by simp [StartupBlockCase.gain] }

/-- Initial startup begins with exactly the accepted all-one constructor. -/
noncomputable def initialBlockState (p : Parameters)
    (s : Fin (n_boot p)) (scalars : PrivateSourceStreams.BlockScalars) :
    StartupState p s :=
  beginBlock p s (initialNumerators p) (initialNumerators_lower_bound p) scalars

theorem beginBlock_numerators (p : Parameters) (s : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (hweights : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (scalars : PrivateSourceStreams.BlockScalars) :
    (beginBlock p s numerators hweights scalars).numerators = numerators := by
  cases hactivity : PrivateSourceStreams.activityScalarDraw p scalars.1 with
  | false => simp [beginBlock, hactivity]
  | true => simp [beginBlock, hactivity]

theorem beginBlock_active_case (p : Parameters) (s : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (hweights : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (scalars : PrivateSourceStreams.BlockScalars)
    (hactive : PrivateSourceStreams.activityScalarDraw p scalars.1 = true) :
    (beginBlock p s numerators hweights scalars).blockCase =
      .active
        (PrivateSourceStreams.heldArmScalarDraw p numerators hweights scalars.2.1)
        (PrivateSourceStreams.privateIDScalarDraw p scalars.2.2)
        0 (BootstrapAllCandidateController.initialRegisters p) := by
  simp [beginBlock, hactive]

theorem beginBlock_inactive_case (p : Parameters) (s : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (hweights : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (scalars : PrivateSourceStreams.BlockScalars)
    (hinactive : PrivateSourceStreams.activityScalarDraw p scalars.1 = false) :
    (beginBlock p s numerators hweights scalars).blockCase = .inactive := by
  simp [beginBlock, hinactive]

theorem initialBlockState_numerators (p : Parameters)
    (s : Fin (n_boot p)) (scalars : PrivateSourceStreams.BlockScalars) :
    (initialBlockState p s scalars).numerators = initialNumerators p := by
  exact beginBlock_numerators p s (initialNumerators p)
    (initialNumerators_lower_bound p) scalars

/-- Honest runtime failures for a block round that is outside the block,
already past its endpoint, or not the next cursor position. -/
inductive RoundFailure (p : Parameters) (s : Fin (n_boot p)) where
  | outsideBlock (time : Fin p.T)
  | blockComplete (time : Fin p.T)
  | outOfOrder (expected actual : ℕ)

/-- A successful validation carries the exact block and cursor facts consumed
by `observe`; failures remain explicit for caller-local routing. -/
inductive RoundValidation (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (time : Fin p.T) where
  | failure (error : RoundFailure p s)
  | next (inBlock : time ∈ calendarBlock p s)
      (cursorOpen : state.processed.val < blockLength p s)
      (isNext : time.val = blockStart p s + state.processed.val)

/-- Validate the actual time coordinate against the carried block prefix. -/
def validateRound (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (time : Fin p.T) :
    RoundValidation p s state time := by
  classical
  by_cases hin : time ∈ calendarBlock p s
  · by_cases hopen : state.processed.val < blockLength p s
    · by_cases hnext : time.val = blockStart p s + state.processed.val
      · exact .next hin hopen hnext
      · exact .failure (.outOfOrder
          (blockStart p s + state.processed.val) time.val)
    · exact .failure (.blockComplete time)
  · exact .failure (.outsideBlock time)

/-- The only per-round randomness read by `choose`: this follower's original
round stream, indexed at the current calendar time. -/
noncomputable def localArm (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (time : Fin p.T)
    (scalars : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p) : Fin p.K :=
  match state.blockCase with
  | .inactive => BootstrapPrivateRoundStreams.fullArmScalarDraw p (scalars time)
  | .active held privateID _ _ =>
      if ids privateID time then
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p held (scalars time)).val
      else held

/-- Choose the current block arm. Invalid repeated or out-of-order times return
an explicit error and do not produce an arm. The same own scalar serves the
exclusive full-uniform and complement-uniform branches. -/
noncomputable def choose (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (time : Fin p.T)
    (scalars : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p) :
    Except (RoundFailure p s) (Fin p.K) :=
  match validateRound p s state time with
  | .failure error => .error error
  | .next _ _ _ => .ok (localArm p s state ids time scalars)

theorem localArm_inactive (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s)
    (ids : IDArray p) (time : Fin p.T)
    (scalars : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)
    (hinactive : state.blockCase = .inactive) :
    localArm p s state ids time scalars =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p (scalars time) := by
  simp [localArm, hinactive]

theorem localArm_active (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s)
    (ids : IDArray p) (time : Fin p.T)
    (scalars : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    localArm p s state ids time scalars =
      if ids privateID time then
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p held (scalars time)).val
      else held := by
  simp [localArm, hactive]

theorem localArm_current_scalar_locality (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (time : Fin p.T)
    (left right : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)
    (heq : left time = right time) :
    localArm p s state ids time left = localArm p s state ids time right := by
  cases state.blockCase with
  | inactive => simp [localArm, heq]
  | active held privateID gain registers => simp [localArm, heq]

theorem choose_current_scalar_locality (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (time : Fin p.T)
    (left right : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)
    (heq : left time = right time) :
    choose p s state ids time left = choose p s state ids time right := by
  unfold choose
  cases hv : validateRound p s state time with
  | failure error => rfl
  | next inBlock cursorOpen isNext =>
      simp [localArm_current_scalar_locality p s state ids time left right heq]

/-- One positive ID-zero stay observation, at an already validated block time.
This event is independent of candidate DATA slots and pending status. -/
def positiveStay (ids : IDArray p) (privateID : Fin (A_id p))
    (time : Fin p.T) (observation : Observation p) : Prop :=
  ids privateID time = false ∧ 0 < observation.val.val

/-- Candidate-local eligibility uses that candidate's DATA slot and forward
bit. It reuses the accepted row predicate and existing register carrier. -/
def observedCandidateEligible (p : Parameters) (s : Fin (n_boot p))
    (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p)) (time : Fin p.T)
    (observation : Observation p) (candidate : Fin (M p)) : Prop :=
  time ∈ calendarBlock p s ∧ active = true ∧ positiveStay ids privateID time observation ∧
    BootstrapAllCandidateController.rowIsData rows candidate time

/-- Apply this observation to existing candidate counts and permanent flags.
The pending field is left empty here because `observationAdvance` first checks
that the incoming pending declaration is absent. -/
def updateObservedEvidence (p : Parameters) (s : Fin (n_boot p))
    (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p) :
    BootstrapAllCandidateController.Registers p := by
  classical
  exact
    { count := fun candidate =>
        if observedCandidateEligible p s ids rows active privateID time observation candidate
        then registers.count candidate + 1 else registers.count candidate
      dead := fun candidate =>
        if observedCandidateEligible p s ids rows active privateID time observation candidate
        then registers.dead candidate ||
          decide ((rows candidate).1 privateID time = false)
        else registers.dead candidate
      pending := none }

/-- Observation-parametric advance on the accepted all-candidate registers.
Once pending, candidate evidence is immutable. -/
noncomputable def observationAdvance (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p) :
    BootstrapAllCandidateController.Registers p := by
  classical
  exact if hpending : registers.pending.isSome then registers else
    if hpositive : time ∈ calendarBlock p s ∧ active = true ∧
        positiveStay ids privateID time observation then
      let updated := updateObservedEvidence p s ids rows active privateID registers time observation
      { count := updated.count
        dead := updated.dead
        pending := BootstrapAllCandidateController.uniqueMember
          (BootstrapAllCandidateController.passingSet updated) }
    else registers

theorem observationAdvance_eq_of_pending (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p)
    (hpending : registers.pending.isSome = true) :
    observationAdvance p s ids rows active privateID registers time observation =
      registers := by
  simp [observationAdvance, hpending]

theorem observationAdvance_count_eq (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p)
    (hpending : registers.pending = none)
    (hpositive : time ∈ calendarBlock p s ∧ active = true ∧
      positiveStay ids privateID time observation) (candidate : Fin (M p)) :
    (observationAdvance p s ids rows active privateID registers time observation).count
        candidate =
      if BootstrapAllCandidateController.rowIsData rows candidate time then
        registers.count candidate + 1 else registers.count candidate := by
  simp [observationAdvance, hpending, hpositive, updateObservedEvidence,
    observedCandidateEligible]

theorem observationAdvance_dead_eq (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p)
    (hpending : registers.pending = none)
    (hpositive : time ∈ calendarBlock p s ∧ active = true ∧
      positiveStay ids privateID time observation) (candidate : Fin (M p)) :
    (observationAdvance p s ids rows active privateID registers time observation).dead
        candidate =
      if BootstrapAllCandidateController.rowIsData rows candidate time then
        registers.dead candidate || decide ((rows candidate).1 privateID time = false)
      else registers.dead candidate := by
  simp [observationAdvance, hpending, hpositive, updateObservedEvidence,
    observedCandidateEligible]

theorem observationAdvance_pending_eq_some_iff (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p) (candidate : Fin (M p))
    (hpending : registers.pending = none)
    (hpositive : time ∈ calendarBlock p s ∧ active = true ∧
      positiveStay ids privateID time observation) :
    (observationAdvance p s ids rows active privateID registers time observation).pending =
      some candidate ↔
        BootstrapAllCandidateController.passingSet
            (updateObservedEvidence p s ids rows active privateID registers time observation) =
      ({candidate} : Finset (Fin (M p))) := by
  simp [observationAdvance, hpending, hpositive, updateObservedEvidence,
    observedCandidateEligible]
  rw [BootstrapAllCandidateController.uniqueMember_eq_some_iff]
  constructor
  · intro h
    rcases h with ⟨hmem, hunique⟩
    apply Finset.ext
    intro other
    simp only [Finset.mem_singleton]
    exact ⟨fun hother => hunique other hother, fun heq => by
      subst other
      exact hmem⟩
  · intro hset
    constructor
    · simp [hset]
    · intro other hother
      have hmem : other ∈ ({candidate} : Finset (Fin (M p))) := by
        simpa [hset] using hother
      simpa using hmem

/-- A typed accepted physical observation for the deterministic specialization
only. Local `observe` never calls this function or runs a physical process. -/
def physicalObservation {p : Parameters} {s : Fin (n_boot p)}
    (input : BootstrapPhysicalBlock.Input p s)
    (follower : {i // i ∈ input.uninformed}) (time : Fin p.T) : Observation p := by
  let player := Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val
  refine ⟨⟨BootstrapPhysicalBlock.feedback input
      (BootstrapPhysicalBlock.run input time.val) time player,
    BootstrapPhysicalBlock.feedback_mem_Icc input _ time player⟩,
    BootstrapPhysicalBlock.observationIndex input
      (BootstrapPhysicalBlock.run input time.val) time player, ?_⟩
  exact (BootstrapPhysicalBlock.observationIndex_value input _ time player).symm

theorem physicalObservation_value {p : Parameters} {s : Fin (n_boot p)}
    (input : BootstrapPhysicalBlock.Input p s)
    (follower : {i // i ∈ input.uninformed}) (time : Fin p.T) :
    (physicalObservation input follower time).val.val =
      BootstrapPhysicalBlock.feedback input
        (BootstrapPhysicalBlock.run input time.val) time
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val) := rfl

theorem physicalObservation_positive_iff {p : Parameters} {s : Fin (n_boot p)}
    (input : BootstrapPhysicalBlock.Input p s)
    (follower : {i // i ∈ input.uninformed}) (time : Fin p.T) :
    0 < (physicalObservation input follower time).val.val ↔
      0 < (BootstrapPhysicalBlock.observationIndex input
        (BootstrapPhysicalBlock.run input time.val) time
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val)).val := by
  rw [physicalObservation_value]
  exact (BootstrapPhysicalBlock.observationIndex_pos_iff input
    (BootstrapPhysicalBlock.run input time.val) time
    (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val)).symm

theorem updateObservedEvidence_eq_accepted (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : BootstrapAllCandidateController.Registers p)
    (time : Fin p.T) (observation : Observation p)
    (input : BootstrapPhysicalBlock.Input p s)
    (follower : {i // i ∈ input.uninformed})
    (hids : ids = input.ids) (hactive : active = input.active follower)
    (hID : privateID = input.privateId follower)
    (hvalue : observation.val.val =
      BootstrapPhysicalBlock.feedback input
        (BootstrapPhysicalBlock.run input time.val) time
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val)) :
    updateObservedEvidence p s ids rows active privateID registers time observation =
      BootstrapAllCandidateController.updateEvidence input rows follower registers time := by
  classical
  have hfbPos : 0 < BootstrapPhysicalBlock.feedback input
        (BootstrapPhysicalBlock.run input time.val) time
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val) ↔
      0 < (BootstrapPhysicalBlock.observationIndex input
        (BootstrapPhysicalBlock.run input time.val) time
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val)).val := by
    exact (BootstrapPhysicalBlock.observationIndex_pos_iff input
      (BootstrapPhysicalBlock.run input time.val) time
      (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m follower.val)).symm
  have helig (candidate : Fin (M p)) :
      observedCandidateEligible p s ids rows active privateID time observation candidate ↔
        BootstrapAllCandidateController.candidateEligible input rows follower candidate time := by
    simp [observedCandidateEligible,
      BootstrapAllCandidateController.candidateEligible,
      BootstrapAllCandidateController.positiveRound,
      BootstrapAllCandidateController.rowIsData, positiveStay,
      and_assoc, hids, hactive, hID, hvalue, hfbPos]
  apply BootstrapAllCandidateController.registers_ext
  · intro candidate
    simp [updateObservedEvidence, BootstrapAllCandidateController.updateEvidence,
      helig candidate]
  · intro candidate
    simp only [updateObservedEvidence, BootstrapAllCandidateController.updateEvidence]
    rw [if_congr (helig candidate)]
    simp only [BootstrapAllCandidateController.candidateForwardBit, hID]
    by_cases hbit : (rows candidate).1 (input.privateId follower) time
    · simp [hbit]
    · simp [hbit]
    all_goals rfl
  · rfl

/-- Exact specialization to the accepted physical advance, using only the
physical feedback observation and matching active/ID/block projections. -/
theorem observationAdvance_eq_accepted (p : Parameters)
    {s : Fin (n_boot p)} (rows : CompleteRows p)
    (registers : BootstrapAllCandidateController.Registers p)
    (input : BootstrapPhysicalBlock.Input p s)
    (follower : {i // i ∈ input.uninformed}) (time : Fin p.T) :
    observationAdvance p s input.ids rows (input.active follower)
        (input.privateId follower) registers time
        (physicalObservation input follower time) =
      BootstrapAllCandidateController.advance input rows follower registers time := by
  classical
  have hpositive :
      (time ∈ calendarBlock p s ∧ input.active follower = true ∧
        positiveStay input.ids (input.privateId follower) time
          (physicalObservation input follower time)) =
        BootstrapAllCandidateController.positiveRound input follower time := by
    apply propext
    simp only [positiveStay, BootstrapAllCandidateController.positiveRound,
      physicalObservation_positive_iff]
  cases hpending : registers.pending with
  | none =>
    have hupdate := updateObservedEvidence_eq_accepted p s input.ids rows
      (input.active follower) (input.privateId follower) registers time
      (physicalObservation input follower time) input follower rfl rfl rfl rfl
    simp only [observationAdvance, BootstrapAllCandidateController.advance,
      hpending, hpositive, hupdate]
  | some pending =>
    simp [observationAdvance, BootstrapAllCandidateController.advance, hpending]

/-- The successful checked observation result. -/
inductive ObserveResult (p : Parameters) (s : Fin (n_boot p)) where
  | rejected (error : RoundFailure p s)
  | accepted (state : StartupState p s)

/-- Candidate and gain branch after one validated local observation. Invalid
round evidence leaves the case unchanged; the public `observe` reports its
failure instead of returning this helper's value. -/
def observeBlockCase (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (validation : RoundValidation p s state time) : StartupBlockCase p :=
  match validation with
  | .failure _ => state.blockCase
  | .next _ _ _ =>
      match state.blockCase with
      | .inactive => .inactive
      | .active held privateID gain registers =>
          .active held privateID
            (if positiveStay ids privateID time observation then gain + 1 else gain)
            (observationAdvance p s ids rows true privateID registers time observation)

theorem observeBlockCase_gain_le (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (validation : RoundValidation p s state time) :
    (observeBlockCase p s state ids rows time observation validation).gain ≤
      state.processed.val + 1 := by
  classical
  cases validation with
  | failure error => exact state.gain_le_processed.trans (Nat.le_succ _)
  | next inBlock cursorOpen isNext =>
      cases hcase : state.blockCase with
      | inactive => simp [observeBlockCase, hcase, StartupBlockCase.gain]
      | active held privateID gain registers =>
          have hprev : gain ≤ state.processed.val := by
            simpa [hcase, StartupBlockCase.gain] using state.gain_le_processed
          by_cases hstay : positiveStay ids privateID time observation
          · simp [observeBlockCase, hcase, hstay, StartupBlockCase.gain]
            omega
          · simp [observeBlockCase, hcase, hstay, StartupBlockCase.gain]
            omega

/-- Apply an observation after the checked next-round facts have been
established by `validateRound`. -/
noncomputable def observeOne (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (_inBlock : time ∈ calendarBlock p s)
    (cursorOpen : state.processed.val < blockLength p s)
    (_isNext : time.val = blockStart p s + state.processed.val) :
    StartupState p s := by
  classical
  let validation := RoundValidation.next _inBlock cursorOpen _isNext
  have hcursor : state.processed.val + 1 < blockLength p s + 1 := by omega
  have hgain := observeBlockCase_gain_le p s state ids rows time observation validation
  exact
    { numerators := state.numerators
      numerators_lower_bound := state.numerators_lower_bound
      processed := ⟨state.processed.val + 1, hcursor⟩
      blockCase := observeBlockCase p s state ids rows time observation validation
      gain_le_processed := hgain }

/-- Consume only this follower's actual current typed observation and the
candidate public rows/ID array. Every successful call advances exactly one
calendar position; a repeated or out-of-order call is rejected. -/
noncomputable def observe (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p) : ObserveResult p s :=
  match validateRound p s state time with
  | .failure error => .rejected error
  | .next hin hopen hnext =>
      .accepted (observeOne p s state ids rows time observation hin hopen hnext)

theorem observe_accepted_processed (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val) :
    observe p s state ids rows time observation =
      .accepted (observeOne p s state ids rows time observation hin hopen hnext) := by
  simp [observe, validateRound, hin, hopen, hnext]

theorem observe_accepted_cursor (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val) :
    (observeOne p s state ids rows time observation hin hopen hnext).processed.val =
      state.processed.val + 1 := rfl

theorem observeOne_numerators (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val) :
    (observeOne p s state ids rows time observation hin hopen hnext).numerators =
      state.numerators := rfl

theorem observeOne_numerators_lower_bound (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val) :
    ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p)
      (observeOne p s state ids rows time observation hin hopen hnext).numerators a :=
  state.numerators_lower_bound

theorem observeOne_active_gain_eq (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hcase : state.blockCase = .active held privateID gain registers) :
    (observeOne p s state ids rows time observation hin hopen hnext).blockCase.gain =
      if positiveStay ids privateID time observation then gain + 1 else gain := by
  simp [observeOne, observeBlockCase, hcase, StartupBlockCase.gain]

theorem observeOne_pending_persists (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hcase : state.blockCase = .active held privateID gain registers)
    (hpending : registers.pending.isSome = true) :
    (observeOne p s state ids rows time observation hin hopen hnext).blockCase =
      .active held privateID
        (if positiveStay ids privateID time observation then gain + 1 else gain)
        registers := by
  simp [observeOne, observeBlockCase, hcase,
    observationAdvance_eq_of_pending p s ids rows true privateID registers time
      observation hpending]

theorem observeOne_inactive_case_eq (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (ids : IDArray p) (rows : CompleteRows p)
    (time : Fin p.T) (observation : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < blockLength p s)
    (hnext : time.val = blockStart p s + state.processed.val)
    (hinactive : state.blockCase = .inactive) :
    (observeOne p s state ids rows time observation hin hopen hnext).blockCase =
      .inactive := by
  simp [observeOne, observeBlockCase, hinactive]

theorem StartupState.gain_le_B_boot (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) :
    state.blockCase.gain ≤ B_boot p := by
  exact state.gain_le_processed.trans
    ((Nat.le_of_lt_succ state.processed.isLt).trans (blockLength_le_B_boot p s))

theorem activeGain_le_B_boot (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (held : Fin p.K) (privateID : Fin (A_id p))
    (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    gain ≤ B_boot p := by
  have hbound := state.gain_le_B_boot p s
  simpa [hactive, StartupBlockCase.gain] using hbound

/-- Active-only input to the accepted dyadic weight updater. -/
def activeWeightBlock (p : Parameters) (held : Fin p.K) (gain : ℕ)
    (hgain : gain ≤ B_boot p) :
    BootstrapWeightPotential.Block p.K (B_boot p) :=
  ⟨true, held, gain, hgain⟩

/-- Numerators after the full block update. Inactive blocks preserve the whole
vector and do not construct a fictitious held arm. -/
noncomputable def updatedNumerators (p : Parameters)
    (s : Fin (n_boot p)) (state : StartupState p s) : Fin p.K → ℕ :=
  match hcase : state.blockCase with
  | .inactive => state.numerators
  | .active held privateID gain registers =>
      let hgain : gain ≤ B_boot p := by
        have hcursor : state.processed.val ≤ blockLength p s :=
          Nat.le_of_lt_succ state.processed.isLt
        have hbound := state.gain_le_processed.trans
          (hcursor.trans (blockLength_le_B_boot p s))
        simpa [hcase, StartupBlockCase.gain] using hbound
      BootstrapWeightPotential.next (b_N p) state.numerators
        (activeWeightBlock p held gain hgain)

theorem updatedNumerators_inactive (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (hinactive : state.blockCase = .inactive) :
    updatedNumerators p s state = state.numerators := by
  cases state with
  | mk numerators lower processed blockCase gainBound =>
      cases blockCase with
      | inactive => rfl
      | active held privateID gain registers => cases hinactive

theorem updatedNumerators_active_eq_next (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (held : Fin p.K) (privateID : Fin (A_id p))
    (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    updatedNumerators p s state =
      BootstrapWeightPotential.next (b_N p) state.numerators
        (activeWeightBlock p held gain
          (activeGain_le_B_boot p s state held privateID gain registers hactive)) := by
  cases state with
  | mk numerators lower processed blockCase gainBound =>
      cases blockCase with
      | inactive => cases hactive
      | active held' privateID' gain' registers' =>
          injection hactive with hheld hID hgain hregisters
          subst held'
          subst privateID'
          subst gain'
          subst registers'
          rfl

theorem updatedNumerators_active_other (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (held : Fin p.K) (privateID : Fin (A_id p))
    (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers)
    (other : Fin p.K) (hother : held ≠ other) :
    updatedNumerators p s state other = state.numerators other := by
  rw [updatedNumerators_active_eq_next p s state held privateID gain registers hactive]
  exact BootstrapWeightPotential.next_other state.numerators
    (activeWeightBlock p held gain
      (activeGain_le_B_boot p s state held privateID gain registers hactive)) other hother

theorem updatedWeight_other_eq (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (held : Fin p.K) (privateID : Fin (A_id p))
    (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers)
    (other : Fin p.K) (hother : held ≠ other) :
    BootstrapWeightPotential.weight (b_N p) (updatedNumerators p s state) other =
      BootstrapWeightPotential.weight (b_N p) state.numerators other := by
  simp only [BootstrapWeightPotential.weight]
  rw [updatedNumerators_active_other p s state held privateID gain registers
    hactive other hother]

theorem updatedNumerators_lower_bound (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) :
    ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) (updatedNumerators p s state) a := by
  intro a
  cases hcase : state.blockCase with
  | inactive =>
      rw [updatedNumerators_inactive p s state hcase]
      exact state.numerators_lower_bound a
  | active held privateID gain registers =>
      rw [updatedNumerators_active_eq_next p s state held privateID gain registers hcase]
      exact (state.numerators_lower_bound a).trans
        (BootstrapWeightPotential.weight_next_mono
        (K_pos p) (B_boot_pos p) state.numerators
        (activeWeightBlock p held gain
          (activeGain_le_B_boot p s state held privateID gain registers hcase)) a)

/-- Literal real weight equation for the enabled held arm, with the full gain
and pre-update mixture. This is the source's dyadic floor update. -/
theorem updatedWeight_held_eq (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (held : Fin p.K) (privateID : Fin (A_id p))
    (gain : ℕ) (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    BootstrapWeightPotential.weight (b_N p) (updatedNumerators p s state) held =
      BootstrapWeightPotential.epsilon (b_N p) *
        (⌊(BootstrapWeightPotential.scale (b_N p) : ℝ) *
          BootstrapWeightPotential.weight (b_N p) state.numerators held *
            (1 + (gain : ℝ) /
              (4 * p.K * B_boot p *
                BootstrapWeightPotential.probability (b_N p) state.numerators held))⌋₊ : ℝ) := by
  rw [updatedNumerators_active_eq_next p s state held privateID gain registers hactive]
  exact BootstrapWeightPotential.weight_next_held state.numerators
    (activeWeightBlock p held gain
      (activeGain_le_B_boot p s state held privateID gain registers hactive)) rfl

/-- The block's pending row, if any. Inactive cases contain no registers. -/
def pendingDeclaration (blockCase : StartupBlockCase p) :
    Option (Fin (M p)) :=
  match blockCase with
  | .inactive => none
  | .active _ _ _ registers => registers.pending

/-- Boundary update failures are explicit; a partial block cannot be
mistaken for a completed calendar endpoint. -/
inductive FinishFailure (p : Parameters) (s : Fin (n_boot p)) where
  | incomplete (processed expected : ℕ)

/-- The two legal boundary handoffs. A declaration carries no bootstrap
weights and creates no ordinary follower state. -/
inductive BoundaryOutput (p : Parameters) (s : Fin (n_boot p)) where
  | continueWithWeights (numerators : Fin p.K → ℕ)
      (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
      (activationRound : Activation p)
  | declareRow (row : Fin (M p)) (activationRound : Activation p)

/-- Finish only after the actual clipped block cursor has reached its endpoint.
The full active gain updates the held numerator before a saved declaration is
returned; activation takes effect at the next source round, including `T+1`. -/
noncomputable def finishBlock (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) :
    Except (FinishFailure p s) (BoundaryOutput p s) := by
  if hcomplete : state.processed.val = blockLength p s then
    let numerators := updatedNumerators p s state
    match hpending : pendingDeclaration state.blockCase with
    | none =>
        exact .ok (.continueWithWeights numerators
          (updatedNumerators_lower_bound p s state) (nextActivationRound p s))
    | some row => exact .ok (.declareRow row (nextActivationRound p s))
  else
    exact .error (.incomplete state.processed.val (blockLength p s))

theorem finishBlock_incomplete (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (hincomplete : state.processed.val ≠ blockLength p s) :
    finishBlock p s state =
      .error (.incomplete state.processed.val (blockLength p s)) := by
  simp [finishBlock, hincomplete]

theorem finishBlock_continue (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (hcomplete : state.processed.val = blockLength p s)
    (hnone : pendingDeclaration state.blockCase = none) :
    finishBlock p s state =
      .ok (.continueWithWeights (updatedNumerators p s state)
        (updatedNumerators_lower_bound p s state) (nextActivationRound p s)) := by
  unfold finishBlock
  rw [dite_eq_left hcomplete]
  cases hpending : pendingDeclaration state.blockCase with
  | none => rfl
  | some row => simp [hpending] at hnone

theorem finishBlock_declare (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (hcomplete : state.processed.val = blockLength p s)
    (row : Fin (M p)) (hpending : pendingDeclaration state.blockCase = some row) :
    finishBlock p s state =
      .ok (.declareRow row (nextActivationRound p s)) := by
  unfold finishBlock
  rw [dite_eq_left hcomplete, hpending]

theorem finishBlock_inactive_preserves_numerators (p : Parameters)
    (s : Fin (n_boot p)) (state : StartupState p s)
    (hinactive : state.blockCase = .inactive) :
    updatedNumerators p s state = state.numerators :=
  updatedNumerators_inactive p s state hinactive

theorem finishBlock_declaration_has_activation (p : Parameters)
    (s : Fin (n_boot p)) (state : StartupState p s)
    (hcomplete : state.processed.val = blockLength p s)
    (row : Fin (M p)) (hpending : pendingDeclaration state.blockCase = some row) :
    ∃ activation : Activation p,
      finishBlock p s state = .ok (.declareRow row activation) ∧
        activation.val = blockStop p s + 1 := by
  refine ⟨nextActivationRound p s, finishBlock_declare p s state hcomplete row hpending, ?_⟩
  rfl

theorem finishBlock_terminal_activation (p : Parameters) (s : Fin (n_boot p))
    (state : StartupState p s) (hcomplete : state.processed.val = blockLength p s)
    (row : Fin (M p)) (hpending : pendingDeclaration state.blockCase = some row)
    (hlast : s.val + 1 = n_boot p) :
    finishBlock p s state = .ok (.declareRow row
      ⟨p.T + 1, by omega⟩) := by
  rw [finishBlock_declare p s state hcomplete row hpending]
  apply congrArg Except.ok
  apply congrArg (BoundaryOutput.declareRow row)
  apply Subtype.ext
  exact nextActivationRound_final_eq_T_succ p s hlast

end Bandits.Support.BootstrapObservedFollower

end
