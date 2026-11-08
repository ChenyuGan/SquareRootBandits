/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.BootstrapPhysicalBlock

import Lean.Elab.Tactic.Omega

/-!
# One physical bootstrap block in the ordinary prelaunch follower replay

This adapter joins the accepted typed ordinary follower replay to one actual
block of `BootstrapPhysicalBlock` actions and collision feedback.  Its source
is `07_public_setup.tex:52-55,129-140`,
`06_interruptions.tex:251-276,296`, and
`appendix_b_communication.tex:128-131`.

The input supplies an earlier bounded typed local prefix, an effective
activation no later than this block's first manuscript round, and a follower
outside the physical block's uninformed set.  The incoming state is defined to
be the existing replay of that supplied prefix.  Current-block arms and
observations are built directly from the physical action recursion and its
rounded feedback.  Earlier prefix physicality, activation production,
initialization success, candidate saves, queue recovery, and launch are not
claimed here.

`PrelaunchBufferRecovery` separately owns buffer-to-queue replay,
`BootstrapPhysicalInput` owns scalar-to-input conversion, and
`BootstrapTruePrefixController` owns candidate saves.  This adapter does not
import or reconstruct those producers.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePrelaunchPhysicalReplay

open BootstrapDimensions
open PublicDiscreteDraws
open ReferencePrelaunchFollower

abbrev blockStart (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) : ℕ :=
  s.val * B_boot p

abbrev blockEnd (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) : ℕ :=
  min p.T ((s.val + 1) * B_boot p)

abbrev blockLength (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) : ℕ :=
  blockEnd p s - blockStart p s

theorem blockStart_le_T (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
    blockStart p s ≤ p.T := by
  obtain ⟨t, ht⟩ := BootstrapDimensions.calendarBlock_nonempty p s
  have h := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht
  exact h.1.trans (Nat.le_of_lt t.isLt)

theorem blockStart_le_end (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
    blockStart p s ≤ blockEnd p s := by
  change blockStart p s ≤ min p.T ((s.val + 1) * B_boot p)
  apply Nat.le_min.mpr
  constructor
  · exact blockStart_le_T p s
  · dsimp [blockStart]
    exact Nat.mul_le_mul_right (B_boot p) (Nat.le_succ s.val)

theorem blockEnd_le_T (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
    blockEnd p s ≤ p.T :=
  Nat.min_le_left _ _

theorem blockEnd_eq_start_add_length (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) :
    blockEnd p s = blockStart p s + blockLength p s := by
  rw [Nat.add_comm (blockStart p s) (blockLength p s)]
  exact (Nat.sub_add_cancel (blockStart_le_end p s)).symm

theorem blockLength_eq_calendarBlock_card (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) :
    blockLength p s = (BootstrapDimensions.calendarBlock p s).card := by
  exact (BootstrapDimensions.calendarBlock_card p s).symm

theorem blockLength_le_T (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
    blockLength p s ≤ p.T := by
  rw [blockLength_eq_calendarBlock_card]
  exact (BootstrapDimensions.calendarBlock_card_le_B_boot p s).trans
    (BootstrapDimensions.B_boot_le_T p)

/-- The `u`th actual round in the clipped block, in increasing calendar order. -/
def blockRound (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (u : Fin (blockLength p s)) : Fin p.T :=
  ⟨blockStart p s + u.val, by
    have hu := Nat.add_lt_add_left u.isLt (blockStart p s)
    rw [← blockEnd_eq_start_add_length p s] at hu
    exact lt_of_lt_of_le hu (blockEnd_le_T p s)⟩

theorem blockRound_val (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (u : Fin (blockLength p s)) : (blockRound p s u).val = blockStart p s + u.val := rfl

theorem blockRound_strictMono (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (u v : Fin (blockLength p s)) (huv : u.val < v.val) :
    (blockRound p s u).val < (blockRound p s v).val := by
  rw [blockRound_val, blockRound_val]
  omega

theorem blockRound_mem (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (u : Fin (blockLength p s)) : blockRound p s u ∈ BootstrapDimensions.calendarBlock p s := by
  rw [BootstrapDimensions.mem_calendarBlock_iff]
  constructor
  · exact Nat.le_add_right _ _
  · have hu := Nat.add_lt_add_left u.isLt (blockStart p s)
    rw [← blockEnd_eq_start_add_length p s] at hu
    have hu' : blockStart p s + u.val < min p.T ((s.val + 1) * B_boot p) := by
      simpa [blockEnd] using hu
    simpa only [blockRound_val] using hu'

theorem exists_blockRound (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    ∃ u : Fin (blockLength p s), blockRound p s u = t := by
  have ht' := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht
  let v := t.val - s.val * B_boot p
  have hv : v < blockLength p s := by
    change t.val - (s.val * B_boot p) <
      min p.T ((s.val + 1) * B_boot p) - (s.val * B_boot p)
    omega
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Fin.ext
  rw [blockRound_val]
  dsimp [v]
  rw [show blockStart p s = s.val * B_boot p by rfl]
  omega

/-- All explicit inputs required to connect one block.  The prefix is typed
only; this structure asserts nothing about its physical origin. -/
structure Input (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) where
  physical : BootstrapPhysicalBlock.Input p s
  follower : ActiveRoundActions.Follower p.m
  follower_outside : follower ∉ physical.uninformed
  eta : ReferencePrelaunchFollower.LearningRate
  activation : ReferencePrelaunchFollower.Activation p
  activation_le_blockStart : activation.val ≤ blockStart p s + 1
  earlierHistory : ReferencePrelaunchFollower.LocalHistory p (blockStart p s)

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

def ownPlayer (z : Input p s) : Fin p.m :=
  PublicDiscreteDraws.followerPlayer p.two_le_m z.follower

def followerIndex (z : Input p s) : Fin (p.m - 1) :=
  ⟨z.follower.val, by simpa [PublicDiscreteDraws.followerCount] using z.follower.isLt⟩

/-- Convert the physical feedback to the accepted typed observation, using
the physical quantized index as its exact grid witness. -/
def physicalObservation (z : Input p s) (t : Fin p.T) :
    ReferencePrelaunchFollower.Observation p := by
  let st := BootstrapPhysicalBlock.run z.physical t.val
  let idx := BootstrapPhysicalBlock.observationIndex z.physical st t (ownPlayer z)
  refine ⟨⟨BootstrapPhysicalBlock.feedback z.physical st t (ownPlayer z),
    BootstrapPhysicalBlock.feedback_mem_Icc z.physical st t (ownPlayer z)⟩, idx, ?_⟩
  change BootstrapPhysicalBlock.feedback z.physical st t (ownPlayer z) =
    (idx.val : ℝ) / (ConstructorDimensions.D p : ℝ)
  rw [← BootstrapPhysicalBlock.observationIndex_value]
  rfl

theorem physicalObservation_index_value (z : Input p s) (t : Fin p.T) :
    RealRewardGridCount.realRewardGridValue (ConstructorDimensions.D p)
      (ConstructorDimensions.D_pos p)
      (BootstrapPhysicalBlock.observationIndex z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z)) =
      (physicalObservation z t).val.val := by
  change RealRewardGridCount.realRewardGridValue (ConstructorDimensions.D p)
      (ConstructorDimensions.D_pos p)
      (BootstrapPhysicalBlock.observationIndex z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z)) =
      BootstrapPhysicalBlock.feedback z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z)
  exact BootstrapPhysicalBlock.observationIndex_value _ _ _ _

/-- The required current physical pair: this player's actual action and the
observation index generated from the same physical action profile. -/
def physicalEntry (z : Input p s) (t : Fin p.T) :
    Fin p.K × ReferencePrelaunchFollower.Observation p :=
  (BootstrapPhysicalBlock.actions z.physical (BootstrapPhysicalBlock.run z.physical t.val)
      t (ownPlayer z), physicalObservation z t)

theorem physicalEntry_action (z : Input p s) (t : Fin p.T) :
    (physicalEntry z t).1 = BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) := rfl

theorem physicalEntry_feedback (z : Input p s) (t : Fin p.T) :
    ((physicalEntry z t).2).val.val = BootstrapPhysicalBlock.feedback z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) := rfl

theorem observationIndex_zero_of_collision (z : Input p s) (t : Fin p.T)
    (h : ¬ FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z)) :
    BootstrapPhysicalBlock.observationIndex z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) = 0 := by
  simp [BootstrapPhysicalBlock.observationIndex, h]

theorem observationIndex_reward_of_collision_free (z : Input p s) (t : Fin p.T)
    (h : FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z)) :
    BootstrapPhysicalBlock.observationIndex z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      z.physical.rewards t ((BootstrapPhysicalBlock.actions z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z)) := by
  simp [BootstrapPhysicalBlock.observationIndex, h]

theorem feedback_zero_of_collision (z : Input p s) (t : Fin p.T)
    (h : ¬ FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z)) :
    BootstrapPhysicalBlock.feedback z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) = 0 := by
  rw [← BootstrapPhysicalBlock.observationIndex_value]
  rw [observationIndex_zero_of_collision z t h]
  simp [RealRewardGridCount.realRewardGridValue]

theorem feedback_reward_of_collision_free (z : Input p s) (t : Fin p.T)
    (h : FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z)) :
    BootstrapPhysicalBlock.feedback z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      RealRewardGridCount.realRewardGridValue (ConstructorDimensions.D p)
        (ConstructorDimensions.D_pos p)
        (z.physical.rewards t ((BootstrapPhysicalBlock.actions z.physical
          (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z))) := by
  calc
    BootstrapPhysicalBlock.feedback z.physical
        (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
        RealRewardGridCount.realRewardGridValue (ConstructorDimensions.D p)
          (ConstructorDimensions.D_pos p)
          (BootstrapPhysicalBlock.observationIndex z.physical
            (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z)) :=
      (BootstrapPhysicalBlock.observationIndex_value _ _ _ _).symm
    _ = RealRewardGridCount.realRewardGridValue (ConstructorDimensions.D p)
          (ConstructorDimensions.D_pos p)
          (z.physical.rewards t ((BootstrapPhysicalBlock.actions z.physical
            (BootstrapPhysicalBlock.run z.physical t.val) t) (ownPlayer z))) := by
      rw [observationIndex_reward_of_collision_free z t h]

theorem physicalAction_eq_unoccupied (z : Input p s) (t : Fin p.T) :
    BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      BootstrapPhysicalBlock.unoccupiedAction z.physical t z.follower := by
  change BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m z.follower) = _
  rw [BootstrapPhysicalBlock.actions_follower]
  simp only [BootstrapPhysicalBlock.followerAction,
    dite_eq_right z.follower_outside]

theorem physicalAction_data (z : Input p s) (t : Fin p.T)
    (hslot : BootstrapPhysicalBlock.slot z.physical t = PublicDiscreteDraws.dataSlot) :
    BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      BootstrapPhysicalBlock.pilot z.physical t (ownPlayer z) := by
  rw [physicalAction_eq_unoccupied]
  simp [BootstrapPhysicalBlock.unoccupiedAction, hslot, ownPlayer]

theorem physicalAction_down (z : Input p s) (t : Fin p.T)
    (hslot : BootstrapPhysicalBlock.slot z.physical t = PublicDiscreteDraws.downSlot) :
    BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      (BootstrapPhysicalBlock.tuple z.physical t).val (ownPlayer z) := by
  rw [physicalAction_eq_unoccupied]
  simpa [ownPlayer] using
    BootstrapPhysicalBlock.unoccupiedAction_down z.physical t z.follower hslot

theorem physicalAction_selected_up (z : Input p s) (t : Fin p.T)
    (hslot : BootstrapPhysicalBlock.slot z.physical t = PublicDiscreteDraws.upSlot)
    (hselected : BootstrapPhysicalBlock.selected z.physical t = z.follower) :
    BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      ActiveRoundActions.sendArm (((z.physical.row.2 t).2 (1, z.follower)).2)
        ((BootstrapPhysicalBlock.tuple z.physical t).val (ownPlayer z))
        ((BootstrapPhysicalBlock.tuple z.physical t).val
          (ActiveRoundActions.coordinator p.two_le_m)) := by
  rw [physicalAction_eq_unoccupied, ← hselected]
  simpa [ownPlayer, hselected] using
    BootstrapPhysicalBlock.unoccupiedAction_selected_up z.physical t hslot

theorem physicalAction_tuple_other (z : Input p s) (t : Fin p.T)
    (hdata : BootstrapPhysicalBlock.slot z.physical t ≠ PublicDiscreteDraws.dataSlot)
    (hnotSelectedUp : ¬ (BootstrapPhysicalBlock.slot z.physical t = PublicDiscreteDraws.upSlot ∧
      BootstrapPhysicalBlock.selected z.physical t = z.follower)) :
    BootstrapPhysicalBlock.actions z.physical
      (BootstrapPhysicalBlock.run z.physical t.val) t (ownPlayer z) =
      (BootstrapPhysicalBlock.tuple z.physical t).val (ownPlayer z) := by
  rw [physicalAction_eq_unoccupied]
  simp [BootstrapPhysicalBlock.unoccupiedAction, hdata, hnotSelectedUp, ownPlayer]

def prefixEmbed (u : Fin (blockStart p s)) : Fin (blockEnd p s) :=
  ⟨u.val, Nat.lt_of_lt_of_le u.isLt (blockStart_le_end p s)⟩

def blockEmbed (u : Fin (blockLength p s)) : Fin (blockEnd p s) :=
  ⟨blockStart p s + u.val, by
    have hu := Nat.add_lt_add_left u.isLt (blockStart p s)
    rw [← blockEnd_eq_start_add_length p s] at hu
    exact hu⟩

def prefixIndices (_z : Input p s) : List (Fin (blockEnd p s)) :=
  (List.ofFn (fun u : Fin (blockStart p s) => u)).map prefixEmbed

def blockIndices (_z : Input p s) : List (Fin (blockEnd p s)) :=
  (List.ofFn (fun u : Fin (blockLength p s) => u)).map blockEmbed

theorem blockIndices_pairwise_increasing (z : Input p s) :
    (blockIndices z).Pairwise (fun t u => t.val < u.val) := by
  unfold blockIndices
  rw [List.pairwise_map, List.pairwise_ofFn]
  intro u v huv
  simp only [blockEmbed]
  omega

def chronologicalHistory (z : Input p s) :
    ReferencePrelaunchFollower.LocalHistory p (blockEnd p s) := fun t =>
  if ht : t.val < blockStart p s then
    z.earlierHistory ⟨t.val, ht⟩
  else
    physicalEntry z ⟨t.val, Nat.lt_of_lt_of_le t.isLt (blockEnd_le_T p s)⟩

theorem chronologicalHistory_prefix (z : Input p s) (u : Fin (blockStart p s)) :
    chronologicalHistory z (prefixEmbed u) = z.earlierHistory u := by
  have hu : (prefixEmbed u).val < blockStart p s := u.isLt
  unfold chronologicalHistory
  rw [dite_eq_left hu]
  rfl

theorem chronologicalHistory_block (z : Input p s) (u : Fin (blockLength p s)) :
    chronologicalHistory z (blockEmbed u) = physicalEntry z (blockRound p s u) := by
  have hu : ¬ (blockEmbed u).val < blockStart p s := by
    simp only [blockEmbed]
    omega
  have hround :
        (⟨(blockEmbed u).val, Nat.lt_of_lt_of_le (blockEmbed u).isLt
        (blockEnd_le_T p s)⟩ : Fin p.T) = blockRound p s u := by
    apply Fin.ext
    rfl
  simp [chronologicalHistory, hu, hround]

def incomingState (z : Input p s) :
    ReferencePrelaunchFollower.State p z.eta :=
  ReferencePrelaunchFollower.replay z.eta (followerIndex z) z.physical.row z.activation
    z.earlierHistory (blockStart_le_T p s)

def blockReplay (z : Input p s) : ReferencePrelaunchFollower.State p z.eta :=
  ReferencePrelaunchFollower.run (followerIndex z) z.physical.row z.activation
    (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z) (incomingState z)

theorem run_prefix_map (z : Input p s) (us : List (Fin (blockStart p s)))
    (st : ReferencePrelaunchFollower.State p z.eta) :
    ReferencePrelaunchFollower.run (followerIndex z) z.physical.row z.activation
        (chronologicalHistory z) (blockEnd_le_T p s) (us.map prefixEmbed) st =
      ReferencePrelaunchFollower.run (followerIndex z) z.physical.row z.activation
        z.earlierHistory (blockStart_le_T p s) us st := by
  induction us generalizing st with
  | nil => rfl
  | cons u us ih =>
    have hcalendar :
        ReferencePrelaunchFollower.calendar (blockEnd_le_T p s) (prefixEmbed u) =
          ReferencePrelaunchFollower.calendar (blockStart_le_T p s) u := by
      apply Fin.ext
      rfl
    simp only [List.map_cons, ReferencePrelaunchFollower.run]
    rw [hcalendar, chronologicalHistory_prefix, ih]

theorem run_append_block (z : Input p s) :
    ReferencePrelaunchFollower.run (followerIndex z) z.physical.row z.activation
        (chronologicalHistory z) (blockEnd_le_T p s)
        (prefixIndices z ++ blockIndices z) (ReferencePrelaunchFollower.initial p z.eta) =
      blockReplay z := by
  rw [ReferencePrelaunchFollower.run_append]
  unfold prefixIndices
  rw [run_prefix_map]
  rfl

theorem activation_le_blockRound (z : Input p s) (u : Fin (blockLength p s)) :
    z.activation.val ≤ (blockRound p s u).val + 1 := by
  have hu : blockStart p s ≤ (blockRound p s u).val := by
    rw [blockRound_val]
    exact Nat.le_add_right _ _
  exact z.activation_le_blockStart.trans (Nat.add_le_add_right hu 1)

theorem blockRound_manuscript_bounds (_z : Input p s) (u : Fin (blockLength p s)) :
    blockStart p s + 1 ≤ (blockRound p s u).val + 1 ∧
      (blockRound p s u).val + 1 ≤ blockEnd p s ∧ blockEnd p s ≤ p.T := by
  have hm := blockRound_mem p s u
  have hb := (BootstrapDimensions.mem_calendarBlock_iff_manuscriptRound p s
    (blockRound p s u)).mp hm
  exact ⟨hb.1, hb.2, blockEnd_le_T p s⟩

theorem blockIndices_length (z : Input p s) : (blockIndices z).length = blockLength p s := by
  simp [blockIndices]

theorem prefixIndices_length (z : Input p s) : (prefixIndices z).length = blockStart p s := by
  simp [prefixIndices]

theorem incomingState_registers (z : Input p s) :
    (incomingState z).lastDown = none ∧
    ReferencePrelaunchFollower.acceptedStart (incomingState z) = 0 ∧
    (incomingState z).S = 0 ∧ (incomingState z).delta = 0 ∧
    (incomingState z).backlog = 0 ∧ (incomingState z).status = .unoccupied := by
  exact ReferencePrelaunchFollower.replay_registers z.eta (followerIndex z) z.physical.row
    z.activation z.earlierHistory (blockStart_le_T p s)

theorem blockReplay_registers (z : Input p s) :
    (blockReplay z).lastDown = none ∧
    ReferencePrelaunchFollower.acceptedStart (blockReplay z) = 0 ∧
    (blockReplay z).S = 0 ∧ (blockReplay z).delta = 0 ∧
    (blockReplay z).backlog = 0 ∧ (blockReplay z).status = .unoccupied := by
  obtain ⟨hin, hstart, hS, hdelta, hbacklog, hstatus⟩ := incomingState_registers z
  obtain ⟨hout, hSout, hdeltaOut, hbacklogOut, hstatusOut⟩ :=
    ReferencePrelaunchFollower.run_registers (followerIndex z) z.physical.row z.activation
      (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z) (incomingState z)
  have hnone : (blockReplay z).lastDown = none := hout.trans hin
  refine ⟨hnone, ?_, hSout.trans hS, hdeltaOut.trans hdelta,
    hbacklogOut.trans hbacklog, hstatusOut.trans hstatus⟩
  unfold ReferencePrelaunchFollower.acceptedStart
  simp [hnone]

theorem blockReplay_failure_iff (z : Input p s) :
    (blockReplay z).initializationFailure = true ↔
      (incomingState z).initializationFailure = true ∨
        ∃ d ∈ ReferencePrelaunchFollower.decisions (followerIndex z) z.physical.row
          z.activation (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z)
          (incomingState z),
          OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p z.eta) 0 (d.1.val + 1) d.2 := by
  have hu := incomingState_registers z |>.2.2.2.2.2
  exact ReferencePrelaunchFollower.run_failure_iff (followerIndex z) z.physical.row z.activation
    (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z) (incomingState z) hu

theorem blockReplay_buffer (z : Input p s) :
    (blockReplay z).buffer = (incomingState z).buffer ++
      (blockIndices z).flatMap (fun u => ReferencePrelaunchFollower.logAt (followerIndex z)
        z.physical.row z.activation (ReferencePrelaunchFollower.calendar
          (blockEnd_le_T p s) u) (chronologicalHistory z u)) := by
  exact ReferencePrelaunchFollower.run_buffer (followerIndex z) z.physical.row z.activation
    (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z) (incomingState z)
    (incomingState_registers z |>.2.2.2.2.2)

theorem blockReplay_batch_spec (z : Input p s) :
    (blockReplay z).downBatch.pending.length < AffineBatchDecoder.quota p ∧
    (∀ b ∈ (blockReplay z).downBatch.completed,
      b.length = AffineBatchDecoder.quota p) ∧
    AffineBatchDecoder.collected (blockReplay z).downBatch =
      AffineBatchDecoder.collected (incomingState z).downBatch ++
        (blockIndices z).flatMap (fun u => AffineBatchDecoder.positiveAt p
          (ReferencePrelaunchFollower.traceAt (followerIndex z) z.physical.row z.activation
            (ReferencePrelaunchFollower.calendar (blockEnd_le_T p s) u)
            (chronologicalHistory z u))
          (ReferencePrelaunchFollower.calendar (blockEnd_le_T p s) u)) := by
  obtain ⟨hk, hc, _⟩ := ReferencePrelaunchFollower.replay_batch_spec z.eta (followerIndex z)
    z.physical.row z.activation z.earlierHistory (blockStart_le_T p s)
  exact ReferencePrelaunchFollower.run_batch_spec (followerIndex z) z.physical.row z.activation
    (chronologicalHistory z) (blockEnd_le_T p s) (blockIndices z) (incomingState z)
    (incomingState_registers z |>.2.2.2.2.2) hk hc

theorem blockReplay_uses_physical_history (z : Input p s)
    (u : Fin (blockLength p s)) :
    chronologicalHistory z (blockEmbed u) =
      ((BootstrapPhysicalBlock.actions z.physical
          (BootstrapPhysicalBlock.run z.physical (blockRound p s u).val)
          (blockRound p s u) (ownPlayer z)),
        physicalObservation z (blockRound p s u)) := by
  rw [chronologicalHistory_block]
  rfl

theorem selected_upWord_eq_initial (z : Input p s) (u : Fin (blockLength p s))
    (hslot : BootstrapPhysicalBlock.slot z.physical (blockRound p s u) =
      PublicDiscreteDraws.upSlot)
    (hselected : BootstrapPhysicalBlock.selected z.physical (blockRound p s u) = z.follower) :
    (ReferencePrelaunchFollower.upWord z.eta (followerIndex z) z.physical.row z.activation
        (blockRound p s u)).map
      (OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p z.eta)) =
      some (BootstrapPhysicalBlock.initialUpWord p) := by
  have hactive := activation_le_blockRound z u
  have hslot' : PublicDiscreteDraws.slotDraw
      (z.physical.row.2 (blockRound p s u)).1 = PublicDiscreteDraws.upSlot := by
    change BootstrapPhysicalBlock.slot z.physical (blockRound p s u) = _
    exact hslot
  have hselected' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (z.physical.row.2 (blockRound p s u)).1 = followerIndex z := by
    apply Fin.ext
    change (BootstrapPhysicalBlock.selected z.physical (blockRound p s u)).val = z.follower.val
    exact congrArg Fin.val hselected
  let empty : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p z.eta) :=
    ⟨OrdinaryMessageCodec.upPlaceholder, by
      change OrdinaryMessageCodec.upPlaceholder = OrdinaryMessageCodec.upPlaceholder ∨ _
      exact Or.inl rfl⟩
  have hOffer : ReferencePrelaunchFollower.upOffer z.eta (followerIndex z) z.physical.row
      z.activation (blockRound p s u) = some empty := by
    unfold ReferencePrelaunchFollower.upOffer
    rw [ite_eq_left ⟨hactive, hslot', hselected'⟩]
  have hflat : OrdinaryMessageCodec.wordEquivFlat
      (ReferencePrelaunchFollower.codecParams p z.eta)
      (OrdinaryMessageCodec.encodeUp (ReferencePrelaunchFollower.codecParams p z.eta)
        empty) = fun _ => 0 := by
    funext i
    change OrdinaryMessageCodec.encodeFive
      (OrdinaryMessageCodec.fieldWidth p.T (ConstructorDimensions.D p))
      0 0 0 0 0 i.divNat i.modNat = 0
    rw [OrdinaryMessageCodec.encodeFive]
    rw [show OrdinaryMessageCodec.fiveField 0 0 0 0 0 i.divNat = 0 by
      unfold OrdinaryMessageCodec.fiveField
      split_ifs <;> rfl]
    simp [OrdinaryMessageCodec.encodeField]
  simp only [ReferencePrelaunchFollower.upWord, hOffer, Option.map_some]
  rw [hflat, BootstrapPhysicalBlock.initialUpWord_eq_zero]
  rfl

theorem selected_upWord_in_unoccupied_replay (z : Input p s)
    (u : Fin (blockLength p s))
    (hslot : BootstrapPhysicalBlock.slot z.physical (blockRound p s u) =
      PublicDiscreteDraws.upSlot)
    (hselected : BootstrapPhysicalBlock.selected z.physical (blockRound p s u) = z.follower) :
    (blockReplay z).status = .unoccupied ∧
      (ReferencePrelaunchFollower.upWord z.eta (followerIndex z) z.physical.row z.activation
        (blockRound p s u)).map
          (OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p z.eta)) =
        some (BootstrapPhysicalBlock.initialUpWord p) := by
  exact ⟨(blockReplay_registers z).2.2.2.2.2,
    selected_upWord_eq_initial z u hslot hselected⟩

end Bandits.Support.ReferencePrelaunchPhysicalReplay

end
