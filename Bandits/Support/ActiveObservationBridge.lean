/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.FiniteBanditModel

/-!
# Physical observation facts for live rounds

The physical feedback rule is from `sources/zip4/manuscript/01_introduction.tex:20-28`.
The affine message equation and literal decoder are from
`sources/zip4/manuscript/05_binary_transport.tex:7-43`; action branches and live
status tests are from lines 65-175; and the recorder's pilot-avoidance test is
from lines 352-424. Parser and local acceptance tests are at
`sources/zip4/manuscript/06_interruptions.tex:123-177`. The stale-batch
exclusion argument is at `sources/zip4/manuscript/appendix_a_local_protocol.tex:87-109`;
it is not proved here.

This module proves deterministic physical feedback identities and adapts
supplied `LiveRoundData` to the accepted literal affine batch decoder. The
segment's acceptance flags remain arbitrary inputs; this does not establish
the chronological local protocol, authenticity, stale-word exclusion, or a
probability bound.
-/

@[expose] public section

namespace Bandits.Support.ActiveObservationBridge

open Bandits.Support.FiniteBanditModel
open Bandits.Support.AffineChannelLaw
open Bandits.Support.PublicDiscreteDraws

variable {m K B : ℕ}

/-! ## Physical DATA recording -/

/-- An unoccupied DATA follower that hits its assigned pilot arm takes that arm. -/
theorem data_unoccupied_pilot_action (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (i : ActiveRoundActions.Follower m) (hslot : r.slot = dataSlot)
    (hstatus : s.status i = .unoccupied)
    (hpilot : r.pilots (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) = a.assigned i) :
    ActiveRoundActions.actions hm s r (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) = a.assigned i := by
  rw [ActiveRoundActions.actions_follower,
    ActiveRoundActions.followerAction_unoccupied_data hm s r i hstatus hslot]
  exact hpilot

/-- An occupied DATA follower always takes its fixed assigned arm. -/
theorem data_occupied_fixed_action (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (i : ActiveRoundActions.Follower m) (hslot : r.slot = dataSlot)
    (hstatus : (s.status i).occupied) :
    ActiveRoundActions.actions hm s r (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) = a.assigned i := by
  rw [ActiveRoundActions.actions_follower,
    ActiveRoundActions.followerAction_occupied_data hm s r i hstatus hslot]

/-- With confirmations missing, the DATA coordinator takes its supplied pilot. -/
theorem data_coordinator_pilot_action (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (hmissing : s.missing ≠ ∅) (hslot : r.slot = dataSlot) :
    ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) =
      r.pilots (ActiveRoundActions.coordinator hm) := by
  rw [ActiveRoundActions.actions_coordinator,
    ActiveRoundActions.coordinatorAction_data hm s r hmissing hslot]

/-- With no confirmations missing, the DATA coordinator takes its supplied fast arm. -/
theorem data_coordinator_fast_action (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (hempty : s.missing = ∅) :
    ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) = r.fast := by
  rw [ActiveRoundActions.actions_coordinator,
    ActiveRoundActions.coordinatorAction_fast hm s r hempty]

/-- A DATA coordinator pilot hit supplies the actual-action premise for arm `j`. -/
theorem data_coordinator_pilot_hit_action (hm : 2 ≤ m)
    (a : ActiveRoundActions.Assignment m K) (s : ActiveRoundActions.Snapshot a)
    (r : ActiveRoundActions.RoundInput a B) (j : Arm K)
    (hmissing : s.missing ≠ ∅) (hslot : r.slot = dataSlot)
    (hpilot : r.pilots (ActiveRoundActions.coordinator hm) = j) :
    ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) = j := by
  rw [data_coordinator_pilot_action hm a s r hmissing hslot]
  exact hpilot

/-- A DATA coordinator fast-arm hit supplies the actual-action premise for arm `j`. -/
theorem data_coordinator_fast_hit_action (hm : 2 ≤ m)
    (a : ActiveRoundActions.Assignment m K) (s : ActiveRoundActions.Snapshot a)
    (r : ActiveRoundActions.RoundInput a B) (j : Arm K)
    (hempty : s.missing = ∅) (hfast : r.fast = j) :
    ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) = j := by
  rw [data_coordinator_fast_action hm a s r hempty]
  exact hfast

/-- The DATA pilot-mask test makes an assigned follower alone on its target.

The mask premise is exactly the literal nonowner-pilot test. Occupied other
followers avoid the target by injectivity of the existing assignment; an
unoccupied coordinator using its fast arm avoids every assigned target by the
existing `fast_outside` field.
-/
theorem follower_data_recording_correct (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow K) (i : ActiveRoundActions.Follower m)
    (hslot : r.slot = dataSlot)
    (haction : ActiveRoundActions.actions hm s r (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) =
      a.assigned i)
    (hmask : ∀ ell : Player m, ell ≠ Bandits.Support.PublicDiscreteDraws.followerPlayer hm i →
      r.pilots ell ≠ a.assigned i) :
    ActiveRoundActions.feedback hm s r row (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) =
      row.val (a.assigned i) := by
  have hfree : collisionFreeFor (ActiveRoundActions.actions hm s r)
      (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) := by
    intro p hpi
    rcases ActiveRoundActions.player_cases hm p with hcoord | ⟨j, hfollow⟩
    · subst p
      have hcoordTarget : ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) ≠
          a.assigned i := by
        by_cases hempty : s.missing = ∅
        · rw [data_coordinator_fast_action hm a s r hempty]
          exact r.fast_outside i
        · rw [data_coordinator_pilot_action hm a s r hempty hslot]
          exact hmask (ActiveRoundActions.coordinator hm)
            (ActiveRoundActions.followerPlayer_ne_coordinator hm i).symm
      intro hsame
      exact hcoordTarget (hsame.trans haction)
    · subst p
      have hji : j ≠ i := fun hij =>
        hpi (congrArg (Bandits.Support.PublicDiscreteDraws.followerPlayer hm) hij)
      have hotherTarget : ActiveRoundActions.actions hm s r
          (Bandits.Support.PublicDiscreteDraws.followerPlayer hm j) ≠ a.assigned i := by
        cases hj : s.status j with
        | unoccupied =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_unoccupied_data hm s r j hj hslot]
            exact hmask (Bandits.Support.PublicDiscreteDraws.followerPlayer hm j)
              (fun heq => hji (ActiveRoundActions.followerPlayer_injective hm heq))
        | pending =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_occupied_data hm s r j (Or.inl hj) hslot]
            exact ActiveRoundActions.assigned_ne j i hji
        | released =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_occupied_data hm s r j (Or.inr hj) hslot]
            exact ActiveRoundActions.assigned_ne j i hji
      intro hsame
      exact hotherTarget (hsame.trans haction)
  calc
    ActiveRoundActions.feedback hm s r row (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) =
        row.val (ActiveRoundActions.actions hm s r
          (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i)) :=
      ActiveRoundActions.feedback_eq_reward_of_collision_free hm s r row _ hfree
    _ = row.val (a.assigned i) := by rw [haction]

/-- The coordinator's DATA pilot-mask test records an arm outside the assigned image. -/
theorem coordinator_data_recording_correct (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow K) (j : Arm K)
    (hslot : r.slot = dataSlot)
    (houtside : ∀ i : ActiveRoundActions.Follower m, j ≠ a.assigned i)
    (haction : ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) = j)
    (hmask : ∀ ell : Player m, ell ≠ ActiveRoundActions.coordinator hm → r.pilots ell ≠ j) :
    ActiveRoundActions.feedback hm s r row (ActiveRoundActions.coordinator hm) = row.val j := by
  have hfree : collisionFreeFor (ActiveRoundActions.actions hm s r)
      (ActiveRoundActions.coordinator hm) := by
    intro p hpc
    rcases ActiveRoundActions.player_cases hm p with hcoord | ⟨i, hfollow⟩
    · subst p
      exact False.elim (hpc rfl)
    · subst p
      have hotherNe : ActiveRoundActions.actions hm s r
          (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) ≠ j := by
        cases hi : s.status i with
        | unoccupied =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_unoccupied_data hm s r i hi hslot]
            exact hmask (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i)
              (ActiveRoundActions.followerPlayer_ne_coordinator hm i)
        | pending =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_occupied_data hm s r i (Or.inl hi) hslot]
            exact (houtside i).symm
        | released =>
            rw [ActiveRoundActions.actions_follower,
              ActiveRoundActions.followerAction_occupied_data hm s r i (Or.inr hi) hslot]
            exact (houtside i).symm
      intro hsame
      exact hotherNe (hsame.trans haction)
  calc
    ActiveRoundActions.feedback hm s r row (ActiveRoundActions.coordinator hm) =
        row.val (ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm)) :=
      ActiveRoundActions.feedback_eq_reward_of_collision_free hm s r row _ hfree
    _ = row.val j := by rw [haction]

/-- Follower recording identity at the live snapshot immediately before a supplied round. -/
theorem live_follower_data_recording_correct (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a B) (t : Fin p.T)
    (row : ActiveRoundActions.RewardRow p.K) (i : ActiveRoundActions.Follower p.m)
    (hslot : (rounds t).input.slot = dataSlot)
    (haction : ActiveRoundActions.actions p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i) = a.assigned i)
    (hmask : ∀ ell : Player p.m, ell ≠ Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i →
      (rounds t).input.pilots ell ≠ a.assigned i) :
    ActiveRoundActions.feedback p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input row (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i) = row.val (a.assigned i) := by
  exact follower_data_recording_correct p.two_le_m a _ _ row i hslot haction hmask

/-- Coordinator recording identity at the live snapshot immediately before a supplied round. -/
theorem live_coordinator_data_recording_correct
    (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a B) (t : Fin p.T)
    (row : ActiveRoundActions.RewardRow p.K) (j : Arm p.K)
    (hslot : (rounds t).input.slot = dataSlot)
    (houtside : ∀ i : ActiveRoundActions.Follower p.m, j ≠ a.assigned i)
    (haction : ActiveRoundActions.actions p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input (ActiveRoundActions.coordinator p.two_le_m) = j)
    (hmask : ∀ ell : Player p.m, ell ≠ ActiveRoundActions.coordinator p.two_le_m →
      (rounds t).input.pilots ell ≠ j) :
    ActiveRoundActions.feedback p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input row (ActiveRoundActions.coordinator p.two_le_m) = row.val j := by
  exact coordinator_data_recording_correct p.two_le_m a _ _ row j hslot houtside haction hmask

/-- Positive DATA feedback by an unoccupied DOWN receiver proves its sent-word equation.
The no-released premise is derived from the live-segment construction at the strict
earlier prefix, not supplied as a hypothesis.
-/
theorem live_unoccupied_down_positive_equation
    (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a B) (t : Fin p.T)
    (i : ActiveRoundActions.Follower p.m)
    (hslot : (rounds t).input.slot = downSlot)
    (hselected : (rounds t).input.selected = i)
    (hmissing : i ∈ (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).missing)
    (hstatus : (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).status i = .unoccupied)
    (hpos : 0 < ActiveRoundActions.feedback p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input (rounds t).rewards
      (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i)) :
    AffineBatchDecoder.equation (rounds t).input.down.sample (rounds t).input.down.word := by
  have hmissing' : (rounds t).input.selected ∈
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val)).missing := by
    rw [hselected]
    exact hmissing
  have hstatus' : (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).status (rounds t).input.selected = .unoccupied := by
    rw [hselected]
    exact hstatus
  have hinvariant : ActiveRoundActions.no_released_while_missing
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val)) :=
    ActiveRoundActions.liveSegment_prefix_no_released p.two_le_m (List.ofFn rounds) t.val
  have hfeedback := ActiveRoundActions.unoccupied_down_feedback p.two_le_m
    (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
    (rounds t).input (rounds t).rewards hslot hmissing' hinvariant hstatus'
  rw [hselected] at hfeedback
  have hbit : (rounds t).input.down.bit = 1 := by
    rcases ActiveRoundActions.bit_eq_zero_or_one (rounds t).input.down.bit with hzero | hone
    · have hzeroFeedback : ActiveRoundActions.feedback p.two_le_m
          (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
          (rounds t).input (rounds t).rewards
          (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i) = 0 := by
        simpa [hzero] using hfeedback
      rw [hzeroFeedback] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
    · exact hone
  have hhash : affineHash (rounds t).input.down.sample (rounds t).input.down.word = 1 := by
    simpa only [ActiveRoundActions.HashedWord.bit] using hbit
  exact (AffineBatchDecoder.equation_iff_affineHash _ _).2 hhash

/-! ## UP physical observation -/

/-- A zero UP bit makes the selected unoccupied follower collide with the coordinator on `R₀`. -/
theorem unoccupied_up_zero_collision (hm : 2 ≤ m) (a : ActiveRoundActions.Assignment m K)
    (s : ActiveRoundActions.Snapshot a) (r : ActiveRoundActions.RoundInput a B)
    (hmissing : r.selected ∈ s.missing) (hstatus : s.status r.selected = .unoccupied)
    (hslot : r.slot = upSlot) (hbit : r.up.bit = 0) :
    ActiveRoundActions.actions hm s r (ActiveRoundActions.coordinator hm) =
      ActiveRoundActions.actions hm s r (Bandits.Support.PublicDiscreteDraws.followerPlayer hm r.selected) := by
  rw [ActiveRoundActions.actions_coordinator, ActiveRoundActions.actions_follower,
    ActiveRoundActions.coordinatorAction_up hm s r
      (ActiveRoundActions.missing_ne_empty_of_mem s r.selected hmissing) hslot,
    ActiveRoundActions.followerAction_unoccupied_up_selected hm s r hstatus hslot,
    hbit, ActiveRoundActions.sendArm_zero]

/-- A positive coordinator observation on a selected unoccupied live UP round proves
the equation for that round's supplied UP word. The missing-set gate is essential:
when it is empty the coordinator uses its fast arm.
-/
theorem live_unoccupied_up_positive_equation
    (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a B) (t : Fin p.T)
    (i : ActiveRoundActions.Follower p.m)
    (hslot : (rounds t).input.slot = upSlot)
    (hselected : (rounds t).input.selected = i)
    (hmissing : i ∈ (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).missing)
    (hstatus : (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).status i = .unoccupied)
    (hpos : 0 < ActiveRoundActions.feedback p.two_le_m
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
      (rounds t).input (rounds t).rewards (ActiveRoundActions.coordinator p.two_le_m)) :
    AffineBatchDecoder.equation (rounds t).input.up.sample (rounds t).input.up.word := by
  have hmissing' : (rounds t).input.selected ∈
      (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val)).missing := by
    rw [hselected]
    exact hmissing
  have hstatus' : (ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn rounds).take t.val)).status (rounds t).input.selected = .unoccupied := by
    rw [hselected]
    exact hstatus
  have hbit : (rounds t).input.up.bit = 1 := by
    rcases ActiveRoundActions.bit_eq_zero_or_one (rounds t).input.up.bit with hzero | hone
    · have hcollision := unoccupied_up_zero_collision p.two_le_m a (ActiveRoundActions.liveSegment
        p.two_le_m ((List.ofFn rounds).take t.val)) (rounds t).input hmissing' hstatus' hslot hzero
      have hzeroFeedback := ActiveRoundActions.feedback_eq_zero_of_collision p.two_le_m
        (ActiveRoundActions.liveSegment p.two_le_m ((List.ofFn rounds).take t.val))
        (rounds t).input (rounds t).rewards (ActiveRoundActions.coordinator p.two_le_m)
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m (rounds t).input.selected)
        (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m (rounds t).input.selected)
        hcollision.symm
      rw [hzeroFeedback] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
    · exact hone
  have hhash : affineHash (rounds t).input.up.sample (rounds t).input.up.word = 1 := by
    simpa only [ActiveRoundActions.HashedWord.bit] using hbit
  exact (AffineBatchDecoder.equation_iff_affineHash _ _).2 hhash

/-! ## DOWN decoder trace adapter -/

/-- Existing live state immediately before `t`, obtained from the strict earlier prefix. -/
noncomputable def liveSnapshotBefore (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (t : Fin p.T) : ActiveRoundActions.Snapshot a :=
  ActiveRoundActions.liveSegment p.two_le_m
    ((List.ofFn (fun s : Fin p.T => rounds s)).take t.val)

/-- The literal DOWN inputs to the accepted batch decoder, using physical feedback.
The selected flag is precisely DOWN, this follower, and still missing; the
receiver-enabled flag is precisely unoccupied. The sample and reward are the
round's supplied affine sample and physical follower feedback.
-/
noncomputable def downObservationTrace (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (i : ActiveRoundActions.Follower p.m) : AffineBatchDecoder.Trace p :=
  fun t =>
    let s := liveSnapshotBefore p a rounds t
    let d := rounds t
    { selected := decide (d.input.slot = downSlot ∧ d.input.selected = i ∧ i ∈ s.missing)
      receiverEnabled := decide (s.status i = .unoccupied)
      sample := d.input.down.sample
      roundedReward := ActiveRoundActions.feedback p.two_le_m s d.input d.rewards
        (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m i) }

/-- At every retained entry of the actual full-horizon decoder state, the equation
for the supplied DOWN word at that entry's own timestamp holds.
-/
theorem down_completed_entry_equation
    (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (i : ActiveRoundActions.Follower p.m)
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hbatch : batch ∈ (AffineBatchDecoder.stateAt p (downObservationTrace p a rounds i) p.T).completed)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) (he : e ∈ batch) :
    AffineBatchDecoder.equation e.sample ((rounds e.time).input.down.word) := by
  obtain ⟨_, hentries⟩ := AffineBatchDecoder.completed_batch_provenance p
    (downObservationTrace p a rounds i) p.T batch hbatch
  rcases hentries e he with ⟨_, heligible, hsample⟩
  change (downObservationTrace p a rounds i e.time).selected = true ∧
      (downObservationTrace p a rounds i e.time).receiverEnabled = true ∧
      0 < (downObservationTrace p a rounds i e.time).roundedReward at heligible
  rcases heligible with ⟨hselectedBool, hreceiverBool, hpositive⟩
  have hselected : (rounds e.time).input.slot = downSlot ∧
      (rounds e.time).input.selected = i ∧
      i ∈ (liveSnapshotBefore p a rounds e.time).missing := by
    simpa only [downObservationTrace, decide_eq_true_eq] using hselectedBool
  have hreceiver : (liveSnapshotBefore p a rounds e.time).status i = .unoccupied := by
    simpa only [downObservationTrace, decide_eq_true_eq] using hreceiverBool
  rcases hselected with ⟨hslot, htarget, hmissing⟩
  have hphysical := live_unoccupied_down_positive_equation p a rounds e.time i
    hslot htarget hmissing hreceiver (by
      simpa only [downObservationTrace, liveSnapshotBefore] using hpositive)
  simpa only [hsample, downObservationTrace, liveSnapshotBefore] using hphysical

/-- If all words actually supplied at the retained timestamps of one completed
batch are a fixed `u`, then `u` belongs to the literal solver's solution set.
Word persistence is the only additional condition; equation correctness is
derived from physical observations and decoder provenance above.
-/
theorem persistent_down_word_mem_solutions
    (p : Bandits.Support.ConstructorDimensions.Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (rounds : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (i : ActiveRoundActions.Follower p.m)
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hbatch : batch ∈ (AffineBatchDecoder.stateAt p (downObservationTrace p a rounds i) p.T).completed)
    (u : Word (AffineBatchDecoder.width p))
    (hpersist : ∀ e ∈ batch, (rounds e.time).input.down.word = u) :
    u ∈ AffineBatchDecoder.solutions (AffineBatchDecoder.samples batch) := by
  rw [AffineBatchDecoder.mem_solutions]
  apply (AffineBatchDecoder.satisfies_samples_iff batch u).2
  intro e he
  have hequation := down_completed_entry_equation p a rounds i batch hbatch e he
  rw [hpersist e he] at hequation
  exact hequation

end Bandits.Support.ActiveObservationBridge

end
