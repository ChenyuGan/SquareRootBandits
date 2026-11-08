/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapTruePrefixController
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.GeneratedClockConditionalMeans
public import Bandits.Support.BootstrapObservedFollower

import Lean.Elab.Tactic.Omega

/-!
# Deterministic multicast acceptance bridge

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:410-437,463-479`
and `sources/zip4/manuscript/07_public_setup.tex:87-109,123-143`.

This module connects actual multicast stay positives to the existing true-row
prefix controller. It proves no probability, false-row suppression, or
source-level closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapTruePrefixController
open Bandits.Support.ActiveRoundActions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.RealRewardGridCount
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBootstrapFiltration
open Bandits.Support.GeneratedClockConditionalMeans
open scoped BigOperators Classical

namespace Bandits.Support.BootstrapMulticastAcceptance

variable {p : Parameters} {s : Fin (n_boot p)}

/-- The literal actual MULTICAST DATA positives of an incoming follower whose
ID bit is zero. The active held-target conditions are exposed in the theorems
that use this set. -/
def multicastStayPositiveSet (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t =>
    (BootstrapPhysicalBlock.run x t.val).mode = .multicast ∧
      BootstrapPhysicalBlock.slot x t = dataSlot ∧
      x.ids (x.privateId i) t = false ∧
      0 < (BootstrapPhysicalBlock.observationIndex x
        (BootstrapPhysicalBlock.run x t.val) t
        (followerPlayer p.two_le_m i.val)).val

theorem eligible_not_discover (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T)
    (hactive : x.active i = true) (hheld : x.held i = x.target)
    (he : BootstrapTruePrefixController.eligible x i t)
    (hmode : (BootstrapPhysicalBlock.run x t.val).mode = .discover) : False := by
  rcases he with ⟨_, _, hzero, hslot, hpositive⟩
  let st := BootstrapPhysicalBlock.run x t.val
  have hcoord : BootstrapPhysicalBlock.actions x st t
      (coordinator p.two_le_m) = x.target := by
    rw [BootstrapPhysicalBlock.actions_coordinator]
    exact BootstrapPhysicalBlock.coordinatorAction_discover_data x st t hmode hslot
  have hfollower : BootstrapPhysicalBlock.actions x st t
      (followerPlayer p.two_le_m i.val) = x.target := by
    rw [BootstrapPhysicalBlock.actions_follower]
    simp [BootstrapPhysicalBlock.followerAction, i.property,
      BootstrapPhysicalBlock.uninformedAction, hactive, hzero, hheld]
  have hfeedback : 0 < BootstrapPhysicalBlock.feedback x st t
      (followerPlayer p.two_le_m i.val) :=
    (BootstrapPhysicalBlock.observationIndex_pos_iff x st t
      (followerPlayer p.two_le_m i.val)).mp hpositive
  have hfree := collisionFreeFor_of_playerFeedback_pos
    (BootstrapPhysicalBlock.actions x st t)
    (fun a => realRewardGridValue (D p) (D_pos p) (x.rewards t a))
    (followerPlayer p.two_le_m i.val) hfeedback
  exact hfree (coordinator p.two_le_m)
    (followerPlayer_ne_coordinator p.two_le_m i.val).symm
    (by rw [hcoord, hfollower])

/-- An actual positive multicast stay round releases the coordinator. The
full retained-list product then forces this follower's original private ID
bit to be one. -/
theorem multicast_positive_has_true_forward_bit
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (t : Fin p.T) (hactive : x.active i = true)
    (hheld : x.held i = x.target)
    (hmode : (BootstrapPhysicalBlock.run x t.val).mode = .multicast)
    (hslot : BootstrapPhysicalBlock.slot x t = dataSlot)
    (hzero : x.ids (x.privateId i) t = false)
    (hpositive : 0 < (BootstrapPhysicalBlock.observationIndex x
      (BootstrapPhysicalBlock.run x t.val) t
      (followerPlayer p.two_le_m i.val)).val) :
    BootstrapPhysicalBlock.forwardProduct x
        (BootstrapPhysicalBlock.run x t.val) t = 1 ∧
      BootstrapTruePrefixController.trueForwardBit x i t = true := by
  let st := BootstrapPhysicalBlock.run x t.val
  have hfeedback : 0 < BootstrapPhysicalBlock.feedback x st t
      (followerPlayer p.two_le_m i.val) :=
    (BootstrapPhysicalBlock.observationIndex_pos_iff x st t
      (followerPlayer p.two_le_m i.val)).mp hpositive
  have hfree := collisionFreeFor_of_playerFeedback_pos
    (BootstrapPhysicalBlock.actions x st t)
    (fun a => realRewardGridValue (D p) (D_pos p) (x.rewards t a))
    (followerPlayer p.two_le_m i.val) hfeedback
  have hfollower : BootstrapPhysicalBlock.actions x st t
      (followerPlayer p.two_le_m i.val) = x.target := by
    rw [BootstrapPhysicalBlock.actions_follower]
    simp [BootstrapPhysicalBlock.followerAction, i.property,
      BootstrapPhysicalBlock.uninformedAction, hactive, hzero, hheld]
  have hcoord_ne : BootstrapPhysicalBlock.coordinatorAction x st t ≠ x.target := by
    intro hcoord
    exact hfree (coordinator p.two_le_m)
      (followerPlayer_ne_coordinator p.two_le_m i.val).symm
      (by rw [BootstrapPhysicalBlock.actions_coordinator, hcoord, hfollower])
  have hproduct : BootstrapPhysicalBlock.forwardProduct x st t = 1 := by
    by_contra hne
    have hcoord := BootstrapPhysicalBlock.coordinatorAction_multicast_data
      x st t hmode hslot
    simp [hne] at hcoord
    exact hcoord_ne hcoord
  have hretained := BootstrapPhysicalBlock.run_retains_id x i hactive hheld t.val
  have hfactor : (if x.row.1 (x.privateId i) t = true then 1 else 0) = 1 := by
    have hbits := (Finset.prod_eq_one_iff.mp hproduct)
    exact hbits (x.privateId i) hretained
  have hbit : x.row.1 (x.privateId i) t = true := by
    by_contra hfalse
    simp [hfalse] at hfactor
  exact ⟨hproduct, hbit⟩

theorem multicastStayPositiveSet_eq_eligiblePrefix_filter
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (k : ℕ) (hactive : x.active i = true) (hheld : x.held i = x.target) :
    BootstrapTruePrefixController.eligiblePrefix x i k =
      (multicastStayPositiveSet x i).filter fun t => t.val < k := by
  classical
  ext t
  rw [BootstrapTruePrefixController.mem_eligiblePrefix_iff]
  simp only [multicastStayPositiveSet, Finset.mem_filter]
  constructor
  · rintro ⟨hcalendar, hlt, he⟩
    have hnotDiscover : (BootstrapPhysicalBlock.run x t.val).mode ≠ .discover := by
      intro hm
      exact eligible_not_discover x i t hactive hheld he hm
    have hmode : (BootstrapPhysicalBlock.run x t.val).mode = .multicast := by
      cases hm : (BootstrapPhysicalBlock.run x t.val).mode with
      | discover => exact (hnotDiscover hm).elim
      | multicast => rfl
    rcases he with ⟨_, _, hzero, hslot, hpositive⟩
    exact ⟨⟨hcalendar, hmode, hslot, hzero, hpositive⟩, hlt⟩
  · rintro ⟨⟨hcalendar, hmode, hslot, hzero, hpositive⟩, hlt⟩
    exact ⟨hcalendar, hlt,
      ⟨hcalendar, hactive, hzero, hslot, hpositive⟩⟩

theorem eligiblePrefix_eq_multicastStayPositiveSet
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (hactive : x.active i = true) (hheld : x.held i = x.target) :
    BootstrapTruePrefixController.eligiblePrefix x i p.T =
      multicastStayPositiveSet x i := by
  rw [multicastStayPositiveSet_eq_eligiblePrefix_filter x i p.T hactive hheld]
  ext t
  simp [multicastStayPositiveSet]

theorem multicastStayPositiveSet_true_forward_prefix
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (hactive : x.active i = true) (hheld : x.held i = x.target)
    (k : ℕ) (t : Fin p.T)
    (ht : t ∈ BootstrapTruePrefixController.eligiblePrefix x i k) :
    BootstrapTruePrefixController.trueForwardBit x i t = true := by
  have hset' : t ∈ (multicastStayPositiveSet x i).filter fun r => r.val < k := by
    rw [← multicastStayPositiveSet_eq_eligiblePrefix_filter x i k hactive hheld]
    exact ht
  rcases Finset.mem_filter.mp hset' with ⟨hmem, _⟩
  rcases Finset.mem_filter.mp hmem with ⟨_, hmode, hslot, hzero, hpositive⟩
  exact (multicast_positive_has_true_forward_bit x i t hactive hheld
    hmode hslot hzero hpositive).2

private theorem exists_eligible_at_quota
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (k : ℕ) (hk : k ≤ p.T) (hqpos : 0 < q_dec p)
    (hq : q_dec p ≤ (BootstrapTruePrefixController.eligiblePrefix x i k).card) :
    ∃ t : Fin p.T, t.val < k ∧ BootstrapTruePrefixController.eligible x i t ∧
      q_dec p ≤
        (BootstrapTruePrefixController.eligiblePrefix x i (t.val + 1)).card := by
  induction k with
  | zero =>
      simp [BootstrapTruePrefixController.eligiblePrefix] at hq
      omega
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      by_cases he : BootstrapTruePrefixController.eligible x i t
      · have hcard := BootstrapTruePrefixController.eligiblePrefix_card_succ x i t he
        have hcard' :
            (BootstrapTruePrefixController.eligiblePrefix x i (k + 1)).card =
              (BootstrapTruePrefixController.eligiblePrefix x i k).card + 1 := by
          simpa [t] using hcard
        by_cases hprev : q_dec p ≤
            (BootstrapTruePrefixController.eligiblePrefix x i k).card
        · obtain ⟨u, hu, hue, huq⟩ := ih (by omega) hprev
          exact ⟨u, by omega, hue, huq⟩
        · have hq' : q_dec p ≤
            (BootstrapTruePrefixController.eligiblePrefix x i k).card + 1 := by
            rw [← hcard']
            exact hq
          have heq : q_dec p =
              (BootstrapTruePrefixController.eligiblePrefix x i k).card + 1 := by
            omega
          have ht' : t.val < k + 1 := by simp [t]
          refine ⟨t, ht', he, ?_⟩
          rw [hcard']
          omega
      · have hprefix : BootstrapTruePrefixController.eligiblePrefix x i (k + 1) =
          BootstrapTruePrefixController.eligiblePrefix x i k := by
          have hflag : BootstrapTruePrefixController.eligibleFlag x i t = false := by
            simp [BootstrapTruePrefixController.eligibleFlag, he]
          have hs := BootstrapTruePrefixController.eligiblePrefix_succ x i t
          simpa [t, hflag] using hs
        obtain ⟨u, hu, hue, huq⟩ := ih (by omega) (by rw [← hprefix]; exact hq)
        exact ⟨u, by omega, hue, huq⟩

theorem physical_multicast_quota_has_real_passing_time
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (hactive : x.active i = true) (hheld : x.held i = x.target)
    (hquota : q_dec p ≤ (multicastStayPositiveSet x i).card) :
    ∃ t : Fin p.T, t.val < p.T ∧
      BootstrapTruePrefixController.passesAt x i t := by
  have hprefixCard : q_dec p ≤
      (BootstrapTruePrefixController.eligiblePrefix x i p.T).card := by
    rw [eligiblePrefix_eq_multicastStayPositiveSet x i hactive hheld]
    exact hquota
  obtain ⟨t, ht, he, hquotaAt⟩ := exists_eligible_at_quota x i p.T le_rfl
    (by
      have hL : 0 < L0 p := by
        unfold L0
        exact Nat.pow_pos (by decide)
      rw [q_dec]
      exact Nat.mul_pos (Nat.mul_pos (by decide) hL) (b_N_pos p)) hprefixCard
  have hall : BootstrapTruePrefixController.allTruePrefix x i (t.val + 1) := by
    intro r hr
    exact multicastStayPositiveSet_true_forward_prefix x i hactive hheld
      (t.val + 1) r hr
  exact ⟨t, ht, ⟨he, hquotaAt, hall⟩⟩

/-- The true controller includes the quota-round observation, freezes only its
pending registers, records the first save, and leaves the physical all-round
gain intact through the clipped block stop. -/
theorem physical_multicast_quota_acceptance
    (x : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ x.uninformed})
    (hactive : x.active i = true) (hheld : x.held i = x.target)
    (hquota : q_dec p ≤ (multicastStayPositiveSet x i).card) :
    (BootstrapTruePrefixController.run x i p.T).pending = true ∧
      (BootstrapTruePrefixController.observationTrace x i false).savedDeclaration s = true ∧
      BootstrapBlockConstruction.effectiveCalendarBlockGain
        (BootstrapTruePrefixController.observationTrace x i false) s =
          BootstrapPhysicalBlock.physicalStayGain x i ∧
      ∃ t : Fin p.T, t.val < p.T ∧
        BootstrapTruePrefixController.passesAt x i t ∧
        ∃ u : Fin p.T, u.val < p.T ∧
          BootstrapTruePrefixController.savedAt x i u = true ∧
          ¬ BootstrapTruePrefixController.hasPassingPrefix x i u.val ∧
          BootstrapTruePrefixController.passesAt x i u ∧
          ∀ v : Fin p.T, BootstrapTruePrefixController.savedAt x i v = true → v = u := by
  obtain ⟨t, ht, hpass⟩ :=
    physical_multicast_quota_has_real_passing_time x i hactive hheld hquota
  have hpending : (BootstrapTruePrefixController.run x i p.T).pending = true :=
    (BootstrapTruePrefixController.pending_iff_passingPrefix x i p.T le_rfl).mpr
      ⟨t, ht, hpass⟩
  have hsaved :
      (BootstrapTruePrefixController.observationTrace x i false).savedDeclaration s = true :=
    (BootstrapTruePrefixController.savedDeclaration_iff_pendingAtEnd x i).mpr hpending
  obtain ⟨u, hu, hsave⟩ := BootstrapTruePrefixController.exists_savedAt_of_pending
    x i p.T le_rfl hpending
  have hfirst := (BootstrapTruePrefixController.savedAt_iff_firstPassingPrefix x i u).mp hsave
  have hunique : ∀ v : Fin p.T,
      BootstrapTruePrefixController.savedAt x i v = true → v = u := by
    intro v hv
    exact BootstrapTruePrefixController.savedAt_unique x i hv hsave
  exact ⟨hpending, hsaved,
    BootstrapTruePrefixController.observationTrace_gain_eq_physicalStayGain x i false,
    t, ht, hpass, u, hu, hsave, hfirst.1, hfirst.2, hunique⟩

/-- The already integrated reference boundary consumes the true controller's
pending declaration after the full physical block update. Existing activations
are retained and a new declaration uses the exact next clipped-block round. -/
theorem reference_multicast_quota_boundary_activation
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (hactive : (ReferenceInitializationRun.physical x b h).active i = true)
    (hheld : (ReferenceInitializationRun.physical x b h).held i =
      (ReferenceInitializationRun.physical x b h).target)
    (hquota : q_dec p ≤ (multicastStayPositiveSet
      (ReferenceInitializationRun.physical x b h) i).card) :
    (ReferenceInitializationRun.candidate x b h i).pending = true ∧
      (ReferenceInitializationRun.finishBlock x b h).activation i.val =
        some (ReferenceInitializationRun.boundaryActivation b) ∧
      ReferenceInitializationRun.boundaryActivation b =
        BootstrapObservedFollower.nextActivationRound p
          (ReferenceInitializationRun.nextBlock b h) ∧
      ∀ j a, b.activation j = some a →
        (ReferenceInitializationRun.finishBlock x b h).activation j = some a := by
  let phys := ReferenceInitializationRun.physical x b h
  have hphysPending := physical_multicast_quota_acceptance phys i hactive hheld hquota
  have hpending : (ReferenceInitializationRun.candidate x b h i).pending = true := by
    simpa [ReferenceInitializationRun.candidate, phys] using hphysPending.1
  have hactivation := ReferenceInitializationRun.saved_activation x b h i hpending
  have hnext : ReferenceInitializationRun.boundaryActivation b =
      BootstrapObservedFollower.nextActivationRound p
        (ReferenceInitializationRun.nextBlock b h) := by
    apply Subtype.ext
    rw [ReferenceInitializationRun.boundaryActivation_timing b h]
    simp [BootstrapObservedFollower.nextActivationRound,
      BootstrapObservedFollower.blockStop]
  refine ⟨hpending, hactivation, hnext, ?_⟩
  intro j a hja
  exact ReferenceInitializationRun.activated_activation x b h j a hja

/-- On a processed generated reference opportunity, the finite real-valued
`multicastClock` sum over the original source coordinates is exactly the cast
of the literal physical MULTICAST DATA ID-zero positive count. -/
theorem generated_multicastClock_sum_eq_physical_count
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompletePublicTable.CompleteRow p)
    (scalarCompletion : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (focal : Follower p.m)
    (hprocessed : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (hincoming : focal ∈ ReferenceInitializationRun.uninformed
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)) :
    let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
    let b := ReferenceInitializationRun.run src s.val
    let hvalid : b.completed < n_boot p := by
      have hc := GeneratedBootstrapRoundLaw.processed_completed
        ids rewards C_star C_h eta s e hprocessed
      have hbc : b.completed = s.val := by simpa [src, b] using hc
      exact hbc ▸ s.isLt
    let phys := ReferenceInitializationRun.physical src b hvalid
    let i : {i // i ∈ phys.uninformed} := ⟨focal, by
      simpa [phys, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput] using hincoming⟩
    (∑ t : Fin p.T,
      GeneratedClockConditionalMeans.multicastClock ids rewards C_star C_h eta
        rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e) =
      ((multicastStayPositiveSet phys i).card : ℝ) := by
  let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run src s.val
  have hcompleted : b.completed = s.val := by
    exact GeneratedBootstrapRoundLaw.processed_completed
      ids rewards C_star C_h eta s e (by simpa [src] using hprocessed)
  have hvalid : b.completed < n_boot p := by
    rw [hcompleted]
    exact s.isLt
  let phys := ReferenceInitializationRun.physical src b hvalid
  have hincomingPhys : focal ∈ phys.uninformed := by
    simpa [phys, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput] using hincoming
  let i : {i // i ∈ phys.uninformed} := ⟨focal, hincomingPhys⟩
  have hnext : ReferenceInitializationRun.nextBlock b hvalid = s := by
    exact GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e
      (by simpa [src] using hprocessed) (by simpa [b] using hvalid)
  let profile := BootstrapPhysicalInput.currentBlockDrawProfile p
    (ReferenceInitializationRun.nextBlock b hvalid) b.numerators b.weight_ge_one src.coordinates
  let target := phys.target
  have hpoint : ∀ t : Fin p.T,
      GeneratedClockConditionalMeans.multicastClock ids rewards C_star C_h eta
        rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e =
        if t ∈ multicastStayPositiveSet phys i then (1 : ℝ) else 0 := by
    intro t
    by_cases ht : t ∈ calendarBlock p s
    · have hdesc : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta
          s t e = some (b, (profile,
            (target, BootstrapPhysicalBlock.run phys t.val))) := by
        simp [GeneratedBootstrapRoundLaw.descriptor,
          GeneratedBootstrapRoundLaw.descriptorAtBoundary, src, b, phys,
          profile, target, hprocessed, hvalid, hnext]
      have htest := GeneratedClockConditionalMeans.actual_multicastTest_eq_physical
        ids rewards C_star C_h eta rowCompletion scalarCompletion s t e focal b profile
        target (BootstrapPhysicalBlock.run phys t.val) hdesc hvalid
      have hsourcePhys : ReferenceInitializationRun.physical
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b hvalid = phys := rfl
      rw [GeneratedClockConditionalMeans.multicastClock_at_sourceIndex
        ids rewards C_star C_h eta rowCompletion scalarCompletion s t ht focal e]
      simp only [GeneratedBootstrapFiltration.testValue]
      rw [htest]
      let sx := GeneratedClockConditionalMeans.descriptorInput ids rewards rowCompletion
        scalarCompletion s (b, (profile,
          (target, BootstrapPhysicalBlock.run phys t.val)))
      let jx : {j // j ∈ sx.uninformed} := ⟨focal, by
        simpa [sx, GeneratedClockConditionalMeans.descriptorInput,
          ReferenceInitializationRun.uninformed] using hincoming⟩
      have hmemDesc : focal ∈ sx.uninformed := by
        simpa [sx, GeneratedClockConditionalMeans.descriptorInput,
          ReferenceInitializationRun.uninformed] using hincoming
      have hprivate : sx.privateId jx = phys.privateId i := by
        change ((profile (BootstrapPhysicalInput.sourceFollowerIndex p focal)).2).2 =
          ((BootstrapPhysicalInput.currentBlockDrawProfile p
            (ReferenceInitializationRun.nextBlock b hvalid) b.numerators
            b.weight_ge_one src.coordinates
            (BootstrapPhysicalInput.sourceFollowerIndex p focal)).2).2
        rfl
      have hids : sx.ids = phys.ids := by
        change ids = ids
        rfl
      have hpos :
          0 < (BootstrapPhysicalBlock.observationIndex phys
            (BootstrapPhysicalBlock.run phys t.val) t
            (followerPlayer p.two_le_m focal)).val ↔
            0 < BootstrapPhysicalBlock.feedback phys
              (BootstrapPhysicalBlock.run phys t.val) t
              (followerPlayer p.two_le_m focal) :=
        BootstrapPhysicalBlock.observationIndex_pos_iff phys
          (BootstrapPhysicalBlock.run phys t.val) t
          (followerPlayer p.two_le_m focal)
      rw [hsourcePhys]
      by_cases hobs : 0 < (BootstrapPhysicalBlock.observationIndex phys
          (BootstrapPhysicalBlock.run phys t.val) t
          (followerPlayer p.two_le_m focal)).val
      · have hobsFin : 0 < BootstrapPhysicalBlock.observationIndex phys
            (BootstrapPhysicalBlock.run phys t.val) t
            (followerPlayer p.two_le_m focal) := Fin.val_pos_iff.mpr hobs
        have hfeedback' := hpos.mp hobs
        simp [sx, jx, i, multicastStayPositiveSet, hmemDesc, hids, hprivate,
          hnext, ht, hobsFin, hfeedback']
      · have hfeedback' : ¬ 0 < BootstrapPhysicalBlock.feedback phys
            (BootstrapPhysicalBlock.run phys t.val) t
            (followerPlayer p.two_le_m focal) := by
          intro hfeedback
          exact hobs (hpos.mpr hfeedback)
        have hobsFin : ¬ 0 < BootstrapPhysicalBlock.observationIndex phys
            (BootstrapPhysicalBlock.run phys t.val) t
            (followerPlayer p.two_le_m focal) := by
          intro hpositive
          exact hobs (Fin.val_pos_iff.mp hpositive)
        simp [sx, jx, i, multicastStayPositiveSet, hmemDesc, hids, hprivate,
          hnext, ht, hobsFin, hfeedback']
    · simp [GeneratedClockConditionalMeans.multicastClock,
        GeneratedClockConditionalMeans.sourceClockIndex, t.isLt, ht,
        hnext, multicastStayPositiveSet]
  calc
    (∑ t : Fin p.T,
        GeneratedClockConditionalMeans.multicastClock ids rewards C_star C_h eta
          rowCompletion scalarCompletion s focal
          (GeneratedClockConditionalMeans.sourceClockIndex t) e) =
      ∑ t : Fin p.T, if t ∈ multicastStayPositiveSet phys i then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hpoint t
    _ = ((multicastStayPositiveSet phys i).card : ℝ) := by
      rw [Finset.sum_boole]
      have hfilter :
          (Finset.univ.filter fun t : Fin p.T =>
            t ∈ multicastStayPositiveSet phys i) = multicastStayPositiveSet phys i := by
        ext t
        simp
      rw [hfilter]

/-- A quota event for the actual generated-reference multicast clock is the
existing true-row test: it saves the candidate declaration, which the
reference boundary activates at the exact next clipped-block round. -/
theorem generated_multicast_quota_boundary_activation
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompletePublicTable.CompleteRow p)
    (scalarCompletion : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (focal : Follower p.m)
    (hprocessed : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (hincoming : focal ∈ ReferenceInitializationRun.uninformed
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)) :
    let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
    let b := ReferenceInitializationRun.run src s.val
    let hvalid : b.completed < n_boot p := by
      have hc := GeneratedBootstrapRoundLaw.processed_completed
        ids rewards C_star C_h eta s e hprocessed
      have hbc : b.completed = s.val := by simpa [src, b] using hc
      exact hbc ▸ s.isLt
    let phys := ReferenceInitializationRun.physical src b hvalid
    let i : {i // i ∈ phys.uninformed} := ⟨focal, by
      simpa [phys, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput] using hincoming⟩
    phys.active i = true → phys.held i = phys.target →
    q_dec p ≤
      ∑ t : Fin p.T, GeneratedClockConditionalMeans.multicastClock
        ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e →
    (ReferenceInitializationRun.candidate src b hvalid i).pending = true ∧
      (ReferenceInitializationRun.finishBlock src b hvalid).activation focal =
        some (BootstrapObservedFollower.nextActivationRound p
          (ReferenceInitializationRun.nextBlock b hvalid)) ∧
      ∀ j a, b.activation j = some a →
        (ReferenceInitializationRun.finishBlock src b hvalid).activation j = some a := by
  intro src b hvalid phys i hactive hheld hquotaClock
  have hclockCount := generated_multicastClock_sum_eq_physical_count
    ids rewards C_star C_h eta rowCompletion scalarCompletion s e focal
    hprocessed hincoming
  have hclockCount' :
      (∑ t : Fin p.T, GeneratedClockConditionalMeans.multicastClock
        ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e) =
      ((multicastStayPositiveSet phys i).card : ℝ) := by
    simpa [src, b, phys, i] using hclockCount
  have hquotaReal : (q_dec p : ℝ) ≤ (multicastStayPositiveSet phys i).card := by
    rw [← hclockCount']
    exact hquotaClock
  have hquota : q_dec p ≤ (multicastStayPositiveSet phys i).card := by
    exact_mod_cast hquotaReal
  have hboundary := reference_multicast_quota_boundary_activation
    src b hvalid i hactive hheld hquota
  have hactivation : (ReferenceInitializationRun.finishBlock src b hvalid).activation focal =
      some (BootstrapObservedFollower.nextActivationRound p
        (ReferenceInitializationRun.nextBlock b hvalid)) := by
    exact hboundary.2.1.trans (congrArg some hboundary.2.2.1)
  exact ⟨hboundary.1, hactivation, hboundary.2.2.2⟩

end Bandits.Support.BootstrapMulticastAcceptance

end
