/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapModeService
public import Bandits.Support.BootstrapPhysicalBlock
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Coordinator complement avoidance and physical DATA stay support

Sources: `sources/zip4/manuscript/07_public_setup.tex:76-94` and
`sources/zip4/manuscript/appendix_b_communication.tex:485-489`.

The private-coordinate statements use the existing second factor of
`BootstrapModeService.currentSnapshotMeasure` and its existing
`currentInputOf`. The physical stay indicator evaluates the existing
`BootstrapPhysicalBlock` actions and feedback; its original-input count remains
a subset of the existing all-slot `physicalStayGain`. This module proves no
snapshot mean or chronological block expectation.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapStayAvoidance

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPhysicalBlock BootstrapModeService PublicDiscreteDraws
open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The existing current-snapshot law factors through its existing public
coordinate law and private-coordinate law. This is the factorization consumed
by the fixed-public-coordinate avoidance bound below. -/
theorem currentSnapshotMeasure_eq_product_factors
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) :
    BootstrapModeService.currentSnapshotMeasure x t =
      (BootstrapModeService.roundCoordinatesMeasure p).prod
        (BootstrapModeService.roundPrivateMeasure x) := rfl

private theorem avoidArm_card (p : ConstructorDimensions.Parameters)
    (z : Arm p.K) : Fintype.card (BootstrapPhysicalBlock.AvoidArm p z) = p.K - 1 := by
  change Fintype.card {c : Fin p.K // c ≠ z} = p.K - 1
  rw [Fintype.card_subtype_compl (fun c : Fin p.K => c = z)]
  simp

/-- Exact mass of the genuine coordinator complement subtype that avoids a
second, distinct arm. The carrier is the existing `{c // c ≠ z}` value type. -/
theorem privateAvoidMeasure_complement_mass
    (p : ConstructorDimensions.Parameters) (z a : Arm p.K) (hza : z ≠ a) :
    (BootstrapModeService.privateAvoidMeasure p z).real
      {c : BootstrapPhysicalBlock.AvoidArm p z | c.val ≠ a} =
        ((p.K - 2 : ℕ) : ℝ) / ((p.K - 1 : ℕ) : ℝ) := by
  classical
  let az : BootstrapPhysicalBlock.AvoidArm p z := ⟨a, hza.symm⟩
  have hmem : az ∈ (Finset.univ : Finset (BootstrapPhysicalBlock.AvoidArm p z)) :=
    Finset.mem_univ az
  have hset :
      ({c : BootstrapPhysicalBlock.AvoidArm p z | c.val ≠ a} :
        Set (BootstrapPhysicalBlock.AvoidArm p z)) =
      ((Finset.univ.erase az : Finset (BootstrapPhysicalBlock.AvoidArm p z)) :
        Set (BootstrapPhysicalBlock.AvoidArm p z)) := by
    ext c
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · intro hc heq
      apply hc
      exact congrArg Subtype.val heq
    · intro hc hval
      apply hc
      apply Subtype.ext
      exact hval
  have hcardAvoid := avoidArm_card p z
  have hcardEvent :
      (Finset.univ.erase az : Finset (BootstrapPhysicalBlock.AvoidArm p z)).card =
        p.K - 2 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, hcardAvoid]
    omega
  rw [Measure.real, BootstrapModeService.privateAvoidMeasure, hset]
  rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset,
    hcardEvent, hcardAvoid]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- Since the constructor has `K > m ≥ 2`, the coordinator complement draw
avoids any fixed distinct held arm with probability at least one half. -/
theorem privateAvoidMeasure_complement_ge_half
    (p : ConstructorDimensions.Parameters) (z a : Arm p.K) (hza : z ≠ a) :
    (1 / 2 : ℝ) ≤
      (BootstrapModeService.privateAvoidMeasure p z).real
        {c : BootstrapPhysicalBlock.AvoidArm p z | c.val ≠ a} := by
  rw [privateAvoidMeasure_complement_mass p z a hza]
  have hKm : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
  have hK3 : 3 ≤ p.K := by
    have hm2 : 2 ≤ p.m := p.two_le_m
    have hmK : p.m < p.K := p.m_lt_K
    omega
  have hnum : p.K - 1 ≤ 2 * (p.K - 2) := by omega
  have hnum' : ((p.K - 1 : ℕ) : ℝ) ≤ 2 * ((p.K - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnum
  have hden : (0 : ℝ) < ((p.K - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.K - 1 by omega)
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem currentInputOf_slot (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) :
    BootstrapPhysicalBlock.slot (BootstrapModeService.currentInputOf x t r d) t =
      BootstrapModeService.roundSlot r := by
  simp [BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
    BootstrapPhysicalBlock.slot, BootstrapModeService.roundSlot,
    BootstrapModeService.roundSlice]

/-- In DATA DISCOVER, the actual coordinator action on the current input is
the fixed target. -/
theorem coordinatorAction_discover_current
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (hm : st.mode = .discover)
    (hdata : BootstrapModeService.roundSlot r = PublicDiscreteDraws.dataSlot) :
    BootstrapPhysicalBlock.actions (BootstrapModeService.currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m) = x.target := by
  have hslot := currentInputOf_slot x t r d
  rw [BootstrapPhysicalBlock.actions_coordinator,
    BootstrapPhysicalBlock.coordinatorAction_discover_data _ _ _ hm
      (hslot.trans hdata)]
  simp [BootstrapModeService.currentInputOf, BootstrapModeService.currentInput]

/-- In DATA MULTICAST, the actual coordinator action uses the existing full
`forwardProduct` test and, on release, the very complement value supplied in
the current private coordinate. -/
theorem coordinatorAction_multicast_current
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (hm : st.mode = .multicast)
    (hdata : BootstrapModeService.roundSlot r = PublicDiscreteDraws.dataSlot) :
    BootstrapPhysicalBlock.actions (BootstrapModeService.currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m) =
      if BootstrapPhysicalBlock.forwardProduct
          (BootstrapModeService.currentInputOf x t r d) st t = 1 then
        d.2.1.val else x.target := by
  have hslot := currentInputOf_slot x t r d
  rw [BootstrapPhysicalBlock.actions_coordinator,
    BootstrapPhysicalBlock.coordinatorAction_multicast_data _ _ _ hm
      (hslot.trans hdata)]
  simp [BootstrapModeService.currentInputOf, BootstrapModeService.currentInput]
  rfl

private theorem roundPrivateMeasure_coordinator_marginal
    (x : BootstrapPhysicalBlock.Input p s) (a : Arm p.K) :
    (BootstrapModeService.roundPrivateMeasure x).real
      {d : BootstrapModeService.RoundPrivateValues x | d.2.1.val ≠ a} =
    (BootstrapModeService.privateAvoidMeasure p x.target).real
      {c : BootstrapPhysicalBlock.AvoidArm p x.target | c.val ≠ a} := by
  have hset :
      ({d : BootstrapModeService.RoundPrivateValues x | d.2.1.val ≠ a} :
        Set (BootstrapModeService.RoundPrivateValues x)) =
      (Set.univ : Set (Player p.m → Arm p.K)) ×ˢ
        (({c : BootstrapPhysicalBlock.AvoidArm p x.target | c.val ≠ a} :
          Set (BootstrapPhysicalBlock.AvoidArm p x.target)) ×ˢ
          (Set.univ : Set
            ((j : {j // j ∈ x.uninformed}) →
              BootstrapPhysicalBlock.AvoidArm p (x.held j)))) := by
    ext d
    rcases d with ⟨uniformArms, coordinatorAvoid, followerAvoid⟩
    simp [Set.mem_prod]
  rw [BootstrapModeService.roundPrivateMeasure, hset]
  simp [Measure.real, Measure.prod_prod]

/-- For every fixed DATA public coordinate and every physical mode/list, the
existing private-coordinate factor of `currentSnapshotMeasure` gives at least
one-half probability that the coordinator avoids a distinct held arm. The
multicast release event remains the actual list-dependent `forwardProduct`. -/
theorem coordinatorAvoidance_probability_ge_half
    (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (a z : Arm p.K)
    (htarget : x.target = z) (hza : z ≠ a)
    (hdata : BootstrapModeService.roundSlot r = PublicDiscreteDraws.dataSlot) :
    (BootstrapModeService.roundPrivateMeasure x).real
      {d : BootstrapModeService.RoundPrivateValues x |
        BootstrapPhysicalBlock.actions
          (BootstrapModeService.currentInputOf x t r d) st t
          (ActiveRoundActions.coordinator p.two_le_m) ≠ a} ≥ 1 / 2 := by
  let releaseValue : ℕ :=
    ∏ u ∈ st.list, if r.1 u = true then 1 else 0
  have hforward (d : BootstrapModeService.RoundPrivateValues x) :
      BootstrapPhysicalBlock.forwardProduct
          (BootstrapModeService.currentInputOf x t r d) st t = releaseValue := by
    simp [releaseValue, BootstrapPhysicalBlock.forwardProduct,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput]
  cases hm : st.mode with
  | discover =>
      have hset :
          ({d : BootstrapModeService.RoundPrivateValues x |
              BootstrapPhysicalBlock.actions
                (BootstrapModeService.currentInputOf x t r d) st t
                (ActiveRoundActions.coordinator p.two_le_m) ≠ a} :
            Set (BootstrapModeService.RoundPrivateValues x)) = Set.univ := by
        ext d
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rw [coordinatorAction_discover_current x st t r d hm hdata, htarget]
        exact hza
      rw [hset]
      simp [Measure.real]
      norm_num
  | multicast =>
      by_cases hrelease : releaseValue = 1
      · have hset :
            ({d : BootstrapModeService.RoundPrivateValues x |
                BootstrapPhysicalBlock.actions
                  (BootstrapModeService.currentInputOf x t r d) st t
                  (ActiveRoundActions.coordinator p.two_le_m) ≠ a} :
              Set (BootstrapModeService.RoundPrivateValues x)) =
            {d : BootstrapModeService.RoundPrivateValues x | d.2.1.val ≠ a} := by
          ext d
          simp only [Set.mem_ofPred_eq]
          rw [coordinatorAction_multicast_current x st t r d hm hdata,
            hforward d]
          simp [hrelease]
        rw [hset, roundPrivateMeasure_coordinator_marginal]
        rw [htarget]
        exact privateAvoidMeasure_complement_ge_half p z a hza
      · have hset :
            ({d : BootstrapModeService.RoundPrivateValues x |
                BootstrapPhysicalBlock.actions
                  (BootstrapModeService.currentInputOf x t r d) st t
                  (ActiveRoundActions.coordinator p.two_le_m) ≠ a} :
              Set (BootstrapModeService.RoundPrivateValues x)) = Set.univ := by
          ext d
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          rw [coordinatorAction_multicast_current x st t r d hm hdata,
            hforward d]
          simp [hrelease, htarget, hza]
        rw [hset]
        simp [Measure.real]
        norm_num

/-- Literal source DATA-stay-positive indicator, evaluated using the existing
physical follower feedback on `currentInputOf`. Inactive, ID-one, non-DATA, and
zero-feedback rounds all contribute zero. -/
def dataStayPositive
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) : ℝ :=
  if x.active j = true ∧ x.ids (x.privateId j) t = false ∧
      BootstrapPhysicalBlock.slot (BootstrapModeService.currentInputOf x t r d) t =
        PublicDiscreteDraws.dataSlot ∧
      0 < BootstrapPhysicalBlock.feedback
        (BootstrapModeService.currentInputOf x t r d) st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)
  then 1 else 0

private theorem chi_eq_one_iff_reward_pos
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) (a : Arm p.K) :
    BootstrapModeService.chi x t a = 1 ↔ 0 < (x.rewards t a).val := by
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards t a) ↔
        0 < (x.rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
    exact_mod_cast (Iff.rfl :
      0 < (x.rewards t a).val ↔ 0 < (x.rewards t a).val)
  simp [BootstrapModeService.chi, hpos]

private theorem dataStayPositive_feedback_characterization
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (a : Arm p.K) (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = false) (hheld : x.held j = a) :
    (0 < BootstrapPhysicalBlock.feedback
      (BootstrapModeService.currentInputOf x t r d) st t
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)) ↔
      BootstrapModeService.chi x t a = 1 ∧
        FiniteBanditModel.collisionFreeFor
          (BootstrapPhysicalBlock.actions
            (BootstrapModeService.currentInputOf x t r d) st t)
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) := by
  let y := BootstrapModeService.currentInputOf x t r d
  let i := PublicDiscreteDraws.followerPlayer p.two_le_m j.val
  have hact : BootstrapPhysicalBlock.actions y st t i = a := by
    rw [BootstrapModeService.distinguishedFollower_IDzero_action
      x st t j r d hactive hid, hheld]
  have hreward : y.rewards t a = x.rewards t a := by
    simp [y, BootstrapModeService.currentInputOf,
      BootstrapModeService.currentInput]
  have hchi : BootstrapModeService.chi x t a = 1 ↔ 0 < (y.rewards t a).val := by
    rw [chi_eq_one_iff_reward_pos, hreward]
  have hobs :
      0 < (BootstrapPhysicalBlock.observationIndex y st t i).val ↔
        BootstrapModeService.chi x t a = 1 ∧
          FiniteBanditModel.collisionFreeFor
            (BootstrapPhysicalBlock.actions y st t) i := by
    rw [BootstrapPhysicalBlock.observationIndex, hact]
    by_cases hfree : FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y st t) i
    · simp [hfree, hchi]
    · simp [hfree]
  rw [← BootstrapPhysicalBlock.observationIndex_pos_iff]
  exact hobs

private theorem coordinatorAvoidance_condition_iff
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (a z : Arm p.K) (htarget : x.target = z) (hza : z ≠ a)
    (hdata : BootstrapModeService.roundSlot r = PublicDiscreteDraws.dataSlot) :
    BootstrapPhysicalBlock.actions
        (BootstrapModeService.currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m) ≠ a ↔
      st.mode = .discover ∨
        (st.mode = .multicast ∧
          (BootstrapPhysicalBlock.forwardProduct
              (BootstrapModeService.currentInputOf x t r d) st t ≠ 1 ∨
            (BootstrapPhysicalBlock.forwardProduct
                (BootstrapModeService.currentInputOf x t r d) st t = 1 ∧
              ((BootstrapModeService.currentInputOf x t r d).coordinatorAvoid t).val ≠ a))) := by
  cases hm : st.mode with
  | discover =>
      rw [coordinatorAction_discover_current x st t r d hm hdata, htarget]
      simp [hza]
  | multicast =>
      rw [coordinatorAction_multicast_current x st t r d hm hdata]
      split_ifs with hrelease
      · constructor
        · intro havoid
          right
          exact ⟨rfl, Or.inr ⟨hrelease, by
            simpa [BootstrapModeService.currentInputOf,
              BootstrapModeService.currentInput] using havoid⟩⟩
        · rintro (hdiscover | ⟨_, hcondition⟩)
          · cases hdiscover
          · rcases hcondition with hnotrelease | ⟨_, havoid⟩
            · exact False.elim (hnotrelease hrelease)
            · simpa [BootstrapModeService.currentInputOf,
                BootstrapModeService.currentInput] using havoid
      · constructor
        · intro _
          right
          exact ⟨rfl, Or.inl hrelease⟩
        · intro _
          simpa [htarget] using hza

private theorem followerCollisionFree_iff_coordinator_and_others
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (a : Arm p.K) (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = false) (hheld : x.held j = a) :
    FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions
          (BootstrapModeService.currentInputOf x t r d) st t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) ↔
      BootstrapPhysicalBlock.actions
          (BootstrapModeService.currentInputOf x t r d) st t
          (ActiveRoundActions.coordinator p.two_le_m) ≠ a ∧
        (∀ q : Player p.m,
          q ≠ ActiveRoundActions.coordinator p.two_le_m →
          q ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.val →
          BootstrapPhysicalBlock.actions
              (BootstrapModeService.currentInputOf x t r d) st t q ≠ a) := by
  let y := BootstrapModeService.currentInputOf x t r d
  let i := PublicDiscreteDraws.followerPlayer p.two_le_m j.val
  have hact : BootstrapPhysicalBlock.actions y st t i = a := by
    rw [BootstrapModeService.distinguishedFollower_IDzero_action
      x st t j r d hactive hid, hheld]
  have hne : ActiveRoundActions.coordinator p.two_le_m ≠ i :=
    (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.val).symm
  constructor
  · intro hfree
    constructor
    · intro hcoord
      apply hfree (ActiveRoundActions.coordinator p.two_le_m) hne
      calc
        BootstrapPhysicalBlock.actions y st t (ActiveRoundActions.coordinator p.two_le_m) =
            a := hcoord
        _ = BootstrapPhysicalBlock.actions y st t i := hact.symm
    · intro q hcoord hfollow heq
      apply hfree q hfollow
      calc
        BootstrapPhysicalBlock.actions y st t q = a := heq
        _ = BootstrapPhysicalBlock.actions y st t i := hact.symm
  · rintro ⟨hcoord, hother⟩ q hq
    by_cases hqcoord : q = ActiveRoundActions.coordinator p.two_le_m
    · subst q
      intro heq
      apply hcoord
      calc
        BootstrapPhysicalBlock.actions y st t (ActiveRoundActions.coordinator p.two_le_m) =
            BootstrapPhysicalBlock.actions y st t i := heq
        _ = a := hact
    · have hqfollow : q ≠ i := by
        intro hqfollow
        subst q
        exact hq (by simp [i])
      have hnot := hother q hqcoord hqfollow
      intro heq
      apply hnot
      calc
        BootstrapPhysicalBlock.actions y st t q =
            BootstrapPhysicalBlock.actions y st t i := heq
        _ = a := hact

/-- At the actual physical follower action, the indicator is exactly positive
rounded reward support, DATA and ID-zero, plus coordinator and every other
actual player's avoidance of the held arm. DISCOVER and both MULTICAST release
branches are displayed explicitly. -/
theorem dataStayPositive_eq_one_iff
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (a z : Arm p.K) (htarget : x.target = z) (hheld : x.held j = a)
    (hza : z ≠ a)
    (hdata : BootstrapModeService.roundSlot r = PublicDiscreteDraws.dataSlot) :
    dataStayPositive x st t j r d = 1 ↔
      x.active j = true ∧ x.ids (x.privateId j) t = false ∧
        BootstrapModeService.chi x t a = 1 ∧
        BootstrapPhysicalBlock.slot
            (BootstrapModeService.currentInputOf x t r d) t =
          PublicDiscreteDraws.dataSlot ∧
        (st.mode = .discover ∨
          (st.mode = .multicast ∧
            (BootstrapPhysicalBlock.forwardProduct
                (BootstrapModeService.currentInputOf x t r d) st t ≠ 1 ∨
              (BootstrapPhysicalBlock.forwardProduct
                  (BootstrapModeService.currentInputOf x t r d) st t = 1 ∧
                ((BootstrapModeService.currentInputOf x t r d).coordinatorAvoid t).val ≠ a)))) ∧
        (∀ q : Player p.m,
          q ≠ ActiveRoundActions.coordinator p.two_le_m →
          q ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.val →
          BootstrapPhysicalBlock.actions
              (BootstrapModeService.currentInputOf x t r d) st t q ≠ a) := by
  let y := BootstrapModeService.currentInputOf x t r d
  let i := PublicDiscreteDraws.followerPlayer p.two_le_m j.val
  have hconditions_from_indicator :
      dataStayPositive x st t j r d = 1 →
        x.active j = true ∧ x.ids (x.privateId j) t = false ∧
          BootstrapPhysicalBlock.slot y t = PublicDiscreteDraws.dataSlot ∧
          0 < BootstrapPhysicalBlock.feedback y st t i := by
    intro h
    unfold dataStayPositive at h
    split_ifs at h with hc
    · exact hc
    · norm_num at h
  have havoid := coordinatorAvoidance_condition_iff
    x st t r d a z htarget hza hdata
  constructor
  · intro hindicator
    have hc := hconditions_from_indicator hindicator
    have hfeed := dataStayPositive_feedback_characterization
      x st t j r d a hc.1 hc.2.1 hheld
    have hsupport := hfeed.mp hc.2.2.2
    have hcollision := followerCollisionFree_iff_coordinator_and_others
      x st t j r d a hc.1 hc.2.1 hheld
    have hfree := hcollision.mp hsupport.2
    refine ⟨hc.1, hc.2.1, hsupport.1, hc.2.2.1, ?_, ?_⟩
    · exact havoid.mp hfree.1
    · intro q hcoord hfollow
      have hq := hfree.2 q hcoord
      exact hq (by simpa [y, i] using hfollow)
  · rintro ⟨hactive, hid, hsupport, hslot, hcoordMode, hother⟩
    have hcoord :
        BootstrapPhysicalBlock.actions y st t
          (ActiveRoundActions.coordinator p.two_le_m) ≠ a :=
      havoid.mpr hcoordMode
    have hcollision := followerCollisionFree_iff_coordinator_and_others
      x st t j r d a hactive hid hheld
    have hcollision' := hcollision.mpr ⟨hcoord, by
      intro q hcoord' hfollow
      exact hother q hcoord' (by simpa [y, i] using hfollow)⟩
    have hfeedback := (dataStayPositive_feedback_characterization
      x st t j r d a hactive hid hheld).mpr ⟨hsupport, hcollision'⟩
    unfold dataStayPositive
    simp [hactive, hid, hslot, hfeedback]

/-- ID-one cannot be recorded as a DATA stay-positive event, regardless of
the actions or rewards elsewhere in the round. -/
theorem dataStayPositive_eq_zero_of_IDone
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (hid : x.ids (x.privateId j) t = true) :
    dataStayPositive x st t j r d = 0 := by
  simp [dataStayPositive, hid]

/-- Zero reward at the held arm gives zero DATA stay-positive indicator on an
active ID-zero follower's actual held-arm action. -/
theorem dataStayPositive_eq_zero_of_zero_held_reward
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x)
    (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = false)
    (hzero : x.rewards t (x.held j) = 0) :
    dataStayPositive x st t j r d = 0 := by
  let y := BootstrapModeService.currentInputOf x t r d
  let i := PublicDiscreteDraws.followerPlayer p.two_le_m j.val
  have hact : BootstrapPhysicalBlock.actions y st t i = x.held j :=
    BootstrapModeService.distinguishedFollower_IDzero_action x st t j r d hactive hid
  have hfeedback : ¬ 0 < BootstrapPhysicalBlock.feedback y st t i := by
    rw [← BootstrapPhysicalBlock.observationIndex_pos_iff,
      BootstrapPhysicalBlock.observationIndex, hact]
    by_cases hfree : FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y st t) i
    · have hreward : y.rewards t (x.held j) = 0 := by
        simpa [y, BootstrapModeService.currentInputOf,
          BootstrapModeService.currentInput] using hzero
      simp [hfree, hreward]
    · simp [hfree]
  have hfeedback' :
      ¬ 0 < BootstrapPhysicalBlock.feedback
        (BootstrapModeService.currentInputOf x t r d) st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) := by
    simpa [y, i] using hfeedback
  simp only [dataStayPositive, hactive, hid, true_and]
  split_ifs with h
  · exact False.elim (hfeedback' h.2)
  · rfl

private theorem currentInputOf_original
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) :
    BootstrapModeService.currentInputOf x t
        (BootstrapModeService.roundCoordinates p t x.row)
        ((fun i => x.uniform i t),
          (x.coordinatorAvoid t, fun j => x.followerAvoid j t)) = x := by
  cases x with
  | mk uninformed active held privateId ids row target uniform coordinatorAvoid followerAvoid rewards =>
      have hrow₁ :
          (fun u q => if q = t then row.1 u t else row.1 u q) = row.1 := by
        funext u q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hrow₂ :
          (fun q => if q = t then row.2 t else row.2 q) = row.2 := by
        funext q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have huniform :
          (fun i q => if q = t then uniform i t else uniform i q) = uniform := by
        funext i q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hcoord :
          (fun q => if q = t then coordinatorAvoid t else coordinatorAvoid q) =
            coordinatorAvoid := by
        funext q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hfollower :
          (fun j q => if q = t then followerAvoid j t else followerAvoid j q) =
            followerAvoid := by
        funext j q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      simp [BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
        BootstrapModeService.roundCoordinates, hrow₁, hrow₂, huniform, hcoord, hfollower]

/-- On the original input and recursive pre-round state, the counted DATA
stay-positive rounds form a subset of the existing all-slot physical stay
rounds. The physical gain itself is not truncated to DATA or to a declaration
cutoff. -/
theorem dataStayPositive_count_le_physicalStayGain
    (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (hactive : x.active j = true) :
    ((BootstrapDimensions.calendarBlock p s).filter fun t =>
      dataStayPositive x (BootstrapPhysicalBlock.run x t.val) t j
        (BootstrapModeService.roundCoordinates p t x.row)
        ((fun i => x.uniform i t),
          (x.coordinatorAvoid t, fun k => x.followerAvoid k t)) = 1).card ≤
      BootstrapPhysicalBlock.physicalStayGain x j := by
  simp only [BootstrapPhysicalBlock.physicalStayGain, hactive, ↓reduceIte]
  apply Finset.card_le_card
  intro t ht
  have htcal : t ∈ BootstrapDimensions.calendarBlock p s :=
    (Finset.mem_filter.mp ht).1
  have hindicator := (Finset.mem_filter.mp ht).2
  have hconditions :
      x.active j = true ∧ x.ids (x.privateId j) t = false ∧
        BootstrapPhysicalBlock.slot
            (BootstrapModeService.currentInputOf x t
              (BootstrapModeService.roundCoordinates p t x.row)
              ((fun i => x.uniform i t),
                (x.coordinatorAvoid t, fun k => x.followerAvoid k t))) t =
          PublicDiscreteDraws.dataSlot ∧
        0 < BootstrapPhysicalBlock.feedback
          (BootstrapModeService.currentInputOf x t
            (BootstrapModeService.roundCoordinates p t x.row)
            ((fun i => x.uniform i t),
              (x.coordinatorAvoid t, fun k => x.followerAvoid k t)))
          (BootstrapPhysicalBlock.run x t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) := by
    unfold dataStayPositive at hindicator
    split_ifs at hindicator with hc
    · exact hc
    · norm_num at hindicator
  have hcurrent := currentInputOf_original x t
  rw [BootstrapPhysicalBlock.physicalStayRounds, Finset.mem_filter]
  refine ⟨htcal, hconditions.2.1, ?_⟩
  simpa only [hcurrent] using hconditions.2.2.2

end Bandits.Support.BootstrapStayAvoidance

end
