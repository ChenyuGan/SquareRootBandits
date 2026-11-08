/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveObservationBridge
public import Bandits.Support.CanonicalFastSampling
public import Bandits.Support.ConstructorDimensions

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-round release kernel and sentinel cost

This module constructs the release round from the actual continuous control
slice, the accepted ordered tuple sampler, and the canonical fast-arm scalar.
Its source is `sources/zip4/manuscript/05_binary_transport.tex:128-153,291-325`
and `sources/zip4/manuscript/04_slow_fast_learner.tex:105-114`. It proves fixed,
one-round event masses and a deterministic pathwise inequality. It makes no
claim about histories, stopping times, or adaptive conditional laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReleaseRoundKernel

open Bandits.Support.ActiveObservationBridge
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.FiniteBanditModel
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PublicDiscreteDraws

/-- The set of arms physically assigned to the followers.

Source: `sources/zip4/manuscript/05_binary_transport.tex:293-325`. -/
def assignedImage {m K : ℕ}
    (a : Assignment m K) : Finset (Arm K) :=
  Finset.univ.image a.assigned

/-- The source indicator `χ_t(j) = 1{r_t(j) > 0}`.

Source: `sources/zip4/manuscript/05_binary_transport.tex:291`. -/
def chi {K : ℕ} (row : RewardRow K) (j : Arm K) : ℝ :=
  if 0 < row.val j then 1 else 0

/-- Reward on the assigned slow set, with its literal finite-set carrier. -/
def slowReward {K m : ℕ} (row : RewardRow K)
    (U : SlowSet K m) : ℝ :=
  ∑ j ∈ U.val, row.val j

/-- Total physical feedback in a deterministic round. -/
noncomputable def physicalFeedbackTotal {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) : ℝ :=
  feedback hm s r row (coordinator hm) +
    ∑ j : Follower m, feedback hm s r row (followerPlayer hm j)

/-- A width-zero hash word used only to fill the unused DOWN and UP fields in
the release slice realization. With every follower occupied, these fields are
never inspected by the action rules. -/
def inertHashWord : HashedWord 0 :=
  ⟨(fun i => Fin.elim0 i, 0), fun i => Fin.elim0 i⟩

/-- The auxiliary arm as an element of the genuine complement of `U`. -/
def auxiliaryFastArm {p : Parameters} (a : Assignment p.m p.K)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a) : FastArm U := by
  have hnot : a.auxiliary ∉ U.val := by
    intro hmem
    rw [hU, assignedImage] at hmem
    rcases Finset.mem_image.mp hmem with ⟨j, _hj, heq⟩
    exact a.auxiliary_outside j heq.symm
  exact ⟨a.auxiliary, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩⟩

/-- The source round input realized on one accepted continuous slice.

The public slot, follower, pilot, tuple, and fast variables are the literal
accepted maps. The fast arm uses the independent `fast` scalar label. -/
def releaseRoundInput (p : Parameters)
    (a : Assignment p.m p.K) (U : SlowSet p.K p.m)
    (hU : U.val = assignedImage a) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (x : Slice p.m p.K) : RoundInput a 0 := by
  let f := sampleFast p eta heta heta_le v w hv hw hvw hwv U
    (coordinate Label.fast x)
  refine ⟨slotDraw x, selectedFollowerDraw p.two_le_m p.m_lt_K x,
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K x,
    (fun q => pilotDraw (K_pos p) q x), inertHashWord, inertHashWord,
    f.1, ?_⟩
  intro j hfast
  have hnot : f.1 ∉ U.val := (Finset.mem_sdiff.mp f.2).2
  have hj : a.assigned j ∈ U.val := by
    rw [hU, assignedImage]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  exact hnot (by rw [hfast]; exact hj)

private theorem chi_nonneg {K : ℕ} (row : RewardRow K) (j : Arm K) :
    0 ≤ chi row j := by
  by_cases h : 0 < row.val j <;> simp [chi, h]

private theorem reward_le_chi {K : ℕ} (row : RewardRow K) (j : Arm K) :
    row.val j ≤ chi row j := by
  by_cases h : 0 < row.val j
  · simp only [chi, ite_eq_left h]
    exact (row.property j).2
  · have hz : row.val j = 0 := by
      have hnonneg := (row.property j).1
      exact le_antisymm (le_of_not_gt h) hnonneg
    simp [chi, hz]

private theorem followerAction_assigned_or_aux {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m)
    (hj : s.status j = .pending ∨ s.status j = .released) :
    followerAction hm s r j = a.assigned j ∨
      followerAction hm s r j = a.auxiliary := by
  cases hs : s.status j with
  | unoccupied =>
      rcases hj with hp | hr
      · rw [hs] at hp
        cases hp
      · rw [hs] at hr
        cases hr
  | pending =>
      have hnot : s.status j ≠ .unoccupied := by rw [hs]; decide
      unfold followerAction
      simp only [ite_eq_right hnot]
      split_ifs <;> (first | exact Or.inl rfl | exact Or.inr rfl)
  | released =>
      exact Or.inl (followerAction_released hm s r j hs)

private theorem released_feedback_eq_assigned {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (j : Follower m) (hj : s.status j = .released) :
    feedback hm s r row (followerPlayer hm j) = row.val (a.assigned j) := by
  have hfree : collisionFreeFor (actions hm s r) (followerPlayer hm j) := by
    intro q hq hsame
    rcases player_cases hm q with hcoord | ⟨k, hk⟩
    · rw [hcoord, actions_coordinator, coordinatorAction_fast hm s r hmissing] at hsame
      have hjAction : actions hm s r (followerPlayer hm j) = a.assigned j := by
        rw [actions_follower, followerAction_released hm s r j hj]
      rw [hjAction] at hsame
      exact r.fast_outside j hsame
    · have hkj : k ≠ j := by
        intro hkj
        subst k
        exact hq hk
      rw [hk, actions_follower] at hsame
      have hjAction : actions hm s r (followerPlayer hm j) = a.assigned j := by
        rw [actions_follower, followerAction_released hm s r j hj]
      rw [hjAction] at hsame
      rcases followerAction_assigned_or_aux hm s r k (hstatus k) with hka | hke
      · rw [hka] at hsame
        exact assigned_ne k j hkj hsame
      · rw [hke] at hsame
        exact a.auxiliary_outside j hsame
  rw [feedback_eq_reward_of_collision_free hm s r row _ hfree,
    actions_follower, followerAction_released hm s r j hj]

private theorem follower_feedback_loss_le {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (j : Follower m) :
    row.val (a.assigned j) -
        feedback hm s r row (followerPlayer hm j) ≤
      if s.status j = .pending then chi row (a.assigned j) else 0 := by
  rcases hstatus j with hp | hr
  · have hfb := (feedback_mem_Icc hm s r row (followerPlayer hm j)).1
    have hbase := reward_le_chi row (a.assigned j)
    have hbound : row.val (a.assigned j) -
        feedback hm s r row (followerPlayer hm j) ≤ chi row (a.assigned j) := by
      linarith
    simpa [hp] using hbound
  · rw [released_feedback_eq_assigned hm s r row hmissing hstatus j hr]
    simp [hr]

private theorem coordinator_feedback_loss_le {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released) :
    row.val r.fast - feedback hm s r row (coordinator hm) ≤
      if r.fast = a.auxiliary ∧ ∃ j, s.status j = .pending then
        row.val a.auxiliary else 0 := by
  classical
  by_cases hfree : collisionFreeFor (actions hm s r) (coordinator hm)
  · rw [feedback_eq_reward_of_collision_free hm s r row _ hfree,
      actions_coordinator, coordinatorAction_fast hm s r hmissing]
    by_cases hcond : r.fast = a.auxiliary ∧ ∃ j, s.status j = .pending
    · simp [hcond]
      exact (row.property a.auxiliary).1
    · simp [hcond]
  · have hex : ∃ q, q ≠ coordinator hm ∧
        actions hm s r q = actions hm s r (coordinator hm) := by
      by_contra h
      apply hfree
      intro q hq hsame
      exact h ⟨q, hq, hsame⟩
    rcases hex with ⟨q, hq, hsame⟩
    rcases player_cases hm q with hcoord | ⟨j, hj⟩
    · exact (hq hcoord).elim
    · have hjstatus := hstatus j
      have hsameActions := hsame
      rw [hj, actions_follower] at hsame
      rw [actions_coordinator, coordinatorAction_fast hm s r hmissing] at hsame
      rcases hjstatus with hp | hr
      · rcases followerAction_assigned_or_aux hm s r j (Or.inl hp) with hja | hje
        · rw [hja] at hsame
          exact (r.fast_outside j hsame.symm).elim
        · rw [hje] at hsame
          have hcond : r.fast = a.auxiliary ∧ ∃ k, s.status k = .pending :=
            ⟨hsame.symm, ⟨j, hp⟩⟩
          have hzero := feedback_eq_zero_of_collision hm s r row
            (coordinator hm) q hq hsameActions
          rw [hzero]
          simp [hcond]
      · rw [followerAction_released hm s r j hr] at hsame
        exact (r.fast_outside j hsame.symm).elim

/-- Deterministic one-round sentinel inequality for every occupied snapshot
and corresponding `RoundInput`.

Source: `sources/zip4/manuscript/05_binary_transport.tex:318-325`. -/
theorem pathwise_sentinel_cost_bound {m K B : ℕ}
    (hm : 2 ≤ m) (a : Assignment m K) (U : SlowSet K m)
    (hU : U.val = assignedImage a) (s : Snapshot a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (r : RoundInput a B) (row : RewardRow K) :
    slowReward row U + row.val r.fast - physicalFeedbackTotal hm s r row ≤
      (∑ j : Follower m,
        if s.status j = .pending then chi row (a.assigned j) else 0) +
      (if r.fast = a.auxiliary ∧ ∃ j, s.status j = .pending then
        row.val a.auxiliary else 0) := by
  classical
  have hsetsum :
      (∑ j : Follower m, row.val (a.assigned j)) = slowReward row U := by
    rw [slowReward, hU, assignedImage]
    exact (Finset.sum_image (fun i _ j _ hij => a.injective hij)).symm
  have hfollowers :
      (∑ j : Follower m,
        (row.val (a.assigned j) -
          feedback hm s r row (followerPlayer hm j))) ≤
        ∑ j : Follower m,
          if s.status j = .pending then chi row (a.assigned j) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    exact follower_feedback_loss_le hm s r row hmissing hstatus j
  have hcoord := coordinator_feedback_loss_le hm s r row hmissing hstatus
  rw [← hsetsum]
  change (∑ j : Follower m, row.val (a.assigned j)) + row.val r.fast -
      (feedback hm s r row (coordinator hm) +
        ∑ j : Follower m, feedback hm s r row (followerPlayer hm j)) ≤ _
  calc
    _ = ((∑ j : Follower m, row.val (a.assigned j)) -
          ∑ j : Follower m, feedback hm s r row (followerPlayer hm j)) +
          (row.val r.fast - feedback hm s r row (coordinator hm)) := by ring
    _ = (∑ j : Follower m,
          (row.val (a.assigned j) -
            feedback hm s r row (followerPlayer hm j))) +
          (row.val r.fast - feedback hm s r row (coordinator hm)) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ _ := add_le_add hfollowers hcoord

/-- The coordinate labels used by the UP release event. -/
private def upCoordinateLabel (p : Parameters) : Fin 4 → Label p.m p.K
  | 0 => Label.slot
  | 1 => Label.sel
  | 2 => Label.tuple ⟨0, lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m⟩
  | 3 => Label.fast

/-- The coordinate labels used by the DATA release event. -/
private def dataCoordinateLabel (p : Parameters) : Fin 2 → Label p.m p.K
  | 0 => Label.slot
  | 1 => Label.pilot ⟨0, lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m⟩

private theorem upCoordinateLabel_injective (p : Parameters) :
    Function.Injective (upCoordinateLabel p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [upCoordinateLabel, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.sel, ContinuousControlSlice.Label.tuple,
      ContinuousControlSlice.Label.fast] at hij ⊢

private theorem dataCoordinateLabel_injective (p : Parameters) :
    Function.Injective (dataCoordinateLabel p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [dataCoordinateLabel, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.pilot] at hij ⊢

/-- The UP variables are read from their five distinct source labels. The
tuple coordinate here is exactly the first coordinate of the accepted tuple
map; later coordinates remain part of that map but do not affect its first
arm. -/
private def upCoordinates (p : Parameters) (x : Slice p.m p.K) : Fin 4 → Scalar :=
  fun i => coordinate (upCoordinateLabel p i) x

/-- The DATA variables are read from the distinct slot and coordinator-pilot
labels of the same product slice. -/
private def dataCoordinates (p : Parameters) (x : Slice p.m p.K) : Fin 2 → Scalar :=
  fun i => coordinate (dataCoordinateLabel p i) x

private theorem map_labelCoordinates {m K : ℕ} {ι : Type*} [Fintype ι]
    (label : ι → Label m K) (hinj : Function.Injective label) :
    (ContinuousControlSlice.sliceLaw m K).map
        (fun x i => coordinate (label i) x) =
      Measure.pi (fun _ : ι => ContinuousControlSlice.scalarLaw) := by
  have hind := (ContinuousControlSlice.iIndepFun_coordinate m K).precomp
    (g := label) hinj
  have hmap := hind.map_fun_eq_pi_map
    (fun i => (ContinuousControlSlice.measurable_coordinate (label i)).aemeasurable)
  change (ContinuousControlSlice.sliceLaw m K).map
      (fun x i => coordinate (label i) x) =
    Measure.pi (fun i : ι =>
      (ContinuousControlSlice.sliceLaw m K).map (coordinate (label i))) at hmap
  simpa only [ContinuousControlSlice.map_coordinate] using hmap

private theorem map_upCoordinates (p : Parameters) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map (upCoordinates p) =
      Measure.pi (fun _ : Fin 4 => ContinuousControlSlice.scalarLaw) := by
  exact map_labelCoordinates (upCoordinateLabel p) (upCoordinateLabel_injective p)

private theorem map_dataCoordinates (p : Parameters) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map (dataCoordinates p) =
      Measure.pi (fun _ : Fin 2 => ContinuousControlSlice.scalarLaw) := by
  exact map_labelCoordinates (dataCoordinateLabel p) (dataCoordinateLabel_injective p)

private theorem measurable_upCoordinates (p : Parameters) : Measurable (upCoordinates p) :=
  measurable_pi_iff.mpr (fun i =>
    ContinuousControlSlice.measurable_coordinate (upCoordinateLabel p i))

private theorem measurable_dataCoordinates (p : Parameters) : Measurable (dataCoordinates p) :=
  measurable_pi_iff.mpr (fun i =>
    ContinuousControlSlice.measurable_coordinate (dataCoordinateLabel p i))

/-- The literal slot map applied to one scalar coordinate. -/
private def slotFromScalar (u : ContinuousControlSlice.Scalar) : Slot :=
  ContinuousCategorical.sample (by decide) slotMass slotMass_sum u

/-- The literal selected-follower map applied to one scalar coordinate. -/
private def selectedFromScalar (p : Parameters)
    (u : ContinuousControlSlice.Scalar) : Follower p.m :=
  ContinuousCategorical.sample (followerCount_pos p.two_le_m)
    (equalMass (followerCount p.m))
    (equalMass_sum _ (followerCount_pos p.two_le_m)) u

/-- The first-arm rule of the actual ordered tuple sampler. -/
private def tupleFirstFromScalar (p : Parameters)
    (u : ContinuousControlSlice.Scalar) : Arm p.K :=
  OrderedTupleSampler.rank p.K (K_pos p) u

private theorem tupleFirstFromScalar_eq_equalArmSample (p : Parameters) :
    tupleFirstFromScalar p = PublicDiscreteDraws.equalArmSample p.K (K_pos p) := by
  funext u
  have hfloor : tupleFirstFromScalar p u =
      PublicDiscreteDraws.pilotFromScalar p.K (K_pos p) u := by
    apply Fin.ext
    rfl
  exact hfloor.trans (PublicDiscreteDraws.pilot_eq_equalArmSample (K_pos p) u)

private theorem univ_orderEmbOfFin_eq_id (K : ℕ) :
    (Finset.univ : Finset (Fin K)).orderEmbOfFin (by simp) =
      OrderEmbedding.id (Fin K) := by
  have h := Finset.orderEmbOfFin_unique'
    (s := (Finset.univ : Finset (Fin K))) (h := by simp)
    (f := OrderEmbedding.id (Fin K)) (fun _ => Finset.mem_univ _)
  exact h.symm

private theorem tuple_coordinator_eq_rank (p : Parameters) (x : Slice p.m p.K) :
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (ActiveRoundActions.coordinator p.two_le_m) =
      tupleFirstFromScalar p
        (coordinate (Label.tuple (ActiveRoundActions.coordinator p.two_le_m)) x) := by
  have hsource := OrderedTupleSampler.sample_source_equation p.two_le_m
    p.m_lt_K x (ActiveRoundActions.coordinator p.two_le_m)
  have hrem : OrderedTupleSampler.remainder
      (OrderedTupleSampler.restrict
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x) 0 (Nat.zero_le p.m)) =
      (Finset.univ : Finset (Fin p.K)) := by
    simp [OrderedTupleSampler.remainder, OrderedTupleSampler.restrict]
  calc
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (ActiveRoundActions.coordinator p.two_le_m) =
      (OrderedTupleSampler.remainder
        (OrderedTupleSampler.restrict
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x) 0 (Nat.zero_le p.m))).orderEmbOfFin
        (OrderedTupleSampler.card_remainder _)
        (OrderedTupleSampler.rank p.K (K_pos p)
          (x (Label.tuple (ActiveRoundActions.coordinator p.two_le_m)))) := hsource
    _ = tupleFirstFromScalar p
        (coordinate (Label.tuple (ActiveRoundActions.coordinator p.two_le_m)) x) := by
      simp [hrem, univ_orderEmbOfFin_eq_id, tupleFirstFromScalar,
        ActiveRoundActions.coordinator, ContinuousControlSlice.coordinate]

private theorem scalar_slot_mass (j : Slot) :
    ContinuousControlSlice.scalarLaw {u | slotFromScalar u = j} =
      ENNReal.ofReal (slotMass j) := by
  rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  exact ContinuousCategorical.uniform_sample_singleton (by decide)
    slotMass_nonneg slotMass_sum j

private theorem scalar_selected_mass (p : Parameters) (i : Follower p.m) :
    ContinuousControlSlice.scalarLaw {u | selectedFromScalar p u = i} =
      ENNReal.ofReal (equalMass (followerCount p.m) i) := by
  rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  exact ContinuousCategorical.uniform_sample_singleton
    (followerCount_pos p.two_le_m) (equalMass_nonneg (followerCount p.m))
    (equalMass_sum _ (followerCount_pos p.two_le_m)) i

private theorem scalar_tupleFirst_mass (p : Parameters) (j : Arm p.K) :
    ContinuousControlSlice.scalarLaw {u | tupleFirstFromScalar p u = j} =
      ENNReal.ofReal (equalMass p.K j) := by
  rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform,
    tupleFirstFromScalar_eq_equalArmSample]
  exact ContinuousCategorical.uniform_sample_singleton
    (K_pos p) (equalMass_nonneg p.K) (equalMass_sum p.K (K_pos p)) j

private theorem scalar_pilot_mass (p : Parameters) (j : Arm p.K) :
    ContinuousControlSlice.scalarLaw
        {u | PublicDiscreteDraws.pilotFromScalar p.K (K_pos p) u = j} =
      ENNReal.ofReal (equalMass p.K j) := by
  rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  have hfun : (fun u : ContinuousControlSlice.Scalar =>
      PublicDiscreteDraws.pilotFromScalar p.K (K_pos p) u) =
      PublicDiscreteDraws.equalArmSample p.K (K_pos p) := by
    funext u
    exact PublicDiscreteDraws.pilot_eq_equalArmSample (K_pos p) u
  change ContinuousCategorical.uniform
    ((fun u : ContinuousControlSlice.Scalar =>
      PublicDiscreteDraws.pilotFromScalar p.K (K_pos p) u) ⁻¹' {j}) = _
  rw [hfun]
  exact ContinuousCategorical.uniform_sample_singleton
    (K_pos p) (equalMass_nonneg p.K) (equalMass_sum p.K (K_pos p)) j

private theorem scalar_fast_auxiliary_complement_mass (p : Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) :
    ContinuousControlSlice.scalarLaw
        {u | sampleFast p eta heta heta_le v w hv hw hvw hwv U u ≠ e} =
      ENNReal.ofReal
        (1 - qGamma p eta heta heta_le v w hv hw hvw hwv U e) := by
  let f := sampleFast p eta heta heta_le v w hv hw hvw hwv U
  have hset : {u : ContinuousControlSlice.Scalar | f u ≠ e} =
      f ⁻¹' {e}ᶜ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
  have hqnonneg := qGamma_nonneg p heta heta_le v w hv hw hvw hwv U e
  rw [hset, Set.preimage_compl,
    measure_compl
      ((measurableSet_singleton e).preimage
        (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U))
      (measure_ne_top _ _),
    ContinuousControlSlice.scalarLaw_eq_categorical_uniform,
    ContinuousCategorical.uniform_univ,
    uniform_sampleFast_singleton p eta heta heta_le v w hv hw hvw hwv U e]
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub]
  exact hqnonneg

private def upFactors (p : Parameters) (i : Follower p.m)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) : Fin 4 → Set ContinuousControlSlice.Scalar
  | 0 => {u | slotFromScalar u = upSlot}
  | 1 => {u | selectedFromScalar p u = i}
  | 2 => {u | tupleFirstFromScalar p u = e.1}
  | 3 => {u | sampleFast p eta heta heta_le v w hv hw hvw hwv U u ≠ e}

private def dataFactors (p : Parameters) (j : Arm p.K) :
    Fin 2 → Set ContinuousControlSlice.Scalar
  | 0 => {u | slotFromScalar u = dataSlot}
  | 1 => {u | pilotFromScalar p.K (K_pos p) u = j}

private def upBox (p : Parameters) (i : Follower p.m)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) : Set (Fin 4 → ContinuousControlSlice.Scalar) :=
  Set.univ.pi (upFactors p i eta heta heta_le v w hv hw hvw hwv U e)

private def dataBox (p : Parameters) (j : Arm p.K) :
    Set (Fin 2 → ContinuousControlSlice.Scalar) :=
  Set.univ.pi (dataFactors p j)

private theorem measurable_upBox (p : Parameters) (i : Follower p.m)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) :
    MeasurableSet (upBox p i eta heta heta_le v w hv hw hvw hwv U e) := by
  apply MeasurableSet.univ_pi
  intro k
  fin_cases k
  · exact (measurableSet_singleton upSlot).preimage
      (ContinuousCategorical.measurable_sample (by decide) slotMass_nonneg slotMass_sum)
  · exact (measurableSet_singleton i).preimage
      (ContinuousCategorical.measurable_sample (followerCount_pos p.two_le_m)
        (equalMass_nonneg _) (equalMass_sum _ (followerCount_pos p.two_le_m)))
  · exact (measurableSet_singleton e.1).preimage
      (by
        have hmeas : Measurable (tupleFirstFromScalar p) := by
          rw [tupleFirstFromScalar_eq_equalArmSample]
          exact ContinuousCategorical.measurable_sample (K_pos p)
            (equalMass_nonneg p.K) (equalMass_sum p.K (K_pos p))
        exact hmeas)
  · exact (measurableSet_singleton e).compl.preimage
      (measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U)

private theorem measurable_dataBox (p : Parameters) (j : Arm p.K) :
    MeasurableSet (dataBox p j) := by
  apply MeasurableSet.univ_pi
  intro k
  fin_cases k
  · exact (measurableSet_singleton dataSlot).preimage
      (ContinuousCategorical.measurable_sample (by decide) slotMass_nonneg slotMass_sum)
  · exact (measurableSet_singleton j).preimage (by
      have hmeas : Measurable (pilotFromScalar p.K (K_pos p)) := by
        rw [show pilotFromScalar p.K (K_pos p) = equalArmSample p.K (K_pos p) by
          funext u
          exact pilot_eq_equalArmSample (K_pos p) u]
        exact ContinuousCategorical.measurable_sample (K_pos p)
          (equalMass_nonneg p.K) (equalMass_sum p.K (K_pos p))
      exact hmeas)

private theorem upBox_product_mass (p : Parameters) (i : Follower p.m)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map (upCoordinates p)
        (upBox p i eta heta heta_le v w hv hw hvw hwv U e) =
      ENNReal.ofReal
        (slotMass upSlot * equalMass (followerCount p.m) i * equalMass p.K e.1 *
          (1 - qGamma p eta heta heta_le v w hv hw hvw hwv U e)) := by
  rw [map_upCoordinates]
  change (Measure.pi (fun _ : Fin 4 => ContinuousControlSlice.scalarLaw))
      (Set.univ.pi (upFactors p i eta heta heta_le v w hv hw hvw hwv U e)) = _
  rw [Measure.pi_pi]
  rw [Fin.prod_univ_four]
  simp only [upFactors]
  rw [scalar_slot_mass, scalar_selected_mass, scalar_tupleFirst_mass,
    scalar_fast_auxiliary_complement_mass]
  rw [← ENNReal.ofReal_mul (slotMass_nonneg upSlot),
    ← ENNReal.ofReal_mul
      (mul_nonneg (slotMass_nonneg upSlot)
        (equalMass_nonneg (followerCount p.m) i)),
    ← ENNReal.ofReal_mul
      (mul_nonneg (mul_nonneg (slotMass_nonneg upSlot)
        (equalMass_nonneg (followerCount p.m) i)) (equalMass_nonneg p.K e.1))]

private theorem dataBox_product_mass (p : Parameters) (j : Arm p.K) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map (dataCoordinates p)
        (dataBox p j) =
      ENNReal.ofReal (slotMass dataSlot * equalMass p.K j) := by
  rw [map_dataCoordinates]
  change (Measure.pi (fun _ : Fin 2 => ContinuousControlSlice.scalarLaw))
      (Set.univ.pi (dataFactors p j)) = _
  rw [Measure.pi_pi]
  rw [Fin.prod_univ_two]
  simp only [dataFactors]
  rw [scalar_slot_mass, scalar_pilot_mass]
  rw [← ENNReal.ofReal_mul (slotMass_nonneg dataSlot)]

private theorem upBox_preimage_iff (p : Parameters) (i : Follower p.m)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (e : FastArm U) (x : Slice p.m p.K) :
    x ∈ upCoordinates p ⁻¹' (upBox p i eta heta heta_le v w hv hw hvw hwv U e) ↔
      slotDraw x = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        tupleFirstFromScalar p
          (coordinate (Label.tuple (coordinator p.two_le_m)) x) = e.1 ∧
        sampleFast p eta heta heta_le v w hv hw hvw hwv U
          (coordinate Label.fast x) ≠ e := by
  change upCoordinates p x ∈
    Set.univ.pi (upFactors p i eta heta heta_le v w hv hw hvw hwv U e) ↔ _
  rw [Set.mem_univ_pi]
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    change slotFromScalar (coordinate Label.slot x) = upSlot at h0
    change selectedFromScalar p (coordinate Label.sel x) = i at h1
    change tupleFirstFromScalar p
      (coordinate (Label.tuple (coordinator p.two_le_m)) x) = e.1 at h2
    change sampleFast p eta heta heta_le v w hv hw hvw hwv U
      (coordinate Label.fast x) ≠ e at h3
    refine ⟨?_, ?_, h2, h3⟩
    · change slotFromScalar (coordinate Label.slot x) = upSlot
      exact h0
    · change selectedFromScalar p (coordinate Label.sel x) = i
      exact h1
  · rintro ⟨h0, h1, h2, h3⟩ k
    fin_cases k
    · change slotFromScalar (coordinate Label.slot x) = upSlot
      change slotFromScalar (coordinate Label.slot x) = upSlot at h0
      exact h0
    · change selectedFromScalar p (coordinate Label.sel x) = i
      change selectedFromScalar p (coordinate Label.sel x) = i at h1
      exact h1
    · change tupleFirstFromScalar p
        (coordinate (Label.tuple (coordinator p.two_le_m)) x) = e.1
      exact h2
    · change sampleFast p eta heta heta_le v w hv hw hvw hwv U
        (coordinate Label.fast x) ≠ e
      exact h3

private theorem dataBox_preimage_iff (p : Parameters) (j : Arm p.K)
    (x : Slice p.m p.K) :
    x ∈ dataCoordinates p ⁻¹' dataBox p j ↔
      slotDraw x = dataSlot ∧
        pilotDraw (K_pos p) (coordinator p.two_le_m) x = j := by
  change dataCoordinates p x ∈ Set.univ.pi (dataFactors p j) ↔ _
  rw [Set.mem_univ_pi]
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    change slotFromScalar (coordinate Label.slot x) = dataSlot at h0
    change pilotFromScalar p.K (K_pos p)
      (coordinate (Label.pilot (coordinator p.two_le_m)) x) = j at h1
    exact ⟨(by change slotFromScalar (coordinate Label.slot x) = dataSlot; exact h0),
      by simpa [pilotDraw, ActiveRoundActions.coordinator] using h1⟩
  · rintro ⟨h0, h1⟩ k
    fin_cases k
    · change slotFromScalar (coordinate Label.slot x) = dataSlot
      change slotFromScalar (coordinate Label.slot x) = dataSlot at h0
      exact h0
    · change pilotFromScalar p.K (K_pos p)
        (coordinate (Label.pilot (coordinator p.two_le_m)) x) = j
      simpa [pilotDraw, ActiveRoundActions.coordinator] using h1

private theorem pending_up_other_action_assigned {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m)
    (hj : s.status j = .pending) (hslot : r.slot = upSlot)
    (hselected : r.selected ≠ j)
    (htuple : r.tuple.val (coordinator hm) = a.auxiliary) :
    followerAction hm s r j = a.assigned j := by
  have haux : a.assigned j ≠ a.auxiliary := fun h => a.auxiliary_outside j h.symm
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  have hnotdown : r.slot ≠ downSlot := by rw [hslot]; decide
  simp [followerAction, dataSlot, downSlot, upSlot, hj, hslot, hselected,
    htuple, haux]

private theorem pending_up_feedback_eq_auxiliary {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : s.status i = .pending)
    (hslot : r.slot = upSlot) (hselected : r.selected = i)
    (htuple : r.tuple.val (coordinator hm) = a.auxiliary)
    (hfast : r.fast ≠ a.auxiliary) :
    feedback hm s r row (followerPlayer hm i) = row.val a.auxiliary := by
  have htarget : followerAction hm s r i = a.auxiliary := by
    rw [← hselected]
    have hselected_status : s.status r.selected = .pending := by
      rw [hselected]
      exact hi
    exact followerAction_pending_up_test hm s r hselected_status hslot htuple
  have hfree : collisionFreeFor (actions hm s r) (followerPlayer hm i) := by
    intro q hq hsame
    rcases player_cases hm q with hcoord | ⟨j, hj⟩
    · rw [hcoord, actions_coordinator,
        coordinatorAction_fast hm s r hmissing, actions_follower, htarget] at hsame
      exact hfast hsame
    · have hji : j ≠ i := by
        intro hji
        subst j
        apply hq
        exact hj
      have hselected_ne : r.selected ≠ j := by
        rw [hselected]
        exact hji.symm
      have hother : followerAction hm s r j = a.assigned j := by
        rcases hstatus j with hjp | hjr
        · exact pending_up_other_action_assigned hm s r j hjp hslot
            hselected_ne htuple
        · exact followerAction_released hm s r j hjr
      rw [hj, actions_follower, actions_follower, hother, htarget] at hsame
      exact a.auxiliary_outside j hsame.symm
  rw [feedback_eq_reward_of_collision_free hm s r row _ hfree,
    actions_follower, htarget]

private theorem pending_data_feedback_eq_assigned {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : (s.status i).occupied)
    (hslot : r.slot = dataSlot) :
    feedback hm s r row (followerPlayer hm i) = row.val (a.assigned i) := by
  have hfree : collisionFreeFor (actions hm s r) (followerPlayer hm i) := by
    intro q hq hsame
    rcases player_cases hm q with hcoord | ⟨j, hj⟩
    · rw [hcoord, actions_coordinator,
        coordinatorAction_fast hm s r hmissing, actions_follower,
        followerAction_occupied_data hm s r i hi hslot] at hsame
      exact r.fast_outside i hsame
    · have hji : j ≠ i := by
        intro hji
        subst j
        apply hq
        exact hj
      rw [hj, actions_follower,
        followerAction_occupied_data hm s r j (hstatus j) hslot,
        actions_follower,
        followerAction_occupied_data hm s r i (hstatus i) hslot] at hsame
      have hne : a.assigned j ≠ a.assigned i := fun heq => hji (a.injective heq)
      exact hne hsame
  rw [feedback_eq_reward_of_collision_free hm s r row _ hfree,
    actions_follower,
    followerAction_occupied_data hm s r i hi hslot]

private theorem pending_up_release_iff {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : s.status i = .pending) :
    (releaseObservation hm s r row i ∧ r.slot = upSlot) ↔
      r.slot = upSlot ∧ r.selected = i ∧
        r.tuple.val (coordinator hm) = a.auxiliary ∧
        r.fast ≠ a.auxiliary ∧ 0 < row.val a.auxiliary := by
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hslot, hselected, htuple⟩ | ⟨hdata, _⟩
    · have hfast : r.fast ≠ a.auxiliary := by
        intro heq
        have htarget : followerAction hm s r i = a.auxiliary := by
          rw [← hselected]
          have hselected_status : s.status r.selected = .pending := by
            rw [hselected]
            exact hi
          exact followerAction_pending_up_test hm s r hselected_status hslot htuple
        have hzero : feedback hm s r row (followerPlayer hm i) = 0 :=
          feedback_eq_zero_of_collision hm s r row _ (coordinator hm)
            (followerPlayer_ne_coordinator hm i).symm (by
              rw [actions_coordinator, coordinatorAction_fast hm s r hmissing,
                actions_follower, htarget, heq])
        rw [hzero] at hpos
        exact (lt_irrefl 0) hpos
      have hreward := pending_up_feedback_eq_auxiliary hm s r row hmissing
        hstatus i hi hslot hselected htuple hfast
      exact ⟨houter, hselected, htuple, hfast, by simpa [hreward] using hpos⟩
    · exact False.elim ((show dataSlot ≠ upSlot by decide) (hdata.symm.trans houter))
  · rintro ⟨hslot, hselected, htuple, hfast, hreward⟩
    refine ⟨⟨?_, Or.inl ⟨hslot, hselected, htuple⟩⟩, hslot⟩
    rw [pending_up_feedback_eq_auxiliary hm s r row hmissing hstatus i hi
      hslot hselected htuple hfast]
    exact hreward

private theorem pending_data_release_iff {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : s.status i = .pending) :
    (releaseObservation hm s r row i ∧ r.slot = dataSlot) ↔
      r.slot = dataSlot ∧ r.pilots (coordinator hm) = a.assigned i ∧
        0 < row.val (a.assigned i) := by
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hup, _, _⟩ | ⟨hslot, hpilot⟩
    · exact False.elim ((show upSlot ≠ dataSlot by decide) (hup.symm.trans houter))
    · have hreward := pending_data_feedback_eq_assigned hm s r row
        hmissing hstatus i (Or.inl hi) houter
      exact ⟨houter, hpilot, by simpa [hreward] using hpos⟩
  · rintro ⟨hslot, hpilot, hreward⟩
    refine ⟨⟨?_, Or.inr ⟨hslot, hpilot⟩⟩, hslot⟩
    rw [pending_data_feedback_eq_assigned hm s r row hmissing hstatus i
      (Or.inl hi) hslot]
    exact hreward

private theorem actual_up_release_event_iff (p : Parameters)
    (a : Assignment p.m p.K) (s : Snapshot a) (row : RewardRow p.K)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower p.m) (hi : s.status i = .pending) (x : Slice p.m p.K) :
    (releaseObservation p.two_le_m s
        (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x) row i ∧
      (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x).slot = upSlot) ↔
      x ∈ upCoordinates p ⁻¹'
        (upBox p i eta heta heta_le v w hv hw hvw hwv U
          (auxiliaryFastArm a U hU)) ∧ 0 < row.val a.auxiliary := by
  let e := auxiliaryFastArm a U hU
  let r := releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x
  have htuple : r.tuple.val (coordinator p.two_le_m) =
      tupleFirstFromScalar p (coordinate (Label.tuple (coordinator p.two_le_m)) x) := by
    simpa [r, releaseRoundInput] using tuple_coordinator_eq_rank p x
  have hiff := pending_up_release_iff p.two_le_m s r row hmissing hstatus i hi
  rw [hiff]
  have hbox := upBox_preimage_iff p i eta heta heta_le v w hv hw hvw hwv U e x
  constructor
  · rintro ⟨hslot, hselected, hcoord, hfast, hreward⟩
    have hscalar : tupleFirstFromScalar p
        (coordinate (Label.tuple (coordinator p.two_le_m)) x) = e.1 :=
      htuple.symm.trans hcoord
    have hfastSubtype :
        sampleFast p eta heta heta_le v w hv hw hvw hwv U
          (coordinate Label.fast x) ≠ e := by
      intro heq
      apply hfast
      have hval := congrArg Subtype.val heq
      simpa [r, releaseRoundInput, e, auxiliaryFastArm] using hval
    have hconditions : slotDraw x = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        tupleFirstFromScalar p
          (coordinate (Label.tuple (coordinator p.two_le_m)) x) = e.1 ∧
        sampleFast p eta heta heta_le v w hv hw hvw hwv U
          (coordinate Label.fast x) ≠ e := by
      refine ⟨?_, ?_, hscalar, ?_⟩
      · simpa [r, releaseRoundInput] using hslot
      · simpa [r, releaseRoundInput] using hselected
      · exact hfastSubtype
    exact ⟨hbox.mpr hconditions, hreward⟩
  · rintro ⟨hboxmem, hreward⟩
    rcases hbox.mp hboxmem with ⟨hslot, hselected, hcoord, hfast⟩
    have hslot' : r.slot = upSlot := by simpa [r, releaseRoundInput] using hslot
    have hselected' : r.selected = i := by simpa [r, releaseRoundInput] using hselected
    have hcoord' : r.tuple.val (coordinator p.two_le_m) = a.auxiliary :=
      htuple.trans (by simpa [e, auxiliaryFastArm] using hcoord)
    have hfast' : r.fast ≠ a.auxiliary := by
      intro heq
      apply hfast
      apply Subtype.ext
      simpa [r, releaseRoundInput, e, auxiliaryFastArm] using heq
    exact ⟨hslot', hselected', hcoord', hfast', hreward⟩

private theorem actual_data_release_event_iff (p : Parameters)
    (a : Assignment p.m p.K) (s : Snapshot a) (row : RewardRow p.K)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower p.m) (hi : s.status i = .pending) (x : Slice p.m p.K) :
    (releaseObservation p.two_le_m s
        (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x) row i ∧
      (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x).slot = dataSlot) ↔
      x ∈ dataCoordinates p ⁻¹' (dataBox p (a.assigned i)) ∧
        0 < row.val (a.assigned i) := by
  let r := releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x
  have hiff := pending_data_release_iff p.two_le_m s r row hmissing hstatus i hi
  have hbox := dataBox_preimage_iff p (a.assigned i) x
  rw [hiff]
  constructor
  · rintro ⟨hslot, hpilot, hreward⟩
    have hconditions : slotDraw x = dataSlot ∧
        pilotDraw (K_pos p) (coordinator p.two_le_m) x = a.assigned i := by
      refine ⟨?_, ?_⟩
      · simpa [r, releaseRoundInput] using hslot
      · simpa [r, releaseRoundInput] using hpilot
    exact ⟨hbox.mpr hconditions, hreward⟩
  · rintro ⟨hboxmem, hreward⟩
    rcases hbox.mp hboxmem with ⟨hslot, hpilot⟩
    have hslot' : r.slot = dataSlot := by simpa [r, releaseRoundInput] using hslot
    have hpilot' : r.pilots (coordinator p.two_le_m) = a.assigned i := by
      simpa [r, releaseRoundInput] using hpilot
    exact ⟨hslot', hpilot', hreward⟩

/-- Exact UP release mass on the actual one-round slice realization.

The slot, selected follower, first ordered-tuple coordinate, and independent
fast scalar are read from the accepted product slice. The source event is the
accepted release observation, with its genuine physical feedback test.

Source: `sources/zip4/manuscript/05_binary_transport.tex:128-153,293-325`.
-/
theorem actual_up_release_probability (p : Parameters)
    (a : Assignment p.m p.K) (s : Snapshot a) (row : RewardRow p.K)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower p.m) (hi : s.status i = .pending) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | releaseObservation p.two_le_m s
          (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x) row i ∧
        (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x).slot = upSlot} =
      ENNReal.ofReal
        (chi row a.auxiliary *
          (1 - qGamma p eta heta heta_le v w hv hw hvw hwv U
            (auxiliaryFastArm a U hU)) /
          (4 * (followerCount p.m : ℝ) * (p.K : ℝ))) := by
  let e := auxiliaryFastArm a U hU
  let r := fun x => releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x
  let E : Set (Slice p.m p.K) := {x | releaseObservation p.two_le_m s (r x) row i ∧
    (r x).slot = upSlot}
  change (ContinuousControlSlice.sliceLaw p.m p.K) E = _
  by_cases hpos : 0 < row.val a.auxiliary
  · have hset : E = upCoordinates p ⁻¹'
        upBox p i eta heta heta_le v w hv hw hvw hwv U e := by
      ext x
      change (releaseObservation p.two_le_m s (r x) row i ∧ (r x).slot = upSlot) ↔
        x ∈ upCoordinates p ⁻¹' upBox p i eta heta heta_le v w hv hw hvw hwv U e
      rw [actual_up_release_event_iff p a s row eta heta heta_le v w hv hw hvw hwv
        U hU hmissing hstatus i hi x]
      simp [hpos, e]
    rw [hset, ← Measure.map_apply (measurable_upCoordinates p)
      (measurable_upBox p i eta heta heta_le v w hv hw hvw hwv U e)]
    rw [upBox_product_mass]
    apply congrArg ENNReal.ofReal
    have hd : (followerCount p.m : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (followerCount_pos p.two_le_m))
    have hK : (p.K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (K_pos p))
    rw [chi, ite_eq_left hpos, slotMass_up]
    simp only [equalMass]
    field_simp [hd, hK]
    ring
  · have hzero : row.val a.auxiliary = 0 :=
      le_antisymm (le_of_not_gt hpos) (row.property a.auxiliary).1
    have hset : E = ∅ := by
      ext x
      constructor
      · intro hx
        have hrow := (actual_up_release_event_iff p a s row eta heta heta_le
          v w hv hw hvw hwv U hU hmissing hstatus i hi x).1 hx
        simpa [hzero] using hrow.2
      · intro hx
        cases hx
    rw [hset]
    simp [chi, hpos]

/-- The UP event has the source lower mass when the auxiliary arm minimizes
the anchor weight on the genuine complement of the assigned image.

This uses the integrated fast-sampler result
`CanonicalFastSampling.qGamma_auxiliary_arm_le_two_thirds`. Source:
`sources/zip4/manuscript/05_binary_transport.tex:128-153,293-325`.
-/
theorem actual_up_release_probability_lower_bound (p : Parameters)
    (a : Assignment p.m p.K) (s : Snapshot a) (row : RewardRow p.K)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower p.m) (hi : s.status i = .pending)
    (hmin : ∀ j : FastArm U,
      v (auxiliaryFastArm a U hU).1 ≤ v j.1) :
    ENNReal.ofReal
        (chi row a.auxiliary /
          (12 * (followerCount p.m : ℝ) * (p.K : ℝ))) ≤
      (ContinuousControlSlice.sliceLaw p.m p.K)
        {x | releaseObservation p.two_le_m s
            (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x) row i ∧
          (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x).slot = upSlot} := by
  have hprob := actual_up_release_probability p a s row eta heta heta_le
    v w hv hw hvw hwv U hU hmissing hstatus i hi
  have hq := qGamma_auxiliary_arm_le_two_thirds p heta heta_le
    v w hv hw hvw hwv U (auxiliaryFastArm a U hU) hmin
  have hdpos : (0 : ℝ) < followerCount p.m := by
    exact_mod_cast followerCount_pos p.two_le_m
  have hKpos : (0 : ℝ) < p.K := by exact_mod_cast K_pos p
  have hden : 0 < (4 * (followerCount p.m : ℝ) * (p.K : ℝ)) :=
    mul_pos (mul_pos (by norm_num) hdpos) hKpos
  have hreal :
      chi row a.auxiliary / (12 * (followerCount p.m : ℝ) * (p.K : ℝ)) ≤
        chi row a.auxiliary *
          (1 - qGamma p eta heta heta_le v w hv hw hvw hwv U
            (auxiliaryFastArm a U hU)) /
          (4 * (followerCount p.m : ℝ) * (p.K : ℝ)) := by
    by_cases hpos : 0 < row.val a.auxiliary
    · have hthird : (1 : ℝ) / 3 ≤
          1 - qGamma p eta heta heta_le v w hv hw hvw hwv U
            (auxiliaryFastArm a U hU) := by linarith
      have hfrac :
          1 / (12 * (followerCount p.m : ℝ) * (p.K : ℝ)) ≤
            (1 - qGamma p eta heta heta_le v w hv hw hvw hwv U
              (auxiliaryFastArm a U hU)) /
              (4 * (followerCount p.m : ℝ) * (p.K : ℝ)) := by
        have hleft :
            1 / (12 * (followerCount p.m : ℝ) * (p.K : ℝ)) =
              (1 / 3) / (4 * (followerCount p.m : ℝ) * (p.K : ℝ)) := by
          field_simp [ne_of_gt hden]
          ring
        rw [hleft]
        exact (div_le_div_iff_of_pos_right hden).2 hthird
      simpa [chi, hpos] using hfrac
    · simp [chi, hpos]
  rw [hprob]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Exact DATA release mass on the actual one-round slice realization.

The pilot is the coordinator's literal DATA pilot coordinate, even though
with all followers occupied the coordinator physically plays the independent
fast arm. Source: `sources/zip4/manuscript/05_binary_transport.tex:128-153,293-325`.
-/
theorem actual_data_release_probability (p : Parameters)
    (a : Assignment p.m p.K) (s : Snapshot a) (row : RewardRow p.K)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : SlowSet p.K p.m) (hU : U.val = assignedImage a)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower p.m) (hi : s.status i = .pending) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | releaseObservation p.two_le_m s
          (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x) row i ∧
        (releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x).slot = dataSlot} =
      ENNReal.ofReal (chi row (a.assigned i) /
        (2 * (p.K : ℝ))) := by
  let r := fun x => releaseRoundInput p a U hU eta heta heta_le v w hv hw hvw hwv x
  let E : Set (Slice p.m p.K) := {x | releaseObservation p.two_le_m s (r x) row i ∧
    (r x).slot = dataSlot}
  change (ContinuousControlSlice.sliceLaw p.m p.K) E = _
  by_cases hpos : 0 < row.val (a.assigned i)
  · have hset : E = dataCoordinates p ⁻¹' (dataBox p (a.assigned i)) := by
      ext x
      change (releaseObservation p.two_le_m s (r x) row i ∧ (r x).slot = dataSlot) ↔
        x ∈ dataCoordinates p ⁻¹' dataBox p (a.assigned i)
      rw [actual_data_release_event_iff p a s row eta heta heta_le
        v w hv hw hvw hwv U hU hmissing hstatus i hi x]
      simp [hpos]
    rw [hset, ← Measure.map_apply (measurable_dataCoordinates p)
      (measurable_dataBox p (a.assigned i))]
    rw [dataBox_product_mass]
    apply congrArg ENNReal.ofReal
    have hK : (p.K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (K_pos p))
    rw [chi, ite_eq_left hpos, slotMass_data]
    simp only [equalMass]
    field_simp [hK]
  · have hzero : row.val (a.assigned i) = 0 :=
      le_antisymm (le_of_not_gt hpos) (row.property (a.assigned i)).1
    have hset : E = ∅ := by
      ext x
      constructor
      · intro hx
        have hrow := (actual_data_release_event_iff p a s row eta heta heta_le
          v w hv hw hvw hwv U hU hmissing hstatus i hi x).1 hx
        simpa [hzero] using hrow.2
      · intro hx
        cases hx
    rw [hset]
    simp [chi, hpos]

end Bandits.Support.ReleaseRoundKernel
