/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteBanditModel
public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.ReleaseRoundKernel
public import Bandits.Support.DownServiceProbability

import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Signed finite-horizon stopped-regret accounting

The finite calendar identity and its deterministic fixed-snapshot adapter are
internal accounting results for
`sources/zip4/manuscript/08_main_theorem.tex:78-109`. The signed auxiliary
quantity and positive-reward count follow
`sources/zip4/manuscript/04_slow_fast_learner.tex:323-325` and
`sources/zip4/manuscript/05_binary_transport.tex:242-245`. The occupied-release
charge consumes the accepted one-round estimate at
`sources/zip4/manuscript/05_binary_transport.tex:293-325`.

Calendar indices are `Fin T`; their manuscript round labels are `t.val + 1`.
The fixed-snapshot adapter uses supplied per-round assignments, slow sets,
snapshots and round inputs, plus a supplied phase partition. It proves the
roundwise deterministic accounting once those data and correspondences are
given. It does not construct chronological phase or scheduler histories, nor
does it certify arbitrary arrays as executions of the physical protocol.
-/

@[expose] public section

open scoped BigOperators

namespace Bandits.Support.SignedStoppedRegretAccounting

open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ReleaseRoundKernel
open Bandits.Support.DownServiceProbability

/-! ## Calendar sets and the generic signed identity -/

/-- One-based manuscript round represented by a calendar index. -/
def calendarRound {T : ℕ} (t : Fin T) : ℕ := t.val + 1

/-- Calendar rounds strictly before launch `L`. -/
def startupRounds (T L : ℕ) : Finset (Fin T) :=
  Finset.univ.filter fun t => calendarRound t < L

/-- Launched rounds through and including the supplied first-bad label `b`. -/
def roundsThroughBad (T L b : ℕ) : Finset (Fin T) :=
  Finset.univ.filter fun t => L ≤ calendarRound t ∧ calendarRound t ≤ b

/-- Calendar rounds strictly after the supplied first-bad label `b`. -/
def roundsAfterBad (T b : ℕ) : Finset (Fin T) :=
  Finset.univ.filter fun t => b < calendarRound t

/-- The source indicator `1{b ≤ T}`. -/
def badWithinHorizon (T b : ℕ) : ℝ := if b ≤ T then 1 else 0

/-- Prelaunch startup reward, with the literal source cutoff `round < L`. -/
def startupReward {T : ℕ} (c : Fin T → ℝ) (L : ℕ) : ℝ :=
  ∑ t ∈ startupRounds T L, c t

/-- The full signed auxiliary sum, including every active continuation round. -/
def fullSignedAuxiliarySum {T : ℕ} (A : Finset (Fin T))
    (c ell : Fin T → ℝ) : ℝ :=
  ∑ t ∈ A, (c t - ell t)

/-- Stopped charge through and including `b`. -/
def stoppedTransportCharge {T : ℕ} (q : Fin T → ℝ) (L b : ℕ) : ℝ :=
  ∑ t ∈ roundsThroughBad T L b, q t

/-- Signed pathwise regret of the physical feedback sequence. -/
def physicalCalendarRegret {T : ℕ} (c y : Fin T → ℝ) : ℝ :=
  ∑ t : Fin T, (c t - y t)

/-- The supplied bad-event set has first bad calendar label `b`, or no bad
round when `b=T+1`. -/
def firstBadCalendar {T : ℕ} (badRounds : Finset (Fin T)) (b : ℕ) : Prop :=
  (∀ t ∈ badRounds, b ≤ calendarRound t) ∧
    (b ≤ T → ∃ t, calendarRound t = b ∧ t ∈ badRounds)

private theorem finite_round_sum_le_horizon {T m : ℕ}
    (s : Finset (Fin T)) (f : Fin T → ℝ)
    (hs : s.card ≤ T) (hf : ∀ t ∈ s, f t ≤ (m : ℝ)) :
    (∑ t ∈ s, f t) ≤ (m : ℝ) * (T : ℝ) := by
  calc
    (∑ t ∈ s, f t) ≤ ∑ t ∈ s, (m : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hf t ht
    _ = (s.card : ℝ) * (m : ℝ) := by simp
    _ ≤ (T : ℝ) * (m : ℝ) := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
    _ = (m : ℝ) * (T : ℝ) := by ring

private theorem calendar_round_le_horizon {T : ℕ} (t : Fin T) :
    calendarRound t ≤ T := by
  simp only [calendarRound]
  omega

private theorem finite_calendar_set_card_le {T : ℕ} (s : Finset (Fin T)) :
    s.card ≤ T := by
  calc
    s.card ≤ (Finset.univ : Finset (Fin T)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = T := by simp

private theorem startup_prebad_tail_partition {T L b : ℕ} :
    startupRounds T L ∪ roundsThroughBad T L b ∪ roundsAfterBad T b =
      (Finset.univ : Finset (Fin T)) := by
  classical
  ext t
  simp only [Finset.mem_union, startupRounds, roundsThroughBad, roundsAfterBad,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    by_cases hstart : calendarRound t < L
    · exact Or.inl (Or.inl hstart)
    · have hlaunch : L ≤ calendarRound t := Nat.le_of_not_gt hstart
      by_cases hthrough : calendarRound t ≤ b
      · exact Or.inl (Or.inr ⟨hlaunch, hthrough⟩)
      · exact Or.inr (Nat.lt_of_not_ge hthrough)

private theorem startup_prebad_disjoint {T L b : ℕ} :
    Disjoint (startupRounds T L) (roundsThroughBad T L b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht₁ ht₂
  simp only [startupRounds, roundsThroughBad, Finset.mem_filter,
    Finset.mem_univ, true_and] at ht₁ ht₂
  omega

private theorem stopped_tail_disjoint {T L b : ℕ} (hLb : L ≤ b) :
    Disjoint (startupRounds T L ∪ roundsThroughBad T L b)
      (roundsAfterBad T b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht₁ ht₂
  rcases Finset.mem_union.mp ht₁ with hs | hp
  · change t ∈ Finset.univ.filter (fun u : Fin T => calendarRound u < L) at hs
    change t ∈ Finset.univ.filter (fun u : Fin T => b < calendarRound u) at ht₂
    have hstart := (Finset.mem_filter.mp hs).2
    have htail := (Finset.mem_filter.mp ht₂).2
    omega
  · change t ∈ Finset.univ.filter (fun u : Fin T => L ≤ calendarRound u ∧
      calendarRound u ≤ b) at hp
    change t ∈ Finset.univ.filter (fun u : Fin T => b < calendarRound u) at ht₂
    rcases (Finset.mem_filter.mp hp).2 with ⟨hlaunch, hthrough⟩
    have htail := (Finset.mem_filter.mp ht₂).2
    omega

private theorem active_before_after_partition {T : ℕ}
    (A : Finset (Fin T)) (b : ℕ) :
    A.filter (fun t => calendarRound t ≤ b) ∪
      A.filter (fun t => b < calendarRound t) = A := by
  classical
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_union, Finset.mem_filter] at ht
    rcases ht with ⟨htA, _⟩ | ⟨htA, _⟩
    · exact htA
    · exact htA
  · intro htA
    by_cases hround : calendarRound t ≤ b
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨htA, hround⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨htA, Nat.lt_of_not_ge hround⟩))

private theorem active_before_subset_prebad {T : ℕ}
    (A : Finset (Fin T)) (L b : ℕ)
    (hA : ∀ t ∈ A, L ≤ calendarRound t) :
    A.filter (fun t => calendarRound t ≤ b) =
      A.filter (fun t => t ∈ roundsThroughBad T L b) := by
  classical
  ext t
  simp only [roundsThroughBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨htA, htb⟩
    exact ⟨htA, hA t htA, htb⟩
  · rintro ⟨htA, _, htb⟩
    exact ⟨htA, htb⟩

/-- The physical tail after `b` is at most `mT·1{b≤T}` whenever each
roundwise physical summand is at most `m`. -/
theorem physical_tail_upper_bound_internal {T m : ℕ}
    (b : ℕ) (f : Fin T → ℝ) (hf : ∀ t, f t ≤ (m : ℝ)) :
    (∑ t ∈ roundsAfterBad T b, f t) ≤
      (m : ℝ) * (T : ℝ) * badWithinHorizon T b := by
  classical
  by_cases hb : b ≤ T
  · have hcard : (roundsAfterBad T b).card ≤ T := by
      exact finite_calendar_set_card_le _
    have hsum := finite_round_sum_le_horizon (roundsAfterBad T b) f hcard
      (fun t _ => hf t)
    simpa [badWithinHorizon, hb] using hsum
  · have hempty : roundsAfterBad T b = ∅ := by
      change (Finset.univ.filter fun t : Fin T => b < calendarRound t) = ∅
      apply Finset.filter_eq_empty_iff.mpr
      intro t ht htb
      have hround := calendar_round_le_horizon t
      omega
    simp [hempty, badWithinHorizon, hb]

/-- The negative signed-auxiliary tail has magnitude at most
`mT·1{b≤T}`. -/
theorem negative_auxiliary_tail_upper_bound_internal {T m : ℕ}
    (A : Finset (Fin T)) (b : ℕ) (c ell : Fin T → ℝ)
    (hc_nonneg : ∀ t, 0 ≤ c t) (hell_le : ∀ t, ell t ≤ (m : ℝ)) :
    (∑ t ∈ A.filter (fun t => b < calendarRound t), (ell t - c t)) ≤
      (m : ℝ) * (T : ℝ) * badWithinHorizon T b := by
  classical
  by_cases hb : b ≤ T
  · let s := A.filter (fun t => b < calendarRound t)
    have hcard : s.card ≤ T := by
      exact finite_calendar_set_card_le s
    have hsum := finite_round_sum_le_horizon s (fun t => ell t - c t) hcard
      (fun t _ => by linarith [hell_le t, hc_nonneg t])
    simpa [s, badWithinHorizon, hb] using hsum
  · have hempty : A.filter (fun t => b < calendarRound t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t ht htb
      have hround := calendar_round_le_horizon t
      omega
    simp [hempty, badWithinHorizon, hb]

/-- Internal finite-set assembly for the signed stopped-regret inequality.

The arrays are visibly bounded. `hprebad` is the explicit one-round accounting
condition through and including `b`; this theorem neither constructs a phase
schedule nor proves that condition. The active set `A` remains complete after
`b`, so its signed tail is retained and controlled separately from the
physical tail. -/
theorem signed_stopped_accounting_internal_of_prebad {T m : ℕ}
    (L b : ℕ) (A badRounds : Finset (Fin T))
    (c ell y q : Fin T → ℝ)
    (_hL : 1 ≤ L ∧ L ≤ T + 1) (hLb : L ≤ b) (_hb : b ≤ T + 1)
    (_hfirst : firstBadCalendar badRounds b)
    (hA : ∀ t ∈ A, L ≤ calendarRound t)
    (hc_nonneg : ∀ t, 0 ≤ c t) (hc_le : ∀ t, c t ≤ (m : ℝ))
    (_hell_nonneg : ∀ t, 0 ≤ ell t) (hell_le : ∀ t, ell t ≤ (m : ℝ))
    (hy_nonneg : ∀ t, 0 ≤ y t) (_hy_le : ∀ t, y t ≤ (m : ℝ))
    (hprebad : ∀ t ∈ roundsThroughBad T L b,
      c t - y t ≤ (if t ∈ A then c t - ell t else 0) + q t) :
    physicalCalendarRegret c y ≤ startupReward c L +
      fullSignedAuxiliarySum A c ell + stoppedTransportCharge q L b +
        2 * (m : ℝ) * (T : ℝ) * badWithinHorizon T b := by
  classical
  have hpartition := startup_prebad_tail_partition (T := T) (L := L) (b := b)
  have hstartstop := startup_prebad_disjoint (T := T) (L := L) (b := b)
  have hdisjoint := stopped_tail_disjoint (T := T) (L := L) (b := b) hLb
  have hsumPartition :
      physicalCalendarRegret c y =
        (∑ t ∈ startupRounds T L, (c t - y t)) +
          (∑ t ∈ roundsThroughBad T L b, (c t - y t)) +
          (∑ t ∈ roundsAfterBad T b, (c t - y t)) := by
    unfold physicalCalendarRegret
    calc
      (∑ t : Fin T, (c t - y t)) =
          ∑ t ∈ (Finset.univ : Finset (Fin T)), (c t - y t) := by simp
      _ = _ := by
        rw [← hpartition, Finset.sum_union hdisjoint,
          Finset.sum_union hstartstop]
  have hstartup :
      (∑ t ∈ startupRounds T L, (c t - y t)) ≤ startupReward c L := by
    unfold startupReward
    apply Finset.sum_le_sum
    intro t ht
    linarith [hy_nonneg t]
  have hpre :
      (∑ t ∈ roundsThroughBad T L b, (c t - y t)) ≤
        (∑ t ∈ roundsThroughBad T L b,
          (if t ∈ A then c t - ell t else 0)) +
          stoppedTransportCharge q L b := by
    calc
      _ ≤ ∑ t ∈ roundsThroughBad T L b,
          ((if t ∈ A then c t - ell t else 0) + q t) := by
            apply Finset.sum_le_sum
            intro t ht
            exact hprebad t ht
      _ = (∑ t ∈ roundsThroughBad T L b,
            (if t ∈ A then c t - ell t else 0)) +
            stoppedTransportCharge q L b := by
            rw [Finset.sum_add_distrib]
            rfl
  have hpreActiveSet :
      A.filter (fun t => t ∈ roundsThroughBad T L b) =
        A.filter (fun t => calendarRound t ≤ b) :=
    (active_before_subset_prebad A L b hA).symm
  have hfilterEq :
      (roundsThroughBad T L b).filter (fun t => t ∈ A) =
        A.filter (fun t => t ∈ roundsThroughBad T L b) := by
    ext t
    simp only [Finset.mem_filter]
    tauto
  have hpreSigned :
      (∑ t ∈ roundsThroughBad T L b,
        (if t ∈ A then c t - ell t else 0)) =
        ∑ t ∈ A.filter (fun t => calendarRound t ≤ b), (c t - ell t) := by
    calc
      _ = ∑ t ∈ (roundsThroughBad T L b).filter (fun t => t ∈ A),
          (c t - ell t) := by rw [Finset.sum_filter]
      _ = ∑ t ∈ A.filter (fun t => t ∈ roundsThroughBad T L b),
          (c t - ell t) := by rw [hfilterEq]
      _ = ∑ t ∈ A.filter (fun t => calendarRound t ≤ b),
          (c t - ell t) := by rw [hpreActiveSet]
  have hactivePartition := active_before_after_partition A b
  have hactiveDisjoint : Disjoint (A.filter (fun t => calendarRound t ≤ b))
      (A.filter (fun t => b < calendarRound t)) := by
    apply Finset.disjoint_left.mpr
    intro t ht₁ ht₂
    simp only [Finset.mem_filter] at ht₁ ht₂
    omega
  have hfullSigned :
      fullSignedAuxiliarySum A c ell =
        (∑ t ∈ A.filter (fun t => calendarRound t ≤ b), (c t - ell t)) +
          (∑ t ∈ A.filter (fun t => b < calendarRound t), (c t - ell t)) := by
    unfold fullSignedAuxiliarySum
    calc
      (∑ t ∈ A, (c t - ell t)) =
          ∑ t ∈ (A.filter (fun t => calendarRound t ≤ b) ∪
            A.filter (fun t => b < calendarRound t)), (c t - ell t) := by
              rw [hactivePartition]
      _ = _ := Finset.sum_union hactiveDisjoint
  have hphysicalTail := physical_tail_upper_bound_internal b
    (fun t => c t - y t) (fun t => by linarith [hc_le t, hy_nonneg t])
  have hnegativeAuxTail := negative_auxiliary_tail_upper_bound_internal A b c ell
    hc_nonneg hell_le
  have htailNeg :
      (∑ t ∈ A.filter (fun t => b < calendarRound t), (ell t - c t)) =
        - (∑ t ∈ A.filter (fun t => b < calendarRound t), (c t - ell t)) := by
    calc
      _ = ∑ t ∈ A.filter (fun t => b < calendarRound t), - (c t - ell t) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hpre' := hpre
  rw [hpreSigned] at hpre'
  rw [hsumPartition, hfullSigned]
  rw [htailNeg] at hnegativeAuxTail
  linarith [hstartup, hpre', hphysicalTail, hnegativeAuxTail]

/-! ## Reward rows and fixed-snapshot calendar data -/

/-- A matrix row viewed through the accepted physical feedback interface. -/
def matrixRewardRow {T K : ℕ} (rewards : RewardMatrix T K) (t : Fin T) :
    ActiveRoundActions.RewardRow K :=
  ⟨rewards.reward t, rewards.reward_mem_Icc t⟩

/-- A supplied calendar of model-shaped per-round data.

Each entry is an existing assignment, source slow-set, snapshot, and accepted
`RoundInput`. `slowSet_eq_assigned` is the explicit correspondence consumed by
the release theorem. No relation between adjacent entries or claim of
chronological reachability is part of this structure. -/
structure FixedSnapshotCalendar (m K B T : ℕ)
    (rewards : RewardMatrix T K) where
  assignment : Fin T → ActiveRoundActions.Assignment m K
  slowSet : Fin T → CanonicalOrientedSetLaw.SlowSet K m
  snapshot : (t : Fin T) → ActiveRoundActions.Snapshot (assignment t)
  roundInput : (t : Fin T) → ActiveRoundActions.RoundInput (assignment t) B
  slowSet_eq_assigned : ∀ t,
    (slowSet t).val = ReleaseRoundKernel.assignedImage (assignment t)

/-- The number `g_t` of arms with positive reward in the same supplied row. -/
noncomputable def positiveRewardCount {T K : ℕ} (rewards : RewardMatrix T K)
    (t : Fin T) : ℝ :=
  ((DownServiceProbability.positiveArms (matrixRewardRow rewards t)).card : ℝ)

/-- The source cap `bar g_t = min(m,g_t)`. -/
noncomputable def cappedPositiveRewardCount {m T K : ℕ} (rewards : RewardMatrix T K)
    (t : Fin T) : ℝ := min (m : ℝ) (positiveRewardCount rewards t)

/-- The comparator's one-round reward, on the same reward row as the feedback. -/
def comparatorRoundReward {m T K : ℕ} (rewards : RewardMatrix T K)
    (S : FixedMSet m K) (t : Fin T) : ℝ :=
  ∑ a ∈ S.val, rewards.reward t a

/-- The enabled auxiliary reward `r_t(U_t)+r_t(j_t)` from the supplied slow set
and the `RoundInput` fast-arm coordinate. -/
def auxiliaryRoundReward {m K B T : ℕ} {rewards : RewardMatrix T K}
    (calendar : FixedSnapshotCalendar m K B T rewards) (t : Fin T) : ℝ :=
  ReleaseRoundKernel.slowReward (matrixRewardRow rewards t) (calendar.slowSet t) +
    (matrixRewardRow rewards t).val (calendar.roundInput t).fast

/-- Physical feedback from the accepted simultaneous-action and collision API. -/
noncomputable def physicalRoundReward {m K B T : ℕ} {rewards : RewardMatrix T K}
    (hm : 2 ≤ m) (calendar : FixedSnapshotCalendar m K B T rewards)
    (t : Fin T) : ℝ :=
  ReleaseRoundKernel.physicalFeedbackTotal hm (calendar.snapshot t)
    (calendar.roundInput t) (matrixRewardRow rewards t)

/-- The actual pending-`chi` plus auxiliary-sentinel release charge. -/
noncomputable def occupiedReleaseSentinelCharge {m K B T : ℕ} {rewards : RewardMatrix T K}
    (calendar : FixedSnapshotCalendar m K B T rewards)
    (t : Fin T) : ℝ :=
  (∑ j : ActiveRoundActions.Follower m,
    if (calendar.snapshot t).status j = .pending then
      ReleaseRoundKernel.chi (matrixRewardRow rewards t)
        ((calendar.assignment t).assigned j) else 0) +
  (if (calendar.roundInput t).fast = (calendar.assignment t).auxiliary ∧
      ∃ j, (calendar.snapshot t).status j = .pending then
    (matrixRewardRow rewards t).val (calendar.assignment t).auxiliary else 0)

/-- The literal stopped charge on the supplied partition. -/
noncomputable def fixedSnapshotStoppedCharge {m K B T : ℕ} {rewards : RewardMatrix T K}
    (calendar : FixedSnapshotCalendar m K B T rewards)
    (enabledCollection frozenCollection occupiedRelease : Finset (Fin T))
    (t : Fin T) : ℝ :=
  if t ∈ enabledCollection then cappedPositiveRewardCount (m := m) rewards t
  else if t ∈ frozenCollection then cappedPositiveRewardCount (m := m) rewards t
  else if t ∈ occupiedRelease then occupiedReleaseSentinelCharge calendar t
  else 0

/-- A sum of rewards in `[0,1]` is bounded by its set size and by the number
of positive-reward arms in that row. -/
private theorem reward_sum_le_card_and_positive_count {K : ℕ}
    (row : ActiveRoundActions.RewardRow K) (S : Finset (Arm K)) :
    (∑ a ∈ S, row.val a) ≤ (S.card : ℝ) ∧
      (∑ a ∈ S, row.val a) ≤
        ((DownServiceProbability.positiveArms row).card : ℝ) := by
  classical
  constructor
  · calc
      (∑ a ∈ S, row.val a) ≤ ∑ a ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (row.property a).2
      _ = (S.card : ℝ) := by simp
  · calc
      (∑ a ∈ S, row.val a) =
          ∑ a ∈ S.filter (fun a => 0 < row.val a), row.val a := by
        rw [← Finset.sum_filter_of_ne (p := fun a => 0 < row.val a)
          (fun a ha hne => lt_of_le_of_ne (row.property a).1 (Ne.symm hne))]
      _ ≤ ∑ a ∈ S.filter (fun a => 0 < row.val a), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (row.property a).2
      _ = ((S.filter (fun a => 0 < row.val a)).card : ℝ) := by simp
      _ ≤ ((DownServiceProbability.positiveArms row).card : ℝ) := by
        have hsubset : S.filter (fun a => 0 < row.val a) ⊆
            DownServiceProbability.positiveArms row := by
          intro a ha
          rcases Finset.mem_filter.mp ha with ⟨_, hpos⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
        exact_mod_cast Finset.card_le_card hsubset

/-- The comparator and auxiliary rewards are bounded by `bar g_t`, derived
from the finite comparator/slow sets and the same reward row. -/
theorem comparator_auxiliary_round_rewards_le_cap {m K B T : ℕ}
    (hm : 2 ≤ m) (rewards : RewardMatrix T K)
    (calendar : FixedSnapshotCalendar m K B T rewards)
    (S : FixedMSet m K) (t : Fin T) :
    comparatorRoundReward rewards S t ≤ cappedPositiveRewardCount (m := m) rewards t ∧
      auxiliaryRoundReward calendar t ≤ cappedPositiveRewardCount (m := m) rewards t := by
  classical
  have hcompBounds := reward_sum_le_card_and_positive_count
    (matrixRewardRow rewards t) S.val
  have hcompCap : comparatorRoundReward rewards S t ≤
      cappedPositiveRewardCount (m := m) rewards t := by
    have hcard : comparatorRoundReward rewards S t ≤ (S.val.card : ℝ) := by
      simpa [comparatorRoundReward, matrixRewardRow] using hcompBounds.1
    have hpositive : comparatorRoundReward rewards S t ≤ positiveRewardCount rewards t := by
      simpa [comparatorRoundReward, positiveRewardCount, matrixRewardRow] using hcompBounds.2
    have hcardm : (S.val.card : ℝ) = (m : ℝ) := by exact_mod_cast S.property.1
    unfold cappedPositiveRewardCount
    exact le_min (by rw [← hcardm]; exact hcard) hpositive
  have hfastNot : (calendar.roundInput t).fast ∉ (calendar.slowSet t).val := by
    intro hmem
    rw [calendar.slowSet_eq_assigned t, ReleaseRoundKernel.assignedImage] at hmem
    rcases Finset.mem_image.mp hmem with ⟨j, _, heq⟩
    exact (calendar.roundInput t).fast_outside j heq.symm
  have hinsertCard :
      (insert (calendar.roundInput t).fast (calendar.slowSet t).val).card = m := by
    rw [Finset.card_insert_of_notMem hfastNot]
    have hslow := CanonicalOrientedSetLaw.slowSet_card hm (calendar.slowSet t)
    omega
  have hellIdentity : auxiliaryRoundReward calendar t =
      ∑ a ∈ insert (calendar.roundInput t).fast (calendar.slowSet t).val,
        (matrixRewardRow rewards t).val a := by
    unfold auxiliaryRoundReward
    unfold ReleaseRoundKernel.slowReward
    rw [Finset.sum_insert hfastNot]
    ring
  have hellBounds := reward_sum_le_card_and_positive_count (matrixRewardRow rewards t)
    (insert (calendar.roundInput t).fast (calendar.slowSet t).val)
  have hellCap : auxiliaryRoundReward calendar t ≤
      cappedPositiveRewardCount (m := m) rewards t := by
    have hcard : auxiliaryRoundReward calendar t ≤
        ((insert (calendar.roundInput t).fast (calendar.slowSet t).val).card : ℝ) := by
      calc
        _ = _ := hellIdentity
        _ ≤ _ := hellBounds.1
    have hpositive : auxiliaryRoundReward calendar t ≤ positiveRewardCount rewards t := by
      calc
        _ = _ := hellIdentity
        _ ≤ _ := by
          simpa [positiveRewardCount, matrixRewardRow] using hellBounds.2
    have hsize :
        ((insert (calendar.roundInput t).fast (calendar.slowSet t).val).card : ℝ) =
          (m : ℝ) := by
      exact_mod_cast hinsertCard
    have hauxM : auxiliaryRoundReward calendar t ≤ (m : ℝ) := by
      exact le_trans hcard (le_of_eq hsize)
    unfold cappedPositiveRewardCount
    exact le_min hauxM hpositive
  exact ⟨hcompCap, hellCap⟩

/-- Explicit raw `g_t` bounds for both literal reward sums. -/
theorem comparator_auxiliary_round_rewards_le_positive_count {m K B T : ℕ}
    (hm : 2 ≤ m) (rewards : RewardMatrix T K)
    (calendar : FixedSnapshotCalendar m K B T rewards)
    (S : FixedMSet m K) (t : Fin T) :
    comparatorRoundReward rewards S t ≤ positiveRewardCount rewards t ∧
      auxiliaryRoundReward calendar t ≤ positiveRewardCount rewards t := by
  have h := comparator_auxiliary_round_rewards_le_cap hm rewards calendar S t
  exact ⟨le_trans h.1 (min_le_right _ _), le_trans h.2 (min_le_right _ _)⟩

/-- Physical feedback on one supplied round is bounded by the number of
players, using the accepted feedback API for the coordinator and every
follower. -/
theorem physical_round_reward_mem_Icc {m K B T : ℕ}
    (hm : 2 ≤ m) (rewards : RewardMatrix T K)
    (calendar : FixedSnapshotCalendar m K B T rewards) (t : Fin T) :
    physicalRoundReward hm calendar t ∈ Set.Icc (0 : ℝ) (m : ℝ) := by
  have hcoord := ActiveRoundActions.feedback_mem_Icc hm (calendar.snapshot t)
    (calendar.roundInput t) (matrixRewardRow rewards t)
    (ActiveRoundActions.coordinator hm)
  have hfollowersNonneg :
      0 ≤ ∑ j : ActiveRoundActions.Follower m,
        ActiveRoundActions.feedback hm (calendar.snapshot t) (calendar.roundInput t)
          (matrixRewardRow rewards t) (PublicDiscreteDraws.followerPlayer hm j) := by
    apply Finset.sum_nonneg
    intro j hj
    exact (ActiveRoundActions.feedback_mem_Icc hm (calendar.snapshot t)
      (calendar.roundInput t) (matrixRewardRow rewards t)
      (PublicDiscreteDraws.followerPlayer hm j)).1
  have hfollowersUpper :
      (∑ j : ActiveRoundActions.Follower m,
        ActiveRoundActions.feedback hm (calendar.snapshot t) (calendar.roundInput t)
          (matrixRewardRow rewards t) (PublicDiscreteDraws.followerPlayer hm j)) ≤
        (PublicDiscreteDraws.followerCount m : ℝ) := by
    calc
      _ ≤ ∑ _j : ActiveRoundActions.Follower m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (ActiveRoundActions.feedback_mem_Icc hm (calendar.snapshot t)
          (calendar.roundInput t) (matrixRewardRow rewards t)
          (PublicDiscreteDraws.followerPlayer hm j)).2
      _ = (PublicDiscreteDraws.followerCount m : ℝ) := by simp
  constructor
  · unfold physicalRoundReward ReleaseRoundKernel.physicalFeedbackTotal
    linarith [hcoord.1, hfollowersNonneg]
  · unfold physicalRoundReward ReleaseRoundKernel.physicalFeedbackTotal
    have hcount := PublicDiscreteDraws.followerCount_add_one hm
    have hcountR :
        (PublicDiscreteDraws.followerCount m : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast hcount
    linarith [hcoord.2, hfollowersUpper, hcountR]

/-- The literal finite-horizon comparator sums to the already accepted fixed
`m`-set reward. -/
theorem sum_comparator_round_reward_eq_fixedMSetReward {m K T : ℕ}
    (rewards : RewardMatrix T K) (S : FixedMSet m K) :
    (∑ t : Fin T, comparatorRoundReward rewards S t) =
      fixedMSetReward rewards S.val := rfl

/-- The actual pending-`chi` plus auxiliary-sentinel formula is nonnegative. -/
theorem occupied_release_sentinel_charge_nonneg {m K B T : ℕ}
    {rewards : RewardMatrix T K}
    (calendar : FixedSnapshotCalendar m K B T rewards) (t : Fin T) :
    0 ≤ occupiedReleaseSentinelCharge calendar t := by
  unfold occupiedReleaseSentinelCharge
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j hj
    by_cases hpending : (calendar.snapshot t).status j = .pending
    · by_cases hpos : 0 < (matrixRewardRow rewards t).val
          ((calendar.assignment t).assigned j)
      · simp [hpending, ReleaseRoundKernel.chi, hpos]
      · simp [hpending, ReleaseRoundKernel.chi, hpos]
    · simp [hpending]
  · split_ifs
    · exact (rewards.reward_mem_Icc t (calendar.assignment t).auxiliary).1
    · exact le_rfl

/-- The accepted release kernel discharges the live-round auxiliary loss by
the stated pending-`chi` plus auxiliary-sentinel charge. -/
theorem occupied_release_auxiliary_loss_le_sentinel {m K B T : ℕ}
    {rewards : RewardMatrix T K} (hm : 2 ≤ m)
    (calendar : FixedSnapshotCalendar m K B T rewards) (t : Fin T)
    (hmissing : (calendar.snapshot t).missing = ∅)
    (hstatus : ∀ j, (calendar.snapshot t).status j = .pending ∨
      (calendar.snapshot t).status j = .released) :
    auxiliaryRoundReward calendar t - physicalRoundReward hm calendar t ≤
      occupiedReleaseSentinelCharge calendar t := by
  have hkernel := ReleaseRoundKernel.pathwise_sentinel_cost_bound hm
    (calendar.assignment t) (calendar.slowSet t) (calendar.slowSet_eq_assigned t)
    (calendar.snapshot t) hmissing hstatus (calendar.roundInput t)
    (matrixRewardRow rewards t)
  simpa [auxiliaryRoundReward, physicalRoundReward, occupiedReleaseSentinelCharge]
    using hkernel

/-- Fixed-snapshot calendar specialization of the generic stopped accounting.

The supplied enabled collection/handover, frozen collection, and occupied
release sets partition every launched round through `b`. Active flags agree
with enabled collection/handover and occupied release on those rounds, so the
signed auxiliary term is retained on every release. Its charge is proved by
the accepted one-round release kernel. The partition, snapshot correspondences
and round data are explicit inputs: this theorem does not construct a
scheduler, chronology, decoder history, or actual protocol execution. -/
theorem fixed_snapshot_signed_stopped_accounting_internal
    {m K B T : ℕ} (hm : 2 ≤ m) (rewards : RewardMatrix T K)
    (calendar : FixedSnapshotCalendar m K B T rewards)
    (S : FixedMSet m K) (L b : ℕ)
    (active badRounds enabledCollection frozenCollection occupiedRelease : Finset (Fin T))
    (hL : 1 ≤ L ∧ L ≤ T + 1) (hLb : L ≤ b) (hb : b ≤ T + 1)
    (hfirst : firstBadCalendar badRounds b)
    (hactive : ∀ t ∈ active, L ≤ calendarRound t)
    (hpartition : ∀ t, t ∈ roundsThroughBad T L b ↔
      t ∈ enabledCollection ∨ t ∈ frozenCollection ∨ t ∈ occupiedRelease)
    (hdisjointEnabledFrozen : Disjoint enabledCollection frozenCollection)
    (hdisjointEnabledRelease : Disjoint enabledCollection occupiedRelease)
    (hdisjointFrozenRelease : Disjoint frozenCollection occupiedRelease)
    (hflags : ∀ t, t ∈ roundsThroughBad T L b →
      (t ∈ active ↔ t ∈ enabledCollection ∨ t ∈ occupiedRelease))
    (hreleaseMissing : ∀ t ∈ occupiedRelease,
      (calendar.snapshot t).missing = ∅)
    (hreleaseStatus : ∀ t ∈ occupiedRelease, ∀ j,
      (calendar.snapshot t).status j = .pending ∨
        (calendar.snapshot t).status j = .released) :
    physicalCalendarRegret
        (comparatorRoundReward rewards S)
        (physicalRoundReward hm calendar) ≤
      startupReward (comparatorRoundReward rewards S) L +
        fullSignedAuxiliarySum active (comparatorRoundReward rewards S)
          (auxiliaryRoundReward calendar) +
        stoppedTransportCharge
          (fixedSnapshotStoppedCharge calendar enabledCollection frozenCollection
            occupiedRelease) L b +
        2 * (m : ℝ) * (T : ℝ) * badWithinHorizon T b := by
  classical
  have hrewardBounds := fun t => comparator_auxiliary_round_rewards_le_cap
    hm rewards calendar S t
  have hyBounds := fun t => physical_round_reward_mem_Icc hm rewards calendar t
  have hprebad : ∀ t ∈ roundsThroughBad T L b,
      comparatorRoundReward rewards S t - physicalRoundReward hm calendar t ≤
        (if t ∈ active then comparatorRoundReward rewards S t -
            auxiliaryRoundReward calendar t else 0) +
          fixedSnapshotStoppedCharge calendar enabledCollection frozenCollection
            occupiedRelease t := by
    intro t ht
    rcases (hpartition t).mp ht with hc | hf | hr
    · have hactiveHere := (hflags t ht).2 (Or.inl hc)
      have hcharge : fixedSnapshotStoppedCharge calendar enabledCollection
          frozenCollection occupiedRelease t =
            cappedPositiveRewardCount (m := m) rewards t := by
        simp [fixedSnapshotStoppedCharge, hc]
      simp [hactiveHere, hcharge]
      have hellBound := (hrewardBounds t).2
      have hyNonneg := (hyBounds t).1
      linarith
    · have hnotEnabled : t ∉ enabledCollection := by
        intro he
        exact (Finset.disjoint_left.mp hdisjointEnabledFrozen) he hf
      have hnotRelease : t ∉ occupiedRelease := by
        intro hr'
        exact (Finset.disjoint_left.mp hdisjointFrozenRelease) hf hr'
      have hnotActive : t ∉ active := by
        intro ha
        rcases (hflags t ht).mp ha with he | hr'
        · exact hnotEnabled he
        · exact hnotRelease hr'
      have hcharge : fixedSnapshotStoppedCharge calendar enabledCollection
          frozenCollection occupiedRelease t =
            cappedPositiveRewardCount (m := m) rewards t := by
        simp [fixedSnapshotStoppedCharge, hnotEnabled, hf]
      simp [hnotActive, hcharge]
      have hcBound := (hrewardBounds t).1
      have hyNonneg := (hyBounds t).1
      linarith
    · have hnotEnabled : t ∉ enabledCollection := by
        intro he
        exact (Finset.disjoint_left.mp hdisjointEnabledRelease) he hr
      have hnotFrozen : t ∉ frozenCollection := by
        intro hf
        exact (Finset.disjoint_left.mp hdisjointFrozenRelease) hf hr
      have hactiveHere := (hflags t ht).2 (Or.inr hr)
      have hcharge : fixedSnapshotStoppedCharge calendar enabledCollection
          frozenCollection occupiedRelease t = occupiedReleaseSentinelCharge calendar t := by
        simp [fixedSnapshotStoppedCharge, hnotEnabled, hnotFrozen, hr]
      simp [hactiveHere, hcharge]
      have hrelease := occupied_release_auxiliary_loss_le_sentinel hm calendar t
        (hreleaseMissing t hr) (hreleaseStatus t hr)
      linarith
  have hcBounds : ∀ t, 0 ≤ comparatorRoundReward rewards S t ∧
      comparatorRoundReward rewards S t ≤ (m : ℝ) := by
    intro t
    have hcap := (hrewardBounds t).1
    constructor
    · unfold comparatorRoundReward
      apply Finset.sum_nonneg
      intro a ha
      exact (rewards.reward_mem_Icc t a).1
    · unfold cappedPositiveRewardCount at hcap
      exact le_trans hcap (min_le_left _ _)
  have hellBounds : ∀ t, 0 ≤ auxiliaryRoundReward calendar t ∧
      auxiliaryRoundReward calendar t ≤ (m : ℝ) := by
    intro t
    have hcap := (hrewardBounds t).2
    constructor
    · unfold auxiliaryRoundReward ReleaseRoundKernel.slowReward
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro a ha
        exact (rewards.reward_mem_Icc t a).1
      · exact (rewards.reward_mem_Icc t (calendar.roundInput t).fast).1
    · unfold cappedPositiveRewardCount at hcap
      exact le_trans hcap (min_le_left _ _)
  exact signed_stopped_accounting_internal_of_prebad L b active badRounds
    (comparatorRoundReward rewards S) (auxiliaryRoundReward calendar)
    (physicalRoundReward hm calendar)
    (fixedSnapshotStoppedCharge calendar enabledCollection frozenCollection occupiedRelease)
    hL hLb hb hfirst hactive
    (fun t => (hcBounds t).1) (fun t => (hcBounds t).2)
    (fun t => (hellBounds t).1) (fun t => (hellBounds t).2)
    (fun t => (hyBounds t).1) (fun t => (hyBounds t).2) hprebad

end Bandits.Support.SignedStoppedRegretAccounting

end
