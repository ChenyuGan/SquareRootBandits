/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteBoundedLocalHistoryCode
public import Bandits.Support.MeasurableLocalRollout

/-!
# Finite-horizon rollout from bounded local histories

The environment feedback and local-information rules follow
sources/zip4/manuscript/01_introduction.tex:18-52. Bounded local observations
and their history carrier follow sources/zip4/manuscript/07_public_setup.tex:27-38,55-114
and sources/zip4/manuscript/06_interruptions.tex:240-296. The comparator and
private-expectation regret convention follow
sources/zip4/manuscript/08_main_theorem.tex:67-75,163-168.

This module constructs a finite typed local-decision model and proves its
measurability and elementary reward bounds. It does not identify the supplied
decisions or private laws with the manuscript protocol.
-/

@[expose] public section

namespace Bandits.Support.FiniteHorizonBoundedLocalRollout

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.FiniteBanditModel
open Bandits.Support.FiniteBoundedLocalHistoryCode
open Bandits.Support.MeasurableLocalRollout
open Bandits.Support.SparseCalendarReplay

variable (p : ConstructorDimensions.Parameters)
variable {Own : Fin p.m → Type*}

/-- The private-input profile keeps a separate carrier for each player. -/
abbrev PrivateProfile (Own : Fin p.m → Type*) := (i : Fin p.m) → Own i

/-- Finite local decision data: a player's output depends on the public output,
that player's own private input, and its full bounded local history. -/
abbrev FiniteBoundedLocalDecision (Own : Fin p.m → Type*) :=
  (i : Fin p.m) → (t : Fin p.T) →
    PublishedOutput p × (Own i × BoundedHistory p t.val) → Fin p.K

/-- The parameter space used for joint measurability. -/
abbrev RolloutParameters (Own : Fin p.m → Type*) :=
  PublishedOutput p × PrivateProfile p Own

/-- The existing run prefix with its feedback bound as a dependent pair. -/
abbrev BoundedRunPrefix (n : ℕ) :=
  {q : RunPrefix p.m p.K n // ∀ s i, q.feedback s i ∈ Set.Icc (0 : ℝ) 1}

/-- The bounded local history extracted from a run retains each past action
and the corresponding feedback together with its actual interval proof. -/
def boundedHistoryOfRun {n : ℕ} (run : RunPrefix p.m p.K n)
    (hfeedback : ∀ s i, run.feedback s i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin p.m) : BoundedHistory p n :=
  fun s =>
    ((localHistoryOfRun run i s).1,
      ⟨(localHistoryOfRun run i s).2, hfeedback s i⟩)

/-- Erasing a bounded history's proof recovers exactly the existing local
history representation. -/
theorem erase_boundedHistoryOfRun {n : ℕ} (run : RunPrefix p.m p.K n)
    (hfeedback : ∀ s i, run.feedback s i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin p.m) :
    eraseBounded p (boundedHistoryOfRun p run hfeedback i) =
      localHistoryOfRun run i := by
  funext s
  rfl

/-- Literal finite recursion of the bounded local environment. At each round
all players choose from their own previous bounded history, then the existing
collision-filtered feedback is appended. -/
noncomputable def boundedLocalPrefix
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K) :
    (n : ℕ) → n ≤ p.T → BoundedRunPrefix p n
  | 0, _ =>
      ⟨⟨Fin.elim0, Fin.elim0⟩, by
        intro s
        exact Fin.elim0 s⟩
  | n + 1, hn =>
      let previous := boundedLocalPrefix D pub rho r n (Nat.le_of_succ_le hn)
      let t : Fin p.T := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      let actions : ActionProfile p.m p.K := fun i =>
        D i t (pub, (rho i,
          boundedHistoryOfRun p previous.val previous.property i))
      let feedback : Fin p.m → ℝ := fun i => playerFeedback actions (r.reward t) i
      ⟨⟨Fin.snoc previous.val.action actions,
          Fin.snoc previous.val.feedback feedback⟩, by
        intro s i
        cases s using Fin.lastCases with
        | cast s =>
            simpa only [Fin.snoc_castSucc] using previous.property s i
        | last =>
            simpa only [Fin.snoc_last] using
              rewardMatrixFeedback_mem_Icc actions r t i⟩

/-- At horizon zero the constructed environment is the existing empty run. -/
theorem boundedLocalPrefix_zero
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K) (hn : 0 ≤ p.T) :
    (boundedLocalPrefix p D pub rho r 0 hn).val =
      (⟨Fin.elim0, Fin.elim0⟩ : RunPrefix p.m p.K 0) := rfl

/-- Every old action is preserved by one recursive extension. -/
theorem boundedLocalPrefix_action_castSucc
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n + 1 ≤ p.T) (s : Fin n) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r (n + 1) hn).val.action s.castSucc i =
      (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).val.action s i := by
  simp [boundedLocalPrefix, Fin.snoc_castSucc]

/-- Every old feedback is preserved by one recursive extension. -/
theorem boundedLocalPrefix_feedback_castSucc
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n + 1 ≤ p.T) (s : Fin n) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r (n + 1) hn).val.feedback s.castSucc i =
      (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).val.feedback s i := by
  simp [boundedLocalPrefix, Fin.snoc_castSucc]

/-- The new action is selected from exactly the previous bounded own history. -/
theorem boundedLocalPrefix_action_last
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n + 1 ≤ p.T) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r (n + 1) hn).val.action (Fin.last n) i =
      D i ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
        (pub, (rho i, boundedHistoryOfRun p
          (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).val
          (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).property i)) := by
  simp [boundedLocalPrefix, Fin.snoc_last]

/-- The new observation is the existing finite-model collision feedback. -/
theorem boundedLocalPrefix_feedback_last
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n + 1 ≤ p.T) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r (n + 1) hn).val.feedback (Fin.last n) i =
      playerFeedback
        (fun j => D j ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
          (pub, (rho j, boundedHistoryOfRun p
            (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).val
            (boundedLocalPrefix p D pub rho r n (Nat.le_of_succ_le hn)).property j)))
        (r.reward ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩) i := by
  simp [boundedLocalPrefix, Fin.snoc_last]

/-- Restricting the extracted history along a finite prefix retains every
recorded action-feedback pair. -/
theorem boundedHistoryOfRun_castLE {n k : ℕ} (hkn : k ≤ n)
    (run : RunPrefix p.m p.K n)
    (hfeedback : ∀ s i, run.feedback s i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin p.m) :
    (fun s : Fin k => boundedHistoryOfRun p run hfeedback i (Fin.castLE hkn s)) =
      fun s : Fin k =>
        ((localHistoryOfRun run i (Fin.castLE hkn s)).1,
          ⟨(localHistoryOfRun run i (Fin.castLE hkn s)).2,
            hfeedback (Fin.castLE hkn s) i⟩) := rfl

/-- Shortening the constructed horizon keeps each earlier action unchanged. -/
theorem boundedLocalPrefix_action_restrict
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    {k n : ℕ} (hkn : k ≤ n) (hn : n ≤ p.T) (s : Fin k) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r n hn).val.action (Fin.castLE hkn s) i =
      (boundedLocalPrefix p D pub rho r k (Nat.le_trans hkn hn)).val.action s i := by
  revert s i
  induction n with
  | zero =>
      intro s i
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      exact Fin.elim0 s
  | succ n ih =>
      intro s i
      by_cases hsmall : k ≤ n
      · have hcast : Fin.castLE hkn s = (Fin.castLE hsmall s).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, boundedLocalPrefix_action_castSucc]
        exact ih hsmall (Nat.le_of_succ_le hn) s i
      · have hnlt : n < k := Nat.lt_of_not_ge hsmall
        have hk : k = n + 1 :=
          Nat.le_antisymm hkn (Nat.succ_le_of_lt hnlt)
        subst k
        have hcast : Fin.castLE hkn s = s := by
          apply Fin.ext
          rfl
        rw [hcast]

/-- Shortening the constructed horizon keeps each earlier feedback unchanged. -/
theorem boundedLocalPrefix_feedback_restrict
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    {k n : ℕ} (hkn : k ≤ n) (hn : n ≤ p.T) (s : Fin k) (i : Fin p.m) :
    (boundedLocalPrefix p D pub rho r n hn).val.feedback (Fin.castLE hkn s) i =
      (boundedLocalPrefix p D pub rho r k (Nat.le_trans hkn hn)).val.feedback s i := by
  revert s i
  induction n with
  | zero =>
      intro s i
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      exact Fin.elim0 s
  | succ n ih =>
      intro s i
      by_cases hsmall : k ≤ n
      · have hcast : Fin.castLE hkn s = (Fin.castLE hsmall s).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, boundedLocalPrefix_feedback_castSucc]
        exact ih hsmall (Nat.le_of_succ_le hn) s i
      · have hnlt : n < k := Nat.lt_of_not_ge hsmall
        have hk : k = n + 1 :=
          Nat.le_antisymm hkn (Nat.succ_le_of_lt hnlt)
        subst k
        have hcast : Fin.castLE hkn s = s := by
          apply Fin.ext
          rfl
        rw [hcast]

/-- The bounded own history of a shortened prefix is exactly the restriction
of the longer history, including each interval proof. -/
theorem boundedLocalPrefix_history_restrict
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K)
    {k n : ℕ} (hkn : k ≤ n) (hn : n ≤ p.T) (i : Fin p.m) :
    (fun s : Fin k =>
      boundedHistoryOfRun p
        (boundedLocalPrefix p D pub rho r n hn).val
        (boundedLocalPrefix p D pub rho r n hn).property i (Fin.castLE hkn s)) =
      boundedHistoryOfRun p
        (boundedLocalPrefix p D pub rho r k (Nat.le_trans hkn hn)).val
        (boundedLocalPrefix p D pub rho r k (Nat.le_trans hkn hn)).property i := by
  funext s
  apply Prod.ext
  · exact boundedLocalPrefix_action_restrict p D pub rho r hkn hn s i
  · apply Subtype.ext
    exact boundedLocalPrefix_feedback_restrict p D pub rho r hkn hn s i

/-- Inductive joint-measurability invariant for every action and feedback
coordinate of the recursively constructed prefix. -/
private theorem boundedLocalPrefix_measurable_internal
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t)) :
    ∀ n hn,
      (∀ s i, Measurable (fun x : RolloutParameters p Own =>
        (boundedLocalPrefix p D x.1 x.2 r n hn).val.action s i)) ∧
      (∀ s i, Measurable (fun x : RolloutParameters p Own =>
        (boundedLocalPrefix p D x.1 x.2 r n hn).val.feedback s i)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn
      constructor
      · intro s
        exact Fin.elim0 s
      · intro s
        exact Fin.elim0 s
  | succ n ih =>
      intro hn
      obtain ⟨hprevAction, hprevFeedback⟩ := ih (Nat.le_of_succ_le hn)
      constructor
      · intro s i
        cases s using Fin.lastCases with
        | cast s =>
            have hcast :
                (fun x : RolloutParameters p Own =>
                  (boundedLocalPrefix p D x.1 x.2 r (n + 1) hn).val.action
                    s.castSucc i) =
                (fun x => (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).val.action s i) := by
              funext x
              exact boundedLocalPrefix_action_castSucc p D x.1 x.2 r n hn s i
            rw [hcast]
            exact hprevAction s i
        | last =>
            have hhistory : Measurable fun x : RolloutParameters p Own =>
                boundedHistoryOfRun p
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).val
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).property i := by
              rw [measurable_pi_iff]
              intro u
              change Measurable (fun x : RolloutParameters p Own =>
                ((localHistoryOfRun
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val i u).1,
                  (⟨(localHistoryOfRun
                      (boundedLocalPrefix p D x.1 x.2 r n
                        (Nat.le_of_succ_le hn)).val i u).2,
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property u i⟩ :
                    SparseCalendarReward)))
              have hsubtype : Measurable (fun x : RolloutParameters p Own =>
                  (⟨(boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val.feedback u i,
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property u i⟩ :
                    SparseCalendarReward)) :=
                (hprevFeedback u i).subtype_mk
                  (h := fun x => (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).property u i)
              exact (hprevAction u i).prodMk hsubtype
            have hprivate : Measurable fun x : RolloutParameters p Own =>
                x.2 i := (measurable_pi_apply i).comp measurable_snd
            have hargs : Measurable fun x : RolloutParameters p Own =>
                (x.1, (x.2 i, boundedHistoryOfRun p
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).val
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).property i)) :=
              measurable_fst.prodMk (hprivate.prodMk hhistory)
            have hlast :
                (fun x : RolloutParameters p Own =>
                  (boundedLocalPrefix p D x.1 x.2 r (n + 1) hn).val.action
                    (Fin.last n) i) =
                (fun x => D i ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
                  (x.1, (x.2 i, boundedHistoryOfRun p
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property i))) := by
              funext x
              exact boundedLocalPrefix_action_last p D x.1 x.2 r n hn i
            rw [hlast]
            exact (hD i ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩).comp hargs
      · intro s i
        cases s using Fin.lastCases with
        | cast s =>
            have hcast :
                (fun x : RolloutParameters p Own =>
                  (boundedLocalPrefix p D x.1 x.2 r (n + 1) hn).val.feedback
                    s.castSucc i) =
                (fun x => (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).val.feedback s i) := by
              funext x
              exact boundedLocalPrefix_feedback_castSucc p D x.1 x.2 r n hn s i
            rw [hcast]
            exact hprevFeedback s i
        | last =>
            let currentActions : RolloutParameters p Own → ActionProfile p.m p.K :=
              fun x j => D j ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
                (x.1, (x.2 j, boundedHistoryOfRun p
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).val
                  (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).property j))
            have hhistory (j : Fin p.m) :
                Measurable fun x : RolloutParameters p Own =>
                  boundedHistoryOfRun p
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property j := by
              rw [measurable_pi_iff]
              intro u
              change Measurable (fun x : RolloutParameters p Own =>
                ((localHistoryOfRun
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val j u).1,
                  (⟨(localHistoryOfRun
                      (boundedLocalPrefix p D x.1 x.2 r n
                        (Nat.le_of_succ_le hn)).val j u).2,
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property u j⟩ :
                    SparseCalendarReward)))
              have hsubtype : Measurable (fun x : RolloutParameters p Own =>
                  (⟨(boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val.feedback u j,
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property u j⟩ :
                    SparseCalendarReward)) :=
                (hprevFeedback u j).subtype_mk
                  (h := fun x => (boundedLocalPrefix p D x.1 x.2 r n
                    (Nat.le_of_succ_le hn)).property u j)
              exact (hprevAction u j).prodMk hsubtype
            have hcurrent (j : Fin p.m) :
                Measurable fun x : RolloutParameters p Own => currentActions x j := by
              dsimp [currentActions]
              have hprivate : Measurable fun x : RolloutParameters p Own =>
                  x.2 j := (measurable_pi_apply j).comp measurable_snd
              have hargs : Measurable fun x : RolloutParameters p Own =>
                  (x.1, (x.2 j, boundedHistoryOfRun p
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).val
                    (boundedLocalPrefix p D x.1 x.2 r n
                      (Nat.le_of_succ_le hn)).property j)) :=
                measurable_fst.prodMk (hprivate.prodMk (hhistory j))
              exact (hD j ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩).comp hargs
            have hactions : Measurable currentActions :=
              measurable_pi_iff.mpr hcurrent
            have hfeedbackMap : Measurable
                (fun a : ActionProfile p.m p.K =>
                  playerFeedback a
                    (r.reward ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩) i) :=
              measurable_of_finite _
            have hfeedback : Measurable fun x : RolloutParameters p Own =>
                playerFeedback (currentActions x)
                  (r.reward ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩) i :=
              hfeedbackMap.comp hactions
            have hlast :
                (fun x : RolloutParameters p Own =>
                  (boundedLocalPrefix p D x.1 x.2 r (n + 1) hn).val.feedback
                    (Fin.last n) i) =
                (fun x => playerFeedback (currentActions x)
                  (r.reward ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩) i) := by
              funext x
              exact boundedLocalPrefix_feedback_last p D x.1 x.2 r n hn i
            rw [hlast]
            exact hfeedback

/-- Every action coordinate of every bounded prefix is jointly measurable. -/
theorem boundedLocalPrefix_action_measurable
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t))
    (n : ℕ) (hn : n ≤ p.T) (s : Fin n) (i : Fin p.m) :
    Measurable fun x : RolloutParameters p Own =>
      (boundedLocalPrefix p D x.1 x.2 r n hn).val.action s i :=
  (boundedLocalPrefix_measurable_internal p D r hD n hn).1 s i

/-- Every feedback coordinate of every bounded prefix is jointly measurable. -/
theorem boundedLocalPrefix_feedback_measurable
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t))
    (n : ℕ) (hn : n ≤ p.T) (s : Fin n) (i : Fin p.m) :
    Measurable fun x : RolloutParameters p Own =>
      (boundedLocalPrefix p D x.1 x.2 r n hn).val.feedback s i :=
  (boundedLocalPrefix_measurable_internal p D r hD n hn).2 s i

/-- Each extracted bounded own history is jointly measurable in the public
output and all private coordinates. -/
theorem boundedLocalPrefix_history_measurable
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t))
    (n : ℕ) (hn : n ≤ p.T) (i : Fin p.m) :
    Measurable fun x : RolloutParameters p Own =>
      boundedHistoryOfRun p
        (boundedLocalPrefix p D x.1 x.2 r n hn).val
        (boundedLocalPrefix p D x.1 x.2 r n hn).property i := by
  rw [measurable_pi_iff]
  intro s
  change Measurable (fun x : RolloutParameters p Own =>
    ((localHistoryOfRun
        (boundedLocalPrefix p D x.1 x.2 r n hn).val i s).1,
      (⟨(localHistoryOfRun
          (boundedLocalPrefix p D x.1 x.2 r n hn).val i s).2,
        (boundedLocalPrefix p D x.1 x.2 r n hn).property s i⟩ :
          SparseCalendarReward)))
  have haction := boundedLocalPrefix_action_measurable p D r hD n hn s i
  have hfeedback := boundedLocalPrefix_feedback_measurable p D r hD n hn s i
  have hsubtype : Measurable (fun x : RolloutParameters p Own =>
      (⟨(boundedLocalPrefix p D x.1 x.2 r n hn).val.feedback s i,
        (boundedLocalPrefix p D x.1 x.2 r n hn).property s i⟩ :
          SparseCalendarReward)) :=
    hfeedback.subtype_mk
      (h := fun x => (boundedLocalPrefix p D x.1 x.2 r n hn).property s i)
  exact haction.prodMk hsubtype

/-- The actual payoff of a finite bounded-local run uses the existing sum over
all players' observed feedback on the full reward horizon. -/
noncomputable def pathwisePayoff (D : FiniteBoundedLocalDecision p Own)
    (pub : PublishedOutput p) (rho : PrivateProfile p Own)
    (r : RewardMatrix p.T p.K) : ℝ :=
  pathwiseCumulativeReward (boundedLocalPrefix p D pub rho r p.T (Nat.le_refl p.T)).val

/-- Literal pathwise regret uses the existing best fixed-set comparator. -/
noncomputable def pathwiseRegret (D : FiniteBoundedLocalDecision p Own)
    (pub : PublishedOutput p) (rho : PrivateProfile p Own)
    (r : RewardMatrix p.T p.K) : ℝ :=
  MeasurableLocalRollout.pathwiseRegret (ConstructorDimensions.m_pos p) p.m_lt_K.le r
    (boundedLocalPrefix p D pub rho r p.T (Nat.le_refl p.T)).val

/-- Joint measurability of the full-horizon payoff for a fixed whole reward
matrix. -/
theorem pathwisePayoff_measurable
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t)) :
    Measurable fun x : RolloutParameters p Own =>
      pathwisePayoff p D x.1 x.2 r := by
  unfold pathwisePayoff
  apply Finset.measurable_sum
  intro t ht
  apply Finset.measurable_sum
  intro i hi
  exact boundedLocalPrefix_feedback_measurable p D r hD p.T
    (Nat.le_refl p.T) t i

/-- Joint measurability of pathwise regret, with the same comparator as the
existing finite rollout. -/
theorem pathwiseRegret_measurable
    [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t)) :
    Measurable fun x : RolloutParameters p Own =>
      pathwiseRegret p D x.1 x.2 r := by
  exact measurable_const.sub (pathwisePayoff_measurable p D r hD)

/-- Every constructed pathwise payoff is in the finite-horizon interval
[0,mT]. -/
theorem pathwisePayoff_mem_Icc
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K) :
    pathwisePayoff p D pub rho r ∈ Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  unfold pathwisePayoff
  apply pathwiseCumulativeReward_mem_Icc
  intro t i
  exact (boundedLocalPrefix p D pub rho r p.T (Nat.le_refl p.T)).property t i

/-- Every constructed pathwise regret is in [-mT,mT]. -/
theorem pathwiseRegret_mem_Icc
    (D : FiniteBoundedLocalDecision p Own) (pub : PublishedOutput p)
    (rho : PrivateProfile p Own) (r : RewardMatrix p.T p.K) :
    pathwiseRegret p D pub rho r ∈
      Set.Icc (-((p.m : ℝ) * (p.T : ℝ))) ((p.m : ℝ) * (p.T : ℝ)) := by
  unfold pathwiseRegret
  exact MeasurableLocalRollout.pathwiseRegret_mem_Icc
    (ConstructorDimensions.m_pos p) p.m_lt_K.le r
    (boundedLocalPrefix p D pub rho r p.T (Nat.le_refl p.T)).val
    (fun t i => (boundedLocalPrefix p D pub rho r p.T
      (Nat.le_refl p.T)).property t i)

/-- The independent product law of explicitly supplied player-specific
private probability measures. -/
noncomputable def privateProfileLaw {Own : Fin p.m → Type*}
    [∀ i, MeasurableSpace (Own i)] (nu : ∀ i, Measure (Own i)) :
    Measure (PrivateProfile p Own) := Measure.pi nu

/-- The product of the supplied private probability laws is a probability
measure. -/
instance privateProfileLaw_isProbabilityMeasure {Own : Fin p.m → Type*}
    [∀ i, MeasurableSpace (Own i)] (nu : ∀ i, Measure (Own i))
    [∀ i, IsProbabilityMeasure (nu i)] :
    IsProbabilityMeasure (privateProfileLaw p nu) := by
  change IsProbabilityMeasure (Measure.pi nu)
  infer_instance

/-- The regret of the produced full-horizon environment integrates over the
explicit independent private profile law only. -/
noncomputable def expectedPrivateRegret
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (pub : PublishedOutput p) : ℝ :=
  ∫ rho, pathwiseRegret p D pub rho r ∂privateProfileLaw p nu

/-- The expected payoff over the same explicit product law. -/
noncomputable def expectedPrivatePayoff
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (pub : PublishedOutput p) : ℝ :=
  ∫ rho, pathwisePayoff p D pub rho r ∂privateProfileLaw p nu

/-- The private-regret integrand is integrable from its produced bound and the
explicit product probability law. -/
theorem pathwiseRegret_integrable
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t))
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (pub : PublishedOutput p) :
    Integrable (fun rho => pathwiseRegret p D pub rho r) (privateProfileLaw p nu) := by
  have hmeas := pathwiseRegret_measurable p D r hD
  have huncurry : Measurable (Function.uncurry fun pub' rho =>
      pathwiseRegret p D pub' rho r) := by
    change Measurable fun x : RolloutParameters p Own =>
      pathwiseRegret p D x.1 x.2 r
    exact hmeas
  have hsection : Measurable fun rho : PrivateProfile p Own =>
      pathwiseRegret p D pub rho r := huncurry.of_uncurry_left
  have hbound : ∀ rho, ‖pathwiseRegret p D pub rho r‖ ≤
      (p.m : ℝ) * (p.T : ℝ) := by
    intro rho
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (pathwiseRegret_mem_Icc p D pub rho r)
  exact Integrable.of_bound hsection.aestronglyMeasurable
    ((p.m : ℝ) * (p.T : ℝ)) (ae_of_all _ hbound)

/-- The private-payoff integrand is integrable from its produced [0,mT]
bound and the explicit product probability law. -/
theorem pathwisePayoff_integrable
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own) (r : RewardMatrix p.T p.K)
    (hD : ∀ i t, Measurable (D i t))
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (pub : PublishedOutput p) :
    Integrable (fun rho => pathwisePayoff p D pub rho r) (privateProfileLaw p nu) := by
  have hmeas := pathwisePayoff_measurable p D r hD
  have huncurry : Measurable (Function.uncurry fun pub' rho =>
      pathwisePayoff p D pub' rho r) := by
    change Measurable fun x : RolloutParameters p Own =>
      pathwisePayoff p D x.1 x.2 r
    exact hmeas
  have hsection : Measurable fun rho : PrivateProfile p Own =>
      pathwisePayoff p D pub rho r := huncurry.of_uncurry_left
  have hbound : ∀ rho, ‖pathwisePayoff p D pub rho r‖ ≤
      (p.m : ℝ) * (p.T : ℝ) := by
    intro rho
    rw [Real.norm_eq_abs]
    have hpay := pathwisePayoff_mem_Icc p D pub rho r
    apply abs_le.mpr
    constructor
    · have hnonneg : 0 ≤ (p.m : ℝ) * (p.T : ℝ) := by positivity
      linarith [hnonneg, hpay.1]
    · exact hpay.2
  exact Integrable.of_bound hsection.aestronglyMeasurable
    ((p.m : ℝ) * (p.T : ℝ)) (ae_of_all _ hbound)

/-- The expected private payoff inherits the pathwise [0,mT] interval. -/
theorem expectedPrivatePayoff_mem_Icc
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (pub : PublishedOutput p)
    (hD : ∀ i t, Measurable (D i t)) :
    expectedPrivatePayoff p D nu r pub ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  let B : ℝ := (p.m : ℝ) * (p.T : ℝ)
  have hpay := pathwisePayoff_integrable p D r hD nu pub
  have hlow : 0 ≤ expectedPrivatePayoff p D nu r pub := by
    rw [expectedPrivatePayoff]
    calc
      (0 : ℝ) = ∫ _ : PrivateProfile p Own, (0 : ℝ) ∂privateProfileLaw p nu := by
        simp [privateProfileLaw]
      _ ≤ ∫ rho, pathwisePayoff p D pub rho r ∂privateProfileLaw p nu := by
        apply integral_mono (integrable_const _) hpay
        intro rho
        exact (pathwisePayoff_mem_Icc p D pub rho r).1
  have hhigh : expectedPrivatePayoff p D nu r pub ≤ B := by
    rw [expectedPrivatePayoff]
    calc
      (∫ rho, pathwisePayoff p D pub rho r ∂privateProfileLaw p nu) ≤
          ∫ _ : PrivateProfile p Own, B ∂privateProfileLaw p nu := by
        apply integral_mono hpay (integrable_const _)
        intro rho
        simpa [B] using (pathwisePayoff_mem_Icc p D pub rho r).2
      _ = B := by simp [privateProfileLaw, B]
  exact ⟨by simpa [B] using hlow, by simpa [B] using hhigh⟩

/-- Expected private regret inherits the same [-mT,mT] bound. -/
theorem expectedPrivateRegret_mem_Icc
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (pub : PublishedOutput p)
    (hD : ∀ i t, Measurable (D i t)) :
    expectedPrivateRegret p D nu r pub ∈
      Set.Icc (-((p.m : ℝ) * (p.T : ℝ))) ((p.m : ℝ) * (p.T : ℝ)) := by
  let B : ℝ := (p.m : ℝ) * (p.T : ℝ)
  have hreg := pathwiseRegret_integrable p D r hD nu pub
  have hlow : -B ≤ expectedPrivateRegret p D nu r pub := by
    rw [expectedPrivateRegret]
    calc
      -B = ∫ _ : PrivateProfile p Own, (-B : ℝ) ∂privateProfileLaw p nu := by
        simp [privateProfileLaw, B]
      _ ≤ ∫ rho, pathwiseRegret p D pub rho r ∂privateProfileLaw p nu := by
        apply integral_mono (integrable_const _) hreg
        intro rho
        simpa [B] using (pathwiseRegret_mem_Icc p D pub rho r).1
  have hhigh : expectedPrivateRegret p D nu r pub ≤ B := by
    rw [expectedPrivateRegret]
    calc
      (∫ rho, pathwiseRegret p D pub rho r ∂privateProfileLaw p nu) ≤
          ∫ _ : PrivateProfile p Own, (B : ℝ) ∂privateProfileLaw p nu := by
        apply integral_mono hreg (integrable_const _)
        intro rho
        simpa [B] using (pathwiseRegret_mem_Icc p D pub rho r).2
      _ = B := by simp [privateProfileLaw, B]
  exact ⟨by simpa [B] using hlow, by simpa [B] using hhigh⟩

/-- Integrating literal pathwise regret is comparator minus expected payoff,
with the comparator fixed outside the private integral. -/
theorem expectedPrivateRegret_eq_comparator_sub_expectedPrivatePayoff
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (pub : PublishedOutput p)
    (hD : ∀ i t, Measurable (D i t)) :
    expectedPrivateRegret p D nu r pub =
      bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r -
        expectedPrivatePayoff p D nu r pub := by
  rw [expectedPrivateRegret, expectedPrivatePayoff]
  have hpay := pathwisePayoff_integrable p D r hD nu pub
  have hconst : Integrable
      (fun _ : PrivateProfile p Own =>
        bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r)
      (privateProfileLaw p nu) := integrable_const _
  calc
    (∫ rho, pathwiseRegret p D pub rho r ∂privateProfileLaw p nu) =
        ∫ rho,
          (bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r -
            pathwisePayoff p D pub rho r) ∂privateProfileLaw p nu := by
          congr 1
    _ = (∫ rho, bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r
          ∂privateProfileLaw p nu) -
        ∫ rho, pathwisePayoff p D pub rho r ∂privateProfileLaw p nu :=
          integral_sub hconst hpay
    _ = bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r -
        ∫ rho, pathwisePayoff p D pub rho r ∂privateProfileLaw p nu := by
          simp [privateProfileLaw]

/-- Expected private regret is measurable in the public output for a fixed
whole reward matrix and the explicitly supplied private product law. -/
theorem expectedPrivateRegret_measurable
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (hD : ∀ i t, Measurable (D i t)) :
    Measurable fun pub => expectedPrivateRegret p D nu r pub := by
  have hreg := pathwiseRegret_measurable p D r hD
  simpa [expectedPrivateRegret, privateProfileLaw] using
    (hreg.stronglyMeasurable.integral_prod_right').measurable

/-- Expected private payoff is measurable in the public output for a fixed
whole reward matrix and the explicitly supplied private product law. -/
theorem expectedPrivatePayoff_measurable
    {Own : Fin p.m → Type*} [∀ i, MeasurableSpace (Own i)]
    (D : FiniteBoundedLocalDecision p Own)
    (nu : ∀ i, Measure (Own i)) [∀ i, IsProbabilityMeasure (nu i)]
    (r : RewardMatrix p.T p.K) (hD : ∀ i t, Measurable (D i t)) :
    Measurable fun pub => expectedPrivatePayoff p D nu r pub := by
  have hpay := pathwisePayoff_measurable p D r hD
  simpa [expectedPrivatePayoff, privateProfileLaw] using
    (hpay.stronglyMeasurable.integral_prod_right').measurable

/-- Restrict a general local decision function to the finite bounded-history
carrier by erasing only the reward subtype proof. -/
def restrictDecision {A : Type*}
    (d : PlayerLocalDecision p.m p.K (PublishedOutput p) A)
    (i : Fin p.m) (t : Fin p.T) :
    PublishedOutput p × (A × BoundedHistory p t.val) → Fin p.K :=
  fun x => d i t.val x.1 (eraseBounded p x.2.2) x.2.1

/-- The bounded-history constructor agrees with the existing general rollout
when finite decisions are restrictions of a common private-carrier policy. -/
theorem boundedLocalPrefix_eq_deterministicRolloutPrefix
    {A : Type*}
    (d : PlayerLocalDecision p.m p.K (PublishedOutput p) A)
    (pub : PublishedOutput p) (rho : (i : Fin p.m) → A)
    (r : RewardMatrix p.T p.K) :
    ∀ n hn,
      (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
        pub rho r n hn).val =
      deterministicRolloutPrefix d pub rho r n hn := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn
      rfl
  | succ n ih =>
      intro hn
      let hn' : n ≤ p.T := Nat.le_of_succ_le hn
      have hprev := ih hn'
      apply congrArg₂ (fun a f =>
        (⟨a, f⟩ : RunPrefix p.m p.K (n + 1)))
      · funext s i
        cases s using Fin.lastCases with
        | cast s =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun run : RunPrefix p.m p.K n => run.action s i) hprev
        | last =>
            simp only [Fin.snoc_last]
            have hhist :
                eraseBounded p (boundedHistoryOfRun p
                  (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                    pub rho r n hn').val
                  (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                    pub rho r n hn').property i) =
                localHistoryOfRun
                  (deterministicRolloutPrefix d pub rho r n hn') i := by
              rw [erase_boundedHistoryOfRun]
              exact congrArg (fun run : RunPrefix p.m p.K n =>
                localHistoryOfRun run i) hprev
            simp [restrictDecision, hhist]
      · funext s i
        cases s using Fin.lastCases with
        | cast s =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun run : RunPrefix p.m p.K n => run.feedback s i) hprev
        | last =>
            simp only [Fin.snoc_last]
            have hactions :
                (fun j => restrictDecision p d j
                    ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
                    (pub, (rho j, boundedHistoryOfRun p
                      (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                        pub rho r n hn').val
                      (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                        pub rho r n hn').property j))) =
                (fun j => d j n pub
                  (localHistoryOfRun
                    (deterministicRolloutPrefix d pub rho r n hn') j) (rho j)) := by
              funext j
              have hhist :
                  eraseBounded p (boundedHistoryOfRun p
                    (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                      pub rho r n hn').val
                    (boundedLocalPrefix p (fun i t => restrictDecision p d i t)
                      pub rho r n hn').property j) =
                  localHistoryOfRun
                    (deterministicRolloutPrefix d pub rho r n hn') j := by
                rw [erase_boundedHistoryOfRun]
                exact congrArg (fun run : RunPrefix p.m p.K n =>
                  localHistoryOfRun run j) hprev
              simp [restrictDecision, hhist]
            rw [hactions]
            have htime :
                (⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩ : Fin p.T) =
                  Fin.castLE hn (Fin.last n) := by
              apply Fin.ext
              rfl
            rw [htime]

end Bandits.Support.FiniteHorizonBoundedLocalRollout

end
