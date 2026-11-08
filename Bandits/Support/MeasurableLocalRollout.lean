module

public import Bandits.Support.FiniteBanditModel
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Tactic.Linarith

/-!
# Measurability and private expectation for the finite local rollout

The regret convention is the best fixed set of `m` arms minus total realized
collision-filtered feedback (`sources/zip4/manuscript/01_introduction.tex:20-36`).
The manuscript takes this expectation over private execution randomness after
fixing public data and the reward matrix. This module proves an internal
measurable-rollout adapter for the existing deterministic finite rollout. Its
measurable policy premise is explicit; it does not establish measurability of
the manuscript protocol or any complete-row concentration claim. The reference
initialization and conditional complete-row quantity motivating later use are
described in `sources/zip4/manuscript/07_public_setup.tex:121-144` and
`sources/zip4/manuscript/08_main_theorem.tex:26-50`; those protocol-specific
objects are not defined or certified here.
-/

@[expose] public section

namespace Bandits.Support.MeasurableLocalRollout

open MeasureTheory
open Bandits.Support.FiniteBanditModel

/-- The parameter space for a rollout: one public datum and one private input
coordinate for each player. -/
abbrev RolloutParameter (m : ℕ) (PublicData PrivateInput : Type*) :=
  PublicData × (Player m → PrivateInput)

/-- The independent product law of all player-local private inputs. -/
noncomputable def privateProfileLaw {m : ℕ} {PrivateInput : Type*} [MeasurableSpace PrivateInput]
    (nu : Player m → Measure PrivateInput) : Measure (Player m → PrivateInput) :=
  Measure.pi nu

/-- The independent product of player probability laws is itself a probability
law. -/
instance privateProfileLaw_isProbabilityMeasure {m : ℕ} {PrivateInput : Type*}
    [MeasurableSpace PrivateInput] (nu : Player m → Measure PrivateInput)
    [∀ i, IsProbabilityMeasure (nu i)] : IsProbabilityMeasure (privateProfileLaw nu) := by
  change IsProbabilityMeasure (Measure.pi nu)
  infer_instance

/-- Literal pathwise regret of a run: the existing best fixed `m`-set
comparator minus the cumulative feedback actually received in the run. -/
noncomputable def pathwiseRegret {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) (run : RunPrefix m K T) : ℝ :=
  bestFixedMSetComparator hm hmK rewards - pathwiseCumulativeReward run

/-- Every rollout pathwise regret lies in `[-mT,mT]`, from the accepted
physical feedback and comparator bounds. -/
theorem pathwiseRegret_mem_Icc {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) (run : RunPrefix m K T)
    (hfeedback : ∀ t i, run.feedback t i ∈ Set.Icc (0 : ℝ) 1) :
    pathwiseRegret hm hmK rewards run ∈
      Set.Icc (-((m : ℝ) * (T : ℝ))) ((m : ℝ) * (T : ℝ)) := by
  have hcomp := bestFixedMSetComparator_mem_Icc hm hmK rewards
  have hrun := pathwiseCumulativeReward_mem_Icc run hfeedback
  rcases hcomp with ⟨hcomp₀, hcomp₁⟩
  rcases hrun with ⟨hrun₀, hrun₁⟩
  change bestFixedMSetComparator hm hmK rewards - pathwiseCumulativeReward run ∈ _
  simp only [Set.mem_Icc]
  constructor <;> linarith

/-- The exact finite collision test and reward lookup are measurable when each
player action coordinate is measurable. -/
private theorem measurablePlayerFeedback {α : Type*} [MeasurableSpace α]
    {m K : ℕ} (actions : α → ActionProfile m K)
    (hactions : ∀ j, Measurable fun x => actions x j)
    (rewards : Arm K → ℝ) (i : Player m) :
    Measurable fun x => playerFeedback (actions x) rewards i := by
  classical
  have hcollision : MeasurableSet {x | collisionFreeFor (actions x) i} := by
    have hcondition (j : Player m) :
        MeasurableSet {x | j = i ∨ actions x j ≠ actions x i} := by
      by_cases hji : j = i
      · simp [hji]
      · have hneq : MeasurableSet {x | actions x j ≠ actions x i} :=
          (measurableSet_eq_fun (hactions j) (hactions i)).compl
        simpa [hji] using hneq
    have hset : {x : α | collisionFreeFor (actions x) i} =
        Set.iInter (fun j : Player m => {x : α | j = i ∨ actions x j ≠ actions x i}) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr (h j hji)
      · intro h j hji
        rcases h j with hji' | hne
        · exact (hji hji').elim
        · exact hne
    rw [hset]
    exact MeasurableSet.iInter hcondition
  have hreward : Measurable fun x => rewards (actions x i) :=
    (Measurable.of_discrete (f := rewards)).comp (hactions i)
  unfold playerFeedback
  exact Measurable.ite hcollision hreward measurable_const

/-- Inductive measurability invariant for every action and every feedback
coordinate of the existing recursively constructed prefix. -/
private theorem deterministicRolloutPrefix_measurable_internal
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2)) :
    ∀ (t : ℕ) (ht : t ≤ T),
      (∀ (s : Fin t) (i : Player m),
        Measurable fun x : RolloutParameter m PublicData PrivateInput =>
          (deterministicRolloutPrefix decide x.1 x.2 rewards t ht).action s i) ∧
      (∀ (s : Fin t) (i : Player m),
        Measurable fun x : RolloutParameter m PublicData PrivateInput =>
          (deterministicRolloutPrefix decide x.1 x.2 rewards t ht).feedback s i) := by
  intro t
  induction t with
  | zero =>
      intro ht
      constructor
      · intro s
        exact Fin.elim0 s
      · intro s
        exact Fin.elim0 s
  | succ t ih =>
      intro ht
      obtain ⟨hprevAction, hprevFeedback⟩ := ih (Nat.le_of_succ_le ht)
      constructor
      · intro s i
        cases s using Fin.lastCases with
        | last =>
            have hlast :
                (fun x : RolloutParameter m PublicData PrivateInput =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards (t + 1) ht).action
                    (Fin.last t) i) =
                (fun x => decide i t x.1
                  (localHistoryOfRun
                    (deterministicRolloutPrefix decide x.1 x.2 rewards t
                      (Nat.le_of_succ_le ht)) i)
                  (x.2 i)) := by
              funext x
              exact deterministicRolloutPrefix_action_last decide x.1 x.2 rewards t ht i
            rw [hlast]
            have hhistory : Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                localHistoryOfRun
                  (deterministicRolloutPrefix decide x.1 x.2 rewards t
                    (Nat.le_of_succ_le ht)) i := by
              rw [measurable_pi_iff]
              intro u
              change Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                ((deterministicRolloutPrefix decide x.1 x.2 rewards t
                  (Nat.le_of_succ_le ht)).action u i,
                 (deterministicRolloutPrefix decide x.1 x.2 rewards t
                  (Nat.le_of_succ_le ht)).feedback u i)
              exact (hprevAction u i).prodMk (hprevFeedback u i)
            have hprivate : Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                x.2 i := (measurable_pi_apply i).comp measurable_snd
            have hargs : Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                (x.1, (localHistoryOfRun
                  (deterministicRolloutPrefix decide x.1 x.2 rewards t
                    (Nat.le_of_succ_le ht)) i, x.2 i)) :=
              measurable_fst.prodMk (hhistory.prodMk hprivate)
            exact (hdecide i t).comp hargs
        | cast s =>
            have hcast :
                (fun x : RolloutParameter m PublicData PrivateInput =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards (t + 1) ht).action
                    s.castSucc i) =
                (fun x =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards t
                    (Nat.le_of_succ_le ht)).action s i) := by
              funext x
              exact deterministicRolloutPrefix_action_castSucc decide x.1 x.2 rewards t ht s i
            rw [hcast]
            exact hprevAction s i
      · intro s i
        cases s using Fin.lastCases with
        | last =>
            have hhistory (j : Player m) :
                Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                  localHistoryOfRun
                    (deterministicRolloutPrefix decide x.1 x.2 rewards t
                      (Nat.le_of_succ_le ht)) j := by
              rw [measurable_pi_iff]
              intro u
              change Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                ((deterministicRolloutPrefix decide x.1 x.2 rewards t
                  (Nat.le_of_succ_le ht)).action u j,
                 (deterministicRolloutPrefix decide x.1 x.2 rewards t
                  (Nat.le_of_succ_le ht)).feedback u j)
              exact (hprevAction u j).prodMk (hprevFeedback u j)
            let currentActions : RolloutParameter m PublicData PrivateInput → ActionProfile m K :=
              fun x j => decide j t x.1
                (localHistoryOfRun
                  (deterministicRolloutPrefix decide x.1 x.2 rewards t
                    (Nat.le_of_succ_le ht)) j)
                (x.2 j)
            have hlast :
                (fun x : RolloutParameter m PublicData PrivateInput =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards (t + 1) ht).feedback
                    (Fin.last t) i) =
                (fun x => playerFeedback (currentActions x)
                  (rewards.reward (Fin.castLE ht (Fin.last t))) i) := by
              funext x
              simpa [currentActions] using
                (deterministicRolloutPrefix_feedback_last decide x.1 x.2 rewards t ht i)
            rw [hlast]
            have hcurrent (j : Player m) :
                Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                  currentActions x j := by
              dsimp [currentActions]
              have hprivate : Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                  x.2 j := (measurable_pi_apply j).comp measurable_snd
              have hargs : Measurable fun x : RolloutParameter m PublicData PrivateInput =>
                  (x.1, (localHistoryOfRun
                    (deterministicRolloutPrefix decide x.1 x.2 rewards t
                      (Nat.le_of_succ_le ht)) j, x.2 j)) :=
                measurable_fst.prodMk ((hhistory j).prodMk hprivate)
              exact (hdecide j t).comp hargs
            have hfb := measurablePlayerFeedback currentActions hcurrent
              (rewards.reward (Fin.castLE ht (Fin.last t))) i
            simpa [currentActions] using hfb
        | cast s =>
            have hcast :
                (fun x : RolloutParameter m PublicData PrivateInput =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards (t + 1) ht).feedback
                    s.castSucc i) =
                (fun x =>
                  (deterministicRolloutPrefix decide x.1 x.2 rewards t
                    (Nat.le_of_succ_le ht)).feedback s i) := by
              funext x
              exact deterministicRolloutPrefix_feedback_castSucc decide x.1 x.2 rewards t ht s i
            rw [hcast]
            exact hprevFeedback s i

/-- Every action coordinate in every prefix is jointly measurable in the
public datum and the complete vector of independent private inputs. -/
theorem deterministicRolloutPrefix_action_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (t : ℕ) (ht : t ≤ T) (s : Fin t) (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      (deterministicRolloutPrefix decide x.1 x.2 rewards t ht).action s i :=
  (deterministicRolloutPrefix_measurable_internal decide rewards hdecide t ht).1 s i

/-- Every feedback coordinate in every prefix is jointly measurable; the proof
uses the rollout's literal finite collision test. -/
theorem deterministicRolloutPrefix_feedback_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (t : ℕ) (ht : t ≤ T) (s : Fin t) (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      (deterministicRolloutPrefix decide x.1 x.2 rewards t ht).feedback s i :=
  (deterministicRolloutPrefix_measurable_internal decide rewards hdecide t ht).2 s i

/-- Every extracted local history in every prefix is jointly measurable. -/
theorem deterministicRolloutPrefix_localHistory_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (t : ℕ) (ht : t ≤ T) (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      localHistoryOfRun
        (deterministicRolloutPrefix decide x.1 x.2 rewards t ht) i := by
  rw [measurable_pi_iff]
  intro s
  change Measurable fun x : RolloutParameter m PublicData PrivateInput =>
    ((deterministicRolloutPrefix decide x.1 x.2 rewards t ht).action s i,
     (deterministicRolloutPrefix decide x.1 x.2 rewards t ht).feedback s i)
  exact (deterministicRolloutPrefix_action_measurable decide rewards hdecide t ht s i).prodMk
    (deterministicRolloutPrefix_feedback_measurable decide rewards hdecide t ht s i)

/-- Every action coordinate of the complete rollout is jointly measurable. -/
theorem deterministicRollout_action_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (s : Fin T) (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      (deterministicRollout decide x.1 x.2 rewards).action s i := by
  exact deterministicRolloutPrefix_action_measurable decide rewards hdecide T
    (Nat.le_refl T) s i

/-- Every feedback coordinate of the complete rollout is jointly measurable. -/
theorem deterministicRollout_feedback_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (s : Fin T) (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      (deterministicRollout decide x.1 x.2 rewards).feedback s i := by
  exact deterministicRolloutPrefix_feedback_measurable decide rewards hdecide T
    (Nat.le_refl T) s i

/-- Every extracted local history of the complete rollout is jointly measurable. -/
theorem deterministicRollout_localHistory_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (i : Player m) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      localHistoryOfRun (deterministicRollout decide x.1 x.2 rewards) i := by
  exact deterministicRolloutPrefix_localHistory_measurable decide rewards hdecide T
    (Nat.le_refl T) i

/-- The cumulative feedback of the complete rollout is jointly measurable. -/
theorem deterministicRollout_pathwiseCumulativeReward_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2)) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      pathwiseCumulativeReward (deterministicRollout decide x.1 x.2 rewards) := by
  apply Finset.measurable_sum
  intro s hs
  apply Finset.measurable_sum
  intro i hi
  exact deterministicRollout_feedback_measurable decide rewards hdecide s i

/-- Literal pathwise regret of the existing complete rollout is jointly
measurable in public data and all player-local private inputs. -/
theorem deterministicRollout_pathwiseRegret_measurable
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2)) :
    Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      pathwiseRegret hm hmK rewards (deterministicRollout decide x.1 x.2 rewards) := by
  exact measurable_const.sub
    (deterministicRollout_pathwiseCumulativeReward_measurable decide rewards hdecide)

/-- The actual private-profile expected regret at fixed public datum and fixed
reward matrix. Its law is the independent product `Measure.pi` of the players'
private-input probability laws. -/
noncomputable def expectedPrivateRegret {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (nu : Player m → Measure PrivateInput)
    [∀ i, IsProbabilityMeasure (nu i)] (publicData : PublicData) : ℝ :=
  ∫ privateInput,
    pathwiseRegret hm hmK rewards (deterministicRollout decide publicData privateInput rewards)
      ∂privateProfileLaw nu

/-- The private regret integrand is integrable, using only its physical
`[-mT,mT]` bound and the finite independent product probability measure. -/
theorem pathwiseRegret_integrable {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (nu : Player m → Measure PrivateInput)
    [∀ i, IsProbabilityMeasure (nu i)] (publicData : PublicData) :
    Integrable
      (fun privateInput =>
        pathwiseRegret hm hmK rewards
          (deterministicRollout decide publicData privateInput rewards))
      (privateProfileLaw nu) := by
  have hmeas := deterministicRollout_pathwiseRegret_measurable hm hmK decide rewards hdecide
  have huncurry : Measurable (Function.uncurry fun publicData' privateInput =>
      pathwiseRegret hm hmK rewards
        (deterministicRollout decide publicData' privateInput rewards)) := by
    change Measurable fun x : RolloutParameter m PublicData PrivateInput =>
      pathwiseRegret hm hmK rewards (deterministicRollout decide x.1 x.2 rewards)
    exact hmeas
  have hsection : Measurable fun privateInput : Player m → PrivateInput =>
      pathwiseRegret hm hmK rewards
        (deterministicRollout decide publicData privateInput rewards) :=
    huncurry.of_uncurry_left
  have hbound : ∀ privateInput, ‖pathwiseRegret hm hmK rewards
      (deterministicRollout decide publicData privateInput rewards)‖ ≤
        (m : ℝ) * (T : ℝ) := by
    intro privateInput
    have hreg := pathwiseRegret_mem_Icc hm hmK rewards
      (deterministicRollout decide publicData privateInput rewards)
      (fun t i => deterministicRollout_feedback_mem_Icc decide publicData privateInput rewards t i)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr hreg
  exact Integrable.of_bound hsection.aestronglyMeasurable ((m : ℝ) * (T : ℝ))
    (ae_of_all _ hbound)

/-- Private expected regret inherits the same `[-mT,mT]` bound. -/
theorem expectedPrivateRegret_mem_Icc {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (nu : Player m → Measure PrivateInput)
    [∀ i, IsProbabilityMeasure (nu i)] (publicData : PublicData) :
    expectedPrivateRegret hm hmK decide rewards nu publicData ∈
      Set.Icc (-((m : ℝ) * (T : ℝ))) ((m : ℝ) * (T : ℝ)) := by
  let B : ℝ := (m : ℝ) * (T : ℝ)
  have hreg := pathwiseRegret_integrable hm hmK decide rewards hdecide nu publicData
  have hlow : -B ≤ expectedPrivateRegret hm hmK decide rewards nu publicData := by
    rw [expectedPrivateRegret]
    calc
      -B = ∫ _ : Player m → PrivateInput, (-B : ℝ) ∂privateProfileLaw nu := by
        simp [privateProfileLaw, B]
      _ ≤ ∫ privateInput,
          pathwiseRegret hm hmK rewards
            (deterministicRollout decide publicData privateInput rewards)
            ∂privateProfileLaw nu := by
        apply integral_mono (integrable_const _) hreg
        intro privateInput
        have hbound := pathwiseRegret_mem_Icc hm hmK rewards
          (deterministicRollout decide publicData privateInput rewards)
          (fun t i => deterministicRollout_feedback_mem_Icc decide publicData privateInput
            rewards t i)
        simpa [B] using hbound.1
  have hhigh : expectedPrivateRegret hm hmK decide rewards nu publicData ≤ B := by
    rw [expectedPrivateRegret]
    calc
      (∫ privateInput,
          pathwiseRegret hm hmK rewards
            (deterministicRollout decide publicData privateInput rewards)
            ∂privateProfileLaw nu) ≤
        ∫ _ : Player m → PrivateInput, (B : ℝ) ∂privateProfileLaw nu := by
          apply integral_mono hreg (integrable_const _)
          intro privateInput
          have hbound := pathwiseRegret_mem_Icc hm hmK rewards
            (deterministicRollout decide publicData privateInput rewards)
            (fun t i => deterministicRollout_feedback_mem_Icc decide publicData privateInput
              rewards t i)
          simpa [B] using hbound.2
      _ = B := by simp [privateProfileLaw, B]
  change -((m : ℝ) * (T : ℝ)) ≤ expectedPrivateRegret hm hmK decide rewards nu publicData ∧
    expectedPrivateRegret hm hmK decide rewards nu publicData ≤ (m : ℝ) * (T : ℝ)
  exact ⟨by simpa [B] using hlow, by simpa [B] using hhigh⟩

/-- The private expected regret is measurable as a function of public data.
The reward matrix is fixed before integration, and the only integration is over
the independent private-profile law. -/
theorem expectedPrivateRegret_measurable {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (rewards : RewardMatrix T K)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (nu : Player m → Measure PrivateInput)
    [∀ i, IsProbabilityMeasure (nu i)] :
    Measurable fun publicData =>
      expectedPrivateRegret hm hmK decide rewards nu publicData := by
  have hreg := deterministicRollout_pathwiseRegret_measurable hm hmK decide rewards hdecide
  simpa [expectedPrivateRegret, privateProfileLaw] using
    (hreg.stronglyMeasurable.integral_prod_right').measurable

end Bandits.Support.MeasurableLocalRollout

end
