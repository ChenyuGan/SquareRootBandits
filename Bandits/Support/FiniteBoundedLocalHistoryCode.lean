/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteHistoryRewardReadouts
public import Bandits.Support.ExpectedRoundedRegret

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Bounded local histories and their finite grid codes

The source bounds each original reward and collision-filtered observation in
`sources/zip4/manuscript/01_introduction.tex:20-36`. It rounds observations
before local updates in `sources/zip4/manuscript/07_public_setup.tex:55-114`,
and compares original and rounded rewards on the same private outcome in
`sources/zip4/manuscript/08_main_theorem.tex:163-168`.

This module codes a supplied finite bounded history by applying the existing
floor quantizer to each observation. Decoding is exact on the existing typed
grid observations. On arbitrary bounded observations, decoding returns the
rounded value, so the floor fibres remain intact: bounded histories are not
identified with finite codes. This is a local-history coding result; it does
not define a policy, a rollout, an extension to unbounded histories, or a law.
-/

@[expose] public section

namespace Bandits.Support.FiniteBoundedLocalHistoryCode

open Bandits.Support.ConstructorDimensions
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FiniteBanditModel
open Classical

/-- Bounded local observations retain the existing subtype of real rewards in
`[0,1]`. -/
abbrev BoundedHistory (p : ConstructorDimensions.Parameters) (n : ℕ) :=
  Fin n → (Fin p.K × SparseCalendarReplay.SparseCalendarReward)

/-- A finite local-history code retains the arm and replaces each observation
by its denominator-`D p` grid index. -/
abbrev HistoryCode (p : ConstructorDimensions.Parameters) (n : ℕ) :=
  Fin n → (Fin p.K × Fin (D p + 1))

/-- The floor index of one bounded observation. This is the existing local
rollout quantizer, with the bound supplied by the observation subtype. -/
noncomputable def q (p : ConstructorDimensions.Parameters)
    (x : SparseCalendarReward) : Fin (D p + 1) :=
  RoundedLocalRollout.roundedIndex (D p) (D_pos p) x.val x.property

/-- Decode one finite grid index into the existing typed prelaunch observation. -/
noncomputable def g (p : ConstructorDimensions.Parameters) (k : Fin (D p + 1)) :
    ReferencePrelaunchFollower.Observation p :=
  ActualInitializationPhysicalStep.observationOfGrid p k

/-- Quantize each observation of a bounded history, retaining its chosen arm. -/
noncomputable def Q (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) : HistoryCode p n :=
  fun u => ((history u).1, q p (history u).2)

/-- Decode each finite code as an existing typed observation, retaining its arm. -/
noncomputable def L (p : ConstructorDimensions.Parameters) {n : ℕ}
    (code : HistoryCode p n) : ReferencePrelaunchFollower.LocalHistory p n :=
  fun u => ((code u).1, g p (code u).2)

/-- Forget only the grid-membership proof of each typed observation. The
bounded real-reward subtype and the arm are retained. -/
def forgetGrid (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) : BoundedHistory p n :=
  fun u => ((history u).1, ((history u).2).val)

/-- Erase the bounded reward subtype proof, leaving exactly the arm and real
observation in `FiniteBanditModel.LocalHistory`. -/
def eraseBounded (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) :
    FiniteBanditModel.LocalHistory p.K n :=
  fun u => ((history u).1, ((history u).2).val)

/-- Erase both observation subtype proofs from a typed grid history, leaving
exactly its arm and real observation. -/
def erase (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) :
    FiniteBanditModel.LocalHistory p.K n :=
  fun u => ((history u).1, ((history u).2).val.val)

/-- Forgetting grid membership leaves each recorded arm unchanged. -/
@[simp] theorem forgetGrid_arm (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) (u : Fin n) :
    (forgetGrid p history u).1 = (history u).1 := rfl

/-- Forgetting grid membership retains the complete bounded reward subtype. -/
@[simp] theorem forgetGrid_observation (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) (u : Fin n) :
    (forgetGrid p history u).2 = ((history u).2).val := rfl

/-- Erasure preserves each arm while dropping only the bounded reward proof. -/
@[simp] theorem erase_arm (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) (u : Fin n) :
    (eraseBounded p history u).1 = (history u).1 := rfl

/-- Erasure returns the underlying real value of the retained reward subtype. -/
@[simp] theorem erase_observation (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) (u : Fin n) :
    (eraseBounded p history u).2 = ((history u).2).val := rfl

/-- Typed erasure agrees with forgetting grid membership and then erasing the
bounded reward proof. -/
theorem erase_eq_eraseBounded_forgetGrid (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) :
    erase p history = eraseBounded p (forgetGrid p history) := rfl

/-- The value of the existing grid decoder. -/
theorem g_value (p : ConstructorDimensions.Parameters) (k : Fin (D p + 1)) :
    (g p k).val.val = (k.val : ℝ) / (D p : ℝ) :=
  ActualInitializationPhysicalStep.observationOfGrid_value p k

/-- The natural-number value selected by `q` is exactly the existing floor. -/
theorem q_val (p : ConstructorDimensions.Parameters) (x : SparseCalendarReward) :
    (q p x).val = Nat.floor ((D p : ℝ) * x.val) := rfl

/-- Quantizing an already decoded grid point returns its original code. -/
theorem q_g (p : ConstructorDimensions.Parameters) (k : Fin (D p + 1)) :
    q p (g p k).val = k := by
  apply Fin.ext
  change Nat.floor ((D p : ℝ) * ((k.val : ℝ) / (D p : ℝ))) = k.val
  have hD : (D p : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D_pos p)
  have hmul : (D p : ℝ) * ((k.val : ℝ) / (D p : ℝ)) = (k.val : ℝ) := by
    field_simp
  rw [hmul, Nat.floor_natCast]

/-- The zero reward is fixed by the finite code. -/
@[simp] theorem q_zero (p : ConstructorDimensions.Parameters) :
    q p (0 : SparseCalendarReward) = 0 := by
  apply Fin.ext
  simp [q, RoundedLocalRollout.roundedIndex]

/-- The top reward is fixed by the last finite code. -/
theorem q_one (p : ConstructorDimensions.Parameters) :
    q p (⟨1, by norm_num⟩ : SparseCalendarReward) = Fin.last (D p) := by
  apply Fin.ext
  simp [q, RoundedLocalRollout.roundedIndex, Fin.last]

/-- Distinct finite grid indices decode to distinct typed observations. -/
theorem g_injective (p : ConstructorDimensions.Parameters) :
    Function.Injective (g p) := by
  intro k l h
  apply RealRewardGridCount.realRewardGridValue_injective (D p) (D_pos p)
  have hv := congrArg (fun o : ReferencePrelaunchFollower.Observation p => o.val.val) h
  simpa only [g_value, RealRewardGridCount.realRewardGridValue] using hv

/-- Decoding after quantization returns the scalar rounded value from the
existing reward-rounding definition. -/
theorem g_q_value (p : ConstructorDimensions.Parameters) (x : SparseCalendarReward) :
    (g p (q p x)).val.val = RewardRounding.rounded (D p) x.val := rfl

/-- The exact floor fibre of one bounded observation. -/
theorem q_eq_iff (p : ConstructorDimensions.Parameters) (x : SparseCalendarReward)
    (k : Fin (D p + 1)) :
    q p x = k ↔ (k.val : ℝ) ≤ (D p : ℝ) * x.val ∧
      (D p : ℝ) * x.val < (k.val : ℝ) + 1 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [q_val] at hv
    exact (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) x.property.1)).mp hv
  · intro h
    apply Fin.ext
    exact (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) x.property.1)).mpr h

/-- A typed observation is the decoder of its unique finite grid index. -/
theorem g_q_observation (p : ConstructorDimensions.Parameters)
    (o : ReferencePrelaunchFollower.Observation p) :
    g p (q p o.val) = o := by
  rcases o.property with ⟨k, hk⟩
  have ho : o = g p k := by
    apply Subtype.ext
    apply Subtype.ext
    rw [g_value]
    exact hk
  rw [ho, q_g]

private def natToFinCode (p : ConstructorDimensions.Parameters) :
    ℕ → Fin (D p + 1) := fun j => ⟨j % (D p + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

private theorem q_eq_natToFinCode_floor (p : ConstructorDimensions.Parameters)
    (x : SparseCalendarReward) :
    q p x = natToFinCode p (Nat.floor ((D p : ℝ) * x.val)) := by
  apply Fin.ext
  change Nat.floor ((D p : ℝ) * x.val) =
    Nat.floor ((D p : ℝ) * x.val) % (D p + 1)
  exact (Nat.mod_eq_of_lt (q p x).isLt).symm

/-- The finite scalar code is measurable: its natural floor is Borel and the
subsequent map from naturals to finite codes is measurable. -/
theorem q_measurable (p : ConstructorDimensions.Parameters) :
    Measurable (q p) := by
  have hscale : Measurable (fun x : SparseCalendarReward => (D p : ℝ) * x.val) :=
    measurable_const.mul measurable_subtype_coe
  have hfloor : Measurable
      (fun x : SparseCalendarReward => Nat.floor ((D p : ℝ) * x.val)) :=
    Nat.measurable_floor.comp hscale
  have hcode : Measurable (natToFinCode p) := measurable_of_countable _
  rw [show q p = natToFinCode p ∘
      (fun x : SparseCalendarReward => Nat.floor ((D p : ℝ) * x.val)) from by
        funext x
        exact q_eq_natToFinCode_floor p x]
  exact hcode.comp hfloor

/-- Decoding is measurable because its finite code domain has the existing
discrete measurable structure. -/
theorem g_measurable (p : ConstructorDimensions.Parameters) : Measurable (g p) :=
  measurable_of_finite _

/-- Quantizing a bounded history is measurable for the existing subtype,
product, and finite-product measurable structures. -/
theorem Q_measurable (p : ConstructorDimensions.Parameters) {n : ℕ} :
    Measurable (Q p : BoundedHistory p n → HistoryCode p n) := by
  rw [measurable_pi_iff]
  intro u
  have hentry : Measurable (fun h : BoundedHistory p n => h u) := measurable_pi_apply u
  change Measurable (fun h : BoundedHistory p n => ((h u).1, q p (h u).2))
  exact (measurable_fst.comp hentry).prodMk
    ((q_measurable p).comp (measurable_snd.comp hentry))

/-- Decoding a finite history code is measurable for the existing product and
subtype measurable structures. -/
theorem L_measurable (p : ConstructorDimensions.Parameters) {n : ℕ} :
    Measurable (L p : HistoryCode p n → ReferencePrelaunchFollower.LocalHistory p n) := by
  rw [measurable_pi_iff]
  intro u
  have hentry : Measurable (fun h : HistoryCode p n => h u) := measurable_pi_apply u
  change Measurable (fun h : HistoryCode p n => ((h u).1, g p (h u).2))
  exact (measurable_fst.comp hentry).prodMk
    ((g_measurable p).comp (measurable_snd.comp hentry))

/-- Erasing the decoded quantized bounded history gives the existing rounded
real local history. -/
theorem erase_L_Q (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) :
    erase p (L p (Q p history)) =
      RoundedLocalRollout.roundLocalHistory (D p) (eraseBounded p history) := by
  funext u
  apply Prod.ext
  · rfl
  · exact g_q_value p ((history u).2)

/-- Encoding a decoded code after forgetting only its observation proof
recovers the same finite code. -/
theorem Q_forgetGrid_L (p : ConstructorDimensions.Parameters) {n : ℕ}
    (code : HistoryCode p n) : Q p (forgetGrid p (L p code)) = code := by
  funext u
  apply Prod.ext
  · rfl
  · exact q_g p (code u).2

/-- Decoding the code of any existing typed grid history recovers that history.
This inverse applies only on the supplied typed grid carrier. -/
theorem L_Q_forgetGrid (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : ReferencePrelaunchFollower.LocalHistory p n) :
    L p (Q p (forgetGrid p history)) = history := by
  funext u
  apply Prod.ext
  · rfl
  · exact g_q_observation p (history u).2

/-- `Q` preserves the recorded arm at every history position. -/
@[simp] theorem Q_arm (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n) (u : Fin n) :
    (Q p history u).1 = (history u).1 := rfl

/-- `L` preserves the recorded arm at every history position. -/
@[simp] theorem L_arm (p : ConstructorDimensions.Parameters) {n : ℕ}
    (code : HistoryCode p n) (u : Fin n) :
    (L p code u).1 = (code u).1 := rfl

/-- `Q` commutes with restriction along `Fin.castLE`. -/
theorem Q_castLE (p : ConstructorDimensions.Parameters) {m n : ℕ}
    (hmn : m ≤ n) (history : BoundedHistory p n) :
    Q p (fun u : Fin m => history (Fin.castLE hmn u)) =
      fun u : Fin m => Q p history (Fin.castLE hmn u) := rfl

/-- `L` commutes with restriction along `Fin.castLE`. -/
theorem L_castLE (p : ConstructorDimensions.Parameters) {m n : ℕ}
    (hmn : m ≤ n) (code : HistoryCode p n) :
    L p (fun u : Fin m => code (Fin.castLE hmn u)) =
      fun u : Fin m => L p code (Fin.castLE hmn u) := rfl

/-- `Q` commutes with appending one bounded arm-observation pair using
`Fin.snoc`. -/
theorem Q_snoc (p : ConstructorDimensions.Parameters) {n : ℕ}
    (history : BoundedHistory p n)
    (entry : Fin p.K × SparseCalendarReward) :
    Q p (Fin.snoc
      (α := fun _ : Fin (n + 1) => Fin p.K × SparseCalendarReward) history entry) =
      Fin.snoc (α := fun _ : Fin (n + 1) => Fin p.K × Fin (D p + 1))
        (Q p history) (entry.1, q p entry.2) := by
  change (fun x : Fin (n + 1) =>
      ((Fin.snoc (α := fun _ : Fin (n + 1) =>
        Fin p.K × SparseCalendarReward) history entry x).1,
        q p (Fin.snoc (α := fun _ : Fin (n + 1) =>
          Fin p.K × SparseCalendarReward) history entry x).2)) =
    Fin.snoc (α := fun _ : Fin (n + 1) => Fin p.K × Fin (D p + 1))
      (fun x : Fin n => ((history x).1, q p (history x).2))
      (entry.1, q p entry.2)
  exact Fin.comp_snoc (fun x : Fin p.K × SparseCalendarReward => (x.1, q p x.2))
    history entry

/-- `L` commutes with appending one finite arm-observation code using
`Fin.snoc`. -/
theorem L_snoc (p : ConstructorDimensions.Parameters) {n : ℕ}
    (code : HistoryCode p n) (entry : Fin p.K × Fin (D p + 1)) :
    L p (Fin.snoc
      (α := fun _ : Fin (n + 1) => Fin p.K × Fin (D p + 1)) code entry) =
      Fin.snoc (α := fun _ : Fin (n + 1) =>
        Fin p.K × ReferencePrelaunchFollower.Observation p)
        (L p code) (entry.1, g p entry.2) := by
  change (fun x : Fin (n + 1) =>
      ((Fin.snoc (α := fun _ : Fin (n + 1) =>
        Fin p.K × Fin (D p + 1)) code entry x).1,
        g p (Fin.snoc (α := fun _ : Fin (n + 1) =>
          Fin p.K × Fin (D p + 1)) code entry x).2)) =
    Fin.snoc (α := fun _ : Fin (n + 1) =>
      Fin p.K × ReferencePrelaunchFollower.Observation p)
      (fun x : Fin n => ((code x).1, g p (code x).2))
      (entry.1, g p entry.2)
  exact Fin.comp_snoc (fun x : Fin p.K × Fin (D p + 1) => (x.1, g p x.2)) code entry

/-- Coding finite feedback on an existing bounded reward row makes collision
freedom a case: a free arm returns its own rounded entry and a collision
returns the zero code. -/
theorem q_playerFeedback (p : ConstructorDimensions.Parameters)
    (r0 : FiniteBanditModel.RewardMatrix p.T p.K) (t : Fin p.T)
    (a : FiniteBanditModel.ActionProfile p.m p.K) (i : Fin p.m) :
    q p ⟨FiniteBanditModel.playerFeedback a (r0.reward t) i,
        FiniteBanditModel.rewardMatrixFeedback_mem_Icc a r0 t i⟩ =
      if FiniteBanditModel.collisionFreeFor a i then
        q p ⟨r0.reward t (a i), r0.reward_mem_Icc t (a i)⟩
      else 0 := by
  classical
  by_cases hfree : FiniteBanditModel.collisionFreeFor a i
  · have hv : FiniteBanditModel.playerFeedback a (r0.reward t) i = r0.reward t (a i) := by
      simp [FiniteBanditModel.playerFeedback, hfree]
    have hs : (⟨FiniteBanditModel.playerFeedback a (r0.reward t) i,
        FiniteBanditModel.rewardMatrixFeedback_mem_Icc a r0 t i⟩ : SparseCalendarReward) =
        ⟨r0.reward t (a i), r0.reward_mem_Icc t (a i)⟩ := by
      exact Subtype.ext hv
    rw [hs]
    simp only [hfree, ↓reduceIte]
  · have hv : FiniteBanditModel.playerFeedback a (r0.reward t) i = 0 := by
      simp [FiniteBanditModel.playerFeedback, hfree]
    have hs : (⟨FiniteBanditModel.playerFeedback a (r0.reward t) i,
        FiniteBanditModel.rewardMatrixFeedback_mem_Icc a r0 t i⟩ : SparseCalendarReward) =
        (0 : SparseCalendarReward) := by
      exact Subtype.ext hv
    rw [hs]
    simp only [hfree, ↓reduceIte, q_zero]

/-- Coding bounded real feedback from a row decoded by `g` returns exactly the
finite grid feedback code. -/
theorem q_playerFeedback_of_gridRow (p : ConstructorDimensions.Parameters)
    (actions : FiniteBanditModel.ActionProfile p.m p.K)
    (row : Fin p.K → Fin (D p + 1)) (i : Fin p.m) :
    q p ⟨FiniteBanditModel.playerFeedback actions
        (fun arm => (g p (row arm)).val.val) i,
        FiniteBanditModel.playerFeedback_mem_Icc_of_bounds actions
          (fun arm => (g p (row arm)).val.val)
          (fun arm => (g p (row arm)).val.property) i⟩ =
      if FiniteBanditModel.collisionFreeFor actions i then row (actions i) else 0 := by
  classical
  by_cases hfree : FiniteBanditModel.collisionFreeFor actions i
  · have hv : FiniteBanditModel.playerFeedback actions
        (fun arm => (g p (row arm)).val.val) i = (g p (row (actions i))).val.val := by
      simp [FiniteBanditModel.playerFeedback, hfree]
    have hs : (⟨FiniteBanditModel.playerFeedback actions
        (fun arm => (g p (row arm)).val.val) i,
        FiniteBanditModel.playerFeedback_mem_Icc_of_bounds actions
          (fun arm => (g p (row arm)).val.val)
          (fun arm => (g p (row arm)).val.property) i⟩ : SparseCalendarReward) =
        (g p (row (actions i))).val := by
      exact Subtype.ext hv
    rw [hs, q_g]
    simp only [hfree, ↓reduceIte]
  · have hv : FiniteBanditModel.playerFeedback actions
        (fun arm => (g p (row arm)).val.val) i = 0 := by
      simp [FiniteBanditModel.playerFeedback, hfree]
    have hs : (⟨FiniteBanditModel.playerFeedback actions
        (fun arm => (g p (row arm)).val.val) i,
        FiniteBanditModel.playerFeedback_mem_Icc_of_bounds actions
          (fun arm => (g p (row arm)).val.val)
          (fun arm => (g p (row arm)).val.property) i⟩ : SparseCalendarReward) =
        (0 : SparseCalendarReward) := by
      exact Subtype.ext hv
    rw [hs, q_zero]
    simp only [hfree, ↓reduceIte]

/-- The bounded-feedback coding agrees with the existing initialization
`gridFeedback` when its finite reward row is decoded by `g`. -/
theorem q_initializationGridFeedback (p : ConstructorDimensions.Parameters)
    {rate : ActualPostlaunchPhysicalStep.RateInput p}
    {block : Fin (BootstrapDimensions.n_boot p)}
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate block)
    (player : Fin p.m) :
    q p ⟨FiniteBanditModel.playerFeedback
        (ActualInitializationPhysicalStep.actionProfile prepared)
        (fun arm => (g p (prepared.rewards prepared.time arm)).val.val) player,
        FiniteBanditModel.playerFeedback_mem_Icc_of_bounds
          (ActualInitializationPhysicalStep.actionProfile prepared)
          (fun arm => (g p (prepared.rewards prepared.time arm)).val.val)
          (fun arm => (g p (prepared.rewards prepared.time arm)).val.property) player⟩ =
      ActualInitializationPhysicalStep.gridFeedback prepared player := by
  rw [q_playerFeedback_of_gridRow]
  rfl

/-- The bounded-feedback coding agrees with the existing postlaunch
`gridFeedback` when its finite reward row is decoded by `g`. -/
theorem q_postlaunchGridFeedback (p : ConstructorDimensions.Parameters)
    {rate : ActualPostlaunchPhysicalStep.RateInput p}
    {block : Fin (BootstrapDimensions.n_boot p)} {cursor : ℕ}
    {input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor}
    (prepared : ActualPostlaunchPhysicalStep.PreparedRound input)
    (player : Fin p.m) :
    q p ⟨FiniteBanditModel.playerFeedback
        (ActualPostlaunchPhysicalStep.actionProfile prepared)
        (fun arm => (g p (input.rewards input.time arm)).val.val) player,
        FiniteBanditModel.playerFeedback_mem_Icc_of_bounds
          (ActualPostlaunchPhysicalStep.actionProfile prepared)
          (fun arm => (g p (input.rewards input.time arm)).val.val)
          (fun arm => (g p (input.rewards input.time arm)).val.property) player⟩ =
      ActualPostlaunchPhysicalStep.gridFeedback prepared player := by
  rw [q_playerFeedback_of_gridRow]
  rfl

end Bandits.Support.FiniteBoundedLocalHistoryCode

end
