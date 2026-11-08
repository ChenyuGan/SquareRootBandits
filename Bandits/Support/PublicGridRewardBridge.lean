/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PublicGridConcentration
public import Bandits.Support.RoundedLocalRollout

/-!
# Bridge rounded finite reward matrices to the public real grid

This module uses the existing real-grid carrier and the existing rounded-code
equivalence to represent every rounded finite reward matrix. It specializes
the all-grid concentration event at one fixed output, and transfers a
conditional pathwise all-grid regret bound through the accepted local rollout
comparison. It does not construct a protocol, a private-input probability
space, or an expected-regret theorem.

Source: `sources/zip4/manuscript/08_main_theorem.tex:60-64,163-168` and
`sources/zip4/manuscript/01_introduction.tex:20-36`.
-/

public section

namespace Bandits.Support.PublicGridRewardBridge

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PublicGridConcentration
open Bandits.Support.RealRewardGridCount
open Bandits.Support.RoundedLocalRollout
open Bandits.Support.WholeRowHoeffding
open MeasureTheory

/-- Encode the existing rounded reward matrix in the existing real-grid carrier.
The code is precisely `roundedRewardMatrixCode (D p) (D_pos p) rewards`.
Source: `sources/zip4/manuscript/08_main_theorem.tex:60-64,163-168`. -/
@[expose] noncomputable def roundedRealRewardMatrix (p : Parameters)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    PublicGridConcentration.RealRewardMatrix p :=
  RealRewardGridCount.realRewardMatrixEncodingEquiv
    (D p) p.K p.T (D_pos p)
    (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards)

/-- The bridge is exactly the accepted concentration-carrier encoding of the
accepted rounded finite code. -/
theorem roundedRealRewardMatrix_eq_encoded_code (p : Parameters)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    roundedRealRewardMatrix p rewards =
      RealRewardGridCount.realRewardMatrixEncodingEquiv
        (D p) p.K p.T (D_pos p)
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) rewards) := by
  rfl

/-- Every entry of the encoded real-grid matrix is exactly its rounded value. -/
theorem roundedRealRewardMatrix_value (p : Parameters)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (t : Fin p.T) (a : Fin p.K) :
    (roundedRealRewardMatrix p rewards t a).val =
      (RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) rewards).reward t a := by
  simpa only [roundedRealRewardMatrix] using
      (RoundedLocalRollout.roundedRewardMatrixCode_equiv_value
        (D p) (D_pos p) rewards t a)

/-- View an existing real-grid matrix as the existing bounded finite reward
matrix. This is a conversion; it does not introduce a second reward carrier. -/
@[expose] def realRewardMatrixAsRewardMatrix (p : Parameters)
    (rewards : PublicGridConcentration.RealRewardMatrix p) :
    FiniteBanditModel.RewardMatrix p.T p.K where
  reward t a := (rewards t a).val
  reward_mem_Icc t a := by
    rcases (rewards t a).property with ⟨k, hk⟩
    rw [← hk]
    exact RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) k

/-- Converting the bridge back to the finite reward-matrix API recovers the
accepted rounded matrix exactly. -/
theorem roundedRealRewardMatrix_asRewardMatrix_eq (p : Parameters)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    realRewardMatrixAsRewardMatrix p (roundedRealRewardMatrix p rewards) =
      RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) rewards := by
  cases hleft : realRewardMatrixAsRewardMatrix p (roundedRealRewardMatrix p rewards) with
  | mk leftReward leftBound =>
    cases hright : RoundedLocalRollout.roundedRewardMatrix (D p) (D_pos p) rewards with
    | mk rightReward rightBound =>
      have hreward : leftReward = rightReward := by
        funext t a
        have hvalue := roundedRealRewardMatrix_value p rewards t a
        calc
          leftReward t a =
              (realRewardMatrixAsRewardMatrix p (roundedRealRewardMatrix p rewards)).reward
                t a := by rw [hleft]
          _ = (roundedRealRewardMatrix p rewards t a).val := rfl
          _ = rightReward t a := by simpa only [hright] using hvalue
      subst rightReward
      have hbound : leftBound = rightBound := Subsingleton.elim _ _
      subst rightBound
      rfl

/-- The accepted rounded-local action equality, expressed using the real-grid
matrix produced by this bridge. The public datum and each private input are
fixed; only local histories enter the decision rule. -/
theorem roundedLocalRolloutPrefix_action_eq_roundedRealRewardMatrix
    {PublicData PrivateInput : Type*} (p : Parameters)
    (decide : PlayerLocalDecision p.m p.K PublicData PrivateInput)
    (publicData : PublicData) (privateInput : Player p.m → PrivateInput)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : ℕ) (ht : t ≤ p.T) (s : Fin t) (i : Player p.m) :
    (deterministicRolloutPrefix
        (RoundedLocalRollout.roundedLocalDecision (D p) decide)
        publicData privateInput rewards t ht).action s i =
      (deterministicRolloutPrefix
        (RoundedLocalRollout.roundedLocalDecision (D p) decide)
        publicData privateInput
        (realRewardMatrixAsRewardMatrix p (roundedRealRewardMatrix p rewards))
        t ht).action s i := by
  have h := (RoundedLocalRollout.roundedLocalRolloutPrefix_invariant
    (D p) (D_pos p) decide publicData privateInput rewards t ht).1 s i
  rw [roundedRealRewardMatrix_asRewardMatrix_eq]
  exact h

/-- A single fixed output in the accepted all-grid good event gives the row
inequality for every original finite reward matrix after applying the exact
rounded-code bridge. The quantifier order is output first, then all rewards.
Source: `sources/zip4/manuscript/08_main_theorem.tex:60-64`. -/
theorem rowConcentrationGoodEvent_roundedRewardMatrix {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    (G : PublicGridConcentration.RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (ω : Ω)
    (hω : ω ∈ PublicGridConcentration.rowConcentrationGoodEvent p μ G) :
    ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
      WholeRowHoeffding.barG (G (roundedRealRewardMatrix p rewards)) ω ≤
        WholeRowHoeffding.muG μ (G (roundedRealRewardMatrix p rewards)) +
          2 * PublicGridConcentration.rowConcentrationScale p := by
  change ∀ r : PublicGridConcentration.RealRewardMatrix p,
    WholeRowHoeffding.barG (G r) ω ≤
      WholeRowHoeffding.muG μ (G r) +
        2 * PublicGridConcentration.rowConcentrationScale p at hω
  intro rewards
  exact hω (roundedRealRewardMatrix p rewards)

/-- Transfer any already-established all-grid pathwise regret bound at one
fixed public datum to every original reward matrix. The named hypothesis is
the explicit conditional trust boundary: this lemma proves no all-grid regret
bound of its own. Private inputs are quantified after rewards, so this is a
pathwise statement and makes no assertion about an expectation over them.
Source comparison: `sources/zip4/manuscript/08_main_theorem.tex:163-168`;
the local decision model is from `sources/zip4/manuscript/01_introduction.tex:20-36`. -/
theorem roundedLocalRollout_regret_le_of_allGridRegretBound
    {PublicData PrivateInput : Type*} (p : Parameters)
    (decide : PlayerLocalDecision p.m p.K PublicData PrivateInput)
    (publicData : PublicData)
    (bound : PublicGridConcentration.RealRewardMatrix p → ℝ)
    (h_allGridRegretBound :
      ∀ gridRewards : PublicGridConcentration.RealRewardMatrix p,
        ∀ privateInput : Player p.m → PrivateInput,
          bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
              (realRewardMatrixAsRewardMatrix p gridRewards) -
            pathwiseCumulativeReward
              (deterministicRollout
                (RoundedLocalRollout.roundedLocalDecision (D p) decide)
                publicData privateInput
                (realRewardMatrixAsRewardMatrix p gridRewards)) ≤
          bound gridRewards) :
    ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
      ∀ privateInput : Player p.m → PrivateInput,
        bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K) rewards -
          pathwiseCumulativeReward
            (deterministicRollout
              (RoundedLocalRollout.roundedLocalDecision (D p) decide)
              publicData privateInput rewards) ≤
          bound (roundedRealRewardMatrix p rewards) +
            (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro rewards privateInput
  have hgrid := h_allGridRegretBound
    (roundedRealRewardMatrix p rewards) privateInput
  rw [roundedRealRewardMatrix_asRewardMatrix_eq] at hgrid
  have hcompare := RoundedLocalRollout.roundedLocalRollout_regret_le
    (m_pos p) (Nat.le_of_lt p.m_lt_K) (D p) (D_pos p) decide
    publicData privateInput rewards
  linarith

/-- Use one fixed public output both in the accepted all-grid event and in an
explicitly supplied all-grid pathwise regret bound. For each original reward
matrix, the event estimate and the rounded-rollout comparison are then
available together. The private-input profile remains universally quantified
after the reward matrix; no private expectation or protocol producer is
asserted. -/
theorem roundedRealRewardMatrix_bridge_of_goodOutput_and_allGridRegretBound
    {Ω PrivateInput : Type*} [MeasurableSpace Ω] (p : Parameters)
    (μ : Measure Ω)
    (G : PublicGridConcentration.RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (decide : PlayerLocalDecision p.m p.K Ω PrivateInput)
    (ω : Ω)
    (hω : ω ∈ PublicGridConcentration.rowConcentrationGoodEvent p μ G)
    (bound : PublicGridConcentration.RealRewardMatrix p → ℝ)
    (h_allGridRegretBound :
      ∀ gridRewards : PublicGridConcentration.RealRewardMatrix p,
        ∀ privateInput : Player p.m → PrivateInput,
          bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K)
              (realRewardMatrixAsRewardMatrix p gridRewards) -
            pathwiseCumulativeReward
              (deterministicRollout
                (RoundedLocalRollout.roundedLocalDecision (D p) decide)
                ω privateInput
                (realRewardMatrixAsRewardMatrix p gridRewards)) ≤
          bound gridRewards) :
    ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
      (WholeRowHoeffding.barG (G (roundedRealRewardMatrix p rewards)) ω ≤
          WholeRowHoeffding.muG μ (G (roundedRealRewardMatrix p rewards)) +
            2 * PublicGridConcentration.rowConcentrationScale p) ∧
        ∀ privateInput : Player p.m → PrivateInput,
          bestFixedMSetComparator (m_pos p) (Nat.le_of_lt p.m_lt_K) rewards -
            pathwiseCumulativeReward
              (deterministicRollout
                (RoundedLocalRollout.roundedLocalDecision (D p) decide)
                ω privateInput rewards) ≤
            bound (roundedRealRewardMatrix p rewards) +
              (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro rewards
  constructor
  · exact rowConcentrationGoodEvent_roundedRewardMatrix p μ G ω hω rewards
  · intro privateInput
    exact roundedLocalRollout_regret_le_of_allGridRegretBound
      p decide ω bound h_allGridRegretBound rewards privateInput

end Bandits.Support.PublicGridRewardBridge

end
