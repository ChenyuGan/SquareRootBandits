/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.MeasurableLocalRollout
public import Bandits.Support.PublicGridRewardBridge
public import Bandits.Support.RoundedLocalRollout

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Private-expectation transfer for rounded local decisions

For a fixed public datum, rounding only the local histories transfers expected
regret from the rounded reward matrix to an arbitrary bounded reward matrix
with cost `m*T/D`. This uses the independent private-profile law and integrates
the accepted pointwise regret comparison; the reward feedback in the original
run remains the actual collision-filtered feedback. The constructor-dimension
consumer is conditional on a supplied all-grid expected-regret bound.

Sources: `sources/zip4/manuscript/01_introduction.tex:19-36` for the private
expectation and collision-filtered reward, and
`sources/zip4/manuscript/08_main_theorem.tex:157-168` for the rounding
transfer. This module does not prove measurability of the actual protocol under
its continuous private draws or produce the all-grid expected-regret bound.
-/

@[expose] public section

namespace Bandits.Support.ExpectedRoundedRegret

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.MeasurableLocalRollout
open Bandits.Support.PublicGridConcentration
open Bandits.Support.PublicGridRewardBridge
open Bandits.Support.RoundedLocalRollout

/-- The scalar rounding arithmetic is measurable, including its actual natural
floor and real cast. -/
theorem rounded_measurable (D : ℕ) : Measurable (RewardRounding.rounded D) := by
  unfold RewardRounding.rounded
  have hscale : Measurable (fun r : ℝ => (D : ℝ) * r) :=
    measurable_const.mul measurable_id
  have hfloor : Measurable (fun r : ℝ => Nat.floor ((D : ℝ) * r)) :=
    Nat.measurable_floor.comp hscale
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable
  exact (hcast.comp hfloor).div_const (D : ℝ)

/-- Rounding every observation in a finite local history is measurable for the
product measurable structure on histories. -/
theorem roundLocalHistory_measurable {K t : ℕ} (D : ℕ) :
    Measurable (roundLocalHistory D : LocalHistory K t → LocalHistory K t) := by
  rw [measurable_pi_iff]
  intro s
  have hentry : Measurable (fun history : LocalHistory K t => history s) :=
    measurable_pi_apply s
  exact (measurable_fst.comp hentry).prodMk
    ((rounded_measurable D).comp (measurable_snd.comp hentry))

/-- The existing local-history rounding wrapper preserves joint measurability
of every local decision from its explicit public/history/private-input premise. -/
theorem roundedLocalDecision_measurable {m K : ℕ}
    {PublicData PrivateInput : Type*} [MeasurableSpace PublicData]
    [MeasurableSpace PrivateInput] (D : ℕ)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2)) :
    ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        roundedLocalDecision D decide i t x.1 x.2.1 x.2.2) := by
  intro i t
  have hargs : Measurable
      (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        (x.1, (roundLocalHistory D x.2.1, x.2.2))) := by
    exact measurable_fst.prodMk
      (((roundLocalHistory_measurable D).comp
          (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  change Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
    decide i t x.1 (roundLocalHistory D x.2.1) x.2.2)
  exact (hdecide i t).comp hargs

/-- At one fixed public datum, expected regret of the rounded-history policy
on an original reward matrix is at most its expected regret on the entrywise
rounded matrix plus `m*T/D`. Both integrands are actual rollout regrets: the
original-matrix integrand retains the original collision-filtered feedback.
The only measurability premise is joint measurability of the base local rule.
Source: `sources/zip4/manuscript/08_main_theorem.tex:157-168`. -/
theorem expectedPrivateRegret_roundedLocalDecision_le
    {m K T : ℕ} {PublicData PrivateInput : Type*}
    [MeasurableSpace PublicData] [MeasurableSpace PrivateInput]
    (hm : 0 < m) (hmK : m ≤ K) (D : ℕ) (hD : 0 < D)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (hdecide : ∀ (i : Player m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (nu : Player m → Measure PrivateInput) [∀ i, IsProbabilityMeasure (nu i)]
    (publicData : PublicData) (rewards : RewardMatrix T K) :
    expectedPrivateRegret hm hmK (roundedLocalDecision D decide) rewards nu publicData ≤
      expectedPrivateRegret hm hmK (roundedLocalDecision D decide)
        (roundedRewardMatrix D hD rewards) nu publicData +
          (m : ℝ) * (T : ℝ) / (D : ℝ) := by
  let μ := privateProfileLaw nu
  let originalRegret := fun privateInput : Player m → PrivateInput =>
    pathwiseRegret hm hmK rewards
      (deterministicRollout (roundedLocalDecision D decide) publicData privateInput rewards)
  let roundedRegret := fun privateInput : Player m → PrivateInput =>
    pathwiseRegret hm hmK (roundedRewardMatrix D hD rewards)
      (deterministicRollout (roundedLocalDecision D decide) publicData privateInput
        (roundedRewardMatrix D hD rewards))
  let roundingCost : ℝ := (m : ℝ) * (T : ℝ) / (D : ℝ)
  have hdecideRounded := roundedLocalDecision_measurable D decide hdecide
  have horiginalIntegrable : Integrable originalRegret μ := by
    exact pathwiseRegret_integrable hm hmK (roundedLocalDecision D decide) rewards
      hdecideRounded nu publicData
  have hroundedIntegrable : Integrable roundedRegret μ := by
    exact pathwiseRegret_integrable hm hmK (roundedLocalDecision D decide)
      (roundedRewardMatrix D hD rewards) hdecideRounded nu publicData
  have hpointwise : ∀ privateInput, originalRegret privateInput ≤
      roundedRegret privateInput + roundingCost := by
    intro privateInput
    dsimp [originalRegret, roundedRegret, roundingCost, pathwiseRegret]
    exact roundedLocalRollout_regret_le hm hmK D hD decide publicData privateInput rewards
  have hsumIntegrable : Integrable (fun privateInput =>
      roundedRegret privateInput + roundingCost) μ :=
    hroundedIntegrable.add (integrable_const roundingCost)
  have hprobability : μ.real Set.univ = 1 := by
    simp [μ, privateProfileLaw]
  unfold expectedPrivateRegret
  change (∫ privateInput, originalRegret privateInput ∂μ) ≤
    (∫ privateInput, roundedRegret privateInput ∂μ) + roundingCost
  calc
    (∫ privateInput, originalRegret privateInput ∂μ) ≤
        ∫ privateInput, (roundedRegret privateInput + roundingCost) ∂μ :=
      integral_mono horiginalIntegrable hsumIntegrable hpointwise
    _ = (∫ privateInput, roundedRegret privateInput ∂μ) + roundingCost := by
      rw [integral_add hroundedIntegrable (integrable_const roundingCost), integral_const]
      simp [hprobability]

/-- Conditional constructor-dimension consumer: at a single fixed public
output, an already established all-grid expected-regret bound for the same
independent private-profile law transfers to every original reward matrix,
with the explicit rounding cost. Quantifiers are output first and then all
rewards; private randomness remains inside each expectation. The premise is
the all-grid producer obligation, not a pointwise-in-private-input bound. -/
theorem expectedPrivateRegret_le_of_allGridExpectedRegretBound
    {PublicData PrivateInput : Type*} [MeasurableSpace PublicData]
    [MeasurableSpace PrivateInput]
    (p : Parameters) (decide : PlayerLocalDecision p.m p.K PublicData PrivateInput)
    (hdecide : ∀ (i : Player p.m) (t : ℕ),
      Measurable (fun x : PublicData × (LocalHistory p.K t × PrivateInput) =>
        decide i t x.1 x.2.1 x.2.2))
    (nu : Player p.m → Measure PrivateInput) [∀ i, IsProbabilityMeasure (nu i)]
    (publicData : PublicData)
    (bound : RealRewardMatrix p → ℝ)
    (h_allGridExpectedRegretBound :
      ∀ gridRewards : RealRewardMatrix p,
        expectedPrivateRegret (m_pos p) (Nat.le_of_lt p.m_lt_K)
          (roundedLocalDecision (D p) decide)
          (realRewardMatrixAsRewardMatrix p gridRewards) nu publicData ≤ bound gridRewards) :
    ∀ rewards : RewardMatrix p.T p.K,
      expectedPrivateRegret (m_pos p) (Nat.le_of_lt p.m_lt_K)
        (roundedLocalDecision (D p) decide) rewards nu publicData ≤
        bound (roundedRealRewardMatrix p rewards) +
          (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
  intro rewards
  have htransfer := expectedPrivateRegret_roundedLocalDecision_le
    (m_pos p) (Nat.le_of_lt p.m_lt_K) (D p) (D_pos p) decide hdecide nu publicData rewards
  have hgrid := h_allGridExpectedRegretBound (roundedRealRewardMatrix p rewards)
  calc
    expectedPrivateRegret (m_pos p) (Nat.le_of_lt p.m_lt_K)
        (roundedLocalDecision (D p) decide) rewards nu publicData ≤
        expectedPrivateRegret (m_pos p) (Nat.le_of_lt p.m_lt_K)
          (roundedLocalDecision (D p) decide)
          (realRewardMatrixAsRewardMatrix p (roundedRealRewardMatrix p rewards))
          nu publicData + (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
      simpa only [← roundedRealRewardMatrix_asRewardMatrix_eq p rewards] using htransfer
    _ ≤ bound (roundedRealRewardMatrix p rewards) +
          (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) :=
      by
        simpa only [add_comm] using
          (add_le_add_right hgrid ((p.m : ℝ) * (p.T : ℝ) / (D p : ℝ)))

end Bandits.Support.ExpectedRoundedRegret

end
