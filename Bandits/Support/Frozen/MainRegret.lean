-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Bandits.Support.ActualMainRegretLocalPolicyPromotion

public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualMainRegretLocalPolicyPromotion

namespace Bandits.Support.Frozen.MainRegret

theorem exists_uniform_actual_main_regret_bound :
    ∃ C1 : ℝ, ∃ hC1 : 0 < C1, ∃ Cb : ℝ, ∃ N0 : ℕ, ∃ C_star C_h C : ℝ,
      16 ≤ Cb ∧ (2 : ℝ) ^ 20 ≤ C_star ∧ (4096 : ℝ) ≤ C_h ∧ 0 < C ∧
      ∀ p : Parameters,
        (∀ (i : Fin p.m) (t : Fin p.T),
          Measurable (decision C1 hC1 C_star C_h Cb N0 p i t)) ∧
        MeasurableSet (goodPublicEvent C1 hC1 C_star C_h Cb N0 p) ∧
        (publishedOutputMeasure p).real
          (goodPublicEvent C1 hC1 C_star C_h Cb N0 p)ᶜ ≤ 5 / (N p : ℝ) ∧
        ∀ published : PublishedOutput p,
          published ∈ goodPublicEvent C1 hC1 C_star C_h Cb N0 p →
          ∀ rewards : FiniteBanditModel.RewardMatrix p.T p.K,
            FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
              (decision C1 hC1 C_star C_h Cb N0 p)
              (FiniteHorizonRolePrivateLaw.nu p) rewards published ≤
              C * BootstrapStartupCostScale.Q_boot p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact Bandits.Support.ActualMainRegretLocalPolicyPromotion.exists_uniform_actual_main_regret_bound
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end Bandits.Support.Frozen.MainRegret

end
-- FROZEN_ANCHOR_SUFFIX_END
