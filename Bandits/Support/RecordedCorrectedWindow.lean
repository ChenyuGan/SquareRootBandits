/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CorrectedFiniteLaw
public import Bandits.Support.PrefixSetSampler
public import Bandits.Support.ProductSetDistribution
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.RecordedQueueRun
public import Bandits.Support.RecordedSlowRefresh

import Bandits.Support.BoundedDomination
import Bandits.Support.RecordedPotentialStep
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Corrected product-set laws on actual recorded prefixes

For a finite list of recorded rounds, each law below is evaluated at the
literal run on `rounds.take r`. Its one-step domination uses the actual queue
transition, including disabled steps and the transition which first sets the
overflow flag. The correction is the finite signed law in
`appendix_a_local_protocol.tex:66-77` and `06_interruptions.tex:376-408`, with
the stability input from `04_slow_fast_learner.tex:176-187,219-243`.

This file constructs an internal corrected law and a normalized-mass input for
the deterministic prefix set sampler. It does not identify prefix indices
with a physical same-episode collection schedule or claim a conditional
physical sampler law.
-/

@[expose] public section

open scoped BigOperators

namespace Bandits.Support.RecordedCorrectedWindow

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ProductSetLaw
open Bandits.Support.RecordedQueueRun

/-- The score vector after the first `r` actual queue inputs. -/
noncomputable def prefixScoreWeight
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ) : Fin p.K → ℝ :=
  fun i => RecordedQueueRun.scoreWeight q
    (RecordedQueueRun.run q (rounds.take r)) i

/-- The existing product-weight `m`-set mass at an actual finite-run prefix.
The carrier is the already defined subtype of `m`-sets of arms. -/
noncomputable def prefixQ
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) : ℝ :=
  ProductSetLaw.Q p.m (prefixScoreWeight p q rounds r) S

/-- The product-set PMF whose atom masses are `prefixQ` at the actual prefix. -/
noncomputable def prefixProductPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ) :
    PMF (ProductSetLaw.ProductSet p.K p.m) :=
  ProductSetDistribution.productSetPMF (prefixScoreWeight p q rounds r)
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (fun i => RecordedSlowRefresh.scoreWeight_pos q
      (RecordedQueueRun.run q (rounds.take r)) i)

/-- Every actual prefix product-set atom is positive. -/
theorem prefixQ_pos (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) : 0 < prefixQ p q rounds r S := by
  exact ProductSetLaw.Q_pos (prefixScoreWeight p q rounds r)
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (fun i => RecordedSlowRefresh.scoreWeight_pos q
      (RecordedQueueRun.run q (rounds.take r)) i) S

/-- The product-set atoms at every actual prefix have total mass one. -/
theorem prefixQ_sum_eq_one (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ) :
    (∑ S : ProductSetLaw.ProductSet p.K p.m, prefixQ p q rounds r S) = 1 := by
  exact ProductSetLaw.Q_sum_eq_one (prefixScoreWeight p q rounds r)
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (fun i => RecordedSlowRefresh.scoreWeight_pos q
      (RecordedQueueRun.run q (rounds.take r)) i)

/-- The prefix PMF has exactly the `prefixQ` atom on every supported set. -/
theorem prefixProductPMF_apply (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    prefixProductPMF p q rounds r S = ENNReal.ofReal (prefixQ p q rounds r S) := by
  exact ProductSetDistribution.productSetPMF_apply_eq_Q
    (prefixScoreWeight p q rounds r) (ConstructorDimensions.m_pos p) p.m_lt_K
    (fun i => RecordedSlowRefresh.scoreWeight_pos q
      (RecordedQueueRun.run q (rounds.take r)) i) S

/-- Consecutive prefixes of the concrete round list differ by the actual
`RecordedQueueRun.step`; the final input at index `r` is included. -/
theorem run_take_succ_eq_step (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (hr : r < rounds.length) :
    RecordedQueueRun.run q (rounds.take (r + 1)) =
      RecordedQueueRun.step q (RecordedQueueRun.run q (rounds.take r)) rounds[r] :=
  RecordedPotentialStep.run_take_succ_eq_step q rounds r hr

/-- One-step `Q` domination along an actual finite-run prefix, with no branch
restriction on enabled status or overflow. -/
theorem prefixQ_step_domination (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (r : ℕ)
    (hr : r < rounds.length) (S : ProductSetLaw.ProductSet p.K p.m) :
    (1 - RecordedSlowRefresh.hazard p q) * prefixQ p q rounds r S ≤
      prefixQ p q rounds (r + 1) S := by
  unfold prefixQ prefixScoreWeight
  rw [run_take_succ_eq_step p q rounds r hr]
  exact RecordedSlowRefresh.step_Q_domination p q
    (RecordedQueueRun.run q (rounds.take r)) rounds[r] S

/-- The preceding actual prefix is dominated independently of the later
window iteration. The `u`th input takes the state from prefix `u - 1` to
prefix `u`. -/
theorem prefixQ_preceding_domination (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u : ℕ)
    (hu : 1 ≤ u) (huLen : u ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (1 - RecordedSlowRefresh.hazard p q) * prefixQ p q rounds (u - 1) S ≤
      prefixQ p q rounds u S := by
  have hprev : u - 1 < rounds.length := by omega
  have hrun := run_take_succ_eq_step p q rounds (u - 1) hprev
  rw [Nat.sub_add_cancel hu] at hrun
  unfold prefixQ prefixScoreWeight
  rw [hrun]
  exact RecordedSlowRefresh.step_Q_domination p q
    (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1] S

/-- Iteration of actual one-step product-set domination only over `[u,v)`.
The case `u = v` is included and gives the zero-step bound. -/
theorem prefixQ_iterated_domination (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (1 - RecordedSlowRefresh.hazard p q) ^ (v - u) * prefixQ p q rounds u S ≤
      prefixQ p q rounds v S := by
  have hquarter := RecordedSlowRefresh.hazard_le_quarter p q hcap
  have hnonneg : 0 ≤ 1 - RecordedSlowRefresh.hazard p q := by linarith
  have hsteps : ∀ k, u ≤ k → k < u + (v - u) →
      (1 - RecordedSlowRefresh.hazard p q) * prefixQ p q rounds k S ≤
        prefixQ p q rounds (k + 1) S := by
    intro k hku hkv
    have hk : k < rounds.length := by omega
    exact prefixQ_step_domination p q rounds k hk S
  have hiter := BoundedDomination.finiteWindowLowerBound
    (a := 1 - RecordedSlowRefresh.hazard p q) hnonneg
    (fun r => prefixQ p q rounds r S) u (v - u) hsteps
  simpa [Nat.add_sub_of_le huv] using hiter

/-- The learning-rate cap proves the source refresh hazard is positive and at
most one quarter. -/
theorem hazard_bounds (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    0 < RecordedSlowRefresh.hazard p q ∧
      RecordedSlowRefresh.hazard p q ≤ 1 / 4 := by
  exact ⟨RecordedSlowRefresh.hazard_pos p q,
    RecordedSlowRefresh.hazard_le_quarter p q hcap⟩

/-- The complete, proved input to the existing finite corrected-law
construction. Its three masses are exactly `Q_v`, `Q_u`, and `Q_(u-1)` on
the existing product-set subtype; all hypotheses are discharged from actual
prefix runs. -/
noncomputable def actualPrefixCorrectedInput
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length) :
    CorrectedFiniteLaw.Input (ProductSetLaw.ProductSet p.K p.m) where
  n := v - u
  h := RecordedSlowRefresh.hazard p q
  h_pos := RecordedSlowRefresh.hazard_pos p q
  h_le_one := le_trans (RecordedSlowRefresh.hazard_le_quarter p q hcap) (by norm_num)
  Q_t := prefixQ p q rounds v
  Q_u := prefixQ p q rounds u
  Q_prev := prefixQ p q rounds (u - 1)
  Q_t_nonneg := fun S => (prefixQ_pos p q rounds v S).le
  Q_u_nonneg := fun S => (prefixQ_pos p q rounds u S).le
  Q_prev_nonneg := fun S => (prefixQ_pos p q rounds (u - 1) S).le
  Q_t_sum_eq_one := prefixQ_sum_eq_one p q rounds v
  Q_u_sum_eq_one := prefixQ_sum_eq_one p q rounds u
  Q_prev_sum_eq_one := prefixQ_sum_eq_one p q rounds (u - 1)
  iterated_domination := prefixQ_iterated_domination p q hcap rounds u v huv hv
  step_domination := prefixQ_preceding_domination p q rounds u hu (le_trans huv hv)

/-- The literal corrected `m`-set mass produced from the proved actual-prefix
input. -/
noncomputable def actualPrefixCorrectedMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) : ℝ :=
  CorrectedFiniteLaw.correctedMass
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv) S

/-- The corrected mass is exactly the source signed formula on the actual
prefix product laws, including the exponent `v - u + 1`. -/
theorem actualPrefixCorrectedMass_formula
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S =
      prefixQ p q rounds v S +
        (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
          RecordedSlowRefresh.hazard p q *
          (prefixQ p q rounds u S - prefixQ p q rounds (u - 1) S) := by
  rfl

/-- Nonnegativity of the actual-prefix corrected mass. -/
theorem actualPrefixCorrectedMass_nonneg
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    0 ≤ actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S :=
  CorrectedFiniteLaw.correctedMass_nonneg
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv) S

/-- The corrected actual-prefix masses sum to one over all supported
`m`-subsets. -/
theorem actualPrefixCorrectedMass_sum_eq_one
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length) :
    (∑ S : ProductSetLaw.ProductSet p.K p.m,
      actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S) = 1 :=
  CorrectedFiniteLaw.correctedMass_sum_eq_one
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv)

/-- The PMF of the actual-prefix corrected `m`-set law. -/
noncomputable def actualPrefixCorrectedPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length) :
    PMF (ProductSetLaw.ProductSet p.K p.m) :=
  CorrectedFiniteLaw.correctedPMF
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv)

/-- Exact atom characterization of the actual-prefix corrected PMF. -/
theorem actualPrefixCorrectedPMF_apply
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    actualPrefixCorrectedPMF p q hcap rounds u v hu huv hv S =
      ENNReal.ofReal (actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S) := by
  exact CorrectedFiniteLaw.correctedPMF_apply
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv) S

/-- Reading an actual-prefix corrected PMF atom as a real recovers its mass. -/
theorem actualPrefixCorrectedPMF_toReal_apply
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (actualPrefixCorrectedPMF p q hcap rounds u v hu huv hv S).toReal =
      actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S := by
  exact CorrectedFiniteLaw.correctedPMF_toReal_apply
    (actualPrefixCorrectedInput p q hcap rounds u v hu huv hv) S

/-- Zero corrected mass remains a zero atom of the corrected PMF. -/
theorem actualPrefixCorrectedPMF_eq_zero_of_mass_eq_zero
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (hzero : actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S = 0) :
    actualPrefixCorrectedPMF p q hcap rounds u v hu huv hv S = 0 := by
  rw [actualPrefixCorrectedPMF_apply, hzero]
  simp

/-- Equivalence between the sampler carrier and the product-law carrier. -/
def samplerProductSetEquiv (K m : ℕ) :
    PrefixSetSampler.SetCarrier K m ≃ ProductSetLaw.ProductSet K m where
  toFun := fun S => ⟨S.1, by simp [ProductSetLaw.support]⟩
  invFun := fun S => ⟨S.1, by simpa [ProductSetLaw.support] using S.2⟩
  left_inv := by
    intro S
    apply Subtype.ext
    rfl
  right_inv := by
    intro S
    apply Subtype.ext
    rfl

/-- The corrected law as the existing deterministic prefix sampler's
normalized-mass input. The carrier conversion is an equivalence between the
two existing presentations of the same supported `m`-sets. -/
noncomputable def actualPrefixSamplerMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length) :
    PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K) where
  weight := fun S => actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
    (samplerProductSetEquiv p.K p.m S)
  weight_nonneg := fun S => actualPrefixCorrectedMass_nonneg p q hcap rounds u v hu huv hv
    (samplerProductSetEquiv p.K p.m S)
  weight_sum_eq_one := by
    calc
      PrefixMassPartition.totalMass
          (Finset.univ : Finset (PrefixSetSampler.SetCarrier p.K p.m))
          (fun S => actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
            (samplerProductSetEquiv p.K p.m S)) =
          ∑ S : PrefixSetSampler.SetCarrier p.K p.m,
            actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
              (samplerProductSetEquiv p.K p.m S) := by
        simp [PrefixMassPartition.totalMass]
      _ = ∑ S : ProductSetLaw.ProductSet p.K p.m,
            actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S := by
        exact Fintype.sum_equiv (samplerProductSetEquiv p.K p.m)
          (fun S => actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
            (samplerProductSetEquiv p.K p.m S))
          (fun S => actualPrefixCorrectedMass p q hcap rounds u v hu huv hv S)
          (fun S => rfl)
      _ = 1 := actualPrefixCorrectedMass_sum_eq_one p q hcap rounds u v hu huv hv

/-- The sampler adapter preserves every corrected mass, including zero
atoms. -/
theorem actualPrefixSamplerMass_weight
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (S : PrefixSetSampler.SetCarrier p.K p.m) :
    (actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight S =
      actualPrefixCorrectedMass p q hcap rounds u v hu huv hv
        (samplerProductSetEquiv p.K p.m S) := rfl

end Bandits.Support.RecordedCorrectedWindow

end
