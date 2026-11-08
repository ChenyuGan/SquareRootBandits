/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Basic.ENNReal.BigOperators
import Bandits.Support.CorrectedPositivity
import Bandits.Support.ResidualMass

/-!
# Finite corrected probability laws

This module combines the corrected-mass positivity and normalization calculations used in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77` and
`sources/zip4/manuscript/06_interruptions.tex:376-408`.

It constructs a PMF on a finite type from the pointwise corrected law. It does not formalize
the conditional stochastic-process identity, the uniform realization of a sampler, or the
continuous public-table semantics in the source.
-/

@[expose] public section

open scoped BigOperators

namespace Bandits.Support.CorrectedFiniteLaw

/-- The input data for a finite corrected law, including the validity hypotheses on its
three input laws and the pointwise inequalities needed for the correction. -/
structure Input (α : Type*) [Fintype α] where
  n : ℕ
  h : ℝ
  h_pos : 0 < h
  h_le_one : h ≤ 1
  Q_t : α → ℝ
  Q_u : α → ℝ
  Q_prev : α → ℝ
  Q_t_nonneg : ∀ x, 0 ≤ Q_t x
  Q_u_nonneg : ∀ x, 0 ≤ Q_u x
  Q_prev_nonneg : ∀ x, 0 ≤ Q_prev x
  Q_t_sum_eq_one : ∑ x, Q_t x = 1
  Q_u_sum_eq_one : ∑ x, Q_u x = 1
  Q_prev_sum_eq_one : ∑ x, Q_prev x = 1
  iterated_domination : ∀ x, (1 - h) ^ n * Q_u x ≤ Q_t x
  step_domination : ∀ x, (1 - h) * Q_prev x ≤ Q_u x

/-- The source's affine correction of `Q_t` by the difference `Q_u - Q_prev`. -/
noncomputable def correctedMass {α : Type*} [Fintype α] (input : Input α) (x : α) : ℝ :=
  input.Q_t x + (1 - input.h) ^ (input.n + 1) / input.h *
    (input.Q_u x - input.Q_prev x)

/-- The actual pointwise domination hypotheses imply nonnegativity of the corrected mass. -/
theorem correctedMass_nonneg {α : Type*} [Fintype α] (input : Input α) (x : α) :
    0 ≤ correctedMass input x := by
  have hbound := CorrectedPositivity.correctedSamplerBounds input.h input.n
    (input.Q_t x) (input.Q_u x) (input.Q_prev x)
    input.h_pos input.h_le_one (input.iterated_domination x) (input.step_domination x)
  exact le_trans hbound.2 hbound.1

/-- The corrected masses sum to one because the three input laws are normalized. -/
theorem correctedMass_sum_eq_one {α : Type*} [Fintype α] (input : Input α) :
    ∑ x, correctedMass input x = 1 := by
  classical
  simpa [correctedMass, ResidualMass.correctedLaw] using
    ResidualMass.correctedLaw_sum_eq_one (1 - input.h) input.h input.n
      input.Q_t input.Q_u input.Q_prev
      input.Q_t_sum_eq_one input.Q_u_sum_eq_one input.Q_prev_sum_eq_one

/-- The finite PMF with the corrected real masses, converted to `ENNReal`. -/
noncomputable def correctedPMF {α : Type*} [Fintype α] (input : Input α) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (correctedMass input x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun x _ => correctedMass_nonneg input x)]
    rw [correctedMass_sum_eq_one]
    simp)

/-- Pointwise mass characterization of the constructed finite PMF. -/
theorem correctedPMF_apply {α : Type*} [Fintype α] (input : Input α) (x : α) :
    correctedPMF input x = ENNReal.ofReal (correctedMass input x) := by
  simp [correctedPMF]

/-- Reading a point mass back as a real recovers the corrected mass exactly. -/
theorem correctedPMF_toReal_apply {α : Type*} [Fintype α] (input : Input α) (x : α) :
    (correctedPMF input x).toReal = correctedMass input x := by
  rw [correctedPMF_apply]
  exact ENNReal.toReal_ofReal (correctedMass_nonneg input x)

end Bandits.Support.CorrectedFiniteLaw

end
