/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ContinuousLearningRows
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Basic

/-!
# Complete public table

The common identification array and each complete row use the accepted constructor dimensions. A complete row pairs the independently sampled bootstrap forward bits with one existing continuous learning/control row. Sources: `sources/zip4/manuscript/07_public_setup.tex:5-25,121-123`, `sources/zip4/manuscript/appendix_b_communication.tex:7-58`, and the whole-row use in `sources/zip4/manuscript/08_main_theorem.tex:26-65`. The product and whole-row laws formalize preprocessing only; they make no claim about conditioning on public-good events or about execution.
-/

public section

open MeasureTheory Measure ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open unitInterval
open scoped unitInterval ENNReal

namespace Bandits.Support.CompletePublicTable

/-- The common ID array carrier, shared by all complete rows. -/
abbrev IDArray (p : ConstructorDimensions.Parameters) :=
  Fin (BootstrapDimensions.A_id p) → Fin p.T → Bool

/-- The forward-bit component of one complete row. -/
abbrev ForwardRow (p : ConstructorDimensions.Parameters) :=
  Fin (BootstrapDimensions.A_id p) → Fin p.T → Bool

/-- The family of forward-bit rows. -/
abbrev ForwardFamily (p : ConstructorDimensions.Parameters) :=
  Fin (ConstructorDimensions.M p) → ForwardRow p

/-- A fair bit law, represented by Mathlib's Bernoulli measure on `Bool`. -/
@[expose] noncomputable def fairBitParameter : I :=
  ⟨(1 / 2 : ℝ), by norm_num⟩

@[expose] noncomputable def fairBitLaw : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false fairBitParameter

instance fairBitLaw_probability : IsProbabilityMeasure fairBitLaw := by
  dsimp [fairBitLaw]
  infer_instance

/-- The accepted bootstrap dimensions put the forward Bernoulli parameter in
the unit interval: `2 * b_N ≤ L0` and `b_N > 0` imply `L0 ≥ 2`. -/
@[expose] noncomputable def forwardBitParameter (p : ConstructorDimensions.Parameters) : I :=
  ⟨1 - 1 / (BootstrapDimensions.L0 p : ℝ), by
    have hb := ConstructorDimensions.b_N_pos p
    have hcutoff := BootstrapDimensions.two_mul_b_N_le_L0 p
    have hLtwo : 2 ≤ BootstrapDimensions.L0 p := by omega
    have hLnat : 1 ≤ BootstrapDimensions.L0 p := Nat.le_trans (by decide) hLtwo
    have hLreal : (1 : ℝ) ≤ (BootstrapDimensions.L0 p : ℝ) := by
      exact_mod_cast hLnat
    have hLpos : (0 : ℝ) < (BootstrapDimensions.L0 p : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hLnat)
    have hrecip_nonneg : (0 : ℝ) ≤ 1 / (BootstrapDimensions.L0 p : ℝ) :=
      le_of_lt (one_div_pos.mpr hLpos)
    have hrecip_le : 1 / (BootstrapDimensions.L0 p : ℝ) ≤ 1 :=
      (div_le_one hLpos).2 hLreal
    constructor <;> linarith⟩

/-- A forward bit has probability `1 - 1/L0` of being true. -/
@[expose] noncomputable def forwardBitLaw (p : ConstructorDimensions.Parameters) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (forwardBitParameter p)

instance forwardBitLaw_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (forwardBitLaw p) := by
  dsimp [forwardBitLaw]
  infer_instance

@[simp] theorem fairBitLaw_true_mass : fairBitLaw.real {true} = (1 / 2 : ℝ) := by
  classical
  simp [fairBitLaw, fairBitParameter]

@[simp] theorem fairBitLaw_false_mass : fairBitLaw.real {false} = (1 / 2 : ℝ) := by
  classical
  norm_num [fairBitLaw, fairBitParameter]

@[simp] theorem forwardBitLaw_true_mass (p : ConstructorDimensions.Parameters) :
    (forwardBitLaw p).real {true} = 1 - 1 / (BootstrapDimensions.L0 p : ℝ) := by
  classical
  simp [forwardBitLaw, forwardBitParameter]

@[simp] theorem forwardBitLaw_false_mass (p : ConstructorDimensions.Parameters) :
    (forwardBitLaw p).real {false} = 1 / (BootstrapDimensions.L0 p : ℝ) := by
  classical
  simp [forwardBitLaw, forwardBitParameter]

/-- Literal finite product law for the shared ID array. -/
@[expose] noncomputable def idArrayMeasure (p : ConstructorDimensions.Parameters) : Measure (IDArray p) :=
  Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
    Measure.pi (fun _ : Fin p.T => fairBitLaw))

instance idArrayMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (idArrayMeasure p) := by
  dsimp [idArrayMeasure]
  infer_instance

/-- Literal finite product law for the forward bits in one row. -/
@[expose] noncomputable def forwardRowMeasure (p : ConstructorDimensions.Parameters) : Measure (ForwardRow p) :=
  Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
    Measure.pi (fun _ : Fin p.T => forwardBitLaw p))

instance forwardRowMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (forwardRowMeasure p) := by
  dsimp [forwardRowMeasure]
  infer_instance

/-- Literal product law for all forward rows. The shared ID array is not
replicated in this carrier. -/
@[expose] noncomputable def forwardFamilyMeasure (p : ConstructorDimensions.Parameters) :
    Measure (ForwardFamily p) :=
  Measure.pi (fun _ : Fin (ConstructorDimensions.M p) => forwardRowMeasure p)

instance forwardFamilyMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (forwardFamilyMeasure p) := by
  dsimp [forwardFamilyMeasure]
  infer_instance

/-- Joint law of the one ID array and the full forward family. -/
@[expose] noncomputable def bootstrapPublicMeasure (p : ConstructorDimensions.Parameters) :
    Measure (IDArray p × ForwardFamily p) :=
  (idArrayMeasure p).prod (forwardFamilyMeasure p)

instance bootstrapPublicMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (bootstrapPublicMeasure p) := by
  dsimp [bootstrapPublicMeasure]
  infer_instance

/-- Evaluation of one ID bit. -/
@[expose] def idCoordinate (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) (x : IDArray p) : Bool :=
  x u t

/-- Evaluation of one forward bit within one row. -/
@[expose] def forwardRowCoordinate (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) (x : ForwardRow p) : Bool :=
  x u t

/-- Evaluation of one forward bit in the family of rows. -/
@[expose] def forwardCoordinate (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) (u : Fin (BootstrapDimensions.A_id p))
    (t : Fin p.T) (x : ForwardFamily p) : Bool :=
  x q u t

theorem measurable_idCoordinate (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    Measurable (idCoordinate p u t) :=
  (measurable_pi_apply t).comp (measurable_pi_apply u)

theorem measurable_forwardRowCoordinate (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    Measurable (forwardRowCoordinate p u t) :=
  (measurable_pi_apply t).comp (measurable_pi_apply u)

theorem measurable_forwardCoordinate (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) (u : Fin (BootstrapDimensions.A_id p))
    (t : Fin p.T) : Measurable (forwardCoordinate p q u t) :=
  (measurable_pi_apply t).comp ((measurable_pi_apply u).comp (measurable_pi_apply q))

theorem measurable_forwardRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    Measurable (fun x : ForwardFamily p => x q) :=
  measurable_pi_apply q

private theorem prod_nested_two_eq_flat {α β γ : Type*} [Fintype α] [Fintype β]
    [CommMonoid γ] (f : α → β → γ) :
    (∏ a, ∏ b, f a b) = ∏ ab : α × β, f ab.1 ab.2 := by
  exact (Fintype.prod_prod_type' f).symm

private theorem real_preimage_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → Bool) (hf : AEMeasurable f μ) (b : Bool) :
    μ.real {x | f x = b} = (μ.map f).real {b} := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hf (by simp : MeasurableSet ({b} : Set Bool))]
  congr 1

private theorem prod_nested_three_eq_flat {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [CommMonoid δ] (f : α → β → γ → δ) :
    (∏ a : α, ∏ b : β, ∏ c : γ, f a b c) =
      ∏ abc : α × β × γ, f abc.1 abc.2.1 abc.2.2 := by
  calc
    (∏ a : α, ∏ b : β, ∏ c : γ, f a b c) =
        ∏ a : α, ∏ bc : β × γ, f a bc.1 bc.2 := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (Fintype.prod_prod_type' (fun b c => f a b c)).symm
    _ = ∏ abc : α × β × γ, f abc.1 abc.2.1 abc.2.2 :=
      (Fintype.prod_prod_type' (fun (a : α) (bc : β × γ) => f a bc.1 bc.2)).symm

private theorem nestedPi₂_flatten_law {ι κ γ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace γ] (ν : Measure γ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => ν))).map
      (fun x : ι → κ → γ => fun ij : ι × κ => x ij.1 ij.2) =
        Measure.pi (fun _ : ι × κ => ν) := by
  classical
  let flatten : (ι → κ → γ) → (ι × κ → γ) := fun x ij => x ij.1 ij.2
  have hflatten : Measurable flatten := by
    apply measurable_pi_iff.mpr
    intro ij
    exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hflatten.aemeasurable (MeasurableSet.univ_pi hs)]
  have hpre : flatten ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    simp [flatten, Set.mem_pi]
  rw [hpre]
  simp_rw [Measure.pi_pi]
  exact prod_nested_two_eq_flat (fun i j => ν (s (i, j)))

private theorem nestedPi₃_flatten_law {ι κ τ γ : Type*} [Fintype ι] [Fintype κ]
    [Fintype τ] [MeasurableSpace γ] (ν : Measure γ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ =>
      Measure.pi (fun _ : τ => ν)))).map
        (fun x : ι → κ → τ → γ => fun ijk : ι × κ × τ =>
          x ijk.1 ijk.2.1 ijk.2.2) =
      Measure.pi (fun _ : ι × κ × τ => ν) := by
  classical
  let flatten : (ι → κ → τ → γ) → (ι × κ × τ → γ) :=
    fun x ijk => x ijk.1 ijk.2.1 ijk.2.2
  have hflatten : Measurable flatten := by
    apply measurable_pi_iff.mpr
    intro ijk
    exact (measurable_pi_apply ijk.2.2).comp
      ((measurable_pi_apply ijk.2.1).comp (measurable_pi_apply ijk.1))
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hflatten.aemeasurable (MeasurableSet.univ_pi hs)]
  have hpre : flatten ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => Set.univ.pi (fun k => s (i, j, k)))) := by
    ext x
    simp [flatten, Set.mem_pi]
  rw [hpre]
  simp_rw [Measure.pi_pi]
  exact prod_nested_three_eq_flat (fun i j k => ν (s (i, j, k)))

@[expose] def idArrayFlatten (p : ConstructorDimensions.Parameters) (x : IDArray p) :
    Fin (BootstrapDimensions.A_id p) × Fin p.T → Bool :=
  fun ij => x ij.1 ij.2

theorem measurable_idArrayFlatten (p : ConstructorDimensions.Parameters) :
    Measurable (idArrayFlatten p) := by
  apply measurable_pi_iff.mpr
  intro ij
  exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)

/-- The complete ID vector has the flat Bernoulli product law, not merely
independent one-coordinate marginals. -/
theorem idArray_flatten_law (p : ConstructorDimensions.Parameters) :
    (idArrayMeasure p).map (idArrayFlatten p) =
      Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => fairBitLaw) := by
  change (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
    Measure.pi (fun _ : Fin p.T => fairBitLaw))).map
      (fun (x : Fin (BootstrapDimensions.A_id p) → Fin p.T → Bool)
        (ij : Fin (BootstrapDimensions.A_id p) × Fin p.T) => x ij.1 ij.2) = _
  exact nestedPi₂_flatten_law fairBitLaw

theorem idCoordinate_map (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (idArrayMeasure p).map (idCoordinate p u t) = fairBitLaw := by
  calc
    (idArrayMeasure p).map (idCoordinate p u t) =
        ((idArrayMeasure p).map (idArrayFlatten p)).map (fun x => x (u, t)) := by
      rw [Measure.map_map (measurable_pi_apply (u, t)) (measurable_idArrayFlatten p)]
      rfl
    _ = (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => fairBitLaw)).map
        (fun x => x (u, t)) := by rw [idArray_flatten_law]
    _ = fairBitLaw :=
      (measurePreserving_eval
        (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => fairBitLaw) (u, t)).map_eq

theorem idCoordinate_true_mass (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (idArrayMeasure p).real {x | idCoordinate p u t x = true} = (1 / 2 : ℝ) := by
  rw [real_preimage_measure (idArrayMeasure p) (idCoordinate p u t)
    (measurable_idCoordinate p u t).aemeasurable true]
  rw [idCoordinate_map, fairBitLaw_true_mass]

theorem idCoordinate_false_mass (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (idArrayMeasure p).real {x | idCoordinate p u t x = false} = (1 / 2 : ℝ) := by
  rw [real_preimage_measure (idArrayMeasure p) (idCoordinate p u t)
    (measurable_idCoordinate p u t).aemeasurable false]
  rw [idCoordinate_map, fairBitLaw_false_mass]

theorem iIndepFun_idCoordinate (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun ij : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
      idCoordinate p ij.1 ij.2) (idArrayMeasure p) := by
  have hmeas : ∀ ij : Fin (BootstrapDimensions.A_id p) × Fin p.T,
      AEMeasurable (idCoordinate p ij.1 ij.2) (idArrayMeasure p) := by
    intro ij
    exact (measurable_idCoordinate p ij.1 ij.2).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  change (idArrayMeasure p).map (idArrayFlatten p) =
    Measure.pi (fun ij : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
      (idArrayMeasure p).map (idCoordinate p ij.1 ij.2))
  rw [idArray_flatten_law]
  congr 1
  funext ij
  exact (idCoordinate_map p ij.1 ij.2).symm

@[expose] def forwardRowFlatten (p : ConstructorDimensions.Parameters) (x : ForwardRow p) :
    Fin (BootstrapDimensions.A_id p) × Fin p.T → Bool :=
  fun ij => x ij.1 ij.2

theorem measurable_forwardRowFlatten (p : ConstructorDimensions.Parameters) :
    Measurable (forwardRowFlatten p) := by
  apply measurable_pi_iff.mpr
  intro ij
  exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)

/-- The complete forward row has its full product law over `(u,t)`. -/
theorem forwardRow_flatten_law (p : ConstructorDimensions.Parameters) :
    (forwardRowMeasure p).map (forwardRowFlatten p) =
      Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p) := by
  change (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
    Measure.pi (fun _ : Fin p.T => forwardBitLaw p))).map
      (fun (x : Fin (BootstrapDimensions.A_id p) → Fin p.T → Bool)
        (ij : Fin (BootstrapDimensions.A_id p) × Fin p.T) => x ij.1 ij.2) = _
  exact nestedPi₂_flatten_law (forwardBitLaw p)

theorem forwardRowCoordinate_map (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (forwardRowMeasure p).map (forwardRowCoordinate p u t) = forwardBitLaw p := by
  calc
    (forwardRowMeasure p).map (forwardRowCoordinate p u t) =
        ((forwardRowMeasure p).map (forwardRowFlatten p)).map (fun x => x (u, t)) := by
      rw [Measure.map_map (measurable_pi_apply (u, t))
        (measurable_forwardRowFlatten p)]
      rfl
    _ = (Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
        forwardBitLaw p)).map (fun x => x (u, t)) := by rw [forwardRow_flatten_law]
    _ = forwardBitLaw p :=
      (measurePreserving_eval
        (fun _ : Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p) (u, t)).map_eq

theorem forwardRowCoordinate_true_mass (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (forwardRowMeasure p).real {x | forwardRowCoordinate p u t x = true} =
      1 - 1 / (BootstrapDimensions.L0 p : ℝ) := by
  rw [real_preimage_measure (forwardRowMeasure p) (forwardRowCoordinate p u t)
    (measurable_forwardRowCoordinate p u t).aemeasurable true]
  rw [forwardRowCoordinate_map, forwardBitLaw_true_mass]

theorem forwardRowCoordinate_false_mass (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (t : Fin p.T) :
    (forwardRowMeasure p).real {x | forwardRowCoordinate p u t x = false} =
      1 / (BootstrapDimensions.L0 p : ℝ) := by
  rw [real_preimage_measure (forwardRowMeasure p) (forwardRowCoordinate p u t)
    (measurable_forwardRowCoordinate p u t).aemeasurable false]
  rw [forwardRowCoordinate_map, forwardBitLaw_false_mass]

theorem iIndepFun_forwardRowCoordinate (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun ij : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
      forwardRowCoordinate p ij.1 ij.2) (forwardRowMeasure p) := by
  have hmeas : ∀ ij : Fin (BootstrapDimensions.A_id p) × Fin p.T,
      AEMeasurable (forwardRowCoordinate p ij.1 ij.2) (forwardRowMeasure p) := by
    intro ij
    exact (measurable_forwardRowCoordinate p ij.1 ij.2).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  change (forwardRowMeasure p).map (forwardRowFlatten p) =
    Measure.pi (fun ij : Fin (BootstrapDimensions.A_id p) × Fin p.T =>
      (forwardRowMeasure p).map (forwardRowCoordinate p ij.1 ij.2))
  rw [forwardRow_flatten_law]
  congr 1
  funext ij
  exact (forwardRowCoordinate_map p ij.1 ij.2).symm

@[expose] def forwardFamilyFlatten (p : ConstructorDimensions.Parameters)
    (x : ForwardFamily p) :
      Fin (ConstructorDimensions.M p) × Fin (BootstrapDimensions.A_id p) × Fin p.T → Bool :=
  fun ijk => x ijk.1 ijk.2.1 ijk.2.2

theorem measurable_forwardFamilyFlatten (p : ConstructorDimensions.Parameters) :
    Measurable (forwardFamilyFlatten p) := by
  apply measurable_pi_iff.mpr
  intro ijk
  exact (measurable_pi_apply ijk.2.2).comp
    ((measurable_pi_apply ijk.2.1).comp (measurable_pi_apply ijk.1))

/-- The full family law is the flat product law over every `(row, ID, time)`
coordinate, preserving the whole vector law. -/
theorem forwardFamily_flatten_law (p : ConstructorDimensions.Parameters) :
    (forwardFamilyMeasure p).map (forwardFamilyFlatten p) =
      Measure.pi (fun _ : Fin (ConstructorDimensions.M p) ×
        Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p) := by
  change (Measure.pi (fun _ : Fin (ConstructorDimensions.M p) =>
    Measure.pi (fun _ : Fin (BootstrapDimensions.A_id p) =>
      Measure.pi (fun _ : Fin p.T => forwardBitLaw p)))).map
        (fun (x : Fin (ConstructorDimensions.M p) →
          Fin (BootstrapDimensions.A_id p) → Fin p.T → Bool)
          (ijk : Fin (ConstructorDimensions.M p) ×
            Fin (BootstrapDimensions.A_id p) × Fin p.T) =>
              x ijk.1 ijk.2.1 ijk.2.2) = _
  exact nestedPi₃_flatten_law (forwardBitLaw p)

theorem forwardCoordinate_map (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) (u : Fin (BootstrapDimensions.A_id p))
    (t : Fin p.T) :
    (forwardFamilyMeasure p).map (forwardCoordinate p q u t) = forwardBitLaw p := by
  calc
    (forwardFamilyMeasure p).map (forwardCoordinate p q u t) =
        ((forwardFamilyMeasure p).map (forwardFamilyFlatten p)).map
          (fun x => x (q, u, t)) := by
      rw [Measure.map_map (measurable_pi_apply (q, u, t))
        (measurable_forwardFamilyFlatten p)]
      rfl
    _ = (Measure.pi (fun _ : Fin (ConstructorDimensions.M p) ×
        Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p)).map
          (fun x => x (q, u, t)) := by rw [forwardFamily_flatten_law]
    _ = forwardBitLaw p :=
      (measurePreserving_eval
        (fun _ : Fin (ConstructorDimensions.M p) ×
          Fin (BootstrapDimensions.A_id p) × Fin p.T => forwardBitLaw p) (q, u, t)).map_eq

theorem forwardCoordinate_true_mass (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) (u : Fin (BootstrapDimensions.A_id p))
    (t : Fin p.T) :
    (forwardFamilyMeasure p).real {x | forwardCoordinate p q u t x = true} =
      1 - 1 / (BootstrapDimensions.L0 p : ℝ) := by
  rw [real_preimage_measure (forwardFamilyMeasure p) (forwardCoordinate p q u t)
    (measurable_forwardCoordinate p q u t).aemeasurable true]
  rw [forwardCoordinate_map, forwardBitLaw_true_mass]

theorem forwardCoordinate_false_mass (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) (u : Fin (BootstrapDimensions.A_id p))
    (t : Fin p.T) :
    (forwardFamilyMeasure p).real {x | forwardCoordinate p q u t x = false} =
      1 / (BootstrapDimensions.L0 p : ℝ) := by
  rw [real_preimage_measure (forwardFamilyMeasure p) (forwardCoordinate p q u t)
    (measurable_forwardCoordinate p q u t).aemeasurable false]
  rw [forwardCoordinate_map, forwardBitLaw_false_mass]

theorem iIndepFun_forwardCoordinate (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun ijk : Fin (ConstructorDimensions.M p) ×
      Fin (BootstrapDimensions.A_id p) × Fin p.T =>
        forwardCoordinate p ijk.1 ijk.2.1 ijk.2.2) (forwardFamilyMeasure p) := by
  have hmeas : ∀ ijk : Fin (ConstructorDimensions.M p) ×
      Fin (BootstrapDimensions.A_id p) × Fin p.T,
      AEMeasurable (forwardCoordinate p ijk.1 ijk.2.1 ijk.2.2) (forwardFamilyMeasure p) := by
    intro ijk
    exact (measurable_forwardCoordinate p ijk.1 ijk.2.1 ijk.2.2).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  change (forwardFamilyMeasure p).map (forwardFamilyFlatten p) =
    Measure.pi (fun ijk : Fin (ConstructorDimensions.M p) ×
      Fin (BootstrapDimensions.A_id p) × Fin p.T =>
        (forwardFamilyMeasure p).map
          (forwardCoordinate p ijk.1 ijk.2.1 ijk.2.2))
  rw [forwardFamily_flatten_law]
  congr 1
  funext ijk
  exact (forwardCoordinate_map p ijk.1 ijk.2.1 ijk.2.2).symm

/-- The pushforward onto one complete forward row is its full row product law. -/
theorem measurePreserving_forwardRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    MeasurePreserving (fun x : ForwardFamily p => x q)
      (forwardFamilyMeasure p) (forwardRowMeasure p) :=
  measurePreserving_eval (fun _ : Fin (ConstructorDimensions.M p) => forwardRowMeasure p) q

theorem map_forwardRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    (forwardFamilyMeasure p).map (fun x : ForwardFamily p => x q) = forwardRowMeasure p :=
  (measurePreserving_forwardRowProjection p q).map_eq

/-- All forward rows are mutually independent as complete vectors. -/
theorem iIndepFun_forwardRows (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun q : Fin (ConstructorDimensions.M p) => fun x : ForwardFamily p => x q)
      (forwardFamilyMeasure p) :=
  iIndepFun_pi (fun _ : Fin (ConstructorDimensions.M p) => aemeasurable_id)

/-- Distinct complete forward rows are independent. -/
theorem indepFun_distinct_forwardRows (p : ConstructorDimensions.Parameters)
    (q r : Fin (ConstructorDimensions.M p)) (hqr : q ≠ r) :
    (fun x : ForwardFamily p => x q) ⟂ᵢ[forwardFamilyMeasure p]
      (fun x => x r) := by
  exact (iIndepFun_forwardRows p).indepFun hqr

/-- Fixing the common ID array leaves the complete forward family with the
same product law. This law concerns the array construction only; it does not
assert independence after conditioning on a published-good event. -/
@[expose] noncomputable def fixedIDForwardFamilyLaw (p : ConstructorDimensions.Parameters)
    (_id : IDArray p) : Measure (ForwardFamily p) :=
  forwardFamilyMeasure p

instance fixedIDForwardFamilyLaw_probability (p : ConstructorDimensions.Parameters)
    (id : IDArray p) : IsProbabilityMeasure (fixedIDForwardFamilyLaw p id) := by
  change IsProbabilityMeasure (forwardFamilyMeasure p)
  infer_instance

theorem fixedID_forwardRows_independent (p : ConstructorDimensions.Parameters)
    (id : IDArray p) :
    iIndepFun (fun q : Fin (ConstructorDimensions.M p) =>
      fun x : ForwardFamily p => x q) (fixedIDForwardFamilyLaw p id) := by
  exact iIndepFun_forwardRows p

/-- The explicit joint law with an ID array held fixed. -/
@[expose] noncomputable def fixedIDPublicMeasure (p : ConstructorDimensions.Parameters)
    (id : IDArray p) : Measure (IDArray p × ForwardFamily p) :=
  (Measure.dirac id).prod (fixedIDForwardFamilyLaw p id)

instance fixedIDPublicMeasure_probability (p : ConstructorDimensions.Parameters)
    (id : IDArray p) : IsProbabilityMeasure (fixedIDPublicMeasure p id) := by
  dsimp [fixedIDPublicMeasure]
  infer_instance

theorem fixedIDPublicMeasure_id_marginal (p : ConstructorDimensions.Parameters)
    (id : IDArray p) :
    (fixedIDPublicMeasure p id).fst = Measure.dirac id := by
  simp [fixedIDPublicMeasure]

theorem fixedIDPublicMeasure_forward_marginal (p : ConstructorDimensions.Parameters)
    (id : IDArray p) :
    (fixedIDPublicMeasure p id).snd = fixedIDForwardFamilyLaw p id := by
  simp [fixedIDPublicMeasure]

/-- The entire ID array and entire forward family are independent under their
joint preprocessing law. -/
theorem indepFun_idArray_forwardFamily (p : ConstructorDimensions.Parameters) :
    (fun x : IDArray p × ForwardFamily p => x.1) ⟂ᵢ[bootstrapPublicMeasure p]
      (fun x => x.2) := by
  exact indepFun_prod measurable_id measurable_id

/-! ## Complete rows and the published output -/

/-- One source complete row: forward bits paired with the accepted continuous
learning/control row, with no replacement carrier for either component.
Source: `sources/zip4/manuscript/appendix_b_communication.tex:17-58`. -/
abbrev CompleteRow (p : ConstructorDimensions.Parameters) :=
  ForwardRow p × ContinuousLearningRows.LearningRow p

/-- The complete-row family, indexed by the source row count `M p`. -/
abbrev CompleteRows (p : ConstructorDimensions.Parameters) :=
  Fin (ConstructorDimensions.M p) → CompleteRow p

/-- The single shared ID array paired with the complete-row family. -/
abbrev PublishedOutput (p : ConstructorDimensions.Parameters) :=
  IDArray p × CompleteRows p

/-- The product law of the bootstrap forward bits and one accepted learning
row. -/
@[expose] noncomputable def completeRowMeasure (p : ConstructorDimensions.Parameters) :
    Measure (CompleteRow p) :=
  (forwardRowMeasure p).prod (ContinuousLearningRows.learningRowLaw p)

instance completeRowMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (completeRowMeasure p) := by
  dsimp [completeRowMeasure]
  infer_instance

/-- Independent complete rows, each with the literal forward/learning product
law. -/
@[expose] noncomputable def completeRowsMeasure (p : ConstructorDimensions.Parameters) :
    Measure (CompleteRows p) :=
  Measure.pi (fun _ : Fin (ConstructorDimensions.M p) => completeRowMeasure p)

instance completeRowsMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (completeRowsMeasure p) := by
  dsimp [completeRowsMeasure]
  infer_instance

/-- The public output law has one common ID array and one independent family
of complete rows. -/
@[expose] noncomputable def publishedOutputMeasure
    (p : ConstructorDimensions.Parameters) : Measure (PublishedOutput p) :=
  (idArrayMeasure p).prod (completeRowsMeasure p)

instance publishedOutputMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (publishedOutputMeasure p) := by
  dsimp [publishedOutputMeasure]
  infer_instance

/-- Projection of the one common ID array from the published output. -/
@[expose] def publishedID (p : ConstructorDimensions.Parameters)
    (x : PublishedOutput p) : IDArray p := x.1

/-- Projection of the complete-row family from the published output. -/
@[expose] def publishedRows (p : ConstructorDimensions.Parameters)
    (x : PublishedOutput p) : CompleteRows p := x.2

theorem measurable_publishedID (p : ConstructorDimensions.Parameters) :
    Measurable (publishedID p) := measurable_fst

theorem measurable_publishedRows (p : ConstructorDimensions.Parameters) :
    Measurable (publishedRows p) := measurable_snd

theorem measurePreserving_publishedID (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (publishedID p) (publishedOutputMeasure p) (idArrayMeasure p) := by
  dsimp [publishedID, publishedOutputMeasure]
  exact measurePreserving_fst

theorem map_publishedID (p : ConstructorDimensions.Parameters) :
    (publishedOutputMeasure p).map (publishedID p) = idArrayMeasure p :=
  (measurePreserving_publishedID p).map_eq

theorem measurePreserving_publishedRows (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (publishedRows p) (publishedOutputMeasure p) (completeRowsMeasure p) := by
  dsimp [publishedRows, publishedOutputMeasure]
  exact measurePreserving_snd

theorem map_publishedRows (p : ConstructorDimensions.Parameters) :
    (publishedOutputMeasure p).map (publishedRows p) = completeRowsMeasure p :=
  (measurePreserving_publishedRows p).map_eq

/-- The forward-family projection of all complete rows. -/
@[expose] def completeRowsForward (p : ConstructorDimensions.Parameters)
    (r : CompleteRows p) : ForwardFamily p :=
  fun q => (r q).1

/-- The learning-family projection reuses the existing learning-row carrier. -/
@[expose] def completeRowsLearning (p : ConstructorDimensions.Parameters)
    (r : CompleteRows p) : ContinuousLearningRows.LearningRows p :=
  fun q => (r q).2

/-- Regroup all complete rows into the full forward family and full learning
family. -/
@[expose] def splitCompleteRows (p : ConstructorDimensions.Parameters)
    (r : CompleteRows p) :
      ForwardFamily p × ContinuousLearningRows.LearningRows p :=
  (completeRowsForward p r, completeRowsLearning p r)

theorem measurable_completeRowsForward (p : ConstructorDimensions.Parameters) :
    Measurable (completeRowsForward p) := by
  apply measurable_pi_iff.mpr
  intro q
  exact measurable_fst.comp (measurable_pi_apply q)

theorem measurable_completeRowsLearning (p : ConstructorDimensions.Parameters) :
    Measurable (completeRowsLearning p) := by
  apply measurable_pi_iff.mpr
  intro q
  exact measurable_snd.comp (measurable_pi_apply q)

theorem measurable_splitCompleteRows (p : ConstructorDimensions.Parameters) :
    Measurable (splitCompleteRows p) :=
  (measurable_completeRowsForward p).prodMk (measurable_completeRowsLearning p)

/-- Regrouping is measure preserving onto the product of the entire forward
family and the entire existing learning-row family. This is a whole-vector
law, not a conclusion from coordinate marginals. -/
theorem measurePreserving_splitCompleteRows (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (splitCompleteRows p) (completeRowsMeasure p)
      ((forwardFamilyMeasure p).prod (ContinuousLearningRows.learningRowsLaw p)) := by
  exact measurePreserving_arrowProdEquivProdArrow
    (ForwardRow p) (ContinuousLearningRows.LearningRow p)
    (Fin (ConstructorDimensions.M p))
    (fun _ => forwardRowMeasure p)
    (fun _ => ContinuousLearningRows.learningRowLaw p)

theorem map_splitCompleteRows (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (splitCompleteRows p) =
      (forwardFamilyMeasure p).prod (ContinuousLearningRows.learningRowsLaw p) :=
  (measurePreserving_splitCompleteRows p).map_eq

/-- Every indexed complete row has the complete-row product law. -/
theorem measurePreserving_completeRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    MeasurePreserving (fun r : CompleteRows p => r q)
      (completeRowsMeasure p) (completeRowMeasure p) :=
  measurePreserving_eval _ q

theorem map_completeRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    (completeRowsMeasure p).map (fun r : CompleteRows p => r q) = completeRowMeasure p :=
  (measurePreserving_completeRowProjection p q).map_eq

theorem measurable_completeRowProjection (p : ConstructorDimensions.Parameters)
    (q : Fin (ConstructorDimensions.M p)) :
    Measurable (fun r : CompleteRows p => r q) :=
  (measurePreserving_completeRowProjection p q).measurable

/-- Forward bits from a whole complete row. -/
@[expose] def completeRowForward (p : ConstructorDimensions.Parameters)
    (r : CompleteRow p) : ForwardRow p := r.1

/-- The existing continuous learning row from a whole complete row. -/
@[expose] def completeRowLearning (p : ConstructorDimensions.Parameters)
    (r : CompleteRow p) : ContinuousLearningRows.LearningRow p := r.2

theorem measurable_completeRowForward (p : ConstructorDimensions.Parameters) :
    Measurable (completeRowForward p) := measurable_fst

theorem measurable_completeRowLearning (p : ConstructorDimensions.Parameters) :
    Measurable (completeRowLearning p) := measurable_snd

theorem measurePreserving_completeRowForward (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeRowForward p) (completeRowMeasure p) (forwardRowMeasure p) := by
  dsimp [completeRowForward, completeRowMeasure]
  exact measurePreserving_fst

theorem map_completeRowForward (p : ConstructorDimensions.Parameters) :
    (completeRowMeasure p).map (completeRowForward p) = forwardRowMeasure p :=
  (measurePreserving_completeRowForward p).map_eq

theorem measurePreserving_completeRowLearning (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeRowLearning p) (completeRowMeasure p)
      (ContinuousLearningRows.learningRowLaw p) := by
  dsimp [completeRowLearning, completeRowMeasure]
  exact measurePreserving_snd

theorem map_completeRowLearning (p : ConstructorDimensions.Parameters) :
    (completeRowMeasure p).map (completeRowLearning p) =
      ContinuousLearningRows.learningRowLaw p :=
  (measurePreserving_completeRowLearning p).map_eq

/-- Complete rows are mutually independent as whole row vectors. -/
theorem iIndepFun_completeRows (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun q : Fin (ConstructorDimensions.M p) =>
      fun r : CompleteRows p => r q) (completeRowsMeasure p) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

theorem indepFun_distinct_completeRows (p : ConstructorDimensions.Parameters)
    (q q' : Fin (ConstructorDimensions.M p)) (hqq' : q ≠ q') :
    (fun r : CompleteRows p => r q) ⟂ᵢ[completeRowsMeasure p]
      (fun r => r q') :=
  (iIndepFun_completeRows p).indepFun hqq'

/-- The two components of one complete row have their independent product
law. -/
theorem indepFun_completeRowForwardLearning (p : ConstructorDimensions.Parameters) :
    (Prod.fst : CompleteRow p → ForwardRow p) ⟂ᵢ[completeRowMeasure p] Prod.snd := by
  exact indepFun_prod measurable_id measurable_id

/-- Push the entire forward family out of the complete-row family. -/
theorem measurePreserving_completeRowsForward (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeRowsForward p) (completeRowsMeasure p)
      (forwardFamilyMeasure p) :=
  measurePreserving_fst.comp (measurePreserving_splitCompleteRows p)

theorem map_completeRowsForward (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (completeRowsForward p) = forwardFamilyMeasure p :=
  (measurePreserving_completeRowsForward p).map_eq

/-- Push the entire accepted learning-row family out of the complete-row
family. -/
theorem measurePreserving_completeRowsLearning (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeRowsLearning p) (completeRowsMeasure p)
      (ContinuousLearningRows.learningRowsLaw p) :=
  measurePreserving_snd.comp (measurePreserving_splitCompleteRows p)

theorem map_completeRowsLearning (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (completeRowsLearning p) =
      ContinuousLearningRows.learningRowsLaw p :=
  (measurePreserving_completeRowsLearning p).map_eq

/-- The entire forward family and the entire learning family remain
independent. -/
private theorem indepFun_pullback {Ω Ω' X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {ν : Measure Ω'} {g : Ω → Ω'}
    (hg : MeasurePreserving g μ ν) {f : Ω' → X} {k : Ω' → Y}
    (hf : Measurable f) (hk : Measurable k) (h : IndepFun f k ν) :
    IndepFun (f ∘ g) (k ∘ g) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hst := h s t hs ht
  rw [← hg.map_eq, Measure.map_apply hg.measurable ((hf hs).inter (hk ht)),
    Measure.map_apply hg.measurable (hf hs), Measure.map_apply hg.measurable (hk ht)] at hst
  exact hst

theorem indepFun_completeRowsForwardLearning (p : ConstructorDimensions.Parameters) :
    (completeRowsForward p) ⟂ᵢ[completeRowsMeasure p] (completeRowsLearning p) := by
  have h := indepFun_pullback (measurePreserving_splitCompleteRows p)
    measurable_fst measurable_snd (indepFun_prod measurable_id measurable_id)
  change IndepFun (Prod.fst ∘ splitCompleteRows p) (Prod.snd ∘ splitCompleteRows p)
    (completeRowsMeasure p)
  exact h

/-- The complete-row family and the one common ID array are independent under
the published-output law. -/
theorem indepFun_publishedID_completeRows (p : ConstructorDimensions.Parameters) :
    (fun x : PublishedOutput p => x.1) ⟂ᵢ[publishedOutputMeasure p]
      (fun x => x.2) :=
  indepFun_prod measurable_id measurable_id

/-- The scalar table of the complete rows, transported through the accepted
learning projection without changing its `[0,1)` coordinates. -/
@[expose] def completeScalarStreams (p : ConstructorDimensions.Parameters)
    (r : CompleteRows p) :
      ContinuousLearningRows.ScalarIndex p → ContinuousLearningRows.Scalar :=
  ContinuousLearningRows.scalarStreams (completeRowsLearning p r)

/-- Every reserved affine vector in the complete-row family. -/
@[expose] def completeAffineStreams (p : ConstructorDimensions.Parameters)
    (r : CompleteRows p) :
      ContinuousLearningRows.AffineIndex p →
        AffineChannelLaw.Sample (ContinuousLearningRows.B p) :=
  ContinuousLearningRows.affineStreams (completeRowsLearning p r)

theorem measurable_completeScalarStreams (p : ConstructorDimensions.Parameters) :
    Measurable (completeScalarStreams p) :=
  (ContinuousLearningRows.measurable_scalarStreams p).comp
    (measurable_completeRowsLearning p)

theorem measurePreserving_completeScalarStreams (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeScalarStreams p) (completeRowsMeasure p)
      (ContinuousLearningRows.scalarStreamsLaw p) := by
  exact (ContinuousLearningRows.measurePreserving_scalarStreams p).comp
    (measurePreserving_completeRowsLearning p)

theorem map_completeScalarStreams (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (completeScalarStreams p) =
      ContinuousLearningRows.scalarStreamsLaw p :=
  (measurePreserving_completeScalarStreams p).map_eq

theorem measurable_completeAffineStreams (p : ConstructorDimensions.Parameters) :
    Measurable (completeAffineStreams p) :=
  (ContinuousLearningRows.measurable_affineStreams p).comp
    (measurable_completeRowsLearning p)

theorem measurePreserving_completeAffineStreams (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (completeAffineStreams p) (completeRowsMeasure p)
      (ContinuousLearningRows.affineStreamsLaw p) := by
  exact (ContinuousLearningRows.measurePreserving_affineStreams p).comp
    (measurePreserving_completeRowsLearning p)

theorem map_completeAffineStreams (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (completeAffineStreams p) =
      ContinuousLearningRows.affineStreamsLaw p :=
  (measurePreserving_completeAffineStreams p).map_eq

/-- The entire scalar table and entire affine-vector table remain independent
inside a complete-row family. -/
theorem indepFun_completeScalarStreams_completeAffineStreams
    (p : ConstructorDimensions.Parameters) :
    (completeScalarStreams p) ⟂ᵢ[completeRowsMeasure p] (completeAffineStreams p) := by
  have h := indepFun_pullback (measurePreserving_completeRowsLearning p)
    (ContinuousLearningRows.measurable_scalarStreams p)
    (ContinuousLearningRows.measurable_affineStreams p)
    (ContinuousLearningRows.indepFun_scalarStreams_affineStreams p)
  change IndepFun
    (ContinuousLearningRows.scalarStreams ∘ completeRowsLearning p)
    (ContinuousLearningRows.affineStreams ∘ completeRowsLearning p)
    (completeRowsMeasure p)
  exact h

/-- The exact joint law of the whole continuous scalar and affine tables. -/
theorem map_completeScalarStreams_completeAffineStreams
    (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (fun r =>
      (completeScalarStreams p r, completeAffineStreams p r)) =
        (ContinuousLearningRows.scalarStreamsLaw p).prod
          (ContinuousLearningRows.affineStreamsLaw p) := by
  rw [(indepFun_completeScalarStreams_completeAffineStreams p).map_prod_eq_prod_map_map
    (measurable_completeScalarStreams p).aemeasurable
    (measurable_completeAffineStreams p).aemeasurable,
    map_completeScalarStreams, map_completeAffineStreams]

/-- The full table of real scalar values has the accepted product-uniform
law on the half-open cube. -/
theorem map_completeRealScalarStreams (p : ConstructorDimensions.Parameters) :
    (completeRowsMeasure p).map (fun r =>
      ContinuousLearningRows.scalarValues (completeScalarStreams p r)) =
        (Measure.pi (fun _ : ContinuousLearningRows.ScalarIndex p =>
          (volume : Measure ℝ))).restrict
          (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  calc
    _ = ((completeRowsMeasure p).map (completeScalarStreams p)).map
        ContinuousLearningRows.scalarValues :=
      (Measure.map_map (ContinuousLearningRows.measurable_scalarValues _)
        (measurable_completeScalarStreams p)).symm
    _ = _ := by
      rw [map_completeScalarStreams]
      exact ContinuousLearningRows.map_scalarValues _

/-- Fixing the one shared ID array leaves all complete rows at their literal
independent product law. -/
@[expose] noncomputable def fixedIDCompleteRowsMeasure
    (p : ConstructorDimensions.Parameters) (_id : IDArray p) : Measure (CompleteRows p) :=
  completeRowsMeasure p

instance fixedIDCompleteRowsMeasure_probability (p : ConstructorDimensions.Parameters)
    (id : IDArray p) : IsProbabilityMeasure (fixedIDCompleteRowsMeasure p id) := by
  change IsProbabilityMeasure (completeRowsMeasure p)
  infer_instance

theorem iIndepFun_fixedID_completeRows (p : ConstructorDimensions.Parameters)
    (id : IDArray p) :
    iIndepFun (fun q : Fin (ConstructorDimensions.M p) =>
      fun r : CompleteRows p => r q) (fixedIDCompleteRowsMeasure p id) := by
  change iIndepFun (fun q : Fin (ConstructorDimensions.M p) =>
    fun r : CompleteRows p => r q) (completeRowsMeasure p)
  exact iIndepFun_completeRows p

/-- The fixed-ID published law has a point mass on the shared ID table and
the unchanged independent complete-row product law. -/
@[expose] noncomputable def fixedIDPublishedOutputMeasure
    (p : ConstructorDimensions.Parameters) (id : IDArray p) :
      Measure (PublishedOutput p) :=
  (Measure.dirac id).prod (fixedIDCompleteRowsMeasure p id)

instance fixedIDPublishedOutputMeasure_probability (p : ConstructorDimensions.Parameters)
    (id : IDArray p) : IsProbabilityMeasure (fixedIDPublishedOutputMeasure p id) := by
  dsimp [fixedIDPublishedOutputMeasure]
  infer_instance

theorem fixedIDPublishedOutputMeasure_id_marginal (p : ConstructorDimensions.Parameters)
    (id : IDArray p) :
    (fixedIDPublishedOutputMeasure p id).fst = Measure.dirac id := by
  simp [fixedIDPublishedOutputMeasure]

theorem fixedIDPublishedOutputMeasure_rows_marginal
    (p : ConstructorDimensions.Parameters) (id : IDArray p) :
    (fixedIDPublishedOutputMeasure p id).snd = fixedIDCompleteRowsMeasure p id := by
  simp [fixedIDPublishedOutputMeasure]

end Bandits.Support.CompletePublicTable

end
