/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceTotalSourceDisintegration
public import Bandits.Support.ReferenceTotalSourcePhysicalCongruence

/-!
# Finite chronological resampling of the original source

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-426`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-46`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

This module iterates the accepted conditional kernel on finite Pi spaces of
the original complete source. Its stages are measure-theoretic source samples,
not a second physical run. The physical congruence is transported along the
actual adjacent source laws. No logical refresh process or deferred logical
slow-set law is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceFiniteSourcePath

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceTotalSourceDisintegration.RateInput
abbrev SourceInput := ReferenceTotalSourceDisintegration.SourceInput
abbrev TimeControl := ReferenceTotalSourceDisintegration.TimeControl
abbrev SourcePath (p : Parameters) (k : ℕ) := Fin (k + 1) → SourceInput p

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)

/-- Append one original-source point to a finite Pi path. -/
def appendFiniteSourcePath (k : ℕ)
    (pair : SourcePath p k × SourceInput p) : SourcePath p (k + 1) :=
  Fin.snoc (α := fun _ : Fin (k + 2) => SourceInput p) pair.1 pair.2

private theorem measurable_appendFiniteSourcePath (k : ℕ) :
    Measurable (appendFiniteSourcePath (p := p) k) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [appendFiniteSourcePath, Fin.snoc_last] using
      (measurable_snd : Measurable (fun pair : SourcePath p k × SourceInput p => pair.2))
  ·
    simp only [appendFiniteSourcePath, Fin.snoc_castSucc]
    convert (measurable_pi_apply j).comp (measurable_fst :
      Measurable (fun pair : SourcePath p k × SourceInput p => pair.1)) using 1
    funext pair
    rfl

/-- Pull the accepted source kernel back along the path's last coordinate.
The time index exists only when `k < T`. -/
def finiteSourcePathTransition (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (k : ℕ) (hk : k < p.T) :
    Kernel (SourcePath p k) (SourceInput p) :=
  (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
    ⟨k, hk⟩ control0).comap (fun path => path (Fin.last k))
      (measurable_pi_apply (Fin.last k))

/-- The finite law on stages `0,...,k`, built from the original source law and
the actual pulled-back source kernel at each playable time. -/
def finiteSourcePathLaw (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    (k : ℕ) → k ≤ p.T → Measure (SourcePath p k)
  | 0, _ => (sourceInputLaw p).map (fun z (_ : Fin 1) => z)
  | k + 1, hk =>
      ((finiteSourcePathLaw rate rewards C_star C_h control0 k
          (Nat.le_of_succ_le hk)).compProd
        (finiteSourcePathTransition rate rewards C_star C_h control0 k
          (Nat.lt_of_succ_le hk))).map
        (appendFiniteSourcePath (p := p) k)

@[simp]
theorem finiteSourcePathLaw_zero (hk : 0 ≤ p.T) :
    finiteSourcePathLaw rate rewards C_star C_h control0 0 hk =
      (sourceInputLaw p).map (fun z (_ : Fin 1) => z) := rfl

/-- Exact chronological recursion. The sole new point is drawn from the
accepted kernel at time `k`, pulled back by the old path's last evaluation. -/
theorem finiteSourcePathLaw_succ (k : ℕ) (hk : k + 1 ≤ p.T) :
    finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk =
      ((finiteSourcePathLaw rate rewards C_star C_h control0 k
          (Nat.le_of_succ_le hk)).compProd
        (finiteSourcePathTransition rate rewards C_star C_h control0 k
          (Nat.lt_of_succ_le hk))).map
        (appendFiniteSourcePath (p := p) k) := rfl

theorem finiteSourcePathLaw_probability (k : ℕ) (hk : k ≤ p.T) :
    IsProbabilityMeasure
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) := by
  induction k with
  | zero =>
      rw [finiteSourcePathLaw_zero]
      infer_instance
  | succ k ih =>
      rw [finiteSourcePathLaw_succ]
      have := ih (Nat.le_of_succ_le hk)
      let κ := finiteSourcePathTransition rate rewards C_star C_h control0 k
        (Nat.lt_of_succ_le hk)
      have : IsMarkovKernel κ := by
        dsimp [κ, finiteSourcePathTransition]
        infer_instance
      have : AEMeasurable (appendFiniteSourcePath (p := p) k)
          (finiteSourcePathLaw rate rewards C_star C_h control0 k
            (Nat.le_of_succ_le hk) ⊗ₘ κ) :=
        (measurable_appendFiniteSourcePath (p := p) k).aemeasurable
      infer_instance

private theorem measurable_adjacentMap (k : ℕ) (i : Fin k) :
    Measurable (fun path : SourcePath p k => (path i.castSucc, path i.succ)) :=
  (measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ)

private theorem measurable_lastPairMap (k : ℕ) :
    Measurable (fun path : SourcePath p (k + 1) =>
      (path (Fin.last k).castSucc, path (Fin.last (k + 1)))) :=
  (measurable_pi_apply _).prodMk (measurable_pi_apply _)

private theorem map_comap_compProd
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel β γ) [IsMarkovKernel κ]
    (f : α → β) (hf : Measurable f) :
    Measure.map (fun z : α × γ => (f z.1, z.2)) (μ.compProd (κ.comap f hf)) =
      (μ.map f).compProd κ := by
  let : IsProbabilityMeasure (μ.compProd (κ.comap f hf)) := inferInstance
  apply Measure.ext_prod
  intro s t hs ht
  change (Measure.map (Prod.map f id) (μ.compProd (κ.comap f hf))) (s ×ˢ t) = _
  rw [Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  have hpre : (Prod.map f id) ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ×ˢ t := by
    ext z
    simp
  rw [hpre, Measure.compProd_apply_prod (hs.preimage hf) ht,
    Measure.compProd_apply_prod hs ht]
  simp only [Kernel.comap_apply]
  exact (MeasureTheory.setLIntegral_map hs (Kernel.measurable_coe κ ht) hf).symm

private theorem map_snoc_old_coordinate (k : ℕ)
    (μ : Measure (SourcePath p k)) [IsProbabilityMeasure μ]
    (κ : Kernel (SourcePath p k) (SourceInput p)) [IsMarkovKernel κ]
    (i : Fin (k + 1)) :
    Measure.map (fun path : SourcePath p (k + 1) => path i.castSucc)
        ((μ.compProd κ).map (appendFiniteSourcePath (p := p) k)) =
      Measure.map (fun path : SourcePath p k => path i) μ := by
  calc
    Measure.map (fun path : SourcePath p (k + 1) => path i.castSucc)
        ((μ.compProd κ).map (appendFiniteSourcePath (p := p) k)) =
      Measure.map (fun pair : SourcePath p k × SourceInput p => pair.1 i)
        (μ.compProd κ) := by
          rw [Measure.map_map (measurable_pi_apply i.castSucc)
            (measurable_appendFiniteSourcePath (p := p) k)]
          congr 1
          funext pair
          simp only [Function.comp_apply, appendFiniteSourcePath, Fin.snoc_castSucc]
    _ = Measure.map (fun path : SourcePath p k => path i)
        ((μ.compProd κ).fst) := by
          change Measure.map (fun pair : SourcePath p k × SourceInput p => pair.1 i)
              (μ.compProd κ) =
            Measure.map (fun path : SourcePath p k => path i)
              (Measure.map Prod.fst (μ.compProd κ))
          rw [Measure.map_map (measurable_pi_apply i) measurable_fst]
          congr 1
    _ = Measure.map (fun path : SourcePath p k => path i) μ := by
          rw [Measure.fst_compProd]

private theorem map_snoc_old_adjacent (k : ℕ)
    (μ : Measure (SourcePath p k)) [IsProbabilityMeasure μ]
    (κ : Kernel (SourcePath p k) (SourceInput p)) [IsMarkovKernel κ]
    (i : Fin k) :
    Measure.map (fun path : SourcePath p (k + 1) =>
      (path i.castSucc.castSucc, path i.succ.castSucc))
        ((μ.compProd κ).map (appendFiniteSourcePath (p := p) k)) =
      Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ)) μ := by
  calc
    Measure.map (fun path : SourcePath p (k + 1) =>
      (path i.castSucc.castSucc, path i.succ.castSucc))
        ((μ.compProd κ).map (appendFiniteSourcePath (p := p) k)) =
      Measure.map (fun pair : SourcePath p k × SourceInput p =>
        (pair.1 i.castSucc, pair.1 i.succ)) (μ.compProd κ) := by
          rw [Measure.map_map
            ((measurable_pi_apply i.castSucc.castSucc).prodMk
              (measurable_pi_apply i.succ.castSucc))
            (measurable_appendFiniteSourcePath (p := p) k)]
          congr 1
          funext pair
          simp only [Function.comp_apply, appendFiniteSourcePath, Fin.snoc_castSucc]
    _ = Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ))
        ((μ.compProd κ).fst) := by
          change Measure.map (fun pair : SourcePath p k × SourceInput p =>
              (pair.1 i.castSucc, pair.1 i.succ)) (μ.compProd κ) =
            Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ))
              (Measure.map Prod.fst (μ.compProd κ))
          rw [Measure.map_map (measurable_adjacentMap k i) measurable_fst]
          congr 1
    _ = Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ)) μ := by
          rw [Measure.fst_compProd]

private theorem finiteSourcePathLaw_lastAdjacent_compProd
    (k : ℕ) (hk : k + 1 ≤ p.T)
    (hlast : Measure.map (fun path : SourcePath p k => path (Fin.last k))
      (finiteSourcePathLaw rate rewards C_star C_h control0 k
        (Nat.le_of_succ_le hk)) = sourceInputLaw p) :
    Measure.map (fun path : SourcePath p (k + 1) =>
      (path (Fin.last k).castSucc, path (Fin.last (k + 1))))
        (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
      (sourceInputLaw p).compProd
        (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
          ⟨k, Nat.lt_of_succ_le hk⟩ control0) := by
  let μ := finiteSourcePathLaw rate rewards C_star C_h control0 k
    (Nat.le_of_succ_le hk)
  let : IsProbabilityMeasure μ :=
    finiteSourcePathLaw_probability rate rewards C_star C_h control0 k
      (Nat.le_of_succ_le hk)
  let κ := finiteSourcePathTransition rate rewards C_star C_h control0 k
    (Nat.lt_of_succ_le hk)
  let t : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
  calc
    Measure.map (fun path : SourcePath p (k + 1) =>
      (path (Fin.last k).castSucc, path (Fin.last (k + 1))))
        (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
      Measure.map (fun pair : SourcePath p k × SourceInput p =>
        (pair.1 (Fin.last k), pair.2)) (μ.compProd κ) := by
          rw [finiteSourcePathLaw_succ]
          rw [Measure.map_map (measurable_lastPairMap k)
            (measurable_appendFiniteSourcePath (p := p) k)]
          congr 1
          funext pair
          simp only [Function.comp_apply, appendFiniteSourcePath, Fin.snoc_castSucc,
            Fin.snoc_last]
    _ = (Measure.map (fun path : SourcePath p k => path (Fin.last k)) μ).compProd
        (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h t control0) := by
          dsimp [μ, κ, finiteSourcePathTransition, t]
          exact map_comap_compProd μ
            (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
              ⟨k, Nat.lt_of_succ_le hk⟩ control0)
            (fun path : SourcePath p k => path (Fin.last k))
            (measurable_pi_apply (Fin.last k))
    _ = (sourceInputLaw p).compProd
        (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h t control0) := by
          rw [hlast]

private theorem finiteSourcePathLaw_lastAdjacent_of_marginal
    (k : ℕ) (hk : k + 1 ≤ p.T)
    (hlast : Measure.map (fun path : SourcePath p k => path (Fin.last k))
      (finiteSourcePathLaw rate rewards C_star C_h control0 k
        (Nat.le_of_succ_le hk)) = sourceInputLaw p) :
    Measure.map (fun path : SourcePath p (k + 1) =>
      (path (Fin.last k).castSucc, path (Fin.last (k + 1))))
        (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
      ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
        ⟨k, Nat.lt_of_succ_le hk⟩ control0 := by
  rw [finiteSourcePathLaw_lastAdjacent_compProd rate rewards C_star C_h control0 k hk hlast]
  exact ReferenceTotalSourceDisintegration.sourceKernel_disintegrate
    rate rewards C_star C_h ⟨k, Nat.lt_of_succ_le hk⟩ control0

private theorem finiteSourcePathLaw_marginal_adjacent
    (k : ℕ) (hk : k ≤ p.T) :
    (∀ a : Fin (k + 1),
      Measure.map (fun path : SourcePath p k => path a)
        (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) = sourceInputLaw p) ∧
    (∀ i : Fin k,
      Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ))
        (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) =
          ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ control0) := by
  induction k with
  | zero =>
      constructor
      · intro a
        cases a using Fin.lastCases with
        | cast i => exact Fin.elim0 i
        | last =>
            rw [finiteSourcePathLaw_zero]
            have hconst : Measurable (fun z : SourceInput p => fun _ : Fin 1 => z) := by
              apply measurable_pi_iff.mpr
              intro i
              exact measurable_id
            rw [Measure.map_map (measurable_pi_apply (Fin.last 0)) hconst]
            have hcomp :
                ((fun path : SourcePath p 0 => path (Fin.last 0)) ∘
                  (fun z : SourceInput p => fun _ : Fin 1 => z)) = id := by
              funext z
              rfl
            rw [hcomp, Measure.map_id]
      · intro i
        exact Fin.elim0 i
  | succ k ih =>
      have hprev := ih (Nat.le_of_succ_le hk)
      have hprob : IsProbabilityMeasure
          (finiteSourcePathLaw rate rewards C_star C_h control0 k
            (Nat.le_of_succ_le hk)) :=
        finiteSourcePathLaw_probability rate rewards C_star C_h control0 k
          (Nat.le_of_succ_le hk)
      let := hprob
      let κ := finiteSourcePathTransition rate rewards C_star C_h control0 k
        (Nat.lt_of_succ_le hk)
      have hκ : IsMarkovKernel κ := by
        dsimp [κ, finiteSourcePathTransition]
        infer_instance
      let := hκ
      constructor
      · intro a
        cases a using Fin.lastCases with
        | cast i =>
            calc
              Measure.map (fun path : SourcePath p (k + 1) => path i.castSucc)
                  (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
                Measure.map (fun path : SourcePath p k => path i)
                  (finiteSourcePathLaw rate rewards C_star C_h control0 k
                    (Nat.le_of_succ_le hk)) := by
                    rw [finiteSourcePathLaw_succ]
                    exact map_snoc_old_coordinate k
                      (finiteSourcePathLaw rate rewards C_star C_h control0 k
                        (Nat.le_of_succ_le hk)) κ i
              _ = sourceInputLaw p := hprev.1 i
        | last =>
            have hlast := hprev.1 (Fin.last k)
            have hpair := finiteSourcePathLaw_lastAdjacent_compProd
              rate rewards C_star C_h control0 k hk hlast
            calc
              Measure.map (fun path : SourcePath p (k + 1) => path (Fin.last (k + 1)))
                  (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
                Measure.map Prod.snd
                  (Measure.map (fun path : SourcePath p (k + 1) =>
                    (path (Fin.last k).castSucc, path (Fin.last (k + 1)))
                  ) (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk)) := by
                    have hfun :
                        (fun path : SourcePath p (k + 1) => path (Fin.last (k + 1))) =
                          Prod.snd ∘ (fun path : SourcePath p (k + 1) =>
                            (path (Fin.last k).castSucc, path (Fin.last (k + 1)))) := by
                      funext path
                      rfl
                    rw [hfun]
                    exact (Measure.map_map measurable_snd (measurable_lastPairMap k)).symm
              _ = Measure.map Prod.snd
                  ((sourceInputLaw p).compProd
                    (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
                      ⟨k, Nat.lt_of_succ_le hk⟩ control0)) := by rw [hpair]
              _ = (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
                    ⟨k, Nat.lt_of_succ_le hk⟩ control0) ∘ₘ (sourceInputLaw p) := by
                    change ((sourceInputLaw p).compProd
                        (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
                          ⟨k, Nat.lt_of_succ_le hk⟩ control0)).snd =
                      (ReferenceTotalSourceDisintegration.sourceKernel rate rewards C_star C_h
                        ⟨k, Nat.lt_of_succ_le hk⟩ control0) ∘ₘ (sourceInputLaw p)
                    exact Measure.snd_compProd _ _
              _ = sourceInputLaw p :=
                    ReferenceTotalSourceDisintegration.sourceKernel_stationary
                      rate rewards C_star C_h ⟨k, Nat.lt_of_succ_le hk⟩ control0
      · intro i
        cases i using Fin.lastCases with
        | cast i =>
            calc
              Measure.map (fun path : SourcePath p (k + 1) =>
                  (path i.castSucc.castSucc, path i.succ.castSucc))
                  (finiteSourcePathLaw rate rewards C_star C_h control0 (k + 1) hk) =
                Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ))
                  (finiteSourcePathLaw rate rewards C_star C_h control0 k
                    (Nat.le_of_succ_le hk)) := by
                    rw [finiteSourcePathLaw_succ]
                    exact map_snoc_old_adjacent k
                      (finiteSourcePathLaw rate rewards C_star C_h control0 k
                        (Nat.le_of_succ_le hk)) κ i
              _ = ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
                    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_succ_le hk)⟩ control0 := hprev.2 i
        | last =>
            exact finiteSourcePathLaw_lastAdjacent_of_marginal
              rate rewards C_star C_h control0 k hk (hprev.1 (Fin.last k))

/-- Every one of the finite stages has the original-source marginal. -/
theorem finiteSourcePathLaw_marginal (k : ℕ) (hk : k ≤ p.T)
    (a : Fin (k + 1)) :
    Measure.map (fun path : SourcePath p k => path a)
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) = sourceInputLaw p :=
  (finiteSourcePathLaw_marginal_adjacent rate rewards C_star C_h control0 k hk).1 a

/-- Every chronological adjacent pair has exactly the admitted total-source
pair law at that same calendar index. -/
theorem finiteSourcePathLaw_adjacent (k : ℕ) (hk : k ≤ p.T) (i : Fin k) :
    Measure.map (fun path : SourcePath p k => (path i.castSucc, path i.succ))
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) =
        ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ control0 :=
  (finiteSourcePathLaw_marginal_adjacent rate rewards C_star C_h control0 k hk).2 i

private theorem finiteSourcePathLaw_adjacentMap_mem_sourceFrameSet
    (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ i : Fin k,
        (path i.castSucc, path i.succ) ∈
          ReferenceTotalSourcePairCoupling.sourceFrameSet
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  rw [ae_all_iff]
  intro i
  have hpair : ∀ᵐ z ∂Measure.map
      (fun path : SourcePath p k => (path i.castSucc, path i.succ))
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk),
        z ∈ ReferenceTotalSourcePairCoupling.sourceFrameSet
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
    rw [finiteSourcePathLaw_adjacent]
    exact ReferenceTotalSourcePairCoupling.ae_totalSourcePairLaw_sourceFrames
      rate rewards C_star C_h ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ control0
  exact ae_of_ae_map (measurable_adjacentMap k i).aemeasurable hpair

theorem ae_finiteSourcePathLaw_adjacent_frames (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ i : Fin k,
        (path i.castSucc, path i.succ) ∈
          ReferenceTotalSourcePairCoupling.sourceFrameSet
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ :=
  finiteSourcePathLaw_adjacentMap_mem_sourceFrameSet rate rewards C_star C_h control0 k hk

private theorem sourceFrame_control_eq
    {x y : SourceInput p} {t : Fin p.T}
    (hxy : (x, y) ∈ ReferenceTotalSourcePairCoupling.sourceFrameSet t)
    (q : Fin (M p)) (v : Fin p.T) (hv : v ≠ t) :
    (x.1.2 q).2 v = (y.1.2 q).2 v := by
  obtain ⟨q₀, hcell⟩ := Set.mem_iUnion.mp hxy
  rcases hcell with ⟨hJx, hJy, _hprivate, _hids, _hforward, hrows, htimes,
    _hscalars, _haffine⟩
  by_cases hq : q = q₀
  · subst q
    exact htimes ⟨v, hv⟩
  · exact congrArg (fun row : CompletePublicTable.CompleteRow p => row.2 v)
      (hrows q hq)

private theorem sourceFrame_invariants
    {x y : SourceInput p} {t : Fin p.T}
    (hxy : (x, y) ∈ ReferenceTotalSourcePairCoupling.sourceFrameSet t) :
    BootstrapPrivateRoundStreams.sourceCoordinatorIndex p x =
        BootstrapPrivateRoundStreams.sourceCoordinatorIndex p y ∧
    x.2 = y.2 ∧ x.1.1 = y.1.1 ∧
    (∀ q : Fin (M p), (x.1.2 q).1 = (y.1.2 q).1) ∧
    (∀ q : Fin (M p), q ≠ BootstrapPrivateRoundStreams.sourceCoordinatorIndex p x →
      x.1.2 q = y.1.2 q) ∧
    (∀ q : Fin (M p), ∀ v : Fin p.T,
      ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((x.1.2 q).2 v)).2.1 label =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((y.1.2 q).2 v)).2.1 label) ∧
    (∀ q : Fin (M p), ∀ v : Fin p.T,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((x.1.2 q).2 v)).2.2 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((y.1.2 q).2 v)).2.2) := by
  obtain ⟨q₀, hcell⟩ := Set.mem_iUnion.mp hxy
  rcases hcell with ⟨hJx, hJy, hprivate, hids, hforward, hrows, htimes, hscalars,
    haffine⟩
  refine ⟨hJx.trans hJy.symm, hprivate, hids, hforward, ?_, ?_, ?_⟩
  · intro q hq
    apply hrows q
    intro hq₀
    exact hq (hq₀.trans hJx.symm)
  · intro q v label
    by_cases hq : q = q₀
    · subst q
      by_cases hv : v = t
      · subst v
        simpa only [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
          using hscalars label
      · have hcontrol := htimes ⟨v, hv⟩
        exact congrArg (fun c : TimeControl p =>
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2.1 label)
          hcontrol
    · exact congrArg (fun row : CompletePublicTable.CompleteRow p =>
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p (row.2 v)).2.1 label)
        (hrows q hq)
  · intro q v
    by_cases hq : q = q₀
    · subst q
      by_cases hv : v = t
      · subst v
        simpa only [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
          using haffine
      · have hcontrol := htimes ⟨v, hv⟩
        exact congrArg (fun c : TimeControl p =>
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2.2)
          hcontrol
    · exact congrArg (fun row : CompletePublicTable.CompleteRow p =>
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p (row.2 v)).2.2)
        (hrows q hq)

private theorem sourcePath_eq_of_edgeRange
    {k : ℕ} {α : Type*} (path : SourcePath p k) (f : SourceInput p → α)
    (a b : Fin (k + 1)) (hab : a.val ≤ b.val)
    (hedge : ∀ i : Fin k, a.val ≤ i.val → i.val < b.val →
      f (path i.castSucc) = f (path i.succ)) :
    f (path a) = f (path b) := by
  have hiterate : ∀ n, a.val ≤ n → ∀ hn : n ≤ k, n ≤ b.val →
      f (path a) = f (path (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (k + 1))) := by
    intro n han
    induction n, han using Nat.le_induction with
    | base =>
        intro hn
        intro hnb
        have hidx : a = (⟨a.val, Nat.lt_succ_of_le hn⟩ : Fin (k + 1)) := Fin.ext rfl
        exact congrArg f (congrArg path hidx)
    | succ n han ih =>
        intro hn
        intro hnext
        by_cases haeq : a.val = n + 1
        · have hidx : a = (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (k + 1)) := Fin.ext haeq
          exact congrArg f (congrArg path hidx)
        · have han' : a.val ≤ n := by omega
          have hprev : n ≤ k := by omega
          have hprefix := ih hprev (by omega)
          let i : Fin k := ⟨n, Nat.lt_of_succ_le hn⟩
          have hleft :
              (⟨n, Nat.lt_succ_of_le hprev⟩ : Fin (k + 1)) = i.castSucc := Fin.ext rfl
          have hright : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (k + 1)) = i.succ := Fin.ext rfl
          have hstep := hedge i (by simpa [i] using han') (by simp [i]; omega)
          have hstep' :
              f (path (⟨n, Nat.lt_succ_of_le hprev⟩ : Fin (k + 1))) =
                f (path (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (k + 1))) := by
            simpa only [hleft, hright] using hstep
          exact hprefix.trans hstep'
  have h := hiterate b.val hab (Nat.le_of_lt_succ b.isLt) le_rfl
  have hb : (⟨b.val, Nat.lt_succ_of_le (Nat.le_of_lt_succ b.isLt)⟩ : Fin (k + 1)) = b :=
    Fin.ext rfl
  simpa only [hb] using h

private theorem sourcePath_eq_any_of_adjacent
    {k : ℕ} {α : Type*} (path : SourcePath p k) (f : SourceInput p → α)
    (hedge : ∀ i : Fin k, f (path i.castSucc) = f (path i.succ))
    (a b : Fin (k + 1)) : f (path a) = f (path b) := by
  by_cases hab : a.val ≤ b.val
  · have h := sourcePath_eq_of_edgeRange path f a b hab
      (fun i _ _ => hedge i)
    exact h
  · have hba : b.val ≤ a.val := by omega
    have h := sourcePath_eq_of_edgeRange path f b a hba
      (fun i _ _ => hedge i)
    exact h.symm

private theorem sourcePath_frozen_control_of_edges
    {k : ℕ} (hk : k ≤ p.T) (path : SourcePath p k)
    (hframes : ∀ i : Fin k,
      (path i.castSucc, path i.succ) ∈ ReferenceTotalSourcePairCoupling.sourceFrameSet
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    (a b : Fin (k + 1)) (hab : a.val ≤ b.val)
    (q : Fin (M p)) (v : Fin p.T)
    (hv : v.val < a.val ∨ b.val ≤ v.val) :
    ((path a).1.2 q).2 v = ((path b).1.2 q).2 v := by
  let f := fun z : SourceInput p => (z.1.2 q).2 v
  have hedge : ∀ i : Fin k, a.val ≤ i.val → i.val < b.val →
      f (path i.castSucc) = f (path i.succ) := by
    intro i hia hib
    let t : Fin p.T := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    have htime : v ≠ t := by
      intro heq
      have hval : v.val = i.val := by
        simpa [t] using congrArg Fin.val heq
      rcases hv with hv | hv
      · omega
      · omega
    exact sourceFrame_control_eq (hframes i) q v htime
  exact sourcePath_eq_of_edgeRange path f a b hab hedge

/-- Across each adjacent transition the actual coordinator index, complete
private arrays (including the original J scalar), IDs, all forward rows,
other-than-original-J whole rows, every nonassignment scalar, and every
affine sample are preserved. This is the unchanged-scope coordinate
consequence of the actual jointly Borel source frames. -/
theorem ae_finiteSourcePathLaw_sourceCoordinates (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ a b : Fin (k + 1), a.val ≤ b.val →
        BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path a) =
          BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path b) ∧
        (path a).2 = (path b).2 ∧
        (path a).1.1 = (path b).1.1 ∧
        (∀ q : Fin (M p), ((path a).1.2 q).1 = ((path b).1.2 q).1) ∧
        (∀ q : Fin (M p), q ≠
            BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path a) →
          (path a).1.2 q = (path b).1.2 q) ∧
        (∀ q : Fin (M p), ∀ v : Fin p.T,
          ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path a).1.2 q).2 v)).2.1 label =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path b).1.2 q).2 v)).2.1 label) ∧
        (∀ q : Fin (M p), ∀ v : Fin p.T,
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path a).1.2 q).2 v)).2.2 =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path b).1.2 q).2 v)).2.2) := by
  filter_upwards [finiteSourcePathLaw_adjacentMap_mem_sourceFrameSet
    rate rewards C_star C_h control0 k hk] with path hframes
  intro a b hab
  have hInv (i : Fin k) := sourceFrame_invariants (hframes i)
  have hJ := sourcePath_eq_of_edgeRange path
    (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p) a b hab
    (fun i _ _ => (hInv i).1)
  have hprivate := sourcePath_eq_of_edgeRange path (fun z => z.2)
    a b hab (fun i _ _ => (hInv i).2.1)
  have hIDs := sourcePath_eq_of_edgeRange path (fun z => z.1.1)
    a b hab (fun i _ _ => (hInv i).2.2.1)
  have hforward (q : Fin (M p)) := sourcePath_eq_of_edgeRange path
    (fun z => (z.1.2 q).1) a b hab
    (fun i _ _ => (hInv i).2.2.2.1 q)
  have hrows (q : Fin (M p))
      (hq : q ≠ BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path a)) :=
    sourcePath_eq_of_edgeRange path (fun z => z.1.2 q) a b hab
      (fun i hir his => by
        have hJi := sourcePath_eq_any_of_adjacent path
          (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p) (fun j => (hInv j).1)
          (i.castSucc) a
        have hq' : q ≠ BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path i.castSucc) := by
          intro heq
          exact hq (heq.trans hJi)
        exact (hInv i).2.2.2.2.1 q hq')
  have hscalars (q : Fin (M p)) (v : Fin p.T)
      (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :=
    sourcePath_eq_of_edgeRange path
      (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((z.1.2 q).2 v)).2.1 label) a b hab
      (fun i _ _ => (hInv i).2.2.2.2.2.1 q v label)
  have haffine (q : Fin (M p)) (v : Fin p.T) :=
    sourcePath_eq_of_edgeRange path
      (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        ((z.1.2 q).2 v)).2.2) a b hab
      (fun i _ _ => (hInv i).2.2.2.2.2.2 q v)
  exact
    (show
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path a) =
          BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path b) ∧
        (path a).2 = (path b).2 ∧
        (path a).1.1 = (path b).1.1 ∧
        (∀ q : Fin (M p), ((path a).1.2 q).1 = ((path b).1.2 q).1) ∧
        (∀ q : Fin (M p), q ≠
            BootstrapPrivateRoundStreams.sourceCoordinatorIndex p (path a) →
          (path a).1.2 q = (path b).1.2 q) ∧
        (∀ q : Fin (M p), ∀ v : Fin p.T,
            ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path a).1.2 q).2 v)).2.1 label =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path b).1.2 q).2 v)).2.1 label) ∧
        (∀ q : Fin (M p), ∀ v : Fin p.T,
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path a).1.2 q).2 v)).2.2 =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (((path b).1.2 q).2 v)).2.2) from
      ⟨hJ, hprivate, hIDs, hforward, hrows, hscalars, haffine⟩)

/-- Whole row-q/time-v controls agree between stages `a` and `b` whenever
their interval does not include the coordinate's own transition time `v`. -/
theorem ae_finiteSourcePathLaw_frozenControls (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ a b : Fin (k + 1), a.val ≤ b.val →
        ∀ q : Fin (M p), ∀ v : Fin p.T,
          (v.val < a.val ∨ b.val ≤ v.val) →
            ((path a).1.2 q).2 v = ((path b).1.2 q).2 v := by
  filter_upwards [finiteSourcePathLaw_adjacentMap_mem_sourceFrameSet
    rate rewards C_star C_h control0 k hk] with path hframes
  intro a b hab q v hv
  exact sourcePath_frozen_control_of_edges hk path hframes a b hab q v hv

private theorem ae_finiteSourcePathLaw_adjacent_complete (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ i : Fin k,
        let x := path i.castSucc
        let y := path i.succ
        ReferenceCompletePhysicalHistory.completeTerminalState rate x rewards C_star C_h =
            ReferenceCompletePhysicalHistory.completeTerminalState rate y rewards C_star C_h ∧
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate x rewards C_star C_h =
            ReferenceCompletePhysicalHistory.completeSuffixEvidence rate y rewards C_star C_h ∧
        ReferenceCompletePhysicalRewards.completeReward rate x rewards C_star C_h =
            ReferenceCompletePhysicalRewards.completeReward rate y rewards C_star C_h := by
  rw [ae_all_iff]
  intro i
  have hpair : ∀ᵐ z ∂Measure.map
      (fun path : SourcePath p k => (path i.castSucc, path i.succ))
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk),
      ReferenceCompletePhysicalHistory.completeTerminalState rate z.1 rewards C_star C_h =
          ReferenceCompletePhysicalHistory.completeTerminalState rate z.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate z.1 rewards C_star C_h =
          ReferenceCompletePhysicalHistory.completeSuffixEvidence rate z.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalRewards.completeReward rate z.1 rewards C_star C_h =
          ReferenceCompletePhysicalRewards.completeReward rate z.2 rewards C_star C_h := by
    rw [finiteSourcePathLaw_adjacent]
    exact ReferenceTotalSourcePhysicalCongruence.ae_totalSourcePairLaw_complete
      rate rewards C_star C_h ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ control0
  filter_upwards [ae_of_ae_map (measurable_adjacentMap k i).aemeasurable hpair] with path h
  exact h

private theorem sourcePath_eq_of_edges
    {k : ℕ} {α : Type*} (path : SourcePath p k) (f : SourceInput p → α)
    (hedge : ∀ i : Fin k, f (path i.castSucc) = f (path i.succ))
    (a b : Fin (k + 1)) (hab : a.val ≤ b.val) :
    f (path a) = f (path b) := by
  exact sourcePath_eq_of_edgeRange path f a b hab (fun i _ _ => hedge i)

/-- Simultaneously, all stages have the same complete physical terminal
state, chronological suffix evidence, and literal complete reward. These
are pathwise transitivity consequences of the actual adjacent congruence. -/
theorem ae_finiteSourcePathLaw_complete (k : ℕ) (hk : k ≤ p.T) :
    ∀ᵐ path ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk,
      ∀ a b : Fin (k + 1), a.val ≤ b.val →
        ReferenceCompletePhysicalHistory.completeTerminalState rate (path a) rewards C_star C_h =
            ReferenceCompletePhysicalHistory.completeTerminalState rate (path b) rewards C_star C_h ∧
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate (path a) rewards C_star C_h =
            ReferenceCompletePhysicalHistory.completeSuffixEvidence rate (path b) rewards C_star C_h ∧
        ReferenceCompletePhysicalRewards.completeReward rate (path a) rewards C_star C_h =
            ReferenceCompletePhysicalRewards.completeReward rate (path b) rewards C_star C_h := by
  filter_upwards [ae_finiteSourcePathLaw_adjacent_complete rate rewards C_star C_h control0 k hk]
    with path h
  intro a b hab
  have hterminal := sourcePath_eq_of_edges path
    (fun z => ReferenceCompletePhysicalHistory.completeTerminalState rate z rewards C_star C_h)
    (fun i => (h i).1) a b hab
  have hevidence := sourcePath_eq_of_edges path
    (fun z => ReferenceCompletePhysicalHistory.completeSuffixEvidence rate z rewards C_star C_h)
    (fun i => (h i).2.1) a b hab
  have hreward := sourcePath_eq_of_edges path
    (fun z => ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h)
    (fun i => (h i).2.2) a b hab
  exact ⟨hterminal, hevidence, hreward⟩

/-- The complete reward of every stage has the original-source distribution. -/
theorem finiteSourcePathLaw_completeReward_distribution
    (k : ℕ) (hk : k ≤ p.T) (a : Fin (k + 1)) :
    Measure.map
      (fun path : SourcePath p k =>
        ReferenceCompletePhysicalRewards.completeReward rate (path a) rewards C_star C_h)
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) =
    Measure.map
      (fun source : SourceInput p =>
        ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h)
      (sourceInputLaw p) := by
  let reward := fun source : SourceInput p =>
    ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  have hreward : Measurable reward :=
    ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h
  have hcoordinate : Measurable (fun path : SourcePath p k => path a) :=
    measurable_pi_apply a
  calc
    Measure.map (reward ∘ fun path : SourcePath p k => path a)
        (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) =
      Measure.map reward
        (Measure.map (fun path : SourcePath p k => path a)
          (finiteSourcePathLaw rate rewards C_star C_h control0 k hk)) := by
            rw [← Measure.map_map hreward hcoordinate]
    _ = Measure.map reward (sourceInputLaw p) := by
          rw [finiteSourcePathLaw_marginal rate rewards C_star C_h control0 k hk a]

/-- Integrability of the path-stage reward is produced from the public source
integrability theorem and the proved stage marginal. -/
theorem finiteSourcePathLaw_completeReward_integrable
    (k : ℕ) (hk : k ≤ p.T) (a : Fin (k + 1)) :
    Integrable
      (fun path : SourcePath p k =>
        ReferenceCompletePhysicalRewards.completeReward rate (path a) rewards C_star C_h)
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) := by
  let reward := fun source : SourceInput p =>
    ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  have hMarg := finiteSourcePathLaw_marginal rate rewards C_star C_h control0 k hk a
  have hbase : Integrable reward
      (Measure.map (fun path : SourcePath p k => path a)
        (finiteSourcePathLaw rate rewards C_star C_h control0 k hk)) := by
    rw [hMarg]
    exact ReferenceCompleteRewardMeasurability.integrable_completeReward_source
      rate rewards C_star C_h
  exact hbase.comp_measurable (measurable_pi_apply a)

/-- The integral of every path-stage reward is the original-source integral;
integrability is established internally without an extra premise. -/
theorem finiteSourcePathLaw_completeReward_integral
    (k : ℕ) (hk : k ≤ p.T) (a : Fin (k + 1)) :
    ∫ path,
      ReferenceCompletePhysicalRewards.completeReward rate (path a) rewards C_star C_h
        ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk =
    ∫ source,
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
        ∂sourceInputLaw p := by
  let reward := fun source : SourceInput p =>
    ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  have hMarg := finiteSourcePathLaw_marginal rate rewards C_star C_h control0 k hk a
  have hmeas : Measurable reward :=
    ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h
  have hmap : AEMeasurable (fun path : SourcePath p k => path a)
      (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) :=
    (measurable_pi_apply a).aemeasurable
  have hstrong : AEStronglyMeasurable reward
      (Measure.map (fun path : SourcePath p k => path a)
        (finiteSourcePathLaw rate rewards C_star C_h control0 k hk)) := by
    rw [hMarg]
    exact hmeas.aestronglyMeasurable
  have h := MeasureTheory.integral_map hmap hstrong
  calc
    ∫ path, reward (path a) ∂finiteSourcePathLaw rate rewards C_star C_h control0 k hk =
        ∫ source, reward source ∂Measure.map (fun path : SourcePath p k => path a)
          (finiteSourcePathLaw rate rewards C_star C_h control0 k hk) := h.symm
    _ = ∫ source, reward source ∂sourceInputLaw p := by rw [hMarg]

end Bandits.Support.ReferenceFiniteSourcePath

end
