/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
All rights reserved. Released under Apache 2.0 license.
-/
module

public import Bandits.Support.DeferredRefreshUniformKernels
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Chronological auxiliary-uniform evaluation on a fixed numerical trace

The trigger uses only label 1 at date `u - 1`. Each subsequent date uses
label 0 for its proposal and label 1 for its residual draw. The numerical
trace is the same recorded trace throughout, independently of the slow set.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:176-187`,
`sources/zip4/manuscript/06_interruptions.tex:399-408`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.
This is an internal finite-trace construction, not a physical conditional law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Bandits.Support.DeferredRefreshUniformEvaluator

open Bandits.Support


abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Pair := Scalar × Scalar
abbrev SlowSet (p : ConstructorDimensions.Parameters) := DeferredRefreshUniformKernels.SlowSet p

/-- One scalar for the trigger, followed by exactly `n` dated pairs. This is
only a coordinate rearrangement carrier, not another auxiliary law. -/
abbrev PrefixCoordinates (n : ℕ) := Scalar × (Fin n → Pair)

variable {p : ConstructorDimensions.Parameters}

/-- The trigger refresh coordinate at the absolute date immediately before `u`. -/
def triggerIndex (s : ℕ) (u t : Fin p.T) (hs : s < u.val) :
    ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t :=
  ⟨(⟨u.val - 1, by omega⟩, 1), by
    change (1 = (1 : Fin 2) ∧ u.val - 1 + 1 = u.val) ∨ _
    exact Or.inl ⟨rfl, by omega⟩⟩

/-- A proposal or residual coordinate at the `n`th subsequent absolute date. -/
def stepIndex (u t : Fin p.T) (n : ℕ) (hn : n < t.val - u.val)
    (label : Fin 2) : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t :=
  ⟨(⟨u.val + n, by omega⟩, label), by
    change _ ∨ (u.val ≤ u.val + n ∧ u.val + n < t.val)
    exact Or.inr ⟨by omega, by omega⟩⟩

theorem triggerIndex_date (s : ℕ) (u t : Fin p.T) (hs : s < u.val) :
    (triggerIndex s u t hs).val.1.val = u.val - 1 := rfl

theorem stepIndex_date (u t : Fin p.T) (n : ℕ) (hn : n < t.val - u.val)
    (label : Fin 2) : (stepIndex u t n hn label).val.1.val = u.val + n := rfl

/-- Distinct dates or labels are distinct auxiliary coordinates. -/
theorem stepIndex_injective (u t : Fin p.T) :
    Function.Injective (fun z : Fin (t.val - u.val) × Fin 2 =>
      stepIndex u t z.1.val z.1.isLt z.2) := by
  intro x y h
  have hd := congrArg (fun i : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t => i.val.1.val) h
  have hl := congrArg (fun i : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t => i.val.2) h
  apply Prod.ext
  · apply Fin.ext
    change u.val + x.1.val = u.val + y.1.val at hd
    omega
  · exact hl

/-- The trigger is never reused by a later step. -/
theorem triggerIndex_ne_stepIndex (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n < t.val - u.val) (label : Fin 2) :
    triggerIndex s u t hs ≠ stepIndex u t n hn label := by
  intro h
  have hd := congrArg (fun i : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t => i.val.1.val) h
  change u.val - 1 = u.val + n at hd
  omega

/-- Literal extraction of the trigger and the first `n` chronological pairs. -/
def prefixCoordinates (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n ≤ t.val - u.val)
    (array : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) : PrefixCoordinates n :=
  (array (triggerIndex s u t hs), fun i =>
    (array (stepIndex u t i.val (by omega) 0),
      array (stepIndex u t i.val (by omega) 1)))

theorem measurable_prefixCoordinates (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n ≤ t.val - u.val) :
    Measurable (prefixCoordinates s u t hs n hn) := by
  apply (measurable_pi_apply _).prodMk
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply _).prodMk (measurable_pi_apply _)

/-- Chronological finite recursion. The successor reads the pre-step numerical
state, updates the previous random set, and uses the last new pair only. -/
noncomputable def prefixValue
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (L : List (RecordedQueueRun.RoundInput p.K)) (uD vD : ℕ)
    (hu : 1 ≤ uD) (huv : uD ≤ vD) (hv : vD ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    (n : ℕ) → n ≤ vD - uD → PrefixCoordinates n → SlowSet p
  | 0, _, z => DeferredRefreshUniformKernels.sampleResidual p q (RecordedQueueRun.run q (L.take (uD - 1)))
      (L[uD - 1]'(by omega)) anchor hanchor z.1
  | n + 1, hn, z => DeferredRefreshUniformKernels.sampleRecordedRefresh p q
      (RecordedQueueRun.run q (L.take (uD + n))) (L[uD + n]'(by omega)) anchor hanchor
      (prefixValue p q L uD vD hu huv hv anchor hanchor n (by omega)
        (z.1, fun i => z.2 i.castSucc)) (z.2 (Fin.last n))

/-- The exposed prefix evaluator uses exactly the existing cell coordinates. -/
noncomputable def evaluatePrefix
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (L : List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val) (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (n : ℕ) (hn : n ≤ t.val - u.val)
    (array : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) : SlowSet p :=
  prefixValue p q L (u.val - s) (t.val - s) (by omega) (by omega) hlen
    anchor hanchor n (by omega) (prefixCoordinates s u t hs n hn array)

/-- Exactly `t-u` later refreshes, after the single triggering residual draw.
The trigger proposal determining the cutoff is not sampled here. -/
noncomputable def evaluate
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (L : List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val) (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    (ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) → SlowSet p :=
  evaluatePrefix p q L s u t hs hut hlen anchor hanchor (t.val - u.val) le_rfl

/-- The base is the residual at relative date `u-s-1` using absolute `u-1`. -/
theorem evaluatePrefix_zero
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val) (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (array : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) :
    evaluatePrefix p q L s u t hs hut hlen anchor hanchor 0 (by omega) array =
      DeferredRefreshUniformKernels.sampleResidual p q (RecordedQueueRun.run q (L.take (u.val - s - 1)))
        (L[u.val - s - 1]'(by omega)) anchor hanchor
        (array (triggerIndex s u t hs)) := rfl

/-- No date is skipped: the successor uses the same recorded input and the
pre-state at relative date `u-s+n`, with the two absolute labels at `u+n`. -/
theorem evaluatePrefix_succ
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val) (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (n : ℕ) (hn : n < t.val - u.val)
    (array : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) :
    evaluatePrefix p q L s u t hs hut hlen anchor hanchor (n + 1) (by omega) array =
      DeferredRefreshUniformKernels.sampleRecordedRefresh p q (RecordedQueueRun.run q (L.take (u.val - s + n)))
        (L[u.val - s + n]'(by omega)) anchor hanchor
        (evaluatePrefix p q L s u t hs hut hlen anchor hanchor n (by omega) array)
        (array (stepIndex u t n hn 0), array (stepIndex u t n hn 1)) := rfl

/-- The numerical state advances by the same input independently of the
sampled slow set, including the first outgoing overflow update. -/
theorem numericalPrefix_succ (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (k : ℕ) (hk : k < L.length) :
    RecordedQueueRun.run q (L.take (k + 1)) =
      RecordedQueueRun.step q (RecordedQueueRun.run q (L.take k)) L[k] := by
  rw [← List.take_concat_get' L k hk]
  unfold RecordedQueueRun.run
  rw [RecordedSlowRefresh.execute_append]
  rfl

/-- Fixed-trace measurability of the finite prefix recursion. -/
theorem measurable_prefixValue
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K)) (uD vD : ℕ)
    (hu : 1 ≤ uD) (huv : uD ≤ vD) (hv : vD ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (n : ℕ) (hn : n ≤ vD - uD) :
    Measurable (prefixValue p q L uD vD hu huv hv anchor hanchor n hn) := by
  induction n with
  | zero => exact (DeferredRefreshUniformKernels.measurable_sampleResidual p q _ _ anchor hanchor).comp measurable_fst
  | succ n ih =>
      have hrestrict : Measurable (fun z : PrefixCoordinates (n + 1) =>
          (z.1, fun i : Fin n => z.2 i.castSucc)) :=
        measurable_fst.prodMk (measurable_pi_iff.mpr
          (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd))
      have hprev := (ih (by omega)).comp hrestrict
      exact DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh_joint p q
        (fun _ => RecordedQueueRun.run q (L.take (uD + n))) (fun _ => L[uD + n]'(by omega))
        anchor hanchor measurable_const measurable_const
        (fun z => z.2 (Fin.last n)) ((measurable_pi_apply _).comp measurable_snd)
        _ hprev

/-- The actual cell evaluator is Borel for every fixed bounded trace. -/
theorem measurable_evaluate
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val) (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a) :
    Measurable (evaluate p q L s u t hs hut hlen anchor hanchor) :=
  (measurable_prefixValue q L _ _ (by omega) (by omega) hlen anchor hanchor
    _ (by omega)).comp (measurable_prefixCoordinates s u t hs _ le_rfl)

/-- Internal varying-trace measurability from the actual finite numerical
coordinates. Neither the state nor the certified round carrier is given a
measurable-space instance. The random current slow set remains in the recursion. -/
theorem measurable_prefixValue_varying
    {Ω : Type*} [MeasurableSpace Ω]
    (q : RecordedQueueRun.Parameters)
    (L : Ω → List (RecordedQueueRun.RoundInput p.K)) (uD vD : ℕ)
    (hu : 1 ≤ uD) (huv : uD ≤ vD) (hv : ∀ x, vD ≤ (L x).length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hstate : ∀ k, uD - 1 ≤ k → k < vD → Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run q ((L x).take k))))
    (hinput : ∀ k, uD - 1 ≤ k → (hk : k < vD) → Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        ((L x)[k]'(by have := hv x; omega))))
    (n : ℕ) (hn : n ≤ vD - uD)
    (z : Ω → PrefixCoordinates n) (hz : Measurable z) :
    Measurable (fun x => prefixValue p q (L x) uD vD hu huv (hv x)
      anchor hanchor n hn (z x)) := by
  induction n with
  | zero =>
      exact DeferredRefreshUniformKernels.measurable_sampleResidual_joint p q
        (fun x => RecordedQueueRun.run q ((L x).take (uD - 1)))
        (fun x => (L x)[uD - 1]'(by have := hv x; omega)) anchor hanchor
        (hstate _ le_rfl (by omega)) (hinput _ le_rfl (by omega))
        (fun x => (z x).1) (measurable_fst.comp hz)
  | succ n ih =>
      have hrestrict : Measurable (fun x =>
          ((z x).1, fun i : Fin n => (z x).2 i.castSucc)) :=
        (measurable_fst.comp hz).prodMk (measurable_pi_iff.mpr
          (fun i => (measurable_pi_apply i.castSucc).comp (measurable_snd.comp hz)))
      have hprev := ih (by omega) _ hrestrict
      exact DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh_joint p q
        (fun x => RecordedQueueRun.run q ((L x).take (uD + n)))
        (fun x => (L x)[uD + n]'(by have := hv x; omega)) anchor hanchor
        (hstate _ (by omega) (by omega)) (hinput _ (by omega) (by omega))
        (fun x => (z x).2 (Fin.last n))
        ((measurable_pi_apply _).comp (measurable_snd.comp hz)) _ hprev

/-- Joint measurability on the actual trace parameter and the auxiliary cell.
The coordinate hypotheses are internal Borel inputs, with actual constructors
`ReferenceFirstCollectionDeferredCalendarProduct.measurable_slotObservation`
and `.measurable_precallReadout` after same-path trace transport. No physical
law, enabledness, no-overflow or positive-atom hypothesis is supplied here. -/
theorem measurable_evaluate_varying
    {Ω : Type*} [MeasurableSpace Ω]
    (q : RecordedQueueRun.Parameters)
    (L : Ω → List (RecordedQueueRun.RoundInput p.K)) (s : ℕ) (u t : Fin p.T)
    (hs : s < u.val) (hut : u.val ≤ t.val)
    (hlen : ∀ x, t.val - s ≤ (L x).length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hstate : ∀ k, u.val - s - 1 ≤ k → k < t.val - s → Measurable (fun x =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run q ((L x).take k))))
    (hinput : ∀ k, u.val - s - 1 ≤ k → (hk : k < t.val - s) → Measurable (fun x =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        ((L x)[k]'(by have := hlen x; omega)))) :
    Measurable (fun z : Ω × (ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar) =>
      evaluate p q (L z.1) s u t hs hut (hlen z.1) anchor hanchor z.2) := by
  exact measurable_prefixValue_varying
    (Ω := Ω × (ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t → Scalar))
    q (fun z => L z.1)
    (u.val - s) (t.val - s) (by omega) (by omega) (fun z => hlen z.1)
    anchor hanchor (fun k hk hkt => (hstate k hk hkt).comp measurable_fst)
    (fun k hk hkt => (hinput k hk hkt).comp measurable_fst)
    (t.val - u.val) (by omega)
    (fun z => prefixCoordinates s u t hs (t.val - u.val) le_rfl z.2)
    ((measurable_prefixCoordinates s u t hs _ le_rfl).comp measurable_snd)

/-- Unrolling the public chronological path definition across an append. -/
private theorem path_append
    (q : RecordedQueueRun.Parameters) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ)))
    (state : RecordedQueueRun.RunState p.K)
    (xs ys : List (RecordedQueueRun.RoundInput p.K)) (μ : PMF (SlowSet p)) :
    DeferredRefreshWindow.refreshPathPMF p q anchor hanchor hcap state (xs ++ ys) μ =
      DeferredRefreshWindow.refreshPathPMF p q anchor hanchor hcap
        (RecordedQueueRun.execute q xs state) ys
        (DeferredRefreshWindow.refreshPathPMF p q anchor hanchor hcap state xs μ) := by
  induction xs generalizing state μ with
  | nil => rfl
  | cons round xs ih =>
      simp only [List.cons_append, DeferredRefreshWindow.refreshPathPMF]
      exact ih _ _

/-- The public PMF prefix has exactly the same successor input and pre-state
as the evaluator. This proof unfolds only the public path/prefix definitions. -/
theorem windowPrefixPMF_succ
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (uD vD : ℕ) (hu : 1 ≤ uD) (huv : uD ≤ vD) (hv : vD ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : n < vD - uD) :
    DeferredRefreshWindow.windowPrefixPMF p q L uD vD hu huv hv anchor hanchor hcap (n + 1) =
      (DeferredRefreshWindow.windowPrefixPMF p q L uD vD hu huv hv anchor hanchor hcap n).bind
        (fun U => RecordedSlowRefresh.recordedRefreshKernel p q
          (RecordedQueueRun.run q (L.take (uD + n))) (L[uD + n]'(by omega))
          anchor hanchor hcap U) := by
  have hpath : (DeferredRefreshWindow.refreshWindowRounds L uD vD).length = vD - uD := by
    simp only [DeferredRefreshWindow.refreshWindowRounds, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hget : n < (DeferredRefreshWindow.refreshWindowRounds L uD vD).length := by
    rw [hpath]
    exact hn
  have htake : (DeferredRefreshWindow.refreshWindowRounds L uD vD).take n =
      (L.drop uD).take n := by
    simp only [DeferredRefreshWindow.refreshWindowRounds, List.take_take,
      Nat.min_eq_left hn.le]
  have hstate : RecordedQueueRun.execute q
      ((DeferredRefreshWindow.refreshWindowRounds L uD vD).take n)
      (RecordedQueueRun.run q (L.take uD)) =
        RecordedQueueRun.run q (L.take (uD + n)) := by
    rw [htake]
    symm
    simpa only [Nat.add_sub_cancel_left] using
      RecordedEpisodeStability.run_take_eq_execute_drop q L uD (uD + n) (by omega)
  have hround : (DeferredRefreshWindow.refreshWindowRounds L uD vD)[n] = L[uD + n] := by
    simp only [DeferredRefreshWindow.refreshWindowRounds, List.getElem_take, List.getElem_drop]
  unfold DeferredRefreshWindow.windowPrefixPMF
  rw [← List.take_concat_get' _ n hget, path_append, hstate]
  simp only [DeferredRefreshWindow.refreshPathPMF, hround]

/-- Finite Fubini for the accepted two-scalar kernel, with an arbitrary
current PMF. There is no enabledness or positive-atom restriction. -/
private theorem refresh_bind_map
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))) (μ : PMF (SlowSet p)) :
    (μ.toMeasure.prod (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
        (fun z => DeferredRefreshUniformKernels.sampleRecordedRefresh p q state round
          anchor hanchor z.1 z.2) =
      (μ.bind (fun U => RecordedSlowRefresh.recordedRefreshKernel p q state round
        anchor hanchor hcap U)).toMeasure := by
  classical
  have hm : Measurable (fun z : SlowSet p × Pair =>
      DeferredRefreshUniformKernels.sampleRecordedRefresh p q state round anchor hanchor z.1 z.2) :=
    DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh_joint p q
      (fun _ => state) (fun _ => round) anchor hanchor measurable_const measurable_const
      Prod.snd measurable_snd Prod.fst measurable_fst
  ext B hB
  rw [Measure.map_apply hm hB, Measure.prod_apply (hm hB),
    PMF.toMeasure_bind_apply _ _ _ hB, lintegral_countable']
  apply tsum_congr
  intro U
  rw [PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U), mul_comm]
  congr 1
  rw [← DeferredRefreshUniformKernels.sampleRecordedRefresh_map p q state round
    anchor hanchor hcap U, Measure.map_apply
      (DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh p q state round
        anchor hanchor U) hB]
  rfl

/-- Splitting off the last pair preserves the explicit finite product measure. -/
private theorem prefix_split_last (n : ℕ) :
    MeasurePreserving
      (fun z : PrefixCoordinates (n + 1) =>
        ((z.1, fun i : Fin n => z.2 i.castSucc), z.2 (Fin.last n)))
      (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin (n + 1) =>
          ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)))
      ((ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin n =>
          ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw))).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) := by
  let ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw
  have hhead := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)
  have htail := (Measure.measurePreserving_swap
    (μ := ν) (ν := Measure.pi (fun _ : Fin n => ν))).comp hhead
  have hpair := (MeasurePreserving.id ContinuousControlSlice.scalarLaw).prod htail
  have hassoc := (measurePreserving_prodAssoc ContinuousControlSlice.scalarLaw
    (Measure.pi (fun _ : Fin n => ν)) ν).symm
  convert hassoc.comp hpair using 1
  change (fun z : PrefixCoordinates (n + 1) =>
      ((z.1, fun i : Fin n => z.2 i.castSucc), z.2 (Fin.last n))) =
    (fun z => ((z.1, fun i => z.2 ((Fin.last n).succAbove i)), z.2 (Fin.last n)))
  simp only [Fin.succAbove_last]

/-- Exact finite binding law on the trigger/pair rearrangement carrier. -/
theorem prefixValue_map
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (uD vD : ℕ) (hu : 1 ≤ uD) (huv : uD ≤ vD) (hv : vD ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))) (n : ℕ) (hn : n ≤ vD - uD) :
    (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin n =>
          ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw))).map
      (prefixValue p q L uD vD hu huv hv anchor hanchor n hn) =
      (DeferredRefreshWindow.windowPrefixPMF p q L uD vD hu huv hv
        anchor hanchor hcap n).toMeasure := by
  induction n with
  | zero =>
      rw [DeferredRefreshWindow.windowPrefixPMF_zero]
      change (_ : Measure (PrefixCoordinates 0)).map
        (DeferredRefreshUniformKernels.sampleResidual p q _ _ anchor hanchor ∘ Prod.fst) = _
      rw [← Measure.map_map
        (DeferredRefreshUniformKernels.measurable_sampleResidual p q _ _ anchor hanchor)
        measurable_fst, measurePreserving_fst.map_eq]
      exact DeferredRefreshUniformKernels.sampleResidual_map p q _ _ anchor hanchor
  | succ n ih =>
      let ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw
      let μ := DeferredRefreshWindow.windowPrefixPMF p q L uD vD hu huv hv anchor hanchor hcap n
      let previous := prefixValue p q L uD vD hu huv hv anchor hanchor n (by omega)
      let sample := fun z : SlowSet p × Pair =>
        DeferredRefreshUniformKernels.sampleRecordedRefresh p q
          (RecordedQueueRun.run q (L.take (uD + n))) (L[uD + n]'(by omega))
          anchor hanchor z.1 z.2
      let split := fun z : PrefixCoordinates (n + 1) =>
        ((z.1, fun i : Fin n => z.2 i.castSucc), z.2 (Fin.last n))
      have hprevious : Measurable previous :=
        measurable_prefixValue q L uD vD hu huv hv anchor hanchor n (by omega)
      have hsample : Measurable sample :=
        DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh_joint p q
          (fun _ => RecordedQueueRun.run q (L.take (uD + n)))
          (fun _ => L[uD + n]'(by omega)) anchor hanchor measurable_const measurable_const
          Prod.snd measurable_snd Prod.fst measurable_fst
      have hsplit := prefix_split_last n
      have hμ : (ContinuousControlSlice.scalarLaw.prod
          (Measure.pi (fun _ : Fin n => ν))).map previous = μ.toMeasure := ih (by omega)
      rw [windowPrefixPMF_succ q L uD vD hu huv hv anchor hanchor hcap n (by omega)]
      change (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin (n + 1) => ν))).map
          ((sample ∘ Prod.map previous id) ∘ split) = _
      rw [← Measure.map_map (hsample.comp (hprevious.prodMap measurable_id)) hsplit.measurable,
        hsplit.map_eq, ← Measure.map_map hsample (hprevious.prodMap measurable_id),
        ← Measure.map_prod_map _ _ hprevious measurable_id, Measure.map_id, hμ]
      exact refresh_bind_map q _ _ anchor hanchor hcap μ

/-- Indexing the trigger, proposal sequence and residual sequence separately
is a literal partition of the coordinates used by one prefix. -/
def coordinateIndex (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n ≤ t.val - u.val) :
    Unit ⊕ (Fin n ⊕ Fin n) → ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t
  | .inl _ => triggerIndex s u t hs
  | .inr (.inl i) => stepIndex u t i.val (by omega) 0
  | .inr (.inr i) => stepIndex u t i.val (by omega) 1

/-- No trigger/proposal/residual coordinate is shared in the rearrangement. -/
theorem coordinateIndex_injective (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n ≤ t.val - u.val) :
    Function.Injective (coordinateIndex s u t hs n hn) := by
  intro x y h
  have hd := congrArg
    (fun i : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t => i.val.1.val) h
  have hl := congrArg
    (fun i : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t => i.val.2) h
  cases x with
  | inl a =>
      cases y with
      | inl b => rfl
      | inr b =>
          cases b <;> change u.val - 1 = u.val + _ at hd <;> omega
  | inr a =>
      cases y with
      | inl b =>
          cases a <;> change u.val + _ = u.val - 1 at hd <;> omega
      | inr b =>
          cases a with
          | inl i =>
              cases b with
              | inl j =>
                  have hij : i = j := Fin.ext (by
                    change u.val + i.val = u.val + j.val at hd
                    omega)
                  exact congrArg (fun k : Fin n => Sum.inr (Sum.inl k)) hij
              | inr j => exact False.elim (by change (0 : Fin 2) = 1 at hl; cases hl)
          | inr i =>
              cases b with
              | inl j => exact False.elim (by change (1 : Fin 2) = 0 at hl; cases hl)
              | inr j =>
                  have hij : i = j := Fin.ext (by
                    change u.val + i.val = u.val + j.val at hd
                    omega)
                  exact congrArg (fun k : Fin n => Sum.inr (Sum.inr k)) hij

/-- A finite injective coordinate selection from a scalar product has the
corresponding scalar product law. This follows from actual Pi independence. -/
private theorem pi_coordinate_selection
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    MeasurePreserving (fun array : ι → Scalar => fun i => array (f i))
      (Measure.pi (fun _ : ι => ContinuousControlSlice.scalarLaw))
      (Measure.pi (fun _ : κ => ContinuousControlSlice.scalarLaw)) := by
  classical
  refine ⟨measurable_pi_iff.mpr (fun _ => measurable_pi_apply _), ?_⟩
  have hi := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : ι => ContinuousControlSlice.scalarLaw)
    (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have h := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (f i)).aemeasurable) (hi.precomp hf)
  have hmarginal (i : κ) :
      (Measure.pi (fun _ : ι => ContinuousControlSlice.scalarLaw)).map
        (fun array => array (f i)) = ContinuousControlSlice.scalarLaw :=
    (measurePreserving_eval (fun _ : ι => ContinuousControlSlice.scalarLaw) (f i)).map_eq
  simpa only [hmarginal] using h

/-- The existing cell law rearranges into its trigger and chronological pairs.
This uses only finite product equivalences and the injective dated indexing. -/
theorem prefixCoordinates_measurePreserving
    (s : ℕ) (u t : Fin p.T) (hs : s < u.val)
    (n : ℕ) (hn : n ≤ t.val - u.val) :
    MeasurePreserving (prefixCoordinates s u t hs n hn)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)
      (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin n =>
          ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw))) := by
  classical
  have hselect := pi_coordinate_selection (coordinateIndex s u t hs n hn)
    (coordinateIndex_injective s u t hs n hn)
  have houter := measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin n ⊕ Fin n) => ContinuousControlSlice.scalarLaw)
  have hinner := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin n => ContinuousControlSlice.scalarLaw)
  have hunit := measurePreserving_piUnique (fun _ : Unit => ContinuousControlSlice.scalarLaw)
  have hsplit := (hunit.prod hinner).comp (houter.comp hselect)
  have hcombine := (measurePreserving_arrowProdEquivProdArrow Scalar Scalar (Fin n)
    (fun _ => ContinuousControlSlice.scalarLaw) (fun _ => ContinuousControlSlice.scalarLaw)).symm
  have hresult := ((MeasurePreserving.id ContinuousControlSlice.scalarLaw).prod hcombine).comp hsplit
  convert hresult using 1 <;> rfl

/-- Every chronological prefix has the accepted finite PMF on the same trace. -/
theorem evaluatePrefix_map
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (s : ℕ) (u t : Fin p.T) (hs : s < u.val) (hut : u.val ≤ t.val)
    (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : n ≤ t.val - u.val) :
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t).map
        (evaluatePrefix p q L s u t hs hut hlen anchor hanchor n hn) =
      (DeferredRefreshWindow.windowPrefixPMF p q L (u.val - s) (t.val - s)
        (by omega) (by omega) hlen anchor hanchor hcap n).toMeasure := by
  have hcoordinates := prefixCoordinates_measurePreserving s u t hs n hn
  change (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t).map
    (prefixValue p q L (u.val - s) (t.val - s) (by omega) (by omega) hlen
      anchor hanchor n (by omega) ∘ prefixCoordinates s u t hs n hn) = _
  rw [← Measure.map_map
    (measurable_prefixValue q L _ _ (by omega) (by omega) hlen anchor hanchor n (by omega))
    hcoordinates.measurable, hcoordinates.map_eq]
  exact prefixValue_map q L _ _ (by omega) (by omega) hlen anchor hanchor hcap n (by omega)

/-- Exact finite binding equality for the existing auxiliary cell law. The
cap is needed only for the one-step probability kernels, not for evaluation.
Disabled and post-overflow dates are retained in the chronological recursion. -/
theorem evaluate_map
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (s : ℕ) (u t : Fin p.T) (hs : s < u.val) (hut : u.val ≤ t.val)
    (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))) :
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t).map
        (evaluate p q L s u t hs hut hlen anchor hanchor) =
      (DeferredRefreshWindow.deferredRefreshWindowPMF p q L (u.val - s) (t.val - s)
        (by omega) (by omega) hlen anchor hanchor hcap).toMeasure := by
  have hN : t.val - s - (u.val - s) = t.val - u.val := by omega
  simpa only [evaluate, DeferredRefreshWindow.deferredRefreshWindowPMF, hN] using
    evaluatePrefix_map q L s u t hs hut hlen anchor hanchor hcap (t.val - u.val) le_rfl

/-- The equivalent atom identity holds for every slow set, including zero
atoms, without conditioning or normalizing a physical cell. -/
theorem evaluate_atom
    (q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (s : ℕ) (u t : Fin p.T) (hs : s < u.val) (hut : u.val ≤ t.val)
    (hlen : t.val - s ≤ L.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ a, 0 < anchor a)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))) (U : SlowSet p) :
    ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t
        (evaluate p q L s u t hs hut hlen anchor hanchor ⁻¹' {U}) =
      DeferredRefreshWindow.deferredRefreshWindowPMF p q L (u.val - s) (t.val - s)
        (by omega) (by omega) hlen anchor hanchor hcap U := by
  rw [← Measure.map_apply (measurable_evaluate q L s u t hs hut hlen anchor hanchor)
    (measurableSet_singleton U), evaluate_map q L s u t hs hut hlen anchor hanchor hcap,
    PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U)]

end Bandits.Support.DeferredRefreshUniformEvaluator

end
