/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentExponentialQueueStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual first-call exponential queue estimate

Join the original cutoff/date cells at the literal first collection call,
under the original source-input law.

Sources: `04_slow_fast_learner.tex:140-188,245-284`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

namespace Bandits.Support.ReferenceFirstCollectionActualCallExponentialQueueEstimate

local instance sourceInputMeasurableSpace {p : Parameters} :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T) (a : Fin p.K)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (t.val + 1)
local notation "G" =>
  ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t

/-- Sum incoming scalar observations over every cutoff/date cell. -/
@[expose] def callXMinus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) (a0 : Fin p.K) :
    SourceInput p → ℝ := fun z =>
  ∑ u0 : Fin p.T, ∑ t0 : Fin p.T,
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
      rate0 rewards0 C_star0 C_h0 u0 t0 a0 z

/-- Sum post-update scalar observations over every cutoff/date cell. -/
@[expose] def callXPlus (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) (a0 : Fin p.K) :
    SourceInput p → ℝ := fun z =>
  ∑ u0 : Fin p.T, ∑ t0 : Fin p.T,
    ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
      rate0 rewards0 C_star0 C_h0 u0 t0 a0 z

/-- The finite union of retained gates indexed by the original cutoff/date
cells of the first actual collection invocation. -/
@[expose] def retainedFirstCall
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ) : Set (SourceInput p) :=
  ⋃ cell : Fin p.T × Fin p.T, ⋃ _hcell : cell ∈ Finset.univ,
    ReferenceFirstCollectionCurrentRetainedGate.G
      rate0 rewards0 C_star0 C_h0 cell.1 cell.2

private theorem firstCell_unique_pair (z : S) (u₁ u₂ t₁ t₂ : Fin p.T)
    (h₁ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₁ t₁)
    (h₂ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₂ t₂) :
    u₁ = u₂ ∧ t₁ = t₂ := by
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₁, t₁) at h₁
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₂, t₂) at h₂
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at h₁
  | some c =>
      simp [hcall] at h₁ h₂
      exact ⟨h₁.1.symm.trans h₂.1, h₁.2.symm.trans h₂.2⟩

private theorem G_unique_pair (z : S) (u₁ u₂ t₁ t₂ : Fin p.T)
    (h₁ : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u₁ t₁)
    (h₂ : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u₂ t₂) :
    u₁ = u₂ ∧ t₁ = t₂ :=
  firstCell_unique_pair rate rewards C_star C_h z u₁ u₂ t₁ t₂ h₁.1 h₂.1

private theorem mem_retainedFirstCall_iff (z : S) :
    z ∈ retainedFirstCall rate rewards C_star C_h ↔
      ∃ u0 t0 : Fin p.T,
        z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u0 t0 := by
  simp only [retainedFirstCall, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨u0, t0⟩, hG⟩
    rcases hG with ⟨_, hG⟩
    exact ⟨u0, t0, hG⟩
  · rintro ⟨u0, t0, hG⟩
    exact ⟨(u0, t0), ⟨Finset.mem_univ _, hG⟩⟩

include control0

/-- The retained finite union is measurable in the ambient original source
space. -/
theorem retainedFirstCall_measurable :
    MeasurableSet (retainedFirstCall rate rewards C_star C_h) := by
  apply Finset.measurableSet_biUnion Finset.univ
  intro cell hcell
  exact (sourcePrefixFiltration control0).le' (cell.2.val + 1) _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 cell.1 cell.2)

omit control0 in
private theorem XMinus_zero_of_not_firstCell (z : S) (u₀ t₀ : Fin p.T)
    (hz : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₀ t₀) :
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
      rate rewards C_star C_h u₀ t₀ a z = 0 := by
  simp [ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus, hz]

omit control0 in
private theorem XPlus_zero_of_not_firstCell (z : S) (u₀ t₀ : Fin p.T)
    (hz : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₀ t₀) :
    ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
      rate rewards C_star C_h u₀ t₀ a z = 0 := by
  simp [ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus, hz]

omit control0 in
private theorem callXMinus_eq_cell_of_firstCollectionCall (z : S)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    callXMinus rate rewards C_star C_h a z =
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z := by
  have hcell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
    change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
    rw [hcall]
    rfl
  have hinner (u₀ : Fin p.T) :
      (∑ t₀ : Fin p.T,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u₀ t₀ a z) =
        if u₀ = u then
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u t a z else 0 := by
    by_cases hu : u₀ = u
    · subst u₀
      rw [Finset.sum_eq_single t]
      · simp
      · intro t₀ _ht₀ htt
        apply XMinus_zero_of_not_firstCell rate rewards C_star C_h a z u t₀
        intro hcell'
        exact htt (firstCell_unique_pair rate rewards C_star C_h z u u t t₀ hcell hcell').2.symm
      · intro hmem
        exact (hmem (Finset.mem_univ t)).elim
    · have hzero : ∀ t₀ : Fin p.T,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u₀ t₀ a z = 0 := by
        intro t₀
        apply XMinus_zero_of_not_firstCell rate rewards C_star C_h a z u₀ t₀
        intro hcell'
        exact hu (firstCell_unique_pair rate rewards C_star C_h z u u₀ t t₀ hcell hcell').1.symm
      simp_rw [hzero]
      simp [hu]
  unfold callXMinus
  rw [show (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u₀ t₀ a z) =
    ∑ u₀ : Fin p.T,
      (if u₀ = u then
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z else 0) by
      apply Finset.sum_congr rfl
      intro u₀ _
      exact hinner u₀]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp

omit control0 in
private theorem callXPlus_eq_cell_of_firstCollectionCall (z : S)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    callXPlus rate rewards C_star C_h a z =
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u t a z := by
  have hcell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
    change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
    rw [hcall]
    rfl
  have hinner (u₀ : Fin p.T) :
      (∑ t₀ : Fin p.T,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u₀ t₀ a z) =
        if u₀ = u then
          ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
            rate rewards C_star C_h u t a z else 0 := by
    by_cases hu : u₀ = u
    · subst u₀
      rw [Finset.sum_eq_single t]
      · simp
      · intro t₀ _ht₀ htt
        apply XPlus_zero_of_not_firstCell rate rewards C_star C_h a z u t₀
        intro hcell'
        exact htt (firstCell_unique_pair rate rewards C_star C_h z u u t t₀ hcell hcell').2.symm
      · intro hmem
        exact (hmem (Finset.mem_univ t)).elim
    · have hzero : ∀ t₀ : Fin p.T,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
            rate rewards C_star C_h u₀ t₀ a z = 0 := by
        intro t₀
        apply XPlus_zero_of_not_firstCell rate rewards C_star C_h a z u₀ t₀
        intro hcell'
        exact hu (firstCell_unique_pair rate rewards C_star C_h z u u₀ t t₀ hcell hcell').1.symm
      simp_rw [hzero]
      simp [hu]
  unfold callXPlus
  rw [show (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u₀ t₀ a z) =
    ∑ u₀ : Fin p.T,
      (if u₀ = u then
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z else 0) by
      apply Finset.sum_congr rfl
      intro u₀ _
      exact hinner u₀]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp

omit control0 in
/-- At an existing original first invocation, the finite sums select exactly
its matching actual-cell observations. -/
theorem callXMinus_callXPlus_eq_actualCell_of_firstCollectionCall (z : S)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    callXMinus rate rewards C_star C_h a z =
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z ∧
      callXPlus rate rewards C_star C_h a z =
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z := by
  exact ⟨callXMinus_eq_cell_of_firstCollectionCall rate rewards C_star C_h
    u t a z theta hcall,
    callXPlus_eq_cell_of_firstCollectionCall rate rewards C_star C_h
      u t a z theta hcall⟩

omit control0 in
private theorem not_firstCell_of_no_firstCollectionCall (z : S)
    (u₀ t₀ : Fin p.T)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) :
    z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₀ t₀ := by
  intro hz
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₀, t₀) at hz
  rw [hcall] at hz
  simp at hz

omit control0 in
/-- When the original first-call selector is absent, both analytical call
sums are zero. -/
theorem callXMinus_callXPlus_eq_zero_of_firstCollectionCall_none (z : S)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none) :
    callXMinus rate rewards C_star C_h a z = 0 ∧
      callXPlus rate rewards C_star C_h a z = 0 := by
  constructor
  · unfold callXMinus
    apply Finset.sum_eq_zero
    intro u₀ _
    apply Finset.sum_eq_zero
    intro t₀ _
    apply XMinus_zero_of_not_firstCell rate rewards C_star C_h a z u₀ t₀
    exact not_firstCell_of_no_firstCollectionCall rate rewards C_star C_h z u₀ t₀ hcall
  · unfold callXPlus
    apply Finset.sum_eq_zero
    intro u₀ _
    apply Finset.sum_eq_zero
    intro t₀ _
    apply XPlus_zero_of_not_firstCell rate rewards C_star C_h a z u₀ t₀
    exact not_firstCell_of_no_firstCollectionCall rate rewards C_star C_h z u₀ t₀ hcall

omit control0 in
/-- The call sums recover the same original L/c queue exponentials at the
actual first invocation. -/
theorem callXMinus_callXPlus_eq_actualReadouts_of_firstCollectionCall (z : S)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      callXMinus rate rewards C_star C_h a z =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
            rate (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L))) a) ∧
      callXPlus rate rewards C_star C_h a z =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
            rate (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
              (RecordedQueueRun.step
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (RecordedQueueRun.run
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c))) a) := by
  have hcell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
    change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
    rw [hcall]
    rfl
  have hsum := callXMinus_callXPlus_eq_actualCell_of_firstCollectionCall
    rate rewards C_star C_h u t a z theta hcall
  obtain ⟨L, c, hL, hc, hminus, hplus⟩ :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.firstCell_XMinus_XPlus_actual_readouts
      rate rewards C_star C_h u t a z hcell
  exact ⟨L, c, hL, hc, hsum.1.trans hminus, hsum.2.trans hplus⟩

omit control0 in
/-- Pointwise, the sum of retained-cell indicators is the indicator of the
actual finite retained-first-call union. -/
theorem retainedFirstCall_indicator_sum_eq (z : S) :
    (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
      (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u₀ t₀).indicator (fun _ : S => (1 : ℝ)) z) =
      (retainedFirstCall rate rewards C_star C_h).indicator
        (fun _ : S => (1 : ℝ)) z := by
  by_cases hz : z ∈ retainedFirstCall rate rewards C_star C_h
  · obtain ⟨u₀, t₀, hG₀⟩ := (mem_retainedFirstCall_iff rate rewards C_star C_h z).mp hz
    have hinner (u₁ : Fin p.T) :
        (∑ t₁ : Fin p.T,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₁ t₁).indicator (fun _ : S => (1 : ℝ)) z) =
          if u₁ = u₀ then 1 else 0 := by
      by_cases hu : u₁ = u₀
      · subst u₁
        rw [Finset.sum_eq_single t₀]
        · simp [hG₀]
        · intro t₁ _ht₁ htne
          have hnot : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u₀ t₁ := by
            intro hG₁
            exact htne (G_unique_pair rate rewards C_star C_h z u₀ u₀ t₀ t₁ hG₀ hG₁).2.symm
          simp [hnot]
        · intro hmem
          exact (hmem (Finset.mem_univ t₀)).elim
      · have hnot (t₁ : Fin p.T) :
            z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u₁ t₁ := by
          intro hG₁
          exact hu (G_unique_pair rate rewards C_star C_h z u₀ u₁ t₀ t₁ hG₀ hG₁).1.symm
        have hsumzero :
            (∑ t₁ : Fin p.T,
              (ReferenceFirstCollectionCurrentRetainedGate.G
                rate rewards C_star C_h u₁ t₁).indicator
                  (fun _ : S => (1 : ℝ)) z) = 0 := by
          apply Finset.sum_eq_zero
          intro t₁ _
          simp [hnot t₁]
        simp [hu, hsumzero]
    have hsum :
        (∑ u₁ : Fin p.T, ∑ t₁ : Fin p.T,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₁ t₁).indicator (fun _ : S => (1 : ℝ)) z) = 1 := by
      rw [show (∑ u₁ : Fin p.T, ∑ t₁ : Fin p.T,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₁ t₁).indicator (fun _ : S => (1 : ℝ)) z) =
        ∑ u₁ : Fin p.T, if u₁ = u₀ then 1 else 0 by
          apply Finset.sum_congr rfl
          intro u₁ _
          exact hinner u₁]
      rw [Finset.sum_ite_eq' Finset.univ u₀]
      simp
    simp [hz, hsum]
  · have hzero (u₀ t₀ : Fin p.T) :
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀).indicator (fun _ : S => (1 : ℝ)) z = 0 := by
      have hnot : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀ := by
        intro hG
        exact hz ((mem_retainedFirstCall_iff rate rewards C_star C_h z).mpr
          ⟨u₀, t₀, hG⟩)
      simp [hnot]
    have hsumzero :
        (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₀ t₀).indicator (fun _ : S => (1 : ℝ)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro u₀ _
      apply Finset.sum_eq_zero
      intro t₀ _
      exact hzero u₀ t₀
    simp [hz, hsumzero]

/-- The finite sum of cell indicators is integrable under the original source
law. -/
theorem retainedFirstCall_indicator_sum_integrable :
    Integrable (fun z : S =>
      ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀).indicator (fun _ : S => (1 : ℝ)) z) mu := by
  apply integrable_finsetSum
  intro u₀ _
  apply integrable_finsetSum
  intro t₀ _
  exact (integrable_const (1 : ℝ)).indicator
    ((sourcePrefixFiltration control0).le' (t₀.val + 1) _
      (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
        rate rewards C_star C_h control0 u₀ t₀))

/-- The finite sum of cell indicators is measurable in the original source
space. -/
theorem retainedFirstCall_indicator_sum_measurable :
    Measurable (fun z : S =>
      ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀).indicator (fun _ : S => (1 : ℝ)) z) := by
  apply Finset.measurable_sum Finset.univ
  intro u₀ _
  apply Finset.measurable_sum Finset.univ
  intro t₀ _
  exact measurable_const.indicator
    ((sourcePrefixFiltration control0).le' (t₀.val + 1) _
      (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
        rate rewards C_star C_h control0 u₀ t₀))

/-- Integrating the pointwise finite indicator identity gives exactly the
mass of the retained first-call event. -/
theorem sum_retainedGate_measures_eq_retainedFirstCall_measure
    :
    (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
      (sourceInputLaw p).real
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u₀ t₀)) =
      (sourceInputLaw p).real (retainedFirstCall rate rewards C_star C_h) := by
  calc
    _ = ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        ∫ z : S,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₀ t₀).indicator
              (fun _ : S => (1 : ℝ)) z ∂mu := by
      apply Finset.sum_congr rfl
      intro u₀ _
      apply Finset.sum_congr rfl
      intro t₀ _
      symm
      exact integral_indicator_one
        ((sourcePrefixFiltration control0).le' (t₀.val + 1) _
          (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
            rate rewards C_star C_h control0 u₀ t₀))
    _ = ∫ z : S,
        ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₀ t₀).indicator
              (fun _ : S => (1 : ℝ)) z ∂mu := by
      symm
      rw [integral_finsetSum Finset.univ (fun u₀ _ =>
        integrable_finsetSum Finset.univ (fun t₀ _ =>
          (integrable_const (1 : ℝ)).indicator
            ((sourcePrefixFiltration control0).le' (t₀.val + 1) _
              (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
                rate rewards C_star C_h control0 u₀ t₀))))]
      apply Finset.sum_congr rfl
      intro u₀ _
      rw [integral_finsetSum Finset.univ (fun t₀ _ =>
        (integrable_const (1 : ℝ)).indicator
          ((sourcePrefixFiltration control0).le' (t₀.val + 1) _
            (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
              rate rewards C_star C_h control0 u₀ t₀)))]
    _ = ∫ z : S,
        (retainedFirstCall rate rewards C_star C_h).indicator
          (fun _ : S => (1 : ℝ)) z ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (retainedFirstCall_indicator_sum_eq rate rewards C_star C_h ·)
    _ = (sourceInputLaw p).real (retainedFirstCall rate rewards C_star C_h) :=
      integral_indicator_one
        (retainedFirstCall_measurable rate rewards C_star C_h control0)

omit control0 in
/-- The retained first-call event has probability at most one. -/
theorem retainedFirstCall_measure_le_one :
    (sourceInputLaw p).real (retainedFirstCall rate rewards C_star C_h) ≤ 1 := by
  exact measureReal_le_one

/-- The incoming call sum is measurable in the original source space. -/
theorem callXMinus_measurable :
    Measurable (callXMinus rate rewards C_star C_h a) := by
  apply Finset.measurable_sum Finset.univ
  intro u₀ _
  apply Finset.measurable_sum Finset.univ
  intro t₀ _
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_measurable_ambient
    rate rewards C_star C_h control0 u₀ t₀ a

/-- The post-update call sum is measurable in the original source space. -/
theorem callXPlus_measurable :
    Measurable (callXPlus rate rewards C_star C_h a) := by
  apply Finset.measurable_sum Finset.univ
  intro u₀ _
  apply Finset.measurable_sum Finset.univ
  intro t₀ _
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_measurable
    rate rewards C_star C_h control0 u₀ t₀ a

/-- The incoming call sum is integrable under the original source law. -/
theorem callXMinus_integrable :
    Integrable (callXMinus rate rewards C_star C_h a) mu := by
  apply integrable_finsetSum
  intro u₀ _
  apply integrable_finsetSum
  intro t₀ _
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
    rate rewards C_star C_h control0 u₀ t₀ a

/-- The post-update call sum is integrable under the original source law. -/
theorem callXPlus_integrable :
    Integrable (callXPlus rate rewards C_star C_h a) mu := by
  apply integrable_finsetSum
  intro u₀ _
  apply integrable_finsetSum
  intro t₀ _
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
    rate rewards C_star C_h control0 u₀ t₀ a

/-- Reconstruct the sharp conditional estimate locally from the public
pointwise gate step, original-law integrability, and retained-increment
conditional exponential bound. -/
theorem condExp_XPlus_le_XMinus_add_G_indicator :
    mu[(ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
      rate rewards C_star C_h u t a) | F] ≤ᵐ[mu]
      (fun z : S =>
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z +
        (G).indicator (fun _ : S => (1 : ℝ)) z) := by
  let g : S → ℝ := (G).indicator (fun _ => (1 : ℝ))
  let prod : S → ℝ :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
      rate rewards C_star C_h u t a *
    ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
      rate rewards C_star C_h u t a
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGfield : MeasurableSet[F] G :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t
  have hGambient : MeasurableSet G := hle _ hGfield
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hGint : Integrable g mu := by
    have h := hone.indicator hGambient
    simpa [g] using h
  have hprodint :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_mul_expRetainedIncrement_integrable
      rate rewards C_star C_h control0 u t a
  have hsumint : Integrable (fun z : S => g z + prod z) mu := by
    exact hGint.add (by simpa [prod] using hprodint)
  have hpoint : ∀ z : S,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u t a z ≤ g z + prod z := by
    intro z
    simpa [g, prod] using
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_le_G_indicator_add_product
        rate rewards C_star C_h u t a z
  have hmono := condExp_mono (m := F)
    (ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
      rate rewards C_star C_h control0 u t a)
    hsumint (Filter.Eventually.of_forall hpoint)
  have hsum := condExp_add hGint (by simpa [prod] using hprodint) F
  have hmask := condExp_indicator (μ := mu) hone hGfield
  have hconst := condExp_const (μ := mu) (m := F)
    (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
  have hGce : mu[g | F] =ᵐ[mu] g := by
    filter_upwards [hmask] with z hmask_z
    rw [hconst] at hmask_z
    simpa [g] using hmask_z
  have hXminusMeas :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_measurable
      rate rewards C_star C_h control0 u t a
  have hXminusAES : AEStronglyMeasurable[F]
      (ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a) mu := hXminusMeas.aestronglyMeasurable
  have hYint :=
    ReferenceFirstCollectionCurrentExponentialIncrement.integrable_expRetainedIncrement
      rate rewards C_star C_h u t a control0
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    hXminusAES hprodint hYint
  have hPullProd : mu[prod | F] =ᵐ[mu]
      (fun z : S =>
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z *
        mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t a | F] z) := by
    filter_upwards [hPull] with z hz
    change mu[prod | F] z = _ at hz
    exact hz
  have hYbound :=
    ReferenceFirstCollectionCurrentExponentialIncrement.condExp_expRetainedIncrement_le_one
      rate rewards C_star C_h control0 u t a
  filter_upwards [hmono, hsum, hGce, hPullProd, hYbound]
    with z hmono_z hsum_z hGce_z hPullProd_z hYbound_z
  have hXnonneg :=
    (ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_bounds
      rate rewards C_star C_h u t a z).1
  calc
    mu[(ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u t a) | F] z ≤
        mu[(fun y : S => g y + prod y) | F] z := hmono_z
    _ = mu[g | F] z + mu[prod | F] z := by
      have hadd : (fun y : S => g y + prod y) = g + prod := by
        funext y
        rfl
      rw [hadd]
      exact hsum_z
    _ = g z +
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z *
          mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
            rate rewards C_star C_h u t a | F] z := by
      rw [hGce_z, hPullProd_z]
    _ ≤ g z +
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z := by
      have hmul := mul_le_mul_of_nonneg_left hYbound_z hXnonneg
      have hmul' :
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
              rate rewards C_star C_h u t a z *
              mu[ReferenceFirstCollectionCurrentExponentialIncrement.expRetainedIncrement
                rate rewards C_star C_h u t a | F] z ≤
            ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
              rate rewards C_star C_h u t a z := by
        simpa using hmul
      linarith
    _ =
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u t a z +
          (G).indicator (fun _ : S => (1 : ℝ)) z := by
      dsimp [g]
      ring

/-- Sharp source-prefix set-integral estimate: a cell pays only the mass of
the intersection with its actual retained gate. -/
theorem setIntegral_XPlus_le_XMinus_add_intersection_measure (B : Set S)
    (hB : MeasurableSet[F] B) :
    (∫ z in B,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u t a z ∂mu) ≤
    (∫ z in B,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z ∂mu) +
      (mu).real (B ∩ G) := by
  have hplus :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
      rate rewards C_star C_h control0 u t a
  have hminus :=
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
      rate rewards C_star C_h control0 u t a
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGambient : MeasurableSet G := hle _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have htarget : Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z +
      (G).indicator (fun _ : S => (1 : ℝ)) z) mu := by
    exact hminus.add ((integrable_const (1 : ℝ)).indicator hGambient)
  calc
    (∫ z in B,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z ∂mu) =
      (∫ z in B,
        mu[ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a | F] z ∂mu) :=
      (setIntegral_condExp hle hplus hB).symm
    _ ≤ (∫ z in B,
        (ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z +
         (G).indicator (fun _ : S => (1 : ℝ)) z) ∂mu) :=
      setIntegral_mono_ae integrable_condExp.integrableOn htarget.integrableOn
        (condExp_XPlus_le_XMinus_add_G_indicator
          rate rewards C_star C_h control0 u t a)
    _ = (∫ z in B,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u t a z ∂mu) +
        (mu).real (B ∩ G) := by
      rw [integral_add hminus.integrableOn
        ((integrable_const (1 : ℝ)).indicator hGambient).integrableOn,
        show (fun z : S => (G).indicator (fun _ : S => (1 : ℝ)) z) =
          (G).indicator (fun _ : S => (1 : ℝ)) from rfl,
        setIntegral_indicator hGambient,
        setIntegral_const]
      simp only [smul_eq_mul, mul_one]

/-- Whole-space sharp estimate for one original first-call cutoff/date cell. -/
theorem integral_XPlus_le_integral_XMinus_add_G_measure :
    (∫ z : S,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
        rate rewards C_star C_h u t a z ∂mu) ≤
    (∫ z : S,
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
        rate rewards C_star C_h u t a z ∂mu) + (mu).real G := by
  calc
    (∫ z : S,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z ∂mu) =
      (∫ z in Set.univ,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
          rate rewards C_star C_h u t a z ∂mu) :=
      setIntegral_univ.symm
    _ ≤ (∫ z in Set.univ,
        ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
          rate rewards C_star C_h u t a z ∂mu) +
        (mu).real (Set.univ ∩ G) :=
      setIntegral_XPlus_le_XMinus_add_intersection_measure
        rate rewards C_star C_h control0 u t a Set.univ MeasurableSet.univ
    _ = (∫ z : S,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u t a z ∂mu) + (mu).real G := by
      rw [setIntegral_univ]
      simp

private theorem integral_callXPlus_eq_sum_integrals :
    (∫ z : S, callXPlus rate rewards C_star C_h a z ∂mu) =
      ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        ∫ z : S,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
            rate rewards C_star C_h u₀ t₀ a z ∂mu := by
  unfold callXPlus
  rw [integral_finsetSum Finset.univ (fun u₀ _ =>
    integrable_finsetSum Finset.univ (fun t₀ _ =>
      ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
        rate rewards C_star C_h control0 u₀ t₀ a))]
  apply Finset.sum_congr rfl
  intro u₀ _
  rw [integral_finsetSum Finset.univ (fun t₀ _ =>
    ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_integrable
      rate rewards C_star C_h control0 u₀ t₀ a)]

private theorem integral_callXMinus_eq_sum_integrals :
    (∫ z : S, callXMinus rate rewards C_star C_h a z ∂mu) =
      ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        ∫ z : S,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
            rate rewards C_star C_h u₀ t₀ a z ∂mu := by
  unfold callXMinus
  rw [integral_finsetSum Finset.univ (fun u₀ _ =>
    integrable_finsetSum Finset.univ (fun t₀ _ =>
      ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
        rate rewards C_star C_h control0 u₀ t₀ a))]
  apply Finset.sum_congr rfl
  intro u₀ _
  rw [integral_finsetSum Finset.univ (fun t₀ _ =>
    ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus_integrable
      rate rewards C_star C_h control0 u₀ t₀ a)]

/-- The original-law integral of the random actual-call sum pays exactly the
probability of its retained first-call event. -/
theorem integral_callXPlus_le_integral_callXMinus_add_retainedFirstCall_measure
    :
    (∫ z : S, callXPlus rate rewards C_star C_h a z ∂mu) ≤
      (∫ z : S, callXMinus rate rewards C_star C_h a z ∂mu) +
        (mu).real (retainedFirstCall rate rewards C_star C_h) := by
  rw [integral_callXPlus_eq_sum_integrals rate rewards C_star C_h control0 a,
    integral_callXMinus_eq_sum_integrals rate rewards C_star C_h control0 a]
  have hcost := sum_retainedGate_measures_eq_retainedFirstCall_measure
    rate rewards C_star C_h control0
  calc
    (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        ∫ z : S,
          ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus
            rate rewards C_star C_h u₀ t₀ a z ∂mu) ≤
      ∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
        ((∫ z : S,
            ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
              rate rewards C_star C_h u₀ t₀ a z ∂mu) +
          (mu).real (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u₀ t₀)) := by
      apply Finset.sum_le_sum
      intro u₀ _
      apply Finset.sum_le_sum
      intro t₀ _
      exact integral_XPlus_le_integral_XMinus_add_G_measure
        rate rewards C_star C_h control0 u₀ t₀ a
    _ = (∑ u₀ : Fin p.T, ∑ t₀ : Fin p.T,
          ∫ z : S,
            ReferenceFirstCollectionCurrentExponentialQueueStep.XMinus
              rate rewards C_star C_h u₀ t₀ a z ∂mu) +
        (mu).real (retainedFirstCall rate rewards C_star C_h) := by
      simp only [Finset.sum_add_distrib, hcost]

/-- The sharp random-call estimate, followed by its probability-at-most-one
consequence under the same original source law. -/
theorem integral_callXPlus_le_integral_callXMinus_add_one :
    (∫ z : S, callXPlus rate rewards C_star C_h a z ∂mu) ≤
      (∫ z : S, callXMinus rate rewards C_star C_h a z ∂mu) + 1 := by
  calc
    (∫ z : S, callXPlus rate rewards C_star C_h a z ∂mu) ≤
        (∫ z : S, callXMinus rate rewards C_star C_h a z ∂mu) +
          (mu).real (retainedFirstCall rate rewards C_star C_h) :=
      integral_callXPlus_le_integral_callXMinus_add_retainedFirstCall_measure
        rate rewards C_star C_h control0 a
    _ ≤ (∫ z : S, callXMinus rate rewards C_star C_h a z ∂mu) + 1 :=
      by
        have hprob := retainedFirstCall_measure_le_one rate rewards C_star C_h
        linarith

end Bandits.Support.ReferenceFirstCollectionActualCallExponentialQueueEstimate

end
