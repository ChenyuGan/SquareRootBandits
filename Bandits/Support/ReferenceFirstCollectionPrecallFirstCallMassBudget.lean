/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity
public import Bandits.Support.ReferenceFirstCollectionPrecallLiveOldMass
public import Bandits.Support.ReferenceFirstCollectionActualCallWeightedEnergy

import Mathlib.Tactic

/-!
# Sharp first-call mass budget on the original source

At each calendar date, the original first-live birth, continuing, and empty
source cells, the retained OLD update, and the retained first-invocation gates
are disjoint subsets of the same source space. Their unnormalized masses fit
one probability budget. Summing the date budgets charges the retained first
invocation exactly once per source.

Sources: `04_slow_fast_learner.tex:140-188,245-318`,
`05_binary_transport.tex:352-431`, and
`06_interruptions.tex:35-100,355-426` under `sources/zip4/manuscript/`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallFirstCallMassBudget

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (t : Fin p.T)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "P" =>
  (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)
local notation "O" =>
  ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
local notation "Q" u:max =>
  ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t

private theorem sourceInputLaw_measure_ne_top (p : Parameters)
    (E : Set (SourceInput p)) : sourceInputLaw p E ≠ (⊤ : ENNReal) := by
  have hprob : IsProbabilityMeasure (sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply ne_of_lt
  calc
    sourceInputLaw p E ≤ sourceInputLaw p Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := hprob.measure_univ
    _ < (⊤ : ENNReal) := ENNReal.one_lt_top

/-- The exact original birth, continuing, and empty source-cell mass at one
date, before it is enlarged to the phase-union mass. -/
@[expose] public def sourceCellMass
    (rate0 : ReferenceActivePhysicalStep.RateInput p)
    (rewards0 : GridRewardTable p) (C_star0 C_h0 : ℝ)
    (date : Fin p.T) (control0 : TimeControl p) : ℝ :=
  (∑ q : Fin (ConstructorDimensions.M p),
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure
        rate0 rewards0 C_star0 C_h0 date
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)).real Set.univ) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (date.val + 1),
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate0 rewards0 C_star0 C_h0 q date v.val (Nat.lt_succ_iff.mp v.isLt) control0).real
          Set.univ +
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
          rate0 rewards0 C_star0 C_h0 q date v.val (Nat.lt_succ_iff.mp v.isLt) control0).real
          Set.univ))

/-- The source-cell expression is exactly the mass of the original LIVE phase
union, with no normalization or additional source premise. -/
theorem sourceCellMass_eq_sourcePhase234 (control0 : TimeControl p) :
    sourceCellMass rate rewards C_star C_h t control0 = Measure.real mu P := by
  simpa only [sourceCellMass] using
    ReferenceFirstLiveCalendarIntegralAssembly.source_cell_mass_eq
      rate rewards C_star C_h t control0

private theorem sourcePhase234_before_firstCallBoundary
    (control0 : TimeControl p) (z : S) (hz : z ∈ P) :
    t.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h z := by
  rcases hz with hz23 | hz4
  · rcases hz23 with hz2 | hz3
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz2
      have hpos := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
        rate rewards C_star C_h t control0 z hz2
      obtain ⟨_, hstart⟩ := hz2
      have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h z
      have hend :=
        ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
          rate rewards C_star C_h z
      omega
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz3
      rcases hz3 with ⟨_, hrest⟩
      rcases hrest with ⟨_, hwindow⟩
      rcases hwindow with ⟨hk, _⟩
      have hend :=
        ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
          rate rewards C_star C_h z
      have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h z
      omega
  · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz4
    rcases hz4 with ⟨_, hrest⟩
    rcases hrest with ⟨_, hwindow⟩
    rcases hwindow with ⟨hk, _⟩
    have hend :=
      ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
        rate rewards C_star C_h z
    have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
      rate rewards C_star C_h z
    omega

/-- Membership in an actual retained gate fixes its calendar date to the
first-call boundary, including a failed sampler invocation. -/
theorem currentRetainedGate_boundary_eq_date (u : Fin p.T) (z : S)
    (hz : z ∈ Q u) :
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h z = t.val := by
  have hcell :
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t := by
    change z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t ∩ _ at hz
    exact hz.1
  exact ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hcell

/-- Different cutoff tags of the actual first invocation cannot occur on one
original source input at the same date. -/
theorem currentRetainedGate_pairwise_disjoint :
    Pairwise (fun u v : Fin p.T => Disjoint (Q u) (Q v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro z hzu hzv
  have hfirstU :
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t := by
    change z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t ∩ _ at hzu
    exact hzu.1
  have hfirstV :
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h v t := by
    change z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h v t ∩ _ at hzv
    exact hzv.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) at hfirstU
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (v, t) at hfirstV
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at hfirstU
  | some c =>
      have hu : (c.1, c.2.1) = (u, t) := by simpa [hcall] using hfirstU
      have hv : (c.1, c.2.1) = (v, t) := by simpa [hcall] using hfirstV
      exact huv (congrArg Prod.fst (hu.symm.trans hv))

/-- The retained call gates are disjoint from the original birth, continuing,
and empty first-live source phases by source chronology. -/
theorem sourcePhase234_disjoint_currentRetainedGateUnion
    (control0 : TimeControl p) :
    Disjoint P (⋃ u : Fin p.T, Q u) := by
  apply Set.disjoint_left.mpr
  intro z hzPhase hzGate
  obtain ⟨u, hzu⟩ := Set.mem_iUnion.mp hzGate
  have hbefore := sourcePhase234_before_firstCallBoundary
    rate rewards C_star C_h t control0 z hzPhase
  have hboundary := currentRetainedGate_boundary_eq_date
    rate rewards C_star C_h t u z hzu
  omega

/-- The retained call gates are disjoint from the original retained OLD
update: OLD is strictly before the invocation boundary, while a call gate is
at that boundary. -/
theorem oldG_disjoint_currentRetainedGateUnion :
    Disjoint O (⋃ u : Fin p.T, Q u) := by
  apply Set.disjoint_left.mpr
  intro z hzOld hzGate
  obtain ⟨u, hzu⟩ := Set.mem_iUnion.mp hzGate
  have hE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t := by
    change z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t ∩ _ ∩ _ at hzOld
    exact hzOld.1.1
  have hbefore :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hE |>.1
  have hboundary := currentRetainedGate_boundary_eq_date
    rate rewards C_star C_h t u z hzu
  omega

/-- Every retained call gate is measurable in the original ambient source
space, by inclusion from its accepted source-prefix field. -/
theorem measurableSet_currentRetainedGate_ambient
    (control0 : TimeControl p) (u : Fin p.T) :
    MeasurableSet (Q u) := by
  have hle :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 1) ≤ (inferInstance : MeasurableSpace S) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  exact hle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
    rate rewards C_star C_h control0 u t)

private theorem sum_currentRetainedGate_real_eq_iUnion
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, Measure.real mu (Q u)) =
      Measure.real mu (⋃ u : Fin p.T, Q u) := by
  symm
  exact measureReal_iUnion_fintype
    (currentRetainedGate_pairwise_disjoint rate rewards C_star C_h t)
    (fun u => measurableSet_currentRetainedGate_ambient
      rate rewards C_star C_h t control0 u)

/-- Exact unnormalized additivity for LIVE source cells, retained OLD updates,
and every retained first-call cutoff gate on the same original source. -/
theorem sourcePhase234_oldG_currentRetainedGate_real_add_eq_union
    (control0 : TimeControl p) :
    sourceCellMass rate rewards C_star C_h t control0 + Measure.real mu O +
        (∑ u : Fin p.T, Measure.real mu (Q u)) =
      Measure.real mu ((P ∪ O) ∪ ⋃ u : Fin p.T, Q u) := by
  have hcell := sourceCellMass_eq_sourcePhase234
    rate rewards C_star C_h t control0
  have hbase :=
    ReferenceFirstCollectionPrecallLiveOldMass.sourcePhase234_G_real_add_eq_union
      rate rewards C_star C_h t control0
  have hdisjoint : Disjoint (P ∪ O) (⋃ u : Fin p.T, Q u) := by
    apply Set.disjoint_left.mpr
    intro z hzBase hzCall
    rcases hzBase with hzPhase | hzOld
    · exact (Set.disjoint_left.mp
        (sourcePhase234_disjoint_currentRetainedGateUnion
          rate rewards C_star C_h t control0)) hzPhase hzCall
    · exact (Set.disjoint_left.mp
        (oldG_disjoint_currentRetainedGateUnion
          rate rewards C_star C_h t)) hzOld hzCall
  have hmeas : MeasurableSet (⋃ u : Fin p.T, Q u) :=
    MeasurableSet.iUnion (fun u => measurableSet_currentRetainedGate_ambient
      rate rewards C_star C_h t control0 u)
  calc
    _ = (Measure.real mu P + Measure.real mu O) +
          Measure.real mu (⋃ u : Fin p.T, Q u) := by
      rw [hcell, sum_currentRetainedGate_real_eq_iUnion
        rate rewards C_star C_h t control0]
    _ = Measure.real mu (P ∪ O) + Measure.real mu (⋃ u : Fin p.T, Q u) := by rw [hbase]
    _ = Measure.real mu ((P ∪ O) ∪ ⋃ u : Fin p.T, Q u) :=
      (measureReal_union hdisjoint hmeas
        (sourceInputLaw_measure_ne_top p (P ∪ O))
        (sourceInputLaw_measure_ne_top p (⋃ u : Fin p.T, Q u))).symm

/-- The original per-date source-cell mass, OLD update, and retained call
mass fit one unnormalized probability budget. -/
theorem sourceCellMass_oldG_currentRetainedGate_le_one
    (control0 : TimeControl p) :
    sourceCellMass rate rewards C_star C_h t control0 + Measure.real mu O +
        (∑ u : Fin p.T, Measure.real mu (Q u)) ≤ 1 := by
  have hprob : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have huniv : mu Set.univ = 1 := hprob.measure_univ
  have hbound :
      Measure.real mu ((P ∪ O) ∪ ⋃ u : Fin p.T, Q u) ≤ 1 := by
    calc
      Measure.real mu ((P ∪ O) ∪ ⋃ u : Fin p.T, Q u) ≤ Measure.real mu Set.univ := by
        exact measureReal_mono (Set.subset_univ _)
          (sourceInputLaw_measure_ne_top p Set.univ)
      _ = 1 := by simp [Measure.real_def, huniv]
  calc
    _ = Measure.real mu ((P ∪ O) ∪ ⋃ u : Fin p.T, Q u) :=
      sourcePhase234_oldG_currentRetainedGate_real_add_eq_union
        rate rewards C_star C_h t control0
    _ ≤ 1 := hbound

/-- Summing the sharp per-date source budgets charges the disjoint retained
first-call gates exactly once, yielding the finite-horizon mass consequence. -/
theorem sum_sourceCellMass_oldG_add_retainedFirstCall_le_horizon
    (control0 : TimeControl p) :
    (∑ date : Fin p.T,
      (sourceCellMass rate rewards C_star C_h date control0 +
        Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h date))) +
      Measure.real mu (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
        rate rewards C_star C_h) ≤ (p.T : ℝ) := by
  let A : Fin p.T → ℝ := fun date =>
    sourceCellMass rate rewards C_star C_h date control0
  have hdate (date : Fin p.T) :
      A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h date) +
        (∑ u : Fin p.T, Measure.real mu
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u date)) ≤ 1 := by
    simpa only [A] using
      sourceCellMass_oldG_currentRetainedGate_le_one
        rate rewards C_star C_h date control0
  have hsum :
      (Finset.univ.sum (fun date : Fin p.T =>
        (A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date)) +
          Finset.univ.sum (fun u : Fin p.T => Measure.real mu
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u date)))) ≤
        Finset.univ.sum (fun _date : Fin p.T => (1 : ℝ)) := by
    apply Finset.sum_le_sum
    intro date _
    exact hdate date
  have hsplit :
      (Finset.univ.sum (fun date : Fin p.T =>
        (A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date)) +
          Finset.univ.sum (fun u : Fin p.T => Measure.real mu
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u date)))) =
        (Finset.univ.sum (fun date : Fin p.T =>
          A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date))) +
        (Finset.univ.sum (fun u : Fin p.T => Finset.univ.sum
          (fun date : Fin p.T => Measure.real mu
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u date)))) := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  have hcall :=
    ReferenceFirstCollectionActualCallExponentialQueueEstimate.sum_retainedGate_measures_eq_retainedFirstCall_measure
      rate rewards C_star C_h control0
  calc
    _ = (Finset.univ.sum (fun date : Fin p.T =>
          A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date))) +
        (Finset.univ.sum (fun u : Fin p.T => Finset.univ.sum
          (fun date : Fin p.T => Measure.real mu
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u date)))) := by
      rw [← hcall]
    _ = Finset.univ.sum (fun date : Fin p.T =>
          (A date + Measure.real mu (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date)) +
            Finset.univ.sum (fun u : Fin p.T => Measure.real mu
              (ReferenceFirstCollectionCurrentRetainedGate.G
                rate rewards C_star C_h u date))) := hsplit.symm
    _ ≤ Finset.univ.sum (fun _date : Fin p.T => (1 : ℝ)) := hsum
    _ = (p.T : ℝ) := by simp

end Bandits.Support.ReferenceFirstCollectionPrecallFirstCallMassBudget

end
