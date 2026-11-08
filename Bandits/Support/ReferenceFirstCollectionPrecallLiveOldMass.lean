/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldCalendarExponentialStep

/-!
# Original first-collection OLD and first-live phase mass

The OLD selector and the first-live birth, continuing, and empty phases are
separated on the same complete source. Their original, unnormalized masses
share one probability budget under the source-input law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallLiveOldMass

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (t : Fin p.T)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p

private theorem old_event_after_whole_firstLiveWindow (z : S)
    (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length ≤ t.val := by
  obtain ⟨_, hcellSome⟩ :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hz
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hcellSome
  obtain ⟨record, hrecord, hread⟩ :=
    Option.bind_eq_some_iff.mp (by
      simpa only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?] using hcell)
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hrecord
    cases hrecord
  have hreadSome :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome = true := by
    rw [hread]
    rfl
  have hbound := ReferenceFirstCollectionPrecallCalendarSupport.old_readout_after_firstLiveWindow
    rate rewards C_star C_h t z hlaunch record hrecord hreadSome
  simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow] using hbound

/-- The original OLD event is disjoint from the union of the actual birth,
continuing, and empty first-live source phases on the whole source. -/
theorem old_event_disjoint_source_phases (control0 : TimeControl p) :
    Disjoint
      (ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t)
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) := by
  apply Set.disjoint_left.mpr
  intro z hzOld hzPhase
  rcases hzPhase with hz23 | hz4
  · rcases hz23 with hz2 | hz3
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase,
        ] at hz2
      have hwindowPos :=
        ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
          rate rewards C_star C_h t control0 z hz2
      obtain ⟨_, hstartEq⟩ := hz2
      have hwindowBound := old_event_after_whole_firstLiveWindow
        rate rewards C_star C_h t z hzOld
      omega
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase,
        ] at hz3
      rcases hz3 with ⟨_, hrest⟩
      rcases hrest with ⟨_, hwindow⟩
      rcases hwindow with ⟨hk, _⟩
      have hwindowBound := old_event_after_whole_firstLiveWindow
        rate rewards C_star C_h t z hzOld
      omega
  · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase,
      ] at hz4
    rcases hz4 with ⟨_, hrest⟩
    rcases hrest with ⟨_, hwindow⟩
    rcases hwindow with ⟨hk, _⟩
    have hwindowBound := old_event_after_whole_firstLiveWindow
      rate rewards C_star C_h t z hzOld
    omega

/-- The source phase union is ambient measurable under the existing
continuous control. -/
theorem measurableSet_sourcePhase234 (control0 : TimeControl p) :
    MeasurableSet
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) := by
  exact ((ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 (2 : Fin 6)).union
    (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 (3 : Fin 6))).union
    (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 (4 : Fin 6))

/-- The original OLD selector is ambient measurable after the established
source-prefix filtration inclusion. -/
theorem measurableSet_E_ambient (control0 : TimeControl p) :
    MeasurableSet
      (ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t) := by
  have hle :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 1) ≤ (inferInstance : MeasurableSpace S) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  exact hle _ (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_E
    rate rewards C_star C_h control0 t)

/-- The retained original OLD update is ambient measurable after the same
source-prefix filtration inclusion. -/
theorem measurableSet_G_ambient (control0 : TimeControl p) :
    MeasurableSet
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t) := by
  have hle :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 1) ≤ (inferInstance : MeasurableSpace S) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  exact hle _ (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
    rate rewards C_star C_h control0 t)

/-- Exact additivity of the original phase-union mass and retained OLD mass. -/
theorem sourcePhase234_G_real_add_eq_union (control0 : TimeControl p) :
    Measure.real mu
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) +
      Measure.real mu
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) =
    Measure.real mu
        ((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) ∪
          ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) := by
  have hsubset :
      ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t ⊆
        ReferenceFirstCollectionOldCalendarExponentialStep.E
          rate rewards C_star C_h t := by
    intro z hz
    exact hz.1.1
  have hdisjoint :
      Disjoint
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) := by
    apply Set.disjoint_left.mpr
    intro z hzPhase hzG
    exact (Set.disjoint_left.mp
      (old_event_disjoint_source_phases rate rewards C_star C_h t control0))
      (hsubset hzG) hzPhase
  rw [measureReal_union hdisjoint
    (measurableSet_G_ambient rate rewards C_star C_h t control0)]

/-- The combined first-live phase and retained OLD mass uses one sharp
probability budget under the original source-input law. -/
theorem sourcePhase234_G_real_add_le_one (control0 : TimeControl p) :
    Measure.real mu
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) +
      Measure.real mu
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) ≤ 1 := by
  have hprob : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hmass : mu Set.univ = 1 := hprob.measure_univ
  have hbound :
      Measure.real mu
          ((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) ∪
            ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t) ≤ 1 := by
    calc
      Measure.real mu _ ≤ Measure.real mu Set.univ := by
        exact measureReal_mono (Set.subset_univ _) (by rw [hmass]; simp)
      _ = 1 := by simp [Measure.real_def, hmass]
  calc
    _ = Measure.real mu
          ((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) ∪
            ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t) :=
      sourcePhase234_G_real_add_eq_union rate rewards C_star C_h t control0
    _ ≤ 1 := hbound

/-- Exact unnormalized birth, continuing, and empty source-cell masses plus
retained OLD mass fit in the same single probability budget. -/
theorem source_cell_masses_add_G_le_one (control0 : TimeControl p) :
    ((∑ q : Fin (ConstructorDimensions.M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
      (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
          (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ))) +
      Measure.real mu
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) ≤ 1 := by
  rw [ReferenceFirstLiveCalendarIntegralAssembly.source_cell_mass_eq
    rate rewards C_star C_h t control0]
  exact sourcePhase234_G_real_add_le_one rate rewards C_star C_h t control0

end Bandits.Support.ReferenceFirstCollectionPrecallLiveOldMass

end
