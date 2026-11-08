/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Bandits.Support.ReferenceAwaitedDownCohortCoverage

/-!
# Probability bound for the fixed awaited DOWN decoder error

The event is the literal finite-calendar existential of the actual fixed-
awaited DOWN failure readout. Its pointwise containment in the joint cohort
event lets the existing quota bound cover all detecting dates at once.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceAwaitedDownDecoderErrorProbability

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The literal event that a fixed-awaited DOWN ambiguity is detected on
some physical calendar date. -/
def fixedAwaitedDownFailureEvent : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | ∃ t : Fin p.T,
    ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t}

/-- The finite union over detecting dates is measurable on the original
source carrier. -/
theorem fixedAwaitedDownFailureEvent_borel :
    MeasurableSet (fixedAwaitedDownFailureEvent rate rewards C_star C_h) := by
  change MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
    ∃ t : Fin p.T,
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t}
  rw [show
    {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ t : Fin p.T,
        ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
          rate rewards C_star C_h z t} =
      ⋃ t : Fin p.T,
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
            rate rewards C_star C_h z t} by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]]
  exact MeasurableSet.iUnion fun t =>
    ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt_borel
      rate rewards C_star C_h t

/-- Every detecting date is covered by the same joint DOWN cohort event. -/
theorem fixedAwaitedDownFailureEvent_subset_downCohortUnionEvent
    (control0 : ContinuousLearningRows.TimeControl p) :
    fixedAwaitedDownFailureEvent rate rewards C_star C_h ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  intro z hz
  change ∃ t : Fin p.T,
    ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t at hz
  obtain ⟨t, hD⟩ := hz
  exact ReferenceAwaitedDownCohortCoverage.fixedAwaitedDownFailureAt_mem_downCohortUnionEvent
    rate rewards C_star C_h control0 z t hD

/-- The original source-law probability of the literal fixed-awaited DOWN
event is bounded by the already established joint cohort quota estimate. -/
theorem fixedAwaitedDownFailureEvent_measureReal_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (fixedAwaitedDownFailureEvent rate rewards C_star C_h) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  apply le_trans
    (measureReal_mono
      (fixedAwaitedDownFailureEvent_subset_downCohortUnionEvent
        rate rewards C_star C_h control0))
  exact ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measureReal_quota_bound
    rate rewards C_star C_h control0

end Bandits.Support.ReferenceAwaitedDownDecoderErrorProbability

end
