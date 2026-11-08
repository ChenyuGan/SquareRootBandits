/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInspectedPastRoundObservations
public import Bandits.Support.ReferenceFirstLiveNumericalPrefixAdaptation

/-!
# Inspected generators for the first-live strict numerical past

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:293-308,331-345`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The exports here identify the strict-past source coordinates available in the
existing inspected field. They preserve the original source carrier, every
whole-round absence tag, the full selected forward row, all private
coordinates, and every selected control before the current round. They do not
identify that field with the manuscript filtration or claim a numerical-cell
or queue-run factorization.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstLiveInspectedNumericalPast

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
  (rate : RateInput p)
  (rewards : RewardTable p)
  (C_star C_h : ℝ)
  (q : Fin (M p))
  (t : Fin p.T)
  (s : ℕ)
  (hs : s ≤ t.val)
  (control0 : TimeControl p)

noncomputable abbrev SourceZ (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)

noncomputable abbrev Inspected (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h
    t.val (Nat.le_of_lt t.isLt)

noncomputable abbrev InspectedOnZ (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) :=
  MeasurableSpace.comap
    (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _)
    (Inspected rate rewards C_star C_h t)

/-- Every real strict-past optional whole-round code remains measurable after
restriction to the actual first-live source stratum and pullback of the exact
inspected history field. -/
theorem measurable_pastRoundObservations :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        ReferenceInspectedPastRoundObservations.pastRoundObservations
          rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val) := by
  exact (ReferenceInspectedPastRoundObservations.pastRoundObservations_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)).comp
      (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- The original complete selected forward row is a generator of the same
inspected field on the source stratum. -/
theorem measurable_selectedForwardRow :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        ReferenceSourceOwnHistoryContainment.selectedForwardRow z.val) := by
  exact (ReferenceInspectedPastRoundObservations.selectedForwardRow_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)).comp
      (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- All original private coordinates, including the coordinator index, remain
available on the same pulled-back inspected field. -/
theorem measurable_privateCoordinates :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        (z.val.2 : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)) := by
  exact (ReferenceInspectedPastRoundObservations.privateCoordinates_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)).comp
      (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- All selected controls at offsets strictly below the current round are
measurable in the pulled-back inspected field. -/
theorem measurable_selectedControlPrefix :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        ReferenceSourceOwnHistoryContainment.selectedControlPrefix t.val
          (Nat.le_of_lt t.isLt) z.val) := by
  exact (ReferenceInspectedPastRoundObservations.selectedControlPrefix_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)).comp
      (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- The incoming source state at the launch offset is available as its exact
optional encoded state. Its presence is not replaced by a default state. -/
theorem measurable_incomingAtLaunch :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
          ⟨s, lt_of_le_of_lt hs t.isLt⟩ z.val) := by
  have hin := ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)
    ⟨s, lt_of_le_of_lt hs t.isLt⟩ hs
  exact hin.comp
    (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- For each local strict-past offset, the exact optional whole-round code at
source time `s + k` is measurable. The bound proves this lookup never reads
the current round. -/
theorem measurable_pastRoundObservationAt (k : Fin (t.val - s)) :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        ReferenceInspectedPastRoundObservations.pastRoundObservations
          rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val
          ⟨s + k.val, by omega⟩) := by
  exact (measurable_pi_apply ⟨s + k.val, by omega⟩).comp
    (measurable_pastRoundObservations rate rewards C_star C_h q t s hs)

/-- The coordinator identifier is retained as an original inspected
generator, alongside the private-coordinate array. -/
theorem measurable_ids :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs => z.val.1.1) := by
  exact (ReferenceInspectedPastRoundObservations.ids_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)).comp
      (comap_measurable (Subtype.val : SourceZ rate rewards C_star C_h q t s hs → _))

/-- The actual selected-row control at each source offset in the first-live
strict-past window is a coordinate of the original selected-control prefix.
This is the current control for that earlier round; the round at `t.val` is
outside the index domain. -/
theorem measurable_localSelectedControl (k : Fin (t.val - s)) :
    Measurable[InspectedOnZ rate rewards C_star C_h q t s hs]
      (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        (ReferenceSourceOwnHistoryContainment.selectedControlPrefix t.val
          (Nat.le_of_lt t.isLt) z.val) ⟨s + k.val, by omega⟩) := by
  exact (measurable_pi_apply ⟨s + k.val, by omega⟩).comp
    (measurable_selectedControlPrefix rate rewards C_star C_h q t s hs)

end Bandits.Support.ReferenceFirstLiveInspectedNumericalPast

end
