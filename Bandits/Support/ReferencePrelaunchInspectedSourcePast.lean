/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
public import Bandits.Support.ReferenceInspectedPastRoundObservations

/-!
# Generated prelaunch prefixes from the exact inspected source field

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/05_binary_transport.tex:7-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The factor below retains the original strict calendar past and the original
extended-private past view.  Its public coordinates are formed directly from
the complete selected forward row and the selected controls inside the exact
inspected history field.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePrelaunchInspectedSourcePast

open MeasureTheory
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ContinuousLearningRows
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The actual `GeneratedBootstrapRoundLaw.Past` assembled from the four
inspected generators.  Only strict-past controls are read. -/
def generatedPastFromInspectedGenerators (n : ℕ)
    (r : Fin p.T) (hr : r.val ≤ n)
    (forward : CompletePublicTable.ForwardRow p)
    (controls : Fin n → TimeControl p)
    (privateCoordinates : ExtendedPrivateCoordinates p) :
    GeneratedBootstrapRoundLaw.Past p r :=
  (fun q =>
      (fun u => forward u q.1,
        controls ⟨q.1.val, by
          have hq : q.1.val < r.val := by
            simpa only [GeneratedBootstrapRoundLaw.cutoff] using q.2
          omega
        ⟩),
    (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r privateCoordinates).1)

private theorem measurable_generatedPastFromInspectedGenerators
    (n : ℕ) (r : Fin p.T) (hr : r.val ≤ n) :
    Measurable (fun x : CompletePublicTable.ForwardRow p ×
        (Fin n → TimeControl p) × ExtendedPrivateCoordinates p =>
      generatedPastFromInspectedGenerators n r hr x.1 x.2.1 x.2.2) := by
  have hforward : Measurable (fun x : CompletePublicTable.ForwardRow p ×
      (Fin n → TimeControl p) × ExtendedPrivateCoordinates p => x.1) := measurable_fst
  have hcontrols : Measurable (fun x : CompletePublicTable.ForwardRow p ×
      (Fin n → TimeControl p) × ExtendedPrivateCoordinates p => x.2.1) :=
    measurable_fst.comp measurable_snd
  have hprivate : Measurable (fun x : CompletePublicTable.ForwardRow p ×
      (Fin n → TimeControl p) × ExtendedPrivateCoordinates p => x.2.2) :=
    measurable_snd.comp measurable_snd
  have hpublic : Measurable (fun x : CompletePublicTable.ForwardRow p ×
      (Fin n → TimeControl p) × ExtendedPrivateCoordinates p =>
        (fun q : CompleteRowStoppingLaw.PastIndex p
            (GeneratedBootstrapRoundLaw.cutoff p r) =>
          (fun u => x.1 u q.1,
            x.2.1 ⟨q.1.val, by
              have hq : q.1.val < r.val := by
                simpa only [GeneratedBootstrapRoundLaw.cutoff] using q.2
              omega
            ⟩))) := by
    apply measurable_pi_iff.mpr
    intro q
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro u
      exact (measurable_pi_apply q.1).comp ((measurable_pi_apply u).comp hforward)
    · exact (measurable_pi_apply ⟨q.1.val, by
          have hq : q.1.val < r.val := by
            simpa only [GeneratedBootstrapRoundLaw.cutoff] using q.2
          omega
        ⟩).comp hcontrols
  have hprivatePast : Measurable (fun x : CompletePublicTable.ForwardRow p ×
      (Fin n → TimeControl p) × ExtendedPrivateCoordinates p =>
        (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r x.2.2).1) :=
    (measurable_fst.comp
      (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r).measurable).comp hprivate
  exact hpublic.prodMk hprivatePast

private theorem generatedPast_eq_factor (n : ℕ) (hn : n ≤ p.T)
    (r : Fin p.T) (hr : r.val ≤ n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      generatedPastFromInspectedGenerators n r hr
        (ReferenceSourceOwnHistoryContainment.selectedForwardRow z)
        (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z) z.2 := by
  apply Prod.ext
  · funext q
    apply Prod.ext
    · funext u
      rfl
    · rfl
  · rfl

private theorem generatedPast_eq_from_inspectedGenerators
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val ≤ n)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (hforward : ReferenceSourceOwnHistoryContainment.selectedForwardRow z =
      ReferenceSourceOwnHistoryContainment.selectedForwardRow z')
    (hcontrols : ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z =
      ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z')
    (hprivate : z.2 = z'.2) :
    GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2) := by
  rw [generatedPast_eq_factor n hn r hr z,
    generatedPast_eq_factor n hn r hr z', hforward, hcontrols, hprivate]

/-- The original strict-past round law is measurable in the exact inspected
history field `ReferenceSourceOwnHistoryContainment.inspectedHistorySpace`. -/
theorem generatedPast_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (r : Fin p.T) (hr : r.val ≤ n) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2)) := by
  let K : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  have hforward : Measurable[K]
      (ReferenceSourceOwnHistoryContainment.selectedForwardRow (p := p)) :=
    ReferenceInspectedPastRoundObservations.selectedForwardRow_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hcontrols : Measurable[K]
      (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn) :=
    ReferenceInspectedPastRoundObservations.selectedControlPrefix_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hprivate : Measurable[K]
      (Prod.snd : BootstrapPrivateRoundStreams.SourceInput p → _) :=
    ReferenceInspectedPastRoundObservations.privateCoordinates_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hinputs : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (ReferenceSourceOwnHistoryContainment.selectedForwardRow z,
        (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z, z.2))) :=
    hforward.prodMk (hcontrols.prodMk hprivate)
  have hfactor :=
    (measurable_generatedPastFromInspectedGenerators n r hr).comp hinputs
  have heq : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2)) =
    (fun z => generatedPastFromInspectedGenerators n r hr
      (ReferenceSourceOwnHistoryContainment.selectedForwardRow z)
      (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z) z.2) := by
    funext z
    exact generatedPast_eq_factor n hn r hr z
  rw [heq]
  exact hfactor

/-- The same exact field makes the pair of varying published IDs and the
original generated strict-past round law measurable. -/
theorem generatedPast_with_ids_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (r : Fin p.T) (hr : r.val ≤ n) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) := by
  let K : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  have hids : Measurable[K]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => z.1.1) :=
    ReferenceInspectedPastRoundObservations.ids_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  exact hids.prodMk
    (generatedPast_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn r hr)

/-- The four literal generators of the inspected field determine the complete
proof-erased prelaunch prefix observation, including every continuous saved
buffer carried by its active state. -/
theorem prefix_eq_of_inspected_generators
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (r : Fin p.T) (hr : r.val ≤ n) (i : Fin (p.m - 1))
    (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (hids : z.1.1 = z'.1.1)
    (hforward : ReferenceSourceOwnHistoryContainment.selectedForwardRow z =
      ReferenceSourceOwnHistoryContainment.selectedForwardRow z')
    (hprivate : (Prod.snd : BootstrapPrivateRoundStreams.SourceInput p → _) z =
      (Prod.snd : BootstrapPrivateRoundStreams.SourceInput p → _) z')
    (hcontrols : ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z =
      ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z') :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation
        rate rewards C_star C_h z i r =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation
        rate rewards C_star C_h z' i r := by
  apply ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i r hids
  exact generatedPast_eq_from_inspectedGenerators n hn r hr z z'
    hforward hcontrols hprivate

end Bandits.Support.ReferencePrelaunchInspectedSourcePast
