/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchInspectedSourcePast
public import Bandits.Support.ReferenceGeneratedPrelaunchDownPastFactor

/-!
# Actual prelaunch prefix codes in the inspected history

Sources: sources/zip4/manuscript/07_public_setup.tex:127-164,
sources/zip4/manuscript/05_binary_transport.tex:20-55, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157.

The exact existing three-branch prefix code, bank, tests, and birth are
adapted through the original generated strict past and varying public IDs.
The finite dated family retains the dependent code space at each offset and
decodes to the original complete observations, including their continuous
saved state and buffers. The completion values below are fixed proof witnesses
only; the exported statements use the original source input and inspected
history field.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePrelaunchInspectedPrefixCode

open MeasureTheory
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceInitializationMeasurability
open PrivateSourceStreams
open scoped Classical

attribute [local instance 3000] ReferenceInitializationMeasurability.listCountableMeasurableSpace
  ReferenceInitializationMeasurability.listCountableMeasurableSingletonClass
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace
  ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass

local instance sumMeasurableSingletonClass (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inl_image (β := β)
    | inr x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inr_image (α := α)

variable {p : ConstructorDimensions.Parameters}

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local instance prefixCodesAtEachIndexMeasurableSpace (n : ℕ) (j : Fin n) :
    MeasurableSpace
      (Fin (p.m - 1) →
        ReferenceGeneratedPrelaunchDownPastFactor.PrefixCode p rate j.val) :=
  MeasurableSpace.pi

local instance prefixCodeFamilyMeasurableSpace (n : ℕ) :
    MeasurableSpace
      ((j : Fin n) → Fin (p.m - 1) →
        ReferenceGeneratedPrelaunchDownPastFactor.PrefixCode p rate j.val) :=
  MeasurableSpace.pi

/-- The actual original prefix code is Borel in exactly the inspected field.
The code still contains each source branch and all original saved coordinates.
-/
theorem sourcePrefixCode_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val ≤ n)
    (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
          rate rewards C_star C_h z i r) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  let scalar0 : PrivateSourceStreams.Scalar := ⟨0, le_rfl, zero_lt_one⟩
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))
  let row0 : CompletePublicTable.CompleteRow p :=
    (fun _ _ => false, fun _ => control0)
  let rows0 : CompletePublicTable.CompleteRows p := fun _ => row0
  let private0 : PrivateSourceStreams.PrivateCoordinates p :=
    (fun _ => fun _ => (scalar0, (scalar0, scalar0)), scalar0)
  let e0 : GeneratedBootstrapRoundLaw.Coordinates p :=
    (row0, (private0, (fun _ => scalar0, fun _ => scalar0)))
  have hpast : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (z.1.1, GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    ReferencePrelaunchInspectedSourcePast.generatedPast_with_ids_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn r hr
  have hfactor : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.prefixCodeFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    (ReferenceGeneratedPrelaunchDownPastFactor.measurable_prefixCodeFromPast
      rate rewards C_star C_h i r rows0 e0).comp hpast
  have hrec : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.prefixCodeFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) =
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
          rate rewards C_star C_h z i r) := by
    funext z
    exact ReferenceGeneratedPrelaunchDownPastFactor.prefixCodeFromPast_reconstruct
      rate rewards C_star C_h i r rows0 e0 z
  rw [← hrec]
  exact hfactor

/-- The original DOWN batch bank is Borel in the exact inspected history. -/
theorem sourceBankCode_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val ≤ n)
    (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourceBankCode
          rate rewards C_star C_h z i r) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  let scalar0 : PrivateSourceStreams.Scalar := ⟨0, le_rfl, zero_lt_one⟩
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))
  let row0 : CompletePublicTable.CompleteRow p :=
    (fun _ _ => false, fun _ => control0)
  let rows0 : CompletePublicTable.CompleteRows p := fun _ => row0
  let private0 : PrivateSourceStreams.PrivateCoordinates p :=
    (fun _ => fun _ => (scalar0, (scalar0, scalar0)), scalar0)
  let e0 : GeneratedBootstrapRoundLaw.Coordinates p :=
    (row0, (private0, (fun _ => scalar0, fun _ => scalar0)))
  have hpast : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (z.1.1, GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    ReferencePrelaunchInspectedSourcePast.generatedPast_with_ids_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn r hr
  have hfactor : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.bankFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    (ReferenceGeneratedPrelaunchDownPastFactor.measurable_bankFromPast
      rate rewards C_star C_h i r rows0 e0).comp hpast
  have hrec : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.bankFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) =
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourceBankCode
          rate rewards C_star C_h z i r) := by
    funext z
    exact ReferenceGeneratedPrelaunchDownPastFactor.bankFromPast_reconstruct
      rate rewards C_star C_h i r rows0 e0 z
  rw [← hrec]
  exact hfactor

/-- The original strict-prefix DOWN tests are Borel in the exact inspected
history, with their dated observations and sent words retained. -/
theorem sourceTestsCode_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val ≤ n)
    (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourceTestsCode
          rate rewards C_star C_h z i r) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  let scalar0 : PrivateSourceStreams.Scalar := ⟨0, le_rfl, zero_lt_one⟩
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))
  let row0 : CompletePublicTable.CompleteRow p :=
    (fun _ _ => false, fun _ => control0)
  let rows0 : CompletePublicTable.CompleteRows p := fun _ => row0
  let private0 : PrivateSourceStreams.PrivateCoordinates p :=
    (fun _ => fun _ => (scalar0, (scalar0, scalar0)), scalar0)
  let e0 : GeneratedBootstrapRoundLaw.Coordinates p :=
    (row0, (private0, (fun _ => scalar0, fun _ => scalar0)))
  have hpast : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (z.1.1, GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    ReferencePrelaunchInspectedSourcePast.generatedPast_with_ids_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn r hr
  have hfactor : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.testsFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    (ReferenceGeneratedPrelaunchDownPastFactor.measurable_testsFromPast
      rate rewards C_star C_h i r rows0 e0).comp hpast
  have hrec : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.testsFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) =
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.sourceTestsCode
          rate rewards C_star C_h z i r) := by
    funext z
    exact ReferenceGeneratedPrelaunchDownPastFactor.testsFromPast_reconstruct
      rate rewards C_star C_h i r rows0 e0 z
  rw [← hrec]
  exact hfactor

/-- The actual source-computed prelaunch prefix birth is Borel in the exact
inspected history, including absent and stopped branches. -/
theorem source_prelaunch_down_prefix_birth_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val ≤ n)
    (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
          rate rewards C_star C_h z i r) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  let scalar0 : PrivateSourceStreams.Scalar := ⟨0, le_rfl, zero_lt_one⟩
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))
  let row0 : CompletePublicTable.CompleteRow p :=
    (fun _ _ => false, fun _ => control0)
  let rows0 : CompletePublicTable.CompleteRows p := fun _ => row0
  let private0 : PrivateSourceStreams.PrivateCoordinates p :=
    (fun _ => fun _ => (scalar0, (scalar0, scalar0)), scalar0)
  let e0 : GeneratedBootstrapRoundLaw.Coordinates p :=
    (row0, (private0, (fun _ => scalar0, fun _ => scalar0)))
  have hpast : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (z.1.1, GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    ReferencePrelaunchInspectedSourcePast.generatedPast_with_ids_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn r hr
  have hfactor : Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.birthFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) :=
    (ReferenceGeneratedPrelaunchDownPastFactor.measurable_birthFromPast
      rate rewards C_star C_h i r rows0 e0).comp hpast
  have hrec : (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.birthFromPast
        rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2))) =
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
          rate rewards C_star C_h z i r) := by
    funext z
    exact ReferenceGeneratedPrelaunchDownPastFactor.birthFromPast_reconstruct
      rate rewards C_star C_h i r rows0 e0 z
  rw [← hrec]
  exact hfactor

/-- The dated original prefix codes, with the genuinely dependent code space
at each calendar offset. The index j denotes the prefix before round j. -/
def sourcePrefixCodeFamily (n : ℕ) (hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (j : Fin n) → Fin (p.m - 1) →
      ReferenceGeneratedPrelaunchDownPastFactor.PrefixCode p rate j.val :=
  fun j i => ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
    rate rewards C_star C_h z i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩

/-- The whole finite dated family is measurable by the dependent Pi criterion;
the empty family at n = 0 is covered by the same statement. -/
theorem sourcePrefixCodeFamily_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (sourcePrefixCodeFamily rate rewards C_star C_h n hn) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro i
  change Measurable[K] (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
      rate rewards C_star C_h z i
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)
  exact sourcePrefixCode_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ (Nat.le_of_lt j.isLt) i

/-- Lossless reconstruction of the same dated family to the original
proof-erased prefix observation, for every date and follower. -/
theorem decode_sourcePrefixCodeFamily
    (n : ℕ) (hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin n) (i : Fin (p.m - 1)) :
    ReferenceGeneratedPrelaunchDownPastFactor.decodePrefixCode rate i
        (sourcePrefixCodeFamily rate rewards C_star C_h n hn z j i) =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation
        rate rewards C_star C_h z i
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ := by
  change ReferenceGeneratedPrelaunchDownPastFactor.decodePrefixCode rate i
      (ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
        rate rewards C_star C_h z i
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩) = _
  exact ReferenceGeneratedPrelaunchDownPastFactor.decode_sourcePrefixCode
    rate rewards C_star C_h z i
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩

end Bandits.Support.ReferencePrelaunchInspectedPrefixCode
