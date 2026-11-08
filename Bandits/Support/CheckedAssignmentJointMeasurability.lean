/-
Copyright (c) 2026 The Bandits Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CheckedAssignmentSample
public import Bandits.Support.CheckedAssignmentOrientation
public import Bandits.Support.CheckedPrefixJointMeasurability

/-!
# Joint measurability of the complete checked assignment

This module composes the accepted arbitrary-raw-mass prefix measurability with
the accepted raw-anchor orientation measurability. The complete assignment
uses the original prefix coordinates and the original `Fin.last` orientation
coordinate, retaining the prefix-first short-circuit and every finite failure
output.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,66-77`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-22`,
`sources/zip4/manuscript/06_interruptions.tex:30-35`, and
`sources/zip4/manuscript/appendix_b_communication.tex:34-44`.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.CheckedAssignmentOrientation
open Bandits.Support.CheckedPrefixJointMeasurability
open Bandits.Support.PrefixSamplerLaw
open Bandits.Support.PrefixSetSampler

namespace Bandits.Support.CheckedAssignmentJointMeasurability

local instance setCarrierMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (PrefixSetSampler.SetCarrier p.K p.m) := ⊤

local instance setCarrierDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (PrefixSetSampler.SetCarrier p.K p.m) :=
  ⟨fun _ => trivial⟩

attribute [local instance]
  CheckedPrefixJointMeasurability.instMeasurableSpaceResult

local instance prefixResultDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (CheckedPrefixSampler.Result p.K p.m) :=
  ⟨fun _ => trivial⟩

attribute [local instance] CheckedAssignmentSample.resultMeasurableSpace

local instance assignmentResultDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (CheckedAssignmentSample.Result p) :=
  ⟨fun _ => trivial⟩

local instance optionSlowSetMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace
      (Option (CanonicalOrientedSetLaw.SlowSet p.K p.m)) := ⊤

local instance optionSlowSetDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace
      (Option (CanonicalOrientedSetLaw.SlowSet p.K p.m)) :=
  ⟨fun _ => trivial⟩

/-- Arbitrary real masses on the existing finite supported-set carrier, with
the ordinary product Borel sigma algebra on the real coordinates. -/
abbrev RawMass (p : ConstructorDimensions.Parameters) :=
  CheckedPrefixJointMeasurability.RawMass p.K p.m

/-- The raw real anchor vector with its ordinary product Borel sigma algebra. -/
abbrev Anchor (p : ConstructorDimensions.Parameters) := Fin p.K → ℝ

/-- The original full `K + 1` half-open scalar vector. -/
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  CheckedAssignmentSample.AssignmentVector p

/-- Joint input with the ordinary product Borel sigma algebra on raw masses,
anchors, and all `K + 1` original scalar coordinates. -/
abbrev JointInput (p : ConstructorDimensions.Parameters) :=
  (RawMass p × Anchor p) × AssignmentVector p

/-- The existing complete checked assignment operation is jointly Borel
measurable in arbitrary real masses, arbitrary real anchors, and the full
original assignment vector. Prefix failures short-circuit before orientation;
successful prefixes retain orientation failures and supported `(S,j)` outputs.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,66-77`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-22`,
`sources/zip4/manuscript/06_interruptions.tex:30-35`, and
`sources/zip4/manuscript/appendix_b_communication.tex:34-44`. -/
theorem measurable_checkedAssignmentSample_joint
    (p : ConstructorDimensions.Parameters) :
    Measurable (fun z : JointInput p =>
      CheckedAssignmentSample.checkedAssignmentSample p z.1.1 z.1.2 z.2) := by
  classical
  let prefixAt : JointInput p → CheckedPrefixSampler.Result p.K p.m :=
    (fun q => CheckedPrefixSampler.checkedSample q.1 q.2) ∘
      (fun z => (z.1.1, PrefixSamplerLaw.prefixValues z.2))
  let rawAt : JointInput p → CheckedAssignmentOrientation.RawInput p :=
    fun z => (z.1.2, z.2 (Fin.last p.K))
  have hpref : Measurable prefixAt := by
    exact CheckedPrefixJointMeasurability.measurable_checkedSample_joint.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((PrefixSamplerLaw.measurable_prefixValues p.K).comp measurable_snd))
  have hraw : Measurable rawAt := by
    exact (measurable_snd.comp measurable_fst).prodMk
      ((measurable_pi_apply (Fin.last p.K)).comp measurable_snd)
  apply measurable_to_countable'
  intro y
  cases y with
  | prefixFailure arm reason =>
      have hpre :
          (fun z : JointInput p =>
            CheckedAssignmentSample.checkedAssignmentSample p
              z.1.1 z.1.2 z.2) ⁻¹'
              {CheckedAssignmentSample.Result.prefixFailure arm reason} =
            prefixAt ⁻¹' {CheckedPrefixSampler.Result.failed arm reason} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample z.1.1
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm' reason' =>
            simp [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, hprefix]
        | sampled S' =>
            simp only [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, Function.comp_apply,
              hprefix]
            change CheckedAssignmentSample.finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S'
                z.1.2 (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                p S' z.1.2 (z.2 (Fin.last p.K)) j h) =
                CheckedAssignmentSample.Result.prefixFailure arm reason ↔
              CheckedPrefixSampler.Result.sampled S' =
                CheckedPrefixSampler.Result.failed arm reason
            have hne :=
              (CheckedAssignmentSample.finishOrientation_eq_prefixFailure_iff p S'
                (CheckedAssignmentOrientation.checkedOrientation p S'
                  z.1.2 (z.2 (Fin.last p.K)))
                (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                  p S' z.1.2 (z.2 (Fin.last p.K)) j h) arm reason).mp
            constructor
            · intro heq
              exact False.elim (hne heq)
            · intro heq
              cases heq
      rw [hpre]
      exact hpref (measurableSet_singleton _)
  | orientationFailure S =>
      let orientationAt : CheckedAssignmentOrientation.RawInput p →
          CheckedAssignmentOrientation.Output p.K :=
        fun z => CheckedAssignmentOrientation.checkedOrientation p S z.1 z.2
      have horient :=
        (CheckedAssignmentOrientation.measurable_checkedOrientation p S)
          (measurableSet_singleton CheckedAssignmentOrientation.Output.failure)
      have hpre :
          (fun z : JointInput p =>
            CheckedAssignmentSample.checkedAssignmentSample p
              z.1.1 z.1.2 z.2) ⁻¹'
              {CheckedAssignmentSample.Result.orientationFailure S} =
            (prefixAt ⁻¹' {CheckedPrefixSampler.Result.sampled S}) ∩
              (rawAt ⁻¹' (orientationAt ⁻¹'
                {CheckedAssignmentOrientation.Output.failure})) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample z.1.1
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm reason =>
            simp [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, rawAt, orientationAt, hprefix]
        | sampled S' =>
            simp only [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, rawAt, orientationAt,
              Function.comp_apply, hprefix]
            change CheckedAssignmentSample.finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S'
                z.1.2 (z.2 (Fin.last p.K)))
              (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                p S' z.1.2 (z.2 (Fin.last p.K)) j h) =
                CheckedAssignmentSample.Result.orientationFailure S ↔
              (CheckedPrefixSampler.Result.sampled S' =
                CheckedPrefixSampler.Result.sampled S) ∧
              CheckedAssignmentOrientation.checkedOrientation p S
                z.1.2 (z.2 (Fin.last p.K)) =
                  CheckedAssignmentOrientation.Output.failure
            have hfinish :=
              CheckedAssignmentSample.finishOrientation_eq_orientationFailure_iff
                p S' S
                (CheckedAssignmentOrientation.checkedOrientation p S'
                  z.1.2 (z.2 (Fin.last p.K)))
                (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                  p S' z.1.2 (z.2 (Fin.last p.K)) j h)
            constructor
            · intro heq
              rcases hfinish.mp heq with ⟨hS, horientation⟩
              constructor
              · exact congrArg CheckedPrefixSampler.Result.sampled hS
              · subst S'
                exact horientation
            · rintro ⟨hpre, horientation⟩
              have hS : S' = S := by
                injection hpre with hS
              subst S'
              exact hfinish.mpr ⟨rfl, horientation⟩
      rw [hpre]
      exact (hpref (measurableSet_singleton _)).inter (hraw horient)
  | sampled outcome =>
      let S : PrefixSetSampler.SetCarrier p.K p.m := outcome.1.1
      let j : Fin p.K := outcome.1.2
      let orientationAt : CheckedAssignmentOrientation.RawInput p →
          CheckedAssignmentOrientation.Output p.K :=
        fun z => CheckedAssignmentOrientation.checkedOrientation p S z.1 z.2
      have horient :=
        (CheckedAssignmentOrientation.measurable_checkedOrientation p S)
          (measurableSet_singleton (CheckedAssignmentOrientation.Output.sampled j))
      have hpre :
          (fun z : JointInput p =>
            CheckedAssignmentSample.checkedAssignmentSample p
              z.1.1 z.1.2 z.2) ⁻¹'
              {CheckedAssignmentSample.Result.sampled outcome} =
            (prefixAt ⁻¹' {CheckedPrefixSampler.Result.sampled S}) ∩
              (rawAt ⁻¹' (orientationAt ⁻¹'
                {CheckedAssignmentOrientation.Output.sampled j})) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
        cases hprefix : CheckedPrefixSampler.checkedSample z.1.1
            (PrefixSamplerLaw.prefixValues z.2) with
        | failed arm reason =>
            simp [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, rawAt, orientationAt, hprefix]
        | sampled S' =>
            simp only [CheckedAssignmentSample.checkedAssignmentSample,
              CheckedAssignmentSample.finishPrefix, prefixAt, rawAt, orientationAt,
              Function.comp_apply, hprefix]
            change CheckedAssignmentSample.finishOrientation p S'
              (CheckedAssignmentOrientation.checkedOrientation p S'
                z.1.2 (z.2 (Fin.last p.K)))
              (fun j' h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                p S' z.1.2 (z.2 (Fin.last p.K)) j' h) =
                CheckedAssignmentSample.Result.sampled outcome ↔
              (CheckedPrefixSampler.Result.sampled S' =
                CheckedPrefixSampler.Result.sampled S) ∧
              CheckedAssignmentOrientation.checkedOrientation p S
                z.1.2 (z.2 (Fin.last p.K)) =
                  CheckedAssignmentOrientation.Output.sampled j
            have hfinish :=
              CheckedAssignmentSample.finishOrientation_eq_sampledOutcome_iff p S'
                (CheckedAssignmentOrientation.checkedOrientation p S'
                  z.1.2 (z.2 (Fin.last p.K)))
                (fun j' h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem
                  p S' z.1.2 (z.2 (Fin.last p.K)) j' h) outcome
            constructor
            · intro heq
              rcases hfinish.mp heq with ⟨hS, horientation⟩
              constructor
              · exact congrArg CheckedPrefixSampler.Result.sampled hS
              · subst S'
                exact horientation
            · rintro ⟨hpre, horientation⟩
              have hS : S' = S := by
                injection hpre with hS
              subst S'
              exact hfinish.mpr ⟨rfl, horientation⟩
      rw [hpre]
      exact (hpref (measurableSet_singleton _)).inter (hraw horient)

/-- Arbitrary-base composition of the complete operation. The three component
measurability proofs are separate map inputs, so no measurability premise is
placed on the combined result. -/
theorem measurable_checkedAssignmentSample_comp {X : Type*} [MeasurableSpace X]
    (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment) :
    Measurable (fun x =>
      CheckedAssignmentSample.checkedAssignmentSample p
        (mass x) (anchor x) (assignment x)) := by
  exact (measurable_checkedAssignmentSample_joint p).comp
    ((hmass.prodMk hanchor).prodMk hassignment)

/-- The successful slow-set `Option` projection is measurable on the joint
raw-mass, raw-anchor, and full-vector input. -/
theorem measurable_successfulSlowSet_joint
    (p : ConstructorDimensions.Parameters) :
    Measurable (fun z : JointInput p =>
      CheckedAssignmentSample.successfulSlowSet p
        (CheckedAssignmentSample.checkedAssignmentSample p
          z.1.1 z.1.2 z.2)) := by
  have hmap : Measurable (fun r : CheckedAssignmentSample.Result p =>
      CheckedAssignmentSample.successfulSlowSet p r) := Measurable.of_discrete
  exact hmap.comp (measurable_checkedAssignmentSample_joint p)

/-- Arbitrary-base measurability of the existing successful slow-set
projection. -/
theorem measurable_successfulSlowSet_comp {X : Type*} [MeasurableSpace X]
    (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment) :
    Measurable (fun x =>
      CheckedAssignmentSample.successfulSlowSet p
        (CheckedAssignmentSample.checkedAssignmentSample p
          (mass x) (anchor x) (assignment x))) := by
  exact (measurable_successfulSlowSet_joint p).comp
    ((hmass.prodMk hanchor).prodMk hassignment)

/-- Every exact output event of the complete checked assignment is measurable
under arbitrary measurable mass, anchor, and full assignment-vector maps.
Instantiating `output` with any failure constructor or successful supported
`(S,j)` gives that exact event. -/
theorem measurableSet_checkedAssignmentSample_eq_comp {X : Type*}
    [MeasurableSpace X] (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment)
    (output : CheckedAssignmentSample.Result p) :
    MeasurableSet {x |
      CheckedAssignmentSample.checkedAssignmentSample p
        (mass x) (anchor x) (assignment x) = output} := by
  exact (measurableSet_singleton output).preimage
    (measurable_checkedAssignmentSample_comp p mass anchor assignment
      hmass hanchor hassignment)

/-- Exact prefix-failure events retain the first failed arm and reason. -/
theorem measurableSet_prefixFailure_comp {X : Type*} [MeasurableSpace X]
    (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment)
    (arm : Option (Fin p.K))
    (reason : CheckedPrefixSampler.FailureReason) :
    MeasurableSet {x |
      CheckedAssignmentSample.checkedAssignmentSample p
        (mass x) (anchor x) (assignment x) =
          CheckedAssignmentSample.Result.prefixFailure arm reason} :=
  measurableSet_checkedAssignmentSample_eq_comp p mass anchor assignment
    hmass hanchor hassignment _

/-- Exact orientation-failure events retain the prefix set that succeeded. -/
theorem measurableSet_orientationFailure_comp {X : Type*}
    [MeasurableSpace X] (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment)
    (S : PrefixSetSampler.SetCarrier p.K p.m) :
    MeasurableSet {x |
      CheckedAssignmentSample.checkedAssignmentSample p
        (mass x) (anchor x) (assignment x) =
          CheckedAssignmentSample.Result.orientationFailure S} :=
  measurableSet_checkedAssignmentSample_eq_comp p mass anchor assignment
    hmass hanchor hassignment _

/-- Exact successful assignment events retain the full supported `(S,j)`
outcome. -/
theorem measurableSet_sampled_comp {X : Type*} [MeasurableSpace X]
    (p : ConstructorDimensions.Parameters)
    (mass : X → RawMass p) (anchor : X → Anchor p)
    (assignment : X → AssignmentVector p)
    (hmass : Measurable mass) (hanchor : Measurable anchor)
    (hassignment : Measurable assignment)
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m) :
    MeasurableSet {x |
      CheckedAssignmentSample.checkedAssignmentSample p
        (mass x) (anchor x) (assignment x) =
          CheckedAssignmentSample.Result.sampled outcome} :=
  measurableSet_checkedAssignmentSample_eq_comp p mass anchor assignment
    hmass hanchor hassignment _

end Bandits.Support.CheckedAssignmentJointMeasurability
