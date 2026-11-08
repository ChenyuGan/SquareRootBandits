/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAssignmentStepNonRead

import Mathlib.Tactic

/-!
# Assignment coordinates before the first collection invocation

This module defines the deterministic assignment-coordinate patch on the
original source input. The patch retains the original public/private arrays
and changes only the selected row's complete assignment vector on the strict
calendar interval from the end of the first LIVE window to the first actual
collection invocation. It states no source-law or conditional-law claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open Bandits.Support.ReferenceActivePhysicalStep (RateInput)
open Bandits.Support.ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open Bandits.Support.ReferenceFirstLiveConfirmationHistory (firstLiveWindow)
open Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport (firstCallBoundary)
open Bandits.Support.CheckedAssignmentSample (AssignmentVector)
open Bandits.Support.LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAssignmentNonRead

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p

/-- Replace every selected-row assignment coordinate in the unused block of
the original first physical collection. The complete non-assignment channel,
other controls, source arrays, IDs, and private coordinates are retained. -/
def firstCollectionAssignmentPatch (z : S) (v : Fin p.T → AssignmentVector p) : S :=
  let q := selectedRowIndex p z
  let row := z.1.2 q
  let start := physicalStart rate z rewards C_star C_h
  let records := completeSuffixRecords rate z rewards C_star C_h
  let beginAt := start + (firstLiveWindow records).length
  let stop := firstCallBoundary rate rewards C_star C_h z
  let split := controlAssignmentSplitEquiv p
  ((z.1.1, Function.update z.1.2 q
    (row.1, fun r =>
      if beginAt ≤ r.val ∧ r.val < stop then
        split.symm (v r, (split (row.2 r)).2)
      else row.2 r)), z.2)

/-- The selected row's complete split is changed by exactly the requested
coordinate replacement; its second component remains the original pair of
all non-assignment scalars and all affine channels. -/
theorem firstCollectionAssignmentPatch_split (z : S)
    (v : Fin p.T → AssignmentVector p) (r : Fin p.T) :
    controlAssignmentSplitEquiv p
      (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
        (selectedRowIndex p z)).2 r) =
      if physicalStart rate z rewards C_star C_h +
            (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
          r.val < firstCallBoundary rate rewards C_star C_h z then
        (v r, (controlAssignmentSplitEquiv p
          ((z.1.2 (selectedRowIndex p z)).2 r)).2)
      else controlAssignmentSplitEquiv p ((z.1.2 (selectedRowIndex p z)).2 r) := by
  simp only [firstCollectionAssignmentPatch, Function.update_self]
  split_ifs <;> simp

/-- On the patch interval all K+1 assignment coordinates are exposed as the
original complete assignment vector. -/
theorem firstCollectionAssignmentPatch_assignment_on (z : S)
    (v : Fin p.T → AssignmentVector p) (r : Fin p.T)
    (hr : physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
        r.val < firstCallBoundary rate rewards C_star C_h z) :
    (controlAssignmentSplitEquiv p
      (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
        (selectedRowIndex p z)).2 r)).1 = v r := by
  rw [firstCollectionAssignmentPatch_split rate rewards C_star C_h z v r]
  simp [hr]

/-- The complete K+1 assignment vector is also unchanged outside the patch
interval. -/
theorem firstCollectionAssignmentPatch_assignment_outside (z : S)
    (v : Fin p.T → AssignmentVector p) (r : Fin p.T)
    (hr : ¬ (physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
        r.val < firstCallBoundary rate rewards C_star C_h z)) :
    (controlAssignmentSplitEquiv p
      (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
        (selectedRowIndex p z)).2 r)).1 =
      (controlAssignmentSplitEquiv p ((z.1.2 (selectedRowIndex p z)).2 r)).1 := by
  rw [firstCollectionAssignmentPatch_split rate rewards C_star C_h z v r]
  simp [hr]

/-- Outside the patch interval the complete selected control is unchanged. -/
theorem firstCollectionAssignmentPatch_control_outside (z : S)
    (v : Fin p.T → AssignmentVector p) (r : Fin p.T)
    (hr : ¬ (physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
        r.val < firstCallBoundary rate rewards C_star C_h z)) :
    ((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
      (selectedRowIndex p z)).2 r = (z.1.2 (selectedRowIndex p z)).2 r := by
  simp only [firstCollectionAssignmentPatch, Function.update_self]
  simp [hr]

/-- The IDs, private coordinates (including J), and selected index stay the
original source values. -/
theorem firstCollectionAssignmentPatch_private_and_id (z : S)
    (v : Fin p.T → AssignmentVector p) :
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.1 = z.1.1 ∧
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v).2 = z.2 ∧
    selectedRowIndex p (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      selectedRowIndex p z := by
  simp [firstCollectionAssignmentPatch, selectedRowIndex]

/-- Every unselected complete row is retained literally. -/
theorem firstCollectionAssignmentPatch_other_rows (z : S)
    (v : Fin p.T → AssignmentVector p) (q : Fin (M p))
    (hq : q ≠ selectedRowIndex p z) :
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2 q = z.1.2 q := by
  simp [firstCollectionAssignmentPatch, Function.update_of_ne hq]

/-- The selected row's original forward-bit array is retained literally. -/
theorem firstCollectionAssignmentPatch_forwards (z : S)
    (v : Fin p.T → AssignmentVector p) :
    ((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
      (selectedRowIndex p z)).1 = (z.1.2 (selectedRowIndex p z)).1 := by
  simp [firstCollectionAssignmentPatch]

/-- All non-assignment scalars and affine channels in the selected row remain
exactly the original split remainder at every calendar date. -/
theorem firstCollectionAssignmentPatch_remainder (z : S)
    (v : Fin p.T → AssignmentVector p) (r : Fin p.T) :
    (controlAssignmentSplitEquiv p
      (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
        (selectedRowIndex p z)).2 r)).2 =
      (controlAssignmentSplitEquiv p
        ((z.1.2 (selectedRowIndex p z)).2 r)).2 := by
  rw [firstCollectionAssignmentPatch_split rate rewards C_star C_h z v r]
  split_ifs <;> rfl

/-- The complete literal retention and replacement interface for the patch. -/
theorem firstCollectionAssignmentPatch_exact (z : S)
    (v : Fin p.T → AssignmentVector p) :
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.1 = z.1.1 ∧
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v).2 = z.2 ∧
    selectedRowIndex p (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      selectedRowIndex p z ∧
    ((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
      (selectedRowIndex p z)).1 = (z.1.2 (selectedRowIndex p z)).1 ∧
    (∀ q, q ≠ selectedRowIndex p z →
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2 q = z.1.2 q) ∧
    (∀ r, physicalStart rate z rewards C_star C_h +
        (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
          r.val < firstCallBoundary rate rewards C_star C_h z →
      (controlAssignmentSplitEquiv p
        (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
          (selectedRowIndex p z)).2 r)).1 = v r) ∧
    (∀ r, (controlAssignmentSplitEquiv p
        (((firstCollectionAssignmentPatch rate rewards C_star C_h z v).1.2
          (selectedRowIndex p z)).2 r)).2 =
      (controlAssignmentSplitEquiv p ((z.1.2 (selectedRowIndex p z)).2 r)).2) := by
  refine ⟨(firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).1,
    (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.1,
    (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.2,
    firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v,
    ?_, ?_, firstCollectionAssignmentPatch_remainder rate rewards C_star C_h z v⟩
  · intro q hq
    exact firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
  · intro r hr
    exact firstCollectionAssignmentPatch_assignment_on rate rewards C_star C_h z v r hr

/-- Truncating the patched source before the assignment block gives the
literal original prefix, with the ordinary supplied suffix control. -/
theorem sourcePrefix_eq_of_before_assignment_block
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : S) (v : Fin p.T → AssignmentVector p)
    (hn : n ≤ physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  have hselected : selectedRowIndex p z' = selectedRowIndex p z :=
    (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.2
  apply Prod.ext
  · apply Prod.ext
    · calc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.1 = z'.1.1 :=
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids control0 n z'
        _ = z.1.1 := (firstCollectionAssignmentPatch_private_and_id
          rate rewards C_star C_h z v).1
        _ = (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).1.1 :=
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids control0 n z).symm
    · funext q
      by_cases hq : q = selectedRowIndex p z
      · subst q
        apply Prod.ext
        · have hleft := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward
            control0 n z' (selectedRowIndex p z')
          have hleft' :
              ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.2
                  (selectedRowIndex p z)).1 =
                (z'.1.2 (selectedRowIndex p z)).1 := by
            simpa only [hselected] using hleft
          have hright := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward
            control0 n z (selectedRowIndex p z)
          calc
            ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.2
                (selectedRowIndex p z)).1 = (z'.1.2 (selectedRowIndex p z)).1 := hleft'
            _ = (z.1.2 (selectedRowIndex p z)).1 :=
              firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
            _ = ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).1.2
                (selectedRowIndex p z)).1 := hright.symm
        · funext r
          have hleft := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
            control0 n z' r
          have hleft' :
              ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.2
                  (selectedRowIndex p z)).2 r =
                if r.val < n then (z'.1.2 (selectedRowIndex p z)).2 r else control0 := by
            simpa only [hselected] using hleft
          have hright := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
            control0 n z r
          rw [hleft', hright]
          by_cases hr : r.val < n
          · have hcontrol := firstCollectionAssignmentPatch_control_outside
              rate rewards C_star C_h z v r (by omega)
            have hcontrol' : (z'.1.2 (selectedRowIndex p z)).2 r =
                (z.1.2 (selectedRowIndex p z)).2 r := by
              simpa only [z'] using hcontrol
            simp [hr, hcontrol']
          · simp [hr]
      · have hq' : q ≠ selectedRowIndex p z' := by
          simpa [hselected] using hq
        change (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.2 q =
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).1.2 q
        calc
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').1.2 q =
              z'.1.2 q :=
            ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 n z' q hq'
          _ = z.1.2 q :=
            firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
          _ = (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).1.2 q :=
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 n z q hq).symm
  · calc
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z').2 = z'.2 :=
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_private control0 n z'
      _ = z.2 := (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.1
      _ = (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z).2 :=
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_private control0 n z).symm

/-- The original incoming physical state is unchanged through the end of the
first LIVE window. This uses the public strict-prefix readout identity; the
assignment block begins at this boundary. -/
theorem incoming_eq_through_first_live_block
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : S) (v : Fin p.T → AssignmentVector p)
    (ht : t.val ≤ physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := by
  have hprefix := sourcePrefix_eq_of_before_assignment_block rate rewards C_star C_h
    control0 t.val z v ht
  calc
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (firstCollectionAssignmentPatch rate rewards C_star C_h z v)) :=
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t (firstCollectionAssignmentPatch rate rewards C_star C_h z v)
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
      congrArg (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) hprefix
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z :=
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t z).symm

/-- The equality above is a lossless state-code equality. This corollary
recovers equality of the actual optional incoming states themselves, retaining
absence on either side rather than inserting a default state. -/
theorem actualIncomingState_eq_through_first_live_block
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : S) (v : Fin p.T → AssignmentVector p)
    (ht : t.val ≤ physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).map
        (fun record => record.input.state) =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        (fun record => record.input.state) := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  have hcode := incoming_eq_through_first_live_block rate rewards C_star C_h
    control0 t z v ht
  have hdecode (source : S) :
      Option.map ReferenceActivePhysicalStepMeasurability.decodeState
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t source) =
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source).map
          (fun record => record.input.state) := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming, Option.map_map]
    congr 1
    funext record
    exact ReferenceActivePhysicalStepMeasurability.decodeState_encodeState record.input.state
  calc
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z').map
        (fun record => record.input.state) =
      Option.map ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z') :=
      (hdecode z').symm
    _ = Option.map ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) :=
      congrArg (Option.map ReferenceActivePhysicalStepMeasurability.decodeState) hcode
    _ = (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        (fun record => record.input.state) := hdecode z

/-- The patch leaves the generated initialization boundary fixed. If the
initialization is exhausted, its physical start is `T` and the patch interval
is empty. On a launched source, the patch is a selected-control suffix update
beginning at the original physical start, so the public initialization
locality theorem retains the exact launch. -/
theorem firstCollectionAssignmentPatch_physicalStart
    (z : S) (v : Fin p.T → AssignmentVector p) :
    physicalStart rate (firstCollectionAssignmentPatch rate rewards C_star C_h z v)
        rewards C_star C_h = physicalStart rate z rewards C_star C_h := by
  let s := physicalStart rate z rewards C_star C_h
  by_cases hsT : s = p.T
  · have hpatch : firstCollectionAssignmentPatch rate rewards C_star C_h z v = z := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext q
          by_cases hq : q = selectedRowIndex p z
          · subst q
            apply Prod.ext
            · exact firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
            · funext r
              have hr : ¬ (s + (firstLiveWindow
                  (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
                  r.val < firstCallBoundary rate rewards C_star C_h z) := by
                rw [hsT]
                omega
              exact firstCollectionAssignmentPatch_control_outside
                rate rewards C_star C_h z v r (by simpa [s] using hr)
          · exact firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
      · exact (firstCollectionAssignmentPatch_private_and_id
          rate rewards C_star C_h z v).2.1
    rw [hpatch]
  · have hslt : s < p.T := by
      have hle := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
      omega
    have hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      cases hopt : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing with
      | none =>
          have hnone := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
            rate z rewards C_star C_h).2 hopt
          have hT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
            rate z rewards C_star C_h hnone
          dsimp [s] at hslt
          omega
      | some crossing => simp
    let t : Fin p.T := ⟨s, hslt⟩
    let patched := firstCollectionAssignmentPatch rate rewards C_star C_h z v
    let suffix : Fin p.T → Bandits.Support.ContinuousLearningRows.TimeControl p :=
      fun r => (patched.1.2 (selectedRowIndex p z)).2 r
    have hsource : patched = ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z t suffix := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext q
          by_cases hq : q = selectedRowIndex p z
          · subst q
            apply Prod.ext
            · calc
                (patched.1.2 (selectedRowIndex p z)).1 =
                    (z.1.2 (selectedRowIndex p z)).1 := by
                  simpa only [patched] using
                    firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
                _ = ((ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
                    z t suffix).1.2 (selectedRowIndex p z)).1 :=
                  (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
                    z t suffix).symm
            · funext r
              by_cases hr : r.val < s
              · have hout : ¬ (s + (firstLiveWindow
                    (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
                    r.val < firstCallBoundary rate rewards C_star C_h z) := by omega
                rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
                  z t r suffix (by simpa [t] using hr)]
                exact firstCollectionAssignmentPatch_control_outside
                  rate rewards C_star C_h z v r (by simpa [s] using hout)
              · simp only [suffix]
                rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
                  z t r suffix (by simpa [t] using (Nat.le_of_not_lt hr))]
          · calc
              patched.1.2 q = z.1.2 q := by
                simpa only [patched] using
                  firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
              _ = (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
                  z t suffix).1.2 q :=
                (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
                  z t suffix q hq).symm
      · calc
          patched.2 = z.2 := by
            simpa only [patched] using
              (firstCollectionAssignmentPatch_private_and_id
                rate rewards C_star C_h z v).2.1
          _ = (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
              z t suffix).2 :=
            (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_private
              z t suffix).symm
    have hlaunch := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      (rate := rate) rewards C_star C_h (selectedRowIndex p z) t s (by rfl) z rfl suffix
      hcross (by rfl)
    have hstart := hlaunch.2.2.1
    have hstart' : physicalStart rate patched rewards C_star C_h =
        physicalStart rate z rewards C_star C_h := by
      calc
        physicalStart rate patched rewards C_star C_h =
            physicalStart rate
              (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix)
              rewards C_star C_h := congrArg
                (fun source : S => physicalStart rate source rewards C_star C_h) hsource
        _ = physicalStart rate z rewards C_star C_h := hstart
    simpa only [patched] using hstart'

/-- The corrected initialization launch, including its full private state, is
retained by the deterministic patch. -/
theorem firstCollectionAssignmentPatch_correctedLaunch
    (z : S) (v : Fin p.T → AssignmentVector p) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h := by
  let s := physicalStart rate z rewards C_star C_h
  by_cases hsT : s = p.T
  · have hpatch : firstCollectionAssignmentPatch rate rewards C_star C_h z v = z := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext q
          by_cases hq : q = selectedRowIndex p z
          · subst q
            apply Prod.ext
            · exact firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
            · funext r
              have hr : ¬ (s + (firstLiveWindow
                  (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
                  r.val < firstCallBoundary rate rewards C_star C_h z) := by
                rw [hsT]
                omega
              exact firstCollectionAssignmentPatch_control_outside
                rate rewards C_star C_h z v r (by simpa [s] using hr)
          · exact firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
      · exact (firstCollectionAssignmentPatch_private_and_id
          rate rewards C_star C_h z v).2.1
    rw [hpatch]
  · have hslt : s < p.T := by
      have hle := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
      omega
    have hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      cases hopt : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing with
      | none =>
          have hnone := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
            rate z rewards C_star C_h).2 hopt
          have hT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
            rate z rewards C_star C_h hnone
          dsimp [s] at hslt
          omega
      | some crossing => simp
    let t : Fin p.T := ⟨s, hslt⟩
    let patched := firstCollectionAssignmentPatch rate rewards C_star C_h z v
    let suffix : Fin p.T → Bandits.Support.ContinuousLearningRows.TimeControl p :=
      fun r => (patched.1.2 (selectedRowIndex p z)).2 r
    have hsource : patched = ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z t suffix := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext q
          by_cases hq : q = selectedRowIndex p z
          · subst q
            apply Prod.ext
            · calc
                (patched.1.2 (selectedRowIndex p z)).1 =
                    (z.1.2 (selectedRowIndex p z)).1 := by
                  simpa only [patched] using
                    firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
                _ = ((ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
                    z t suffix).1.2 (selectedRowIndex p z)).1 :=
                  (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
                    z t suffix).symm
            · funext r
              by_cases hr : r.val < s
              · have hout : ¬ (s + (firstLiveWindow
                    (completeSuffixRecords rate z rewards C_star C_h)).length ≤ r.val ∧
                    r.val < firstCallBoundary rate rewards C_star C_h z) := by omega
                rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
                  z t r suffix (by simpa [t] using hr)]
                exact firstCollectionAssignmentPatch_control_outside
                  rate rewards C_star C_h z v r (by simpa [s] using hout)
              · simp only [suffix]
                rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
                  z t r suffix (by simpa [t] using (Nat.le_of_not_lt hr))]
          · calc
              patched.1.2 q = z.1.2 q := by
                simpa only [patched] using
                  firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
              _ = (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
                  z t suffix).1.2 q :=
                (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
                  z t suffix q hq).symm
      · calc
          patched.2 = z.2 := by
            simpa only [patched] using
              (firstCollectionAssignmentPatch_private_and_id
                rate rewards C_star C_h z v).2.1
          _ = (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
              z t suffix).2 :=
            (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_private
              z t suffix).symm
    have hlaunch := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      (rate := rate) rewards C_star C_h (selectedRowIndex p z) t s (by rfl) z rfl suffix
      hcross (by rfl)
    calc
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate patched rewards C_star C_h =
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate
            (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix)
              rewards C_star C_h := congrArg
                (fun source : S => ReferenceCorrectedInitializationLaunch.correctedLaunch
                  rate source rewards C_star C_h) hsource
      _ = ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h :=
        hlaunch.2.2.2.symm

/-- The literal physical evidence agrees at every date strictly before the
assignment block. The current whole control and every earlier proposal scalar
are still original there, and the actual incoming state equality supplies the
same accepted step input state. -/
theorem actualRecord_evidence_eq_before_assignment_block
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : S) (v : Fin p.T → AssignmentVector p)
    (ht : t.val < physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  let s := physicalStart rate z rewards C_star C_h
  have hstart := firstCollectionAssignmentPatch_physicalStart
    rate rewards C_star C_h z v
  by_cases hbefore : t.val < s
  · have hleft := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z' (by rw [hstart]; exact hbefore)
    have hright := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z hbefore
    change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z').map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence
    rw [hleft, hright]
  · have hs : s ≤ t.val := Nat.le_of_not_gt hbefore
    have hnotnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h ≠ none := by
      intro hnone
      have hT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hnone
      have htT := t.isLt
      dsimp [s] at hs
      omega
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hnotnone hlaunch)
    | some active =>
        have hlaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate z' rewards C_star C_h = some active := by
          rw [firstCollectionAssignmentPatch_correctedLaunch rate rewards C_star C_h z v]
          exact hlaunch
        have hstart' : physicalStart rate z' rewards C_star C_h = s := by
          simpa only [z', s] using hstart
        have hs' : physicalStart rate z' rewards C_star C_h ≤ t.val := by
          rw [hstart']
          exact hs
        have hmode1 : ReferenceActivePhysicalHorizon.allActiveAtStart active s := by
          rw [← hstart']
          exact ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate z' rewards C_star C_h active hlaunch'
        let r0 : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (selectedRowIndex p z) rewards s (t.val - s)
            (by have h := t.isLt; dsimp [s]; omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate z rewards C_star C_h active hlaunch)
        let r1 : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
          ReferenceAssignmentPayloadChronology.actualRunRecordAt active z'.1.2
            (selectedRowIndex p z') rewards s (t.val - s)
            (by have h := t.isLt; dsimp [s]; omega)
            hmode1
        have hrecord0 : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z = some r0 := by
          simpa [r0] using ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
            rate rewards C_star C_h t z active hlaunch hs
        have hrecord1 : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z' = some r1 := by
          simpa [r1, hstart'] using ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
            rate rewards C_star C_h t z' active hlaunch' hs'
        have hstatesOpt := actualIncomingState_eq_through_first_live_block
          rate rewards C_star C_h control0 t z v (by omega)
        rw [hrecord1, hrecord0] at hstatesOpt
        have hstates : r1.input.state = r0.input.state := Option.some.inj hstatesOpt
        have htime0 : r0.input.time = t := by
          apply Fin.ext
          dsimp [r0, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
            ReferenceActivePhysicalHorizon.roundInputAt]
          have hs' : s ≤ t.val := hs
          omega
        have htime1 : r1.input.time = t := by
          apply Fin.ext
          dsimp [r1, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
            ReferenceActivePhysicalHorizon.roundInputAt]
          have hs' : s ≤ t.val := hs
          omega
        have hselected : r0.input.selected = r1.input.selected := by
          change selectedRowIndex p z = selectedRowIndex p z'
          exact (firstCollectionAssignmentPatch_private_and_id
            rate rewards C_star C_h z v).2.2.symm
        have hrows0 : r0.input.rows = z.1.2 := rfl
        have hrows1 : r1.input.rows = z'.1.2 := rfl
        have hcontrol (u : Fin p.T)
            (hu : u.val < s + (firstLiveWindow
              (completeSuffixRecords rate z rewards C_star C_h)).length) :
            (z'.1.2 (selectedRowIndex p z)).2 u =
              (z.1.2 (selectedRowIndex p z)).2 u := by
          apply firstCollectionAssignmentPatch_control_outside rate rewards C_star C_h z v u
          intro hpatch
          omega
        have hcurrent : (r0.input.rows r0.input.selected).2 r0.input.time =
            (r1.input.rows r0.input.selected).2 r0.input.time := by
          rw [hrows0, hrows1, hselected, htime0]
          exact (hcontrol t (by dsimp [s]; exact ht)).symm
        have hpast : ∀ u : Fin p.T, u.val < r0.input.time.val →
            ((r0.input.rows r0.input.selected).2 u).1
                ContinuousControlSlice.Label.prop =
              ((r1.input.rows r0.input.selected).2 u).1
                ContinuousControlSlice.Label.prop := by
          intro u hu
          rw [hrows0, hrows1, hselected]
          have hut : u.val < t.val := by simpa only [htime0] using hu
          exact congrArg (fun control : Bandits.Support.ContinuousLearningRows.TimeControl p =>
            control.1 ContinuousControlSlice.Label.prop)
              (hcontrol u (by omega)).symm
        have htemporal := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
          r0.input.state r0.input.rows r1.input.rows r0.input.selected r0.input.time
          r0.input.active r0.input.rewards r1.input.rewards hcurrent hpast rfl
        let y : ReferenceActivePhysicalStep.RoundInput p rate :=
          ⟨r0.input.state, r1.input.rows, r0.input.selected, r0.input.time,
            r0.input.active, r1.input.rewards⟩
        have hcongr : ReferenceActivePhysicalHorizon.computedEvidence y =
            ReferenceActivePhysicalHorizon.computedEvidence r1.input := by
          apply ReferenceActivePhysicalHorizon.computedEvidence_congr y r1.input
          · exact hstates.symm
          · exact hselected
          · exact htime0.trans htime1.symm
          · rfl
          · cases hselected
            rfl
        have hevidence : r0.evidence = r1.evidence := by
          calc
            r0.evidence = ReferenceActivePhysicalHorizon.computedEvidence r0.input := rfl
            _ = ReferenceActivePhysicalHorizon.computedEvidence y := by
              simpa [y] using htemporal
            _ = ReferenceActivePhysicalHorizon.computedEvidence r1.input := hcongr
            _ = r1.evidence := rfl
        rw [hrecord1, hrecord0]
        exact congrArg some hevidence.symm

/-- Raw-buffer diagnostics are a projection of the actual coordinator
observation retained in each physical evidence value. Thus the per-date
evidence equality before the assignment block also preserves the literal
optional raw gate/arrival pair, including absence. -/
theorem actualRawDiagnostic_eq_before_assignment_block
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : S) (v : Fin p.T → AssignmentVector p)
    (ht : t.val < physicalStart rate z rewards C_star C_h +
      (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).map
        ReferenceCollectionRawBufferHistory.rawDiagnostic =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        ReferenceCollectionRawBufferHistory.rawDiagnostic := by
  let diagnostic := fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence
      (p := p) (rate := rate) =>
    evidence.coordinator.recording.bind fun output =>
      output.gateArm.map fun arm => (arm, output.rawArrival)
  have hfactor (source : S) :
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source).map
          ReferenceCollectionRawBufferHistory.rawDiagnostic =
        Option.map diagnostic
          ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source).map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    simp only [Option.map_map]
    congr 1
  have hevidence := actualRecord_evidence_eq_before_assignment_block
    rate rewards C_star C_h control0 t z v ht
  calc
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).map
        ReferenceCollectionRawBufferHistory.rawDiagnostic =
      Option.map diagnostic
        ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
          (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence) := hfactor _
    _ = Option.map diagnostic
        ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
      congrArg (Option.map diagnostic) hevidence
    _ = (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        ReferenceCollectionRawBufferHistory.rawDiagnostic := (hfactor z).symm


open ReferenceActivePhysicalHorizon (RoundRecord Connected)
open ReferenceFirstCollectionAssignmentStepNonRead
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCoordinatorRecorderCallTrace (cell)
open ReferenceActiveHorizonMeasurability (roundRecordCode)

local notation "R" z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "s" z:max => physicalStart rate z rewards C_star C_h
local notation "b" z:max => firstCallBoundary rate rewards C_star C_h z
local notation "tag" => ReferenceCollectionPhaseHistory.cutoffChosen

private theorem record_fields (z : S) (k : ℕ)
    (r : RoundRecord (p := p) (rate := rate)) (hr : (R z)[k]? = some r) :
    r.input.rows = z.1.2 ∧ r.input.selected = selectedRowIndex p z ∧
      r.input.rewards = rewards ∧ r.input.time.val = s z + k := by
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k r hr
  by_cases hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none
  · simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hn] at hr
  · let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate z rewards C_star C_h hn
    have hl := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
      rate z rewards C_star C_h hn
    have hm := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h active hl
    have hrec := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hl
    rw [hrec] at hr
    have hf := ReferenceActivePhysicalHorizon.run_record_inputs active z.1.2
      (selectedRowIndex p z) rewards (s z) (p.T - s z)
      (by have h := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z rewards C_star C_h; omega) hm r (List.mem_of_getElem? hr)
    exact ⟨hf.1, hf.2.1, hf.2.2, ht⟩

private theorem connected_state_succ
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hc : Connected initial records final) (k : ℕ) (hk : k + 1 < records.length) :
    records[k + 1].input.state = records[k].output.next := by
  have hd := ReferenceFollowerReplyChronology.connected_drop_from_output hc k (by omega)
  rw [List.drop_eq_getElem_cons hk] at hd
  exact hd.1

/-- The actual calendar induction jointly preserves the incoming state and
all four option-bearing observations strictly before the original first call.
The endpoint state is retained even though its assignment draw may be read. -/
theorem calendar_comparison (z : S) (v : Fin p.T → AssignmentVector p)
    (k : ℕ) (hk : k < (R z).length) (hbound : s z + k ≤ b z) :
    let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
    ∃ (hk' : k < (R z').length),
      (R z)[k].input.state = (R z')[k].input.state ∧
      (s z + k < b z →
        (R z)[k].evidence = (R z')[k].evidence ∧
        cell (roundRecordCode (R z)[k]) = cell (roundRecordCode (R z')[k]) ∧
        tag (R z)[k].input = tag (R z')[k].input ∧
        cell0 rate (R z)[k] = cell0 rate (R z')[k]) := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  have hstart : s z' = s z := firstCollectionAssignmentPatch_physicalStart
    rate rewards C_star C_h z v
  have hlen : (R z').length = (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
  have hselected : selectedRowIndex p z' = selectedRowIndex p z :=
    (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.2
  have hlaunch := firstCollectionAssignmentPatch_correctedLaunch rate rewards C_star C_h z v
  have hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro h
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, h] at hk
  let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
    rate z rewards C_star C_h hn
  have hl := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate z rewards C_star C_h hn
  have hl' : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z' rewards C_star C_h = some active := hlaunch.trans hl
  have hc : ∃ final, Connected active (R z) final := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hl]
    exact ⟨_, ReferenceActivePhysicalHorizon.run_connected ..⟩
  have hc' : ∃ final, Connected active (R z') final := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z' rewards C_star C_h active hl']
    exact ⟨_, ReferenceActivePhysicalHorizon.run_connected ..⟩
  obtain ⟨final, hc⟩ := hc
  obtain ⟨final', hc'⟩ := hc'
  induction k with
  | zero =>
      have hk' : 0 < (R z').length := by omega
      refine ⟨hk', ?_, ?_⟩
      · have h0 := ReferenceFollowerReplyChronology.connected_take_to_input hc 0 hk
        have h1 := ReferenceFollowerReplyChronology.connected_take_to_input hc' 0 hk'
        simpa only [List.take_zero, Connected] using h0.trans h1.symm
      · intro hb
        have hs : (R z)[0].input.state = (R z')[0].input.state := by
          have h0 := ReferenceFollowerReplyChronology.connected_take_to_input hc 0 hk
          have h1 := ReferenceFollowerReplyChronology.connected_take_to_input hc' 0 hk'
          simpa only [List.take_zero, Connected] using h0.trans h1.symm
        exact compare_records hs hb
  | succ k ih =>
      have hk0 : k < (R z).length := by omega
      obtain ⟨hk0', hs0, hcmp0⟩ := ih hk0 (by omega)
      have he := (hcmp0 (by omega)).1
      have hk' : k + 1 < (R z').length := by rw [hlen]; exact hk
      have hs : (R z)[k + 1].input.state = (R z')[k + 1].input.state := by
        rw [connected_state_succ rate hc k hk,
          connected_state_succ rate hc' k hk']
        exact congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after he
      refine ⟨hk', hs, ?_⟩
      intro hb
      exact compare_records hs hb
where
  compare_records {k : ℕ} {hk : k < (R z).length}
      {hk' : k < (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).length}
      (hs : (R z)[k].input.state =
        (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k].input.state)
      (hb : s z + k < b z) :
      (R z)[k].evidence =
          (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k].evidence ∧
      cell (roundRecordCode (R z)[k]) =
        cell (roundRecordCode (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k]) ∧
      tag (R z)[k].input =
        tag (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k].input ∧
      cell0 rate (R z)[k] =
        cell0 rate (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k] := by
    let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
    let left := (R z)[k]
    let right := (R z')[k]
    have h0 := record_fields rate rewards C_star C_h z k left (List.getElem?_eq_getElem hk)
    have h1 := record_fields rate rewards C_star C_h z' k right (List.getElem?_eq_getElem hk')
    have hstart := firstCollectionAssignmentPatch_physicalStart rate rewards C_star C_h z v
    have hsel := (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.2
    have hi : left.input.selected = right.input.selected := h0.2.1.trans (hsel.symm.trans h1.2.1.symm)
    have ht : left.input.time = right.input.time := by
      apply Fin.ext
      rw [h0.2.2.2, h1.2.2.2, hstart]
    have hw : left.input.rewards = right.input.rewards := h0.2.2.1.trans h1.2.2.1.symm
    have hr0 : left.input.row = z.1.2 (selectedRowIndex p z) := by
      change left.input.rows left.input.selected = _
      rw [h0.1, h0.2.1]
    have hr1 : right.input.row = z'.1.2 (selectedRowIndex p z) := by
      change right.input.rows right.input.selected = _
      rw [h1.1, h1.2.1, hsel]
    have hp : ∀ t : Fin p.T, t.val < left.input.time.val →
        (left.input.row.2 t).1 ContinuousControlSlice.Label.prop =
          (right.input.row.2 t).1 ContinuousControlSlice.Label.prop := by
      intro t _
      rw [hr0, hr1]
      have hr := firstCollectionAssignmentPatch_remainder rate rewards C_star C_h z v t
      exact congrArg (fun rem => rem.1 ⟨ContinuousControlSlice.Label.prop, by
        rintro ⟨j, hj⟩; cases hj⟩) hr.symm
    by_cases ha : s z + (firstLiveWindow (R z)).length ≤ left.input.time.val
    · have hsource := actual_source_assignment rate rewards C_star C_h z ⟨k, hk⟩
        (v left.input.time) ha (by rw [h0.2.2.2]; exact hb)
      apply compare_of_remainder left right hs hi ht hw _ hp hsource.2.1 hsource.1
      rw [hr0, hr1, ← ht]
      exact (firstCollectionAssignmentPatch_remainder
        rate rewards C_star C_h z v left.input.time).symm
    · apply compare_of_current left right hs hi ht hw _ hp
      rw [hr0, hr1, ← ht]
      exact (firstCollectionAssignmentPatch_control_outside rate rewards C_star C_h z v
        left.input.time (by omega)).symm


private theorem patched_length (z : S) (v : Fin p.T → AssignmentVector p) :
    (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).length =
      (R z).length := by
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
    firstCollectionAssignmentPatch_physicalStart]

private theorem indexed_time (z : S) (k : ℕ) (hk : k < (R z).length)
    (v : Fin p.T → AssignmentVector p)
    (hk' : k < (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).length) :
    (R z)[k].input.time =
      (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))[k].input.time := by
  apply Fin.ext
  rw [(record_fields rate rewards C_star C_h z k _ (List.getElem?_eq_getElem hk)).2.2.2,
    (record_fields rate rewards C_star C_h _ k _ (List.getElem?_eq_getElem hk')).2.2.2,
    firstCollectionAssignmentPatch_physicalStart]

/-- Every ordinary incoming-state query through the original call boundary
agrees, including absence before launch and on an exhausted initializer. -/
theorem incoming_eq_through_first_call (t : Fin p.T) (z : S)
    (v : Fin p.T → AssignmentVector p) (ht : t.val ≤ b z) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  have hstart : s z' = s z := firstCollectionAssignmentPatch_physicalStart
    rate rewards C_star C_h z v
  unfold ReferenceSourcePrefixHistoryFiltration.incoming
    ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [hstart]
  by_cases hs : s z ≤ t.val
  · rw [ite_eq_left hs, ite_eq_left hs]
    have hk : t.val - s z < (R z).length := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
      have hT := t.isLt
      omega
    obtain ⟨hk', he, _⟩ := calendar_comparison rate rewards C_star C_h z v
      (t.val - s z) hk (by omega)
    rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
    exact congrArg (fun state => some (ReferenceActivePhysicalStepMeasurability.encodeState state))
      he.symm
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- The first actual invocation, including its absence, date, old cutoff and
whole sampler parameters, is retained. Failed checked sampling is included. -/
theorem firstCollectionAssignmentPatch_firstCollectionCall (z : S)
    (v : Fin p.T → AssignmentVector p) :
    ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z := by
  let z' := firstCollectionAssignmentPatch rate rewards C_star C_h z v
  have hlen : (R z').length = (R z).length := patched_length rate rewards C_star C_h z v
  cases hf : ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z with
  | none =>
      apply (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff
        (rate := rate) rewards C_star C_h z').2
      intro r hr
      obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
      subst r
      have hk0 : k < (R z).length := by simpa only [hlen] using hk
      have hb : s z + k ≤ b z := by
        have htime := (record_fields rate rewards C_star C_h z k _
          (List.getElem?_eq_getElem hk0)).2.2.2
        have hT := (R z)[k].input.time.isLt
        simp only [firstCallBoundary, hf]
        omega
      obtain ⟨_, hs, _⟩ := calendar_comparison rate rewards C_star C_h z v k hk0 hb
      rw [← ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
        (R z)[k].input (R z')[k].input hs
        (indexed_time rate rewards C_star C_h z k hk0 v hk)]
      exact (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff
        (rate := rate) rewards C_star C_h z).1 hf _ (List.getElem_mem hk0)
  | some call =>
      obtain ⟨u, t, theta⟩ := call
      obtain ⟨k, r, hr, htime, hcall, hprevious⟩ :=
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
          (rate := rate) rewards C_star C_h z u t theta).1 hf
      have hk : k < (R z).length := List.getElem?_eq_some_iff.mp hr |>.1
      have heq : (R z)[k] = r := by
        exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hr)
      subst r
      have hk' : k < (R z').length := by rw [hlen]; exact hk
      have hb : s z + k = b z := by
        rw [firstCallBoundary, hf]
        exact ((record_fields rate rewards C_star C_h z k _
          (List.getElem?_eq_getElem hk)).2.2.2).symm.trans (congrArg Fin.val htime)
      obtain ⟨_, hs, _⟩ := calendar_comparison rate rewards C_star C_h z v k hk (by omega)
      have ht := indexed_time rate rewards C_star C_h z k hk v hk'
      apply (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
        (rate := rate) rewards C_star C_h z' u t theta).2
      refine ⟨k, (R z')[k], List.getElem?_eq_getElem hk', ht.symm.trans htime, ?_, ?_⟩
      · change ReferenceFirstCollectionSamplerCall.collectionCallOnInput (R z')[k].input = _
        rw [← ReferenceFirstCollectionSamplerCall.collectionCallOnInput_eq_of_state_eq_time_eq
          (R z)[k].input (R z')[k].input hs ht]
        exact hcall
      · intro j hj earlier hearlier
        have hj' : j < (R z').length := by omega
        have hj0 : j < (R z).length := by omega
        have hearlier' : (R z')[j] = earlier := by
          exact Option.some.inj ((List.getElem?_eq_getElem hj').symm.trans hearlier)
        subst earlier
        obtain ⟨_, hsj, _⟩ := calendar_comparison rate rewards C_star C_h z v j hj0 (by omega)
        rw [← ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
          (R z)[j].input (R z')[j].input hsj
          (indexed_time rate rewards C_star C_h z j hj0 v hj')]
        exact hprevious j hj _ (List.getElem?_eq_getElem hj0)

/-- The natural-valued first-call boundary retains its terminal sentinel. -/
theorem firstCollectionAssignmentPatch_firstCallBoundary (z : S)
    (v : Fin p.T → AssignmentVector p) :
    b (firstCollectionAssignmentPatch rate rewards C_star C_h z v) = b z := by
  unfold firstCallBoundary
  rw [firstCollectionAssignmentPatch_firstCollectionCall]

private theorem patch_eq_self_of_empty (z : S) (v : Fin p.T → AssignmentVector p)
    (h : b z ≤ s z + (firstLiveWindow (R z)).length) :
    firstCollectionAssignmentPatch rate rewards C_star C_h z v = z := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext q
      by_cases hq : q = selectedRowIndex p z
      · subst q
        apply Prod.ext
        · exact firstCollectionAssignmentPatch_forwards rate rewards C_star C_h z v
        · funext t
          exact firstCollectionAssignmentPatch_control_outside
            rate rewards C_star C_h z v t (by omega)
      · exact firstCollectionAssignmentPatch_other_rows rate rewards C_star C_h z v q hq
  · rfl

private theorem takeWhile_length_eq {α : Type*} (f : α → Bool)
    (left right : List α) (hlen : left.length = right.length)
    (h : ∀ k (hk : k < left.length) (hk' : k < right.length),
      k ≤ (left.takeWhile f).length → f left[k] = f right[k]) :
    (left.takeWhile f).length = (right.takeWhile f).length := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons a left ih =>
      cases right with
      | nil => simp at hlen
      | cons c right =>
          have hhead := h 0 (by simp) (by simp) (by omega)
          simp only [List.getElem_cons_zero] at hhead
          cases hf : f a with
          | false => simp only [List.takeWhile_cons, hf, ← hhead, Bool.false_eq_true,
              ↓reduceIte, List.length_nil]
          | true =>
              have htail : (left.takeWhile f).length = (right.takeWhile f).length := by
                apply ih right (by simpa using hlen)
                intro k hk hk' hb
                have hstep := h (k + 1) (by simpa using Nat.succ_lt_succ hk)
                  (by simpa using Nat.succ_lt_succ hk')
                simp only [List.takeWhile_cons, hf, ↓reduceIte, List.length_cons] at hstep
                exact hstep (by omega)
              simp only [List.takeWhile_cons, hf, ← hhead, ↓reduceIte,
                List.length_cons, htail]

/-- The first chosen cutoff head stays at exactly the same calendar date. -/
theorem firstCollectionAssignmentPatch_assignmentBegin (z : S)
    (v : Fin p.T → AssignmentVector p) :
    s (firstCollectionAssignmentPatch rate rewards C_star C_h z v) +
        (firstLiveWindow (R (firstCollectionAssignmentPatch rate rewards C_star C_h z v))).length =
      s z + (firstLiveWindow (R z)).length := by
  by_cases hempty : b z ≤ s z + (firstLiveWindow (R z)).length
  · rw [patch_eq_self_of_empty rate rewards C_star C_h z v hempty]
  · rw [firstCollectionAssignmentPatch_physicalStart]
    congr 1
    apply Eq.symm
    apply takeWhile_length_eq (fun r => !tag r.input) (R z) _
      (patched_length rate rewards C_star C_h z v).symm
    intro k hk hk' hleft
    change k ≤ (firstLiveWindow (R z)).length at hleft
    obtain ⟨_, _, hc⟩ := calendar_comparison rate rewards C_star C_h z v k hk (by omega)
    exact congrArg Bool.not (hc (by omega)).2.2.1

/-- Actual evidence on the entire strict pre-invocation suffix. Whole
row-bearing records themselves are deliberately retained on each side. -/
theorem precall_evidence_eq (z : S) (v : Fin p.T → AssignmentVector p) :
    ((R (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).take (b z - s z)).map
        RoundRecord.evidence =
      ((R z).take (b z - s z)).map RoundRecord.evidence := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, patched_length]
  · intro k hk hk'
    simp only [List.length_map, List.length_take] at hk hk'
    have hk0 : k < (R z).length := by omega
    obtain ⟨_, _, hc⟩ := calendar_comparison rate rewards C_star C_h z v k hk0 (by omega)
    simpa only [List.getElem_map, List.getElem_take] using (hc (by omega)).1.symm

/-- The optional raw gate and entire arrival diagnostics are unchanged on
that actual suffix prefix, with every absent recorder left absent. -/
theorem precall_rawDiagnostic_eq (z : S) (v : Fin p.T → AssignmentVector p) :
    ((R (firstCollectionAssignmentPatch rate rewards C_star C_h z v)).take (b z - s z)).map
        ReferenceCollectionRawBufferHistory.rawDiagnostic =
      ((R z).take (b z - s z)).map ReferenceCollectionRawBufferHistory.rawDiagnostic := by
  let diagnostic := fun e : ReferenceActivePhysicalHorizon.RoundEvidence
      (p := p) (rate := rate) =>
    e.coordinator.recording.bind fun output =>
      output.gateArm.map fun arm => (arm, output.rawArrival)
  have h := congrArg (List.map diagnostic) (precall_evidence_eq rate rewards C_star C_h z v)
  have factor : ReferenceCollectionRawBufferHistory.rawDiagnostic =
      diagnostic ∘ (RoundRecord.evidence (p := p) (rate := rate)) := by
    funext r
    rfl
  rw [factor]
  simpa only [List.map_map] using h


open ReferenceFirstCollectionPrecallCalendarSupport

/-- Every finite cutoff reads the same original optional numerical slots.
The entire enabled flag, arm, reward function and rate function are retained. -/
theorem firstCollectionAssignmentPatch_precallSlots (n : ℕ) (z : S)
    (v : Fin p.T → AssignmentVector p) :
    precallSlots rate rewards C_star C_h n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      precallSlots rate rewards C_star C_h n z := by
  unfold precallSlots cutBoundary
  rw [firstCollectionAssignmentPatch_firstCallBoundary,
    firstCollectionAssignmentPatch_physicalStart]
  apply List.map_congr_left
  intro k hk
  have hkb : k < min n (b z) - s z := List.mem_range.mp hk
  have hk0 : k < (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hb := firstCallBoundary_le_T rate rewards C_star C_h z
    have hmin := Nat.min_le_right n (b z)
    omega
  obtain ⟨hk', _, hc⟩ := calendar_comparison rate rewards C_star C_h z v k hk0 (by
    have hmin := Nat.min_le_right n (b z)
    omega)
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk0]
  exact (hc (by have hmin := Nat.min_le_right n (b z); omega)).2.2.2.symm

private theorem actualLaunchBy_patch (n : ℕ) (z : S)
    (v : Fin p.T → AssignmentVector p) :
    ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) ↔
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n z := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
  rw [firstCollectionAssignmentPatch_physicalStart]
  have hc := ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h
  have hc' := ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate (firstCollectionAssignmentPatch rate rewards C_star C_h z v) rewards C_star C_h
  change _ ↔ (ReferenceCompletePhysicalHistory.generatedBoundary
    rate z rewards C_star C_h).crossing.isSome = true at hc
  change _ ↔ (ReferenceCompletePhysicalHistory.generatedBoundary rate
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v)
      rewards C_star C_h).crossing.isSome = true at hc'
  rw [← hc', ← hc, firstCollectionAssignmentPatch_correctedLaunch]

/-- Launch absence and every absent numerical readout remain absent. A present
zero-arrival cell retains its service update in the original queue run. -/
theorem firstCollectionAssignmentPatch_precallCells (n : ℕ) (z : S)
    (v : Fin p.T → AssignmentVector p) :
    precallCells? rate rewards C_star C_h n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      precallCells? rate rewards C_star C_h n z := by
  unfold precallCells?
  have hcut : cutBoundary rate rewards C_star C_h n
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      cutBoundary rate rewards C_star C_h n z := by
    unfold cutBoundary
    rw [firstCollectionAssignmentPatch_firstCallBoundary]
  rw [hcut, firstCollectionAssignmentPatch_precallSlots,
    propext (actualLaunchBy_patch rate rewards C_star C_h _ z v)]

/-- The existing stopped queue readout, including its first overflow update,
is exactly the same option at every finite boundary. -/
theorem firstCollectionAssignmentPatch_precallReadout (n : ℕ) (z : S)
    (v : Fin p.T → AssignmentVector p) :
    precallReadout? rate rewards C_star C_h n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      precallReadout? rate rewards C_star C_h n z := by
  unfold precallReadout?
  rw [firstCollectionAssignmentPatch_precallCells]

/-- The literal overflow event uses the unchanged optional prefixes and the
same original queue computation, retaining the detecting update. -/
theorem firstCollectionAssignmentPatch_mem_precallOverflow (z : S)
    (v : Fin p.T → AssignmentVector p) :
    firstCollectionAssignmentPatch rate rewards C_star C_h z v ∈
        ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ↔
      z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h := by
  simp only [ReferenceFirstCollectionPrecallOverflowBound.precallOverflow, Set.mem_ofPred_eq,
    firstCollectionAssignmentPatch_precallCells]

end Bandits.Support.ReferenceFirstCollectionAssignmentNonRead

end
