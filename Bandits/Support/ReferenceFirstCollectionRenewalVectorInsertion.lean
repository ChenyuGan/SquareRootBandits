/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalPastLocality

/-!
# Insert the complete assignment vector into the original renewal source

Sources: sources/zip4/manuscript/06_interruptions.tex:399-423,
sources/zip4/manuscript/07_public_setup.tex:121-164,
sources/zip4/manuscript/04_slow_fast_learner.tex:176-215, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64.

This module changes the assignment coordinates at one calendar cell in the
original whole source. The old source and full auxiliary array remain in the
analytical extension. The resulting physical record is identified with the
existing complete-vector sampler input. No marginal law after insertion or
physical installation is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalPastLocality
open Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.LaunchAssignmentCoordinateSplit
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstCollectionSamplerCall
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.AssignmentParameterFibreKernel
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion

abbrev S (p : ConstructorDimensions.Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev V (p : ConstructorDimensions.Parameters) := CheckedAssignmentSample.AssignmentVector p
abbrev Z {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) :=
  RenewalCallSource rate rewards C_star C_h u t
abbrev A (p : ConstructorDimensions.Parameters) := AuxiliaryArray p
abbrev W {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) := RenewalBase rate rewards C_star C_h u t × V p
abbrev Lambda {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) := renewalLiftLaw rate rewards C_star C_h u t

/-- The selected row is determined by the original private coordinator scalar. -/
abbrev q {p : ConstructorDimensions.Parameters} (s : S p) : Fin (M p) :=
  ActualInitializationPhysicalStep.selectedRowIndex p s

/-- The complete control at the selected row and current calendar cell. -/
abbrev c {p : ConstructorDimensions.Parameters} (t : Fin p.T) (s : S p) :
    ContinuousLearningRows.TimeControl p := (s.1.2 (q s)).2 t

/-- The original launch-coordinate split. -/
abbrev e (p : ConstructorDimensions.Parameters) := controlAssignmentSplitEquiv p

/-- The original complete assignment vector at the selected current cell. -/
abbrev av {p : ConstructorDimensions.Parameters} (t : Fin p.T) (s : S p) : V p :=
  LaterAssignmentStartOperation.ownAssignmentVector (s.1.2 (q s)) t

/-- Replace just the assignment-vector component in the original control. -/
def ctrl {p : ConstructorDimensions.Parameters} (t : Fin p.T) (s : S p) (v : V p) :
    ContinuousLearningRows.TimeControl p :=
  (e p).symm (v, ((e p) (c t s)).2)

/-- Insert the replacement control at the selected row and current cell in
the original whole source, preserving every other source coordinate. -/
def insert {p : ConstructorDimensions.Parameters} (t : Fin p.T) (s : S p) (v : V p) : S p :=
  replaceSourceControl p t s (ctrl t s v)

/-- The corresponding complete selected-row suffix. It changes the current
cell while retaining all earlier and future controls. -/
def suffix {p : ConstructorDimensions.Parameters} (t : Fin p.T) (s : S p) (v : V p) :
    Fin p.T → ContinuousLearningRows.TimeControl p :=
  Function.update (s.1.2 (q s)).2 t (ctrl t s v)

/-- Insert the vector into a renewal subtype using the already-proved source
membership preservation. -/
def put {p : ConstructorDimensions.Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : Z rate rewards C_star C_h u t) (v : V p) :
    Z rate rewards C_star C_h u t :=
  renewalSourceWithSuffix rate rewards C_star C_h u t z (suffix t z.val v)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (u t : Fin p.T)

/-- Applying the inverse split restores the chosen vector and retains the
entire non-assignment scalar and affine coordinate. -/
theorem controlAssignmentSplit_ctrl (s : S p) (v : V p) :
    (e p) (ctrl t s v) = (v, ((e p) (c t s)).2) := by
  exact (e p).apply_symm_apply _

private theorem measurable_selectedRow (p : ConstructorDimensions.Parameters) :
    Measurable (fun s : S p => s.1.2 (q s)) := by
  have hq : Measurable (q (p := p)) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hrows : Measurable (fun s : S p => s.1.2) :=
    measurable_snd.comp (measurable_fst : Measurable (fun s : S p => s.1))
  have hbranch : ∀ j : Fin (M p), Measurable (fun s : S p => s.1.2 j) := by
    intro j
    exact (measurable_pi_apply j).comp hrows
  exact (measurable_from_prod_countable_right
      (f := fun z : Fin (M p) × S p => z.2.1.2 z.1) hbranch).comp
    (hq.prodMk measurable_id)

private theorem measurable_currentControl (p : ConstructorDimensions.Parameters) (t : Fin p.T) :
    Measurable (fun s : S p => c t s) := by
  exact (measurable_pi_apply t).comp
    (measurable_snd.comp (measurable_selectedRow p))

private theorem measurable_ctrl (p : ConstructorDimensions.Parameters) (t : Fin p.T) :
    Measurable (fun sv : S p × V p => ctrl t sv.1 sv.2) := by
  have hc : Measurable (fun sv : S p × V p => c t sv.1) :=
    (measurable_currentControl p t).comp measurable_fst
  exact ((e p).symm.measurable).comp
    (measurable_snd.prodMk (measurable_snd.comp ((e p).measurable.comp hc)))

private def fixedControlInsert {p : ConstructorDimensions.Parameters} (t : Fin p.T) (j : Fin (M p))
    (sv : S p × V p) : S p :=
  ((sv.1.1.1,
      Function.update sv.1.1.2 j
        ((sv.1.1.2 j).1,
          Function.update (sv.1.1.2 j).2 t (ctrl t sv.1 sv.2))),
    sv.1.2)

private theorem measurable_by_finite_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Finite β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun z : β × α => branch z.1 z.2) hbranch).comp
      (hkey.prodMk measurable_id)

private theorem measurable_fixedControlInsert {p : ConstructorDimensions.Parameters} (t : Fin p.T)
    (j : Fin (M p)) : Measurable (fixedControlInsert t j) := by
  have hctrl := measurable_ctrl p t
  have hrows : Measurable (fun sv : S p × V p => sv.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hrow : Measurable (fun sv : S p × V p => sv.1.1.2 j) :=
    (measurable_pi_apply j).comp hrows
  have hcontrols : Measurable (fun sv : S p × V p =>
      Function.update (sv.1.1.2 j).2 t (ctrl t sv.1 sv.2)) :=
    (measurable_update' (a := t)).comp
      ((measurable_snd.comp hrow).prodMk hctrl)
  have hnewRow : Measurable (fun sv : S p × V p =>
      ((sv.1.1.2 j).1, Function.update (sv.1.1.2 j).2 t (ctrl t sv.1 sv.2))) :=
    (measurable_fst.comp hrow).prodMk hcontrols
  have hnewRows : Measurable (fun sv : S p × V p =>
      Function.update sv.1.1.2 j
        ((sv.1.1.2 j).1, Function.update (sv.1.1.2 j).2 t (ctrl t sv.1 sv.2))) :=
    (measurable_update' (a := j)).comp (hrows.prodMk hnewRow)
  exact (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
    hnewRows).prodMk (measurable_snd.comp measurable_fst))

/-- The original-source insertion is jointly measurable in the whole source
and the complete vector. -/
theorem measurable_insert :
    Measurable (fun sv : S p × V p => insert t sv.1 sv.2) := by
  classical
  have hkey : Measurable (fun sv : S p × V p => q sv.1) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
      measurable_fst
  have hcases := measurable_by_finite_cases (fun sv : S p × V p => q sv.1)
    hkey (fixedControlInsert t) (fun j => measurable_fixedControlInsert t j)
  have heq : (fun sv : S p × V p => fixedControlInsert t (q sv.1) sv) =
      (fun sv => insert t sv.1 sv.2) := by
    funext sv
    rcases sv with ⟨s, v⟩
    simp [fixedControlInsert, insert, replaceSourceControl, q,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  rw [← heq]
  exact hcases

/-- The suffix itself is jointly measurable; future cells remain the original
ones because it is a single function update. -/
theorem measurable_suffix :
    Measurable (fun sv : S p × V p => suffix t sv.1 sv.2) := by
  have hselected := measurable_selectedRow p
  have hbase : Measurable (fun sv : S p × V p => (sv.1.1.2 (q sv.1)).2) :=
    (measurable_snd.comp hselected).comp measurable_fst
  exact (measurable_update' (a := t)).comp
    (hbase.prodMk (measurable_ctrl p t))

/-- At a fixed time, this original source replacement is exactly the public
selected-control suffix replacement. -/
theorem insert_eq_replaceSelectedControlSuffix (s : S p) (v : V p) :
    insert t s v =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        s t (suffix t s v) := by
  have hcontrols : Function.update (s.1.2 (q s)).2 t (ctrl t s v) =
      (fun r => if r.val < t.val then (s.1.2 (q s)).2 r else suffix t s v r) := by
    funext r
    by_cases hbefore : r.val < t.val
    · have hne : r ≠ t := by
        intro h
        subst r
        omega
      simp [hbefore, hne]
    · by_cases heq : r = t
      · subst r
        simp [suffix]
      · simp [hbefore, suffix, heq]
  dsimp only [insert, replaceSourceControl,
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix, suffix]
  rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = q s
      · subst j
        simp only [Function.update_self]
        exact congrArg (fun controls => ((s.1.2 (q s)).1, controls)) hcontrols
      · simp only [Function.update_of_ne hj]
  · rfl

/-- The subtype source body is exactly the original-source insertion. -/
theorem put_val (z : Z rate rewards C_star C_h u t) (v : V p) :
    (put rate rewards C_star C_h u t z v).val = insert t z.val v := by
  rw [put, renewalSourceWithSuffix_val, insert_eq_replaceSelectedControlSuffix]

/-- The source-subtype update is jointly measurable as well. Its range proof
is the already established renewal membership of `put`. -/
theorem measurable_put :
    Measurable (fun zv : Z rate rewards C_star C_h u t × V p =>
      put rate rewards C_star C_h u t zv.1 zv.2) := by
  have hsource : Measurable (fun zv : Z rate rewards C_star C_h u t × V p => zv.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hbase : Measurable (fun zv : Z rate rewards C_star C_h u t × V p =>
      insert t zv.1.val zv.2) :=
    (measurable_insert (p := p) (t := t)).comp (hsource.prodMk measurable_snd)
  have hval : Measurable (fun zv : Z rate rewards C_star C_h u t × V p =>
      (put rate rewards C_star C_h u t zv.1 zv.2).val) := by
    have hsame : (fun zv : Z rate rewards C_star C_h u t × V p =>
        (put rate rewards C_star C_h u t zv.1 zv.2).val) =
        (fun zv => insert t zv.1.val zv.2) := by
      funext zv
      exact put_val rate rewards C_star C_h u t zv.1 zv.2
    rw [hsame]
    exact hbase
  exact hval.subtype_mk

/-- The current control of the inserted source is exactly ctrl. -/
theorem currentControl_insert (s : S p) (v : V p) :
    c t (insert t s v) = ctrl t s v := by
  rw [insert_eq_replaceSelectedControlSuffix]
  change ((ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      s t (suffix t s v)).1.2 (q s)).2 t = ctrl t s v
  rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
    s t t (suffix t s v) (Nat.le_refl _)]
  simp [suffix]

/-- Extracting the full vector after insertion returns the inserted vector. -/
theorem av_insert (s : S p) (v : V p) : av t (insert t s v) = v := by
  change ((e p) (c t (insert t s v))).1 = v
  rw [currentControl_insert, controlAssignmentSplit_ctrl]

private theorem ctrl_original (s : S p) : ctrl t s (av t s) = c t s := by
  unfold ctrl
  have hav : av t s = ((e p) (c t s)).1 := rfl
  rw [hav]
  exact (e p).symm_apply_apply (c t s)

/-- Inserting the vector already present at the original cell is the identity
on the whole source. -/
theorem insert_original_vector (s : S p) : insert t s (av t s) = s := by
  rw [insert, ctrl_original]
  simpa only [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    using ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p t s

/-- The identity array, all private arrays (including the selecting scalar
J), and the selected row index are retained exactly. -/
theorem insert_identity_private_selector (s : S p) (v : V p) :
    (insert t s v).1.1 = s.1.1 ∧
    (insert t s v).2 = s.2 ∧
    q (insert t s v) = q s := by
  refine ⟨?_, ?_, ?_⟩
  · exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_id p t s
      (ctrl t s v)
  · exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_private p t s
      (ctrl t s v)
  · rfl

/-- The selected row's complete forward component is retained. -/
theorem insert_selected_forward (s : S p) (v : V p) :
    ((insert t s v).1.2 (q s)).1 = (s.1.2 (q s)).1 := by
  simpa only [insert, q,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    using ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_forward p t s
      (ctrl t s v)

/-- Every row other than the selected original row is retained verbatim. -/
theorem insert_other_row (s : S p) (v : V p) (j : Fin (M p))
    (hj : j ≠ q s) : (insert t s v).1.2 j = s.1.2 j := by
  simp [insert, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex, hj]

/-- Every selected-row time cell other than t is retained, including future
cells after the insertion time. -/
theorem insert_other_time (s : S p) (v : V p) (r : Fin p.T)
    (hr : r ≠ t) : ((insert t s v).1.2 (q s)).2 r = (s.1.2 (q s)).2 r := by
  simp only [insert, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    q, Function.update_self]
  exact Function.update_of_ne hr _ _

/-- All non-assignment scalar labels at the current cell are unchanged. -/
theorem insert_nonAssignmentScalars (s : S p) (v : V p)
    (label : NonAssignmentLabel p) :
    (c t (insert t s v)).1 label.val = (c t s).1 label.val := by
  rw [currentControl_insert]
  change ((e p) (ctrl t s v)).2.1 label = ((e p) (c t s)).2.1 label
  exact congrArg (fun z => z.2.1 label) (controlAssignmentSplit_ctrl t s v)

/-- Every affine sample at the current cell is unchanged. -/
theorem insert_affineSamples (s : S p) (v : V p) :
    (c t (insert t s v)).2 = (c t s).2 := by
  rw [currentControl_insert]
  change ((e p) (ctrl t s v)).2.2 = ((e p) (c t s)).2.2
  rw [controlAssignmentSplit_ctrl]

/-- The original selected-row assignment vector is the first coordinate of
the split current control. -/
theorem av_eq_controlSplit (s : S p) : av t s = ((e p) (c t s)).1 := rfl

private theorem record_source_fields_of_launch
    (source : S p) (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ completeSuffixRecords rate source rewards C_star C_h) :
    record.input.rows = source.1.2 ∧
      record.input.selected = q source ∧ record.input.rewards = rewards := by
  have hstart := physicalStart_le_T rate source rewards C_star C_h
  let start := physicalStart rate source rewards C_star C_h
  have hspan : start + (p.T - start) ≤ p.T := by
    dsimp [start]
    omega
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate source rewards C_star C_h active hlaunch
  have hrun : record ∈ (ReferenceActivePhysicalHorizon.run active source.1.2
      (q source) rewards start (p.T - start) hspan hmode).records := by
    rw [← completeSuffixRecords_on_launch rate source rewards C_star C_h active hlaunch]
    exact hrecord
  exact ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
    (q source) rewards start (p.T - start) hspan hmode record hrun

private theorem completeSuffixRecord_time_at
    (source : S p) (n : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : (completeSuffixRecords rate source rewards C_star C_h)[n]? = some record) :
    record.input.time.val = physicalStart rate source rewards C_star C_h + n := by
  have hn : n < p.T - physicalStart rate source rewards C_star C_h := by
    obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hrecord
    simpa only [completeSuffixRecords_length] using hn
  have htimes := congrArg (fun l : List ℕ => l[n]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h)
  rw [List.getElem?_map, hrecord] at htimes
  simp only [Option.map_some, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range' hn, Nat.one_mul] at htimes
  exact Option.some.inj htimes

private theorem roundInput_eq_of_fields
    (a b : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : a.state = b.state) (hrows : a.rows = b.rows)
    (hselected : a.selected = b.selected) (htime : a.time = b.time)
    (hrewards : a.rewards = b.rewards) : a = b := by
  cases a with
  | mk stateA rowsA selectedA timeA activeA rewardsA =>
    cases b with
    | mk stateB rowsB selectedB timeB activeB rewardsB =>
      simp only at hstate hrows hselected htime hrewards
      subst stateB
      subst rowsB
      subst selectedB
      subst timeB
      subst rewardsB
      have hactive : activeA = activeB := Subsingleton.elim _ _
      subst activeB
      rfl

private theorem updated_record_input_eq
    (source : S p) (v : V p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h source = some (u, (t, theta)))
    (a b : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ha : a ∈ completeSuffixRecords rate source rewards C_star C_h)
    (hb : b ∈ completeSuffixRecords rate
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        source t (suffix t source v)) rewards C_star C_h)
    (hstate : a.input.state = b.input.state)
    (hta : a.input.time = t) (htb : b.input.time = t) :
    b.input = ReferenceLaterAssignmentFibreStep.withAssignment a.input v := by
  let suffix0 := suffix t source v
  let changed := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
    source t suffix0
  obtain ⟨active, hlaunch, _, _, hlaunchChanged⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_launch_of_firstCollectionCall
      rate rewards C_star C_h source u t theta suffix0 hcall
  have hfieldsA := record_source_fields_of_launch rate rewards C_star C_h
    source active hlaunch a ha
  have hfieldsB := record_source_fields_of_launch rate rewards C_star C_h
    changed active hlaunchChanged b (by simpa [changed] using hb)
  have hrowA : a.input.row = source.1.2 (q source) := by
    simp [ReferenceActivePhysicalStep.RoundInput.row, hfieldsA.1, hfieldsA.2.1]
  have hcontrol : ctrl t source v =
      ReferenceLaterAssignmentFibreStep.controlWithAssignment a.input v := by
    dsimp only [ctrl, c, q, ReferenceLaterAssignmentFibreStep.controlWithAssignment]
    rw [hrowA, hta]
  have hselectedRow : changed.1.2 (q source) =
      ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v := by
    apply Prod.ext
    · have hforward : (changed.1.2 (q source)).1 = (source.1.2 (q source)).1 := by
        simpa only [q] using
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
            source t suffix0
      calc
        (changed.1.2 (q source)).1 = (source.1.2 (q source)).1 := hforward
        _ = a.input.row.1 := congrArg Prod.fst hrowA.symm
        _ = (ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v).1 :=
          (ReferenceLaterAssignmentFibreStep.rowWithAssignment_arrays a.input v).symm
    · funext r
      by_cases hbefore : r.val < t.val
      · have hne : r ≠ t := by
          intro h
          subst r
          omega
        rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
          source t r suffix0 hbefore]
        simp [ReferenceLaterAssignmentFibreStep.rowWithAssignment,
          ReferenceLaterAssignmentFibreStep.controlWithAssignment, hta, hrowA,
          Function.update_of_ne hne]
      · have hafter : t.val ≤ r.val := Nat.le_of_not_gt hbefore
        rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
          source t r suffix0 hafter]
        simp [suffix0, suffix, ReferenceLaterAssignmentFibreStep.rowWithAssignment,
          ReferenceLaterAssignmentFibreStep.controlWithAssignment, hta, hrowA, hcontrol]
  have hrows : b.input.rows =
      (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).rows := by
    funext j
    by_cases hj : j = q source
    · subst j
      calc
        b.input.rows (q source) = changed.1.2 (q source) := by rw [hfieldsB.1]
        _ = ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v := hselectedRow
        _ = (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).rows
            (q source) := by
          change ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v =
            Function.update a.input.rows a.input.selected
              (ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v) (q source)
          rw [hfieldsA.2.1, Function.update_self]
    · calc
        b.input.rows j = changed.1.2 j := by rw [hfieldsB.1]
        _ = source.1.2 j :=
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
            source t suffix0 j hj
        _ = (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).rows j := by
          change source.1.2 j = Function.update a.input.rows a.input.selected
            (ReferenceLaterAssignmentFibreStep.rowWithAssignment a.input v) j
          rw [hfieldsA.1, hfieldsA.2.1, Function.update_of_ne hj]
  have hselected : b.input.selected =
      (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).selected := by
    calc
      b.input.selected = q changed := hfieldsB.2.1
      _ = q source := by
        simpa only [q] using
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_selected
            source t suffix0
      _ = a.input.selected := hfieldsA.2.1.symm
      _ = (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).selected := rfl
  have htime : b.input.time =
      (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).time := by
    calc
      b.input.time = t := htb
      _ = a.input.time := hta.symm
      _ = (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).time := rfl
  have hrewards : b.input.rewards =
      (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).rewards := by
    calc
      b.input.rewards = rewards := hfieldsB.2.2
      _ = a.input.rewards := hfieldsA.2.2.symm
      _ = (ReferenceLaterAssignmentFibreStep.withAssignment a.input v).rewards := rfl
  exact roundInput_eq_of_fields rate b.input
    (ReferenceLaterAssignmentFibreStep.withAssignment a.input v)
    hstate.symm hrows hselected htime hrewards

/-- An actual first collection call has its inserted complete vector in the
actual updated record, whose input is exactly the existing sampler update. -/
theorem actual_call_vector_insertion (z : Z rate rewards C_star C_h u t)
    (v : V p) :
    ∃ (n : ℕ) (a b : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)),
      (completeSuffixRecords rate z.val rewards C_star C_h)[n]? = some a ∧
      (completeSuffixRecords rate (put rate rewards C_star C_h u t z v).val
        rewards C_star C_h)[n]? = some b ∧
      a.input.time = t ∧
      b.input = ReferenceLaterAssignmentFibreStep.withAssignment a.input v ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt b =
        some (u, renewalCallParameter rate rewards C_star C_h u t z) ∧
      LaterAssignmentStartOperation.ownAssignmentVector b.input.row b.input.time = v := by
  let suffix0 := suffix t z.val v
  have hcall := firstCollectionCall_eq rate rewards C_star C_h u t z
  obtain ⟨nCall, original, hOriginal, htimeOriginal, hlocalOriginal, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z)).mp hcall
  obtain ⟨n, hcalendar, hindexed⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_records_of_firstCollectionCall
      rate rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z) suffix0 hcall
  have htimeIndex := completeSuffixRecord_time_at rate rewards C_star C_h
    z.val nCall original hOriginal
  have hcalendarCall : physicalStart rate z.val rewards C_star C_h + nCall = t.val := by
    have htimeVal := congrArg Fin.val htimeOriginal
    omega
  have hnCall : nCall = n := by omega
  subst nCall
  obtain ⟨a, b, ha, hb, hstate, htimeAB⟩ := hindexed n (by omega)
  have haOriginal : a = original := Option.some.inj (ha.symm.trans hOriginal)
  have hta : a.input.time = t := by rw [haOriginal]; exact htimeOriginal
  have htb : b.input.time = t := htimeAB.symm.trans hta
  have hcallA : ReferenceFirstCollectionSamplerCall.collectionCallAt a =
      some (u, renewalCallParameter rate rewards C_star C_h u t z) := by
    rw [haOriginal]
    exact hlocalOriginal
  have hcalls := ReferenceFirstCollectionSamplerCall.collectionCallOnInput_eq_of_state_eq_time_eq
    a.input b.input hstate htimeAB
  have hcallB : ReferenceFirstCollectionSamplerCall.collectionCallAt b =
      some (u, renewalCallParameter rate rewards C_star C_h u t z) := by
    have hcallInputA : ReferenceFirstCollectionSamplerCall.collectionCallOnInput a.input =
        some (u, renewalCallParameter rate rewards C_star C_h u t z) := by
      simpa only [ReferenceFirstCollectionSamplerCall.collectionCallAt] using hcallA
    have hcallInputB := hcalls.symm.trans hcallInputA
    simpa only [ReferenceFirstCollectionSamplerCall.collectionCallAt] using hcallInputB
  have hinput := updated_record_input_eq rate rewards C_star C_h u t z.val v
    (renewalCallParameter rate rewards C_star C_h u t z) hcall a b
    (List.mem_of_getElem? ha) (by simpa [suffix0] using (List.mem_of_getElem? hb))
    hstate hta htb
  have hbPut : (completeSuffixRecords rate
      (put rate rewards C_star C_h u t z v).val rewards C_star C_h)[n]? = some b := by
    rw [put_val, insert_eq_replaceSelectedControlSuffix]
    exact hb
  have hvector : LaterAssignmentStartOperation.ownAssignmentVector
      b.input.row b.input.time = v := by
    rw [hinput, ReferenceLaterAssignmentFibreStep.withAssignment_row]
    exact ReferenceLaterAssignmentFibreStep.ownAssignmentVector_rowWithAssignment a.input v
  exact ⟨n, a, b, ha, hbPut, hta, hinput, hcallB, hvector⟩

/-- Under the original renewal extension, inserting its sampled whole vector
produces an actual ActualRenewalCall whose real current vector is that
sample, and whose exact selected-sampler outcome is the retained auxiliary
draw. -/
theorem ae_renewalLiftLaw_inserted_sampler :
    ∀ᵐ wv : W rate rewards C_star C_h u t ∂
      Lambda rate rewards C_star C_h u t,
      ∃ d : ActualRenewalCall rate rewards C_star C_h u t
          (put rate rewards C_star C_h u t wv.1.1 wv.2),
        LaterAssignmentStartOperation.ownAssignmentVector
          d.record.input.row d.instruction.time = wv.2 ∧
        AssignmentParameterFibreKernel.successfulSlowSet p
          (LaterAssignmentStartMeasurability.selectedSamplerParameters d.old
            (CoordinatorRoundDispatch.collectionOperationLedger
              (collectionView rate u d.record.input d.old d.ledger d.saved)
              d.core.payload_n_eq)
            d.instruction d.out d.reconstruction_eq)
          (LaterAssignmentStartOperation.ownAssignmentVector
            d.record.input.row d.instruction.time) =
          some (renewalAuxiliarySample rate rewards C_star C_h u t
            (put rate rewards C_star C_h u t wv.1.1 wv.2) wv.1.2) := by
  filter_upwards [ReferenceFirstCollectionRenewalPastLocality.ae_renewalLiftLaw_actual_call_and_outcome
      rate rewards C_star C_h u t] with wv h
  let sourceSubtype := wv.1.1
  let vector := wv.2
  let suffix0 := suffix t sourceSubtype.val vector
  have hcall := firstCollectionCall_eq rate rewards C_star C_h u t sourceSubtype
  obtain ⟨a, b, old, ledger, saved, ha, hb, hta, htb, hstate, hca, hcb,
      hcut, hfreeze, started, coreA, coreB, instruction, hclockA, hclockB,
      hinstruction, hinstructionTime, hrenewal, out, hrecA, hrecB,
      hparameterA, hparameterB⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_renewal_reconstruction_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t sourceSubtype suffix0
  have hinput := updated_record_input_eq rate rewards C_star C_h u t
    sourceSubtype.val vector (renewalCallParameter rate rewards C_star C_h u t sourceSubtype)
    hcall a b ha hb hstate hta htb
  have hvector : LaterAssignmentStartOperation.ownAssignmentVector
      b.input.row b.input.time = vector := by
    rw [hinput, ReferenceLaterAssignmentFibreStep.withAssignment_row]
    exact ReferenceLaterAssignmentFibreStep.ownAssignmentVector_rowWithAssignment a.input vector
  have hmemB : b ∈ completeSuffixRecords rate
      (put rate rewards C_star C_h u t sourceSubtype vector).val rewards C_star C_h := by
    simpa only [put_val, insert_eq_replaceSelectedControlSuffix] using hb
  let d : ActualRenewalCall rate rewards C_star C_h u t
      (put rate rewards C_star C_h u t sourceSubtype vector) := {
    record := b
    record_mem := hmemB
    time_eq := htb
    old := old
    ledger := ledger
    saved := saved
    coordinator_eq := hcb
    cutoff_eq := hcut
    freeze_le := hfreeze
    started := started
    clock_eq := hclockB
    core := coreB
    instruction := instruction
    instruction_eq := hinstruction
    instruction_time := hinstructionTime.trans htb.symm
    renewal := hrenewal
    out := out
    reconstruction_eq := hrecB
    parameter_eq := by
      change renewalCallParameter rate rewards C_star C_h u t
          (renewalSourceWithSuffix rate rewards C_star C_h u t sourceSubtype suffix0) =
        LaterAssignmentStartMeasurability.selectedSamplerParameters old
          (CoordinatorRoundDispatch.collectionOperationLedger
            (collectionView rate u b.input old ledger saved) coreB.payload_n_eq)
          instruction out hrecB
      exact hparameterB
  }
  have hvectorD : LaterAssignmentStartOperation.ownAssignmentVector
      d.record.input.row d.instruction.time = vector := by
    rw [d.instruction_time]
    exact hvector
  have hrealize := h suffix0
  rcases hrealize with ⟨_, _, _, houtcome⟩
  refine ⟨d, hvectorD, ?_⟩
  rw [← d.parameter_eq, hvectorD]
  simpa only [put, suffix0, suffix] using houtcome

end Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion

end
