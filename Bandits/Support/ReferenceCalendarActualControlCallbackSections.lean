/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCalendarLaterSamplerPredictability

/-!
# Actual calendar codes under whole current-control replacement

The callback retains the actual physical record code after replacing the
complete current control in the original round input. The section law uses
the original-source successor-prefix field and integrates the whole
`TimeControl` law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceCalendarActualControlCallbackSections

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual optional physical record code at calendar date `t`. -/
def codeAt (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode

/-- The physical code of the original round input with its whole current
control replaced by `c`. -/
def controlCallback
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) :=
  let x := ReferenceLaterOptionalControlResampling.withControl r.input c
  ReferenceActiveHorizonMeasurability.roundRecordCode
    (show ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) from
      { input := x, output := ReferenceActivePhysicalStep.step x, output_eq := rfl })

/-- Integrate the callback code over the complete current control. The absent
record branch remains the original `none` tag. -/
def callbackSection (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => ∫ c, B.indicator (fun _ => (1 : ℝ)) (none, c)
      ∂ContinuousLearningRows.timeControlLaw p
  | some r => ∫ c, B.indicator (fun _ => (1 : ℝ))
      (some (controlCallback rate r c), c)
      ∂ContinuousLearningRows.timeControlLaw p

private theorem actualRecord_input_fields (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  · obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
    have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
      rate rewards C_star C_h _ ⟨z, hk⟩
    dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
      List.get_eq_getElem] at hf
    rw [hrecord] at hf
    have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h
    have hk' : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h < p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h := by
      simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
    have hget := congrArg (fun l : List ℕ => l[t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?) ht
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
      List.getElem?_range' hk', Nat.one_mul] at hget
    rw [List.getElem?_eq_getElem hk, hrecord] at hget
    apply And.intro hf.1
    apply And.intro hf.2.1
    apply And.intro
    · apply Fin.ext
      have hv := Option.some.inj hget
      simpa only [Nat.add_sub_of_le hs] using hv
    · exact hf.2.2.1

private theorem replaceSourceControl_selectedRowIndex
    (t : Fin p.T) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) =
      ActualInitializationPhysicalStep.selectedRowIndex p source := by
  rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c),
    ← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p source]
  rfl

private theorem sourcePrefix_replaceCurrent_eq
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  calc
    _ = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
      ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
        control0 t (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c
    _ = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z :=
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val t.val le_rfl z

private theorem replacement_source_current
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t = c := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  have hidx : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref =
      ActualInitializationPhysicalStep.selectedRowIndex p z := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
  change ((Function.update pref.1.2
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)
      ((pref.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)).1,
        Function.update (pref.1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)).2 t c))
      (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t = c
  simp [hidx]

private theorem replacement_source_past
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) (v : Fin p.T)
    (hv : v.val < t.val) :
    (((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1
        ContinuousControlSlice.Label.prop =
      ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1
        ContinuousControlSlice.Label.prop := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  have hidx : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref =
      ActualInitializationPhysicalStep.selectedRowIndex p z := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
  have hvt : v ≠ t := by
    intro heq
    subst v
    omega
  change (((Function.update pref.1.2
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)
      ((pref.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)).1,
        Function.update (pref.1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref)).2 t c))
      (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1
        ContinuousControlSlice.Label.prop = _
  simp [pref, hidx,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hv,
    Function.update_of_ne hvt]

private theorem incoming_eq_of_current_replacement
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t pref c
  have hpref : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val replaced = pref := by
    simpa only [pref, replaced] using sourcePrefix_replaceCurrent_eq control0 t z c
  calc
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t pref :=
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t z
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val replaced) := by
      rw [hpref]
    _ = _ := (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
      control0 t replaced).symm

private theorem actualRecord_none_of_incoming_none
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z = none) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => rfl
  | some r =>
      rw [ReferenceSourcePrefixHistoryFiltration.incoming, hr] at hin
      simp at hin

private theorem roundRecordCode_eq_step
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        (show ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) from
          { input := r.input, output := ReferenceActivePhysicalStep.step r.input,
            output_eq := rfl }) := by
  cases r with
  | mk input output houtput =>
      cases houtput
      rfl

/-- Borel measurability of the original optional record code. -/
theorem measurable_codeAt (t : Fin p.T) :
    Measurable (codeAt rate rewards C_star C_h t) := by
  have h := ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
    rate rewards C_star C_h p.T (Nat.le_refl p.T)
  have hcoord := (measurable_pi_iff.mp h) t
  have heq :
      (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceInspectedPastRoundObservations.pastRoundObservations
          rate rewards C_star C_h p.T (Nat.le_refl p.T) z t) =
      codeAt rate rewards C_star C_h t := by
    funext z
    rfl
  rw [heq] at hcoord
  exact hcoord

/-- The date-`t` code depends on the original source through the end of
calendar round `t`, including all absent and terminal-launch cases. -/
theorem codeAt_successor_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    codeAt rate rewards C_star C_h t z =
      codeAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  let z' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
        ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
          control0 t z
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z') := by
        rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
          control0 t.val (t.val + 1) (by omega) z]
      _ = _ := (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t z').symm
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
      have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' = none := by
        have hinc' : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' = none := by
          calc
            _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := hin.symm
            _ = none := by simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
        exact actualRecord_none_of_incoming_none rate rewards C_star C_h t z' hinc'
      simp only [codeAt, z', hr, hr', Option.map_none]
  | some r =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
      | none =>
          have hleft : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
              some (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
          have hright : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' = none := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr']
          rw [hleft, hright] at hin
          have hinc := hin
          simp at hinc
      | some r' =>
          have hencoded :
              ReferenceActivePhysicalStepMeasurability.encodeState r.input.state =
                ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state := by
            have hleft : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
                some (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) := by
              simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
            have hright : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' =
                some (ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state) := by
              simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr']
            rw [hleft, hright] at hin
            exact Option.some.inj hin
          have hstate : r.input.state = r'.input.state := by
            simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
              using congrArg ReferenceActivePhysicalStepMeasurability.decodeState hencoded
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t z' r' hr'
          have hsel : ActualInitializationPhysicalStep.selectedRowIndex p z' =
              ActualInitializationPhysicalStep.selectedRowIndex p z := by
            exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected
              control0 (t.val + 1) z).symm
          have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
            simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
              hselected, hselected', htime, htime']
            rw [hsel, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
            simp
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
                (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            rw [htime] at hv
            simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
              hselected, hselected', hsel]
            rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
            simp [Nat.lt_succ_of_lt hv]
          have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
            r.input r'.input hstate (by rw [hselected, hselected', hsel])
            (htime.trans htime'.symm) (hrewards.trans hrewards'.symm) hcurrent hpast
          have hrecordCode : ReferenceActiveHorizonMeasurability.roundRecordCode r =
              ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
            calc
              ReferenceActiveHorizonMeasurability.roundRecordCode r =
                  ReferenceActiveHorizonMeasurability.roundRecordCode
                    (show ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) from
                      { input := r.input, output := ReferenceActivePhysicalStep.step r.input,
                        output_eq := rfl }) := roundRecordCode_eq_step rate r
              _ = ReferenceActiveHorizonMeasurability.roundRecordCode
                    (show ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) from
                      { input := r'.input, output := ReferenceActivePhysicalStep.step r'.input,
                        output_eq := rfl }) := hcode
              _ = ReferenceActiveHorizonMeasurability.roundRecordCode r' :=
                    (roundRecordCode_eq_step rate r').symm
          simpa only [codeAt, z', hr, hr', Option.map_some] using congrArg some hrecordCode

/-- The actual record after replacing its current whole control has the
callback code of the original physical input with exactly that replacement. -/
theorem actual_control_callback (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (c : ContinuousLearningRows.TimeControl p) :
    codeAt rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) =
      some (controlCallback rate r c) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t pref c
  have hin := incoming_eq_of_current_replacement rate rewards C_star C_h control0 t z c
  cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
  | none =>
      have hleft : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
          some (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) := by
        simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
      have hright : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' = none := by
        simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr']
      rw [hleft, hright] at hin
      simp at hin
  | some r' =>
      have hencoded :
          ReferenceActivePhysicalStepMeasurability.encodeState r.input.state =
            ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state := by
        have hleft : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
            some (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) := by
          simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
        have hright : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' =
            some (ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state) := by
          simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr']
        rw [hleft, hright] at hin
        exact Option.some.inj hin
      have hstate : r'.input.state = r.input.state := by
        simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
          using congrArg ReferenceActivePhysicalStepMeasurability.decodeState hencoded.symm
      obtain ⟨hrows, hselected, htime, hrewards⟩ :=
        actualRecord_input_fields rate rewards C_star C_h t z r hr
      obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
        actualRecord_input_fields rate rewards C_star C_h t z' r' hr'
      have hselpref : ActualInitializationPhysicalStep.selectedRowIndex p pref =
          ActualInitializationPhysicalStep.selectedRowIndex p z :=
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected control0 t.val z
      have hsel' : ActualInitializationPhysicalStep.selectedRowIndex p z' =
          ActualInitializationPhysicalStep.selectedRowIndex p z := by
        exact (replaceSourceControl_selectedRowIndex t pref c).trans hselpref
      have hselected'': r'.input.selected = r.input.selected := by
        calc
          r'.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z' := hselected'
          _ = ActualInitializationPhysicalStep.selectedRowIndex p z := hsel'
          _ = r.input.selected := hselected.symm
      have htime'': r'.input.time = r.input.time := htime'.trans htime.symm
      have hrewards'': r'.input.rewards = r.input.rewards := hrewards'.trans hrewards.symm
      have hcurrent : r'.input.row.2 r'.input.time =
          (ReferenceLaterOptionalControlResampling.withControl r.input c).row.2
            (ReferenceLaterOptionalControlResampling.withControl r.input c).time := by
        rw [htime', ReferenceLaterOptionalControlResampling.withControl_time,
          htime]
        change ((r'.input.rows r'.input.selected).2 t) =
          ((ReferenceLaterOptionalControlResampling.withControl r.input c).row.2 t)
        rw [hrows', hselected', hsel', replacement_source_current control0 t z c]
        simp [ReferenceLaterOptionalControlResampling.withControl_row, htime]
      have hpast : ∀ v : Fin p.T, v.val < r'.input.time.val →
          (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop =
            ((ReferenceLaterOptionalControlResampling.withControl r.input c).row.2 v).1
              ContinuousControlSlice.Label.prop := by
        intro v hv
        have hv' : v.val < t.val := by rw [htime'] at hv; exact hv
        have hvne : v ≠ r.input.time := by
          intro h
          rw [h, htime] at hv'
          exact (Nat.lt_irrefl _) hv'
        change ((r'.input.rows r'.input.selected).2 v).1
            ContinuousControlSlice.Label.prop =
          ((ReferenceLaterOptionalControlResampling.withControl r.input c).row.2 v).1
            ContinuousControlSlice.Label.prop
        rw [hrows', hselected', hsel',
          replacement_source_past control0 t z c v hv']
        rw [ReferenceLaterOptionalControlResampling.withControl_otherTime r.input c v hvne]
        change ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1
            ContinuousControlSlice.Label.prop =
          ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop
        rw [hrows, hselected]
      have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
        r'.input (ReferenceLaterOptionalControlResampling.withControl r.input c)
        hstate hselected'' htime'' hrewards'' hcurrent hpast
      have hrecordCode : ReferenceActiveHorizonMeasurability.roundRecordCode r' =
          controlCallback rate r c := by
        calc
          ReferenceActiveHorizonMeasurability.roundRecordCode r' =
              ReferenceActiveHorizonMeasurability.roundRecordCode
                (show ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) from
                  { input := r'.input, output := ReferenceActivePhysicalStep.step r'.input,
                    output_eq := rfl }) := roundRecordCode_eq_step rate r'
          _ = controlCallback rate r c := by
            simpa only [controlCallback] using hcode
      simp only [codeAt, z', pref, hr', Option.map_some, hrecordCode]

private theorem callbackSection_eq_sourceIntegral (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    callbackSection rate rewards C_star C_h t B z =
      ∫ c, B.indicator (fun _ => (1 : ℝ))
        (codeAt rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c)
        ∂ContinuousLearningRows.timeControlLaw p := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
      have hnone (c : ContinuousLearningRows.TimeControl p) :
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) = none := by
        have hinc' : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) = none := by
          calc
            _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z :=
              (incoming_eq_of_current_replacement rate rewards C_star C_h control0 t z c).symm
            _ = none := by simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
        exact actualRecord_none_of_incoming_none rate rewards C_star C_h t _ hinc'
      simp only [callbackSection, hr]
      apply integral_congr_ae
      filter_upwards with c
      simp [codeAt, hnone c]
  | some r =>
      simp only [callbackSection, hr]
      apply integral_congr_ae
      filter_upwards with c
      have hc := actual_control_callback rate rewards C_star C_h control0 t z r hr c
      rw [hc]

/-- Conditional expectation of the actual code/control test, given the
original-source pre-choice successor field. -/
theorem codeAt_controlSection_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (codeAt rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z))
        | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      callbackSection rate rewards C_star C_h t B := by
  let B' : Set (BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p) :=
    {x | (codeAt rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2), x.2) ∈ B}
  have hreplace := ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t
  have hcode : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p =>
        codeAt rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) :=
    (measurable_codeAt rate rewards C_star C_h t).comp hreplace
  have hpair : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p =>
        (codeAt rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2), x.2)) :=
    hcode.prodMk measurable_snd
  have hB' : MeasurableSet B' := hpair hB
  have htest :
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B' =
        (fun z => B.indicator (fun _ => (1 : ℝ))
          (codeAt rate rewards C_star C_h t z,
            ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
    funext z
    rw [ReferenceSourceCurrentControlFreshness.sourceControlTest,
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    have hrestore := ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore
      control0 t z
    have hcurrent : ReferenceSourceCurrentControlFreshness.u_t p t z =
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t) := rfl
    have hcode' : codeAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (ReferenceSourceCurrentControlFreshness.u_t p t z)) =
          codeAt rate rewards C_star C_h t z := by
      rw [hcurrent, ← hrestore]
      exact (codeAt_successor_factor rate rewards C_star C_h control0 t z).symm
    simp [B', Set.indicator, hcode']
  have hsection :
      (fun z => ∫ c, B'.indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c)
        ∂ContinuousLearningRows.timeControlLaw p) =
        callbackSection rate rewards C_star C_h t B := by
    funext z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    exact (callbackSection_eq_sourceIntegral rate rewards C_star C_h t B control0 z).symm
  have hcond := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t B' hB'
  rw [← htest, ← hsection]
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
    using hcond

/-- The callback section is strongly measurable in the exact successor
source-prefix filtration. -/
theorem callbackSection_stronglyMeasurable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (callbackSection rate rewards C_star C_h t B) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
  let G : BootstrapPrivateRoundStreams.SourceInput p → ℝ := fun s =>
    ∫ c, B.indicator (fun _ => (1 : ℝ))
      (codeAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c), c)
      ∂ContinuousLearningRows.timeControlLaw p
  have hreplace := ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t
  have hcode : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p =>
        codeAt rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) :=
    (measurable_codeAt rate rewards C_star C_h t).comp hreplace
  have hpair : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p =>
        (codeAt rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2), x.2)) :=
    hcode.prodMk measurable_snd
  have hfun : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p =>
        B.indicator (fun _ => (1 : ℝ))
          (codeAt rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2), x.2)) :=
    (measurable_const.indicator hB).comp hpair
  have hG : StronglyMeasurable G := by
    dsimp [G]
    exact hfun.stronglyMeasurable.integral_prod_right'
      (ν := ContinuousLearningRows.timeControlLaw p)
  have hpref : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] pref := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ control0 t.val]
    exact comap_measurable pref
  have hcomp : StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => G (pref z)) := hG.comp_measurable hpref
  have hfactor : (callbackSection rate rewards C_star C_h t B) = fun z => G (pref z) := by
    funext z
    exact callbackSection_eq_sourceIntegral rate rewards C_star C_h t B control0 z
  rw [hfactor]
  exact hcomp

/-- The original-control section is a probability average of indicators. -/
theorem callbackSection_bounds (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ callbackSection rate rewards C_star C_h t B z ∧
      callbackSection rate rewards C_star C_h t B z ≤ 1 := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
      simp only [callbackSection, hr]
      let f : ContinuousLearningRows.TimeControl p → ℝ := fun c =>
        B.indicator (fun _ => (1 : ℝ)) (none, c)
      have hmeas : Measurable f := by
        exact (measurable_const.indicator hB).comp (measurable_const.prodMk measurable_id)
      have hint : Integrable f (ContinuousLearningRows.timeControlLaw p) := by
        have hbound : ∀ c, ‖f c‖ ≤ 1 := by
          intro c
          by_cases hc : (none, c) ∈ B <;> simp [f, Set.indicator, hc]
        exact (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hbound)
      have hnonneg : ∀ c, 0 ≤ f c := by
        intro c
        by_cases hc : (none, c) ∈ B <;> simp [f, Set.indicator, hc]
      constructor
      · exact integral_nonneg hnonneg
      · calc
          (∫ c, f c ∂ContinuousLearningRows.timeControlLaw p) ≤
              ∫ _ : ContinuousLearningRows.TimeControl p, (1 : ℝ)
                ∂ContinuousLearningRows.timeControlLaw p := by
            apply integral_mono hint (integrable_const (1 : ℝ))
            intro c
            by_cases hc : (none, c) ∈ B <;> simp [f, Set.indicator, hc]
          _ = 1 := by simp
  | some r =>
      simp only [callbackSection, hr]
      let control0 := ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t)
      let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
      let f : ContinuousLearningRows.TimeControl p → ℝ := fun c =>
        B.indicator (fun _ => (1 : ℝ))
          (some (controlCallback rate r c), c)
      have hreplace := ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t
      have hreplacement : Measurable (fun c : ContinuousLearningRows.TimeControl p =>
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t pref c) :=
        hreplace.comp (measurable_const.prodMk measurable_id)
      have hcode : Measurable (fun c : ContinuousLearningRows.TimeControl p =>
          codeAt rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t pref c)) :=
        (measurable_codeAt rate rewards C_star C_h t).comp hreplacement
      have hpair : Measurable (fun c : ContinuousLearningRows.TimeControl p =>
          (some (controlCallback rate r c), c)) := by
        have heq : (fun c : ContinuousLearningRows.TimeControl p =>
            (some (controlCallback rate r c), c)) =
            (fun c => (codeAt rate rewards C_star C_h t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t pref c), c)) := by
          funext c
          exact Prod.ext (actual_control_callback rate rewards C_star C_h
            control0 t z r hr c).symm rfl
        rw [heq]
        exact hcode.prodMk measurable_id
      have hmeas : Measurable f := (measurable_const.indicator hB).comp hpair
      have hint : Integrable f (ContinuousLearningRows.timeControlLaw p) := by
        have hbound : ∀ c, ‖f c‖ ≤ 1 := by
          intro c
          by_cases hc : (some (controlCallback rate r c), c) ∈ B <;>
            simp [f, Set.indicator, hc]
        exact (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hbound)
      have hnonneg : ∀ c, 0 ≤ f c := by
        intro c
        by_cases hc : (some (controlCallback rate r c), c) ∈ B <;>
          simp [f, Set.indicator, hc]
      constructor
      · exact integral_nonneg hnonneg
      · calc
          (∫ c, f c ∂ContinuousLearningRows.timeControlLaw p) ≤
              ∫ _ : ContinuousLearningRows.TimeControl p, (1 : ℝ)
                ∂ContinuousLearningRows.timeControlLaw p := by
            apply integral_mono hint (integrable_const (1 : ℝ))
            intro c
            by_cases hc : (some (controlCallback rate r c), c) ∈ B <;>
              simp [f, Set.indicator, hc]
          _ = 1 := by simp

/-- Integrability follows from the measurable original-source section and
its pointwise unit bound. -/
theorem callbackSection_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B : Set (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    Integrable (callbackSection rate rewards C_star C_h t B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hfield : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1) ≤
        (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hsm := callbackSection_stronglyMeasurable rate rewards C_star C_h control0 t B hB
  have hsm' : StronglyMeasurable (callbackSection rate rewards C_star C_h t B) := hsm.mono hfield
  have hmeas : Measurable (callbackSection rate rewards C_star C_h t B) := hsm'.measurable
  have hbound : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      ‖callbackSection rate rewards C_star C_h t B z‖ ≤ 1 := by
    intro z
    have hb := callbackSection_bounds rate rewards C_star C_h t B hB z
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  exact (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end Bandits.Support.ReferenceCalendarActualControlCallbackSections

end
