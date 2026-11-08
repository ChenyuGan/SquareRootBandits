/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverBeforeDownService
public import Bandits.Support.ReferenceFirstLiveHandoverNoGateStopMask

/-!
# Actual first-handover pending stage partition

Every pending follower in the original stopped first-handover support belongs
at each actual live record to exactly one of the literal before-acceptance and
after-acceptance sections. The source events retain the original full source,
physical records, selected assignment, and strict stop mask.

Sources: ZIP4 05_binary_transport.tex:253-281 and
06_interruptions.tex:431-490.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
open Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverPendingStagePartition

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "W" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
  rate rewards C_star C_h
local notation "P" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
  rate rewards C_star C_h

private theorem window_crossing (z : SourceInput p)
    (hW : 0 < (W z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hlaunch] at hW
      simp at hW
  | some active =>
      apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp
      simp [hlaunch]

private theorem before_after_not_both
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (i : Fin (p.m - 1)) :
    ¬ (Before (rate := rate) r i ∧ After (rate := rate) r selected i) := by
  rintro ⟨⟨s₁, memory₁, h₁, hnone⟩, ⟨s₂, memory₂, h₂, hsome⟩⟩
  have hstate := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (h₁.symm.trans h₂)
  rcases hstate with ⟨rfl, rfl⟩
  have hcontra := hnone.symm.trans hsome
  cases hcontra

/-- The actual first-live record has its retained selection and initial
payload, and every follower is in exactly one of the two source-defined
confirmation stages. -/
theorem source_window_stage_partition
    (z : SourceInput p)
    (k : Fin (W z).length) :
    let r := (W z)[k.val]
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r = some selected ∧
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z =
        some selected.view.payload ∧
      ∀ i : Fin (p.m - 1),
        (Before (rate := rate) r i ∨ After (rate := rate) r selected i) ∧
        ¬ (Before (rate := rate) r i ∧ After (rate := rate) r selected i) := by
  classical
  dsimp only
  let hcross := window_crossing rate rewards C_star C_h z (by
    have hk := k.isLt
    omega)
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hcross
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - start
  have hstart : start ≤ p.T := by
    simpa only [start, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : start + count ≤ p.T := by dsimp [count]; omega
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hcross
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate z rewards C_star C_h initial hlaunch
  let execution := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count hspan hmode
  let runWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  have hcomplete := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hlaunch
  have hwindow : W z = runWindow := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) = _
    rw [hcomplete]
  have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro j state memory hconfiguration
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hconfiguration.symm.trans (seed.configuration j))
    exact ⟨by rw [heq.1]; exact seed.unoccupied j,
      by rw [heq.1]; exact seed.lastDown_none j⟩
  have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    start count hspan hmode seed.coordinatorFirst hinitial
  have hsafety := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    start count hspan hmode seed.coordinatorFirst seed.followers seed.memory
    seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none
    seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hprov := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
    rate rewards C_star C_h z hcross
  rcases hprov with hzero | ⟨hpositive, firstInstalled, firstSelected,
      hfirstSelected, hinitialInstall, hfirstPayload, hinitialPending,
      hinitialPayload, hrows⟩
  · have hk := k.isLt
    simp only [hzero] at hk
    omega
  · have hrow := hrows k
    dsimp only at hrow
    rcases hrow with ⟨selected, hselected, hpayload, hphaseRun,
      next, nextOwned, nextBase, hnext, hnextPayload, hnextPending, hfail, hfollowers⟩
    let r := (W z)[k.val]
    have hcalendar := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k
    have htime : r.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
      simpa only [r, List.get_eq_getElem,
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using hcalendar.1
    have hstartEq : start =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
    have htimeStart : r.input.time.val = start + k.val := by
      calc
        r.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := htime
        _ = start + k.val := by rw [hstartEq]
    have hprefixRun : start + k.val ≤ p.T := by
      rw [← htimeStart]
      exact Nat.le_of_lt r.input.time.isLt
    have hrecordState : ((W z)[k.val]).input.state =
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z)
          rewards start k.val hprefixRun hmode).finalState := by
      have hrecord := hcalendar.2
      have hrunRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
        rate rewards C_star C_h r.input.time z initial hlaunch (by
          rw [htime]
          exact Nat.le_add_right _ _)
      have hsame := Option.some.inj (hrecord.symm.trans hrunRecord)
      have hindexActual : r.input.time.val -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k.val := by
        rw [htime]
        omega
      have hsameState := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord => record.input.state) hsame
      simpa only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt, hindexActual, hstartEq] using hsameState
    have hkRun : k.val < runWindow.length := by rw [← hwindow]; exact k.isLt
    have hphase : ReferenceFirstLiveConfirmationHistory.FirstLiveState
        ((W z)[k.val]).input.state := by
      have h := hcarried ⟨k.val, hkRun⟩
      simpa only [runWindow, hwindow] using h
    refine ⟨selected, ?_, ?_, ?_⟩
    · exact hselected
    · exact hinitialPayload.trans (congrArg some hpayload.symm)
    · intro i
      obtain ⟨hprefix, hsafetyAt⟩ := hsafety.1 k.val (Nat.le_of_lt hkRun)
      obtain ⟨incoming, incomingMemory, hordinary, hdomain, hmass,
        hpair, hbuffer, hstatus, hoccupied⟩ := hsafetyAt i
      have hordinaryInput :
          ((W z)[k.val]).input.state.followers i =
            .ordinary incoming incomingMemory := by
        rw [hrecordState]
        exact hordinary
      have hnotBoth := before_after_not_both (rate := rate)
        ((W z)[k.val]) selected i
      have hstage :
          Before (rate := rate) ((W z)[k.val]) i ∨
            After (rate := rate) ((W z)[k.val]) selected i := by
        cases hcoord : ((W z)[k.val]).input.state.coordinator with
        | first =>
            have hinitialState : ReferenceFirstLiveConfirmationHistory.InitialFollowers
                ((W z)[k.val]).input.state := by
              simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hcoord] using hphase
            obtain ⟨hunocc, hnone⟩ := hinitialState i incoming incomingMemory hordinaryInput
            exact Or.inl ⟨incoming, incomingMemory, hordinaryInput, hnone⟩
        | live registers owned base =>
            have hphase' :
                ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload
                    ((W z)[k.val]).input.state ∧
                  (∀ j state memory,
                    ((W z)[k.val]).input.state.followers j = .ordinary state memory →
                      registers.pendingAtChoice.Nonempty → state.status ≠ .released) := by
              simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hcoord] using hphase
            have hlive :
                ReferenceActiveDataOwnership.carriedOccupiedFields registers.payload
                  ((W z)[k.val]).input.state := by
              exact hphase'.1
            have hselectedPayload : selected.view.payload = registers.payload := by
              have hphaseRun' : selected.view.payload = registers.payload ∧
                  selected.view.pendingAtChoice = registers.pendingAtChoice := by
                have hphaseRunElem := hphaseRun
                simpa only [List.get_eq_getElem, hcoord] using hphaseRunElem
              exact hphaseRun'.1
            rw [← hselectedPayload] at hlive
            by_cases hu : incoming.status = .unoccupied
            · have hnone := (hstatus hu).1
              exact Or.inl ⟨incoming, incomingMemory, hordinaryInput, hnone⟩
            · have hfields := hlive i
              have hfields' : incoming.status ≠ .unoccupied →
                  incoming.lastDown = some (selected.view.payload.downRecord i) := by
                simpa only [ReferenceActiveDataOwnership.occupiedFields, hordinaryInput] using hfields
              exact Or.inr ⟨incoming, incomingMemory, hordinaryInput, hfields' hu⟩
        | collection payload ledger proposal =>
            simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hcoord] at hphase
        | dagger =>
            have hphaseRunElem := hphaseRun
            simp only [List.get_eq_getElem, hcoord] at hphaseRunElem
      exact ⟨hstage, hnotBoth⟩

private theorem actual_record_time_eq_calendar
    (t : Fin p.T) (z : SourceInput p)
    (hcross : ReferenceFirstLiveHandoverBoundaryFactorization.crossed
      rate rewards C_star C_h z)
    (hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z ≤ t.val)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val at hstart
  have hinit : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    change (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true at hcross
    simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hcross
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z rewards C_star C_h hinit
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hinit
  have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z initial hlaunch hstart
  have hrecordEq := Option.some.inj (hr.symm.trans hrecord)
  rw [hrecordEq]
  apply Fin.ext
  dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
    ReferenceActivePhysicalHorizon.roundInputAt]
  omega

private theorem pending_of_section_fields
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (sf : Fin (t.val + 1))
    (hcross : ReferenceFirstLiveHandoverBoundaryFactorization.crossed
      rate rewards C_star C_h z)
    (hphysical : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z = sf.val)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hwindow : r ∈ ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow
      rate rewards C_star C_h z)
    (hselection : r.output.preparation.coordinator.selection = some selected)
    (hipending : i ∈ selected.view.pendingAtChoice)
    (hstrict : t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
      rate rewards C_star C_h z) :
    i ∈ P t.val z := by
  classical
  have hstartLe : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z ≤ t.val := by
    rw [hphysical]
    omega
  have htime := actual_record_time_eq_calendar rate rewards C_star C_h t z
    hcross hstartLe r hrecord
  have hwindowW : r ∈ W z := by
    simpa only [ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.window] using hwindow
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hwindowW
  subst r
  have hmiss : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (W z)[n] =
      selected.view.pendingAtChoice := by
    have hselectedEndpoint : ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
        rate (W z)[n] = some selected := by
      change (W z)[n].output.preparation.coordinator.selection = some selected
      exact hselection
    unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
    rw [hselectedEndpoint]
    rfl
  have hmissingNonempty :
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (W z)[n]).Nonempty := by
    rw [hmiss]
    refine ⟨i, ?_⟩
    change i ∈ (selected.view.pendingAtChoice : Finset (Fin (p.m - 1)))
    exact hipending
  have hstrictDate : (W z)[n].input.time.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z := by
    rw [htime]
    exact hstrict
  have hstrictDateT : t.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z := by
    rw [← htime]
    exact hstrictDate
  have hdate : t.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z := by
    apply (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
      rate rewards C_star C_h z (t.val + 1)).mpr
    have hgetSame : (W z)[(⟨n, hn⟩ : Fin (W z).length)] = (W z)[n] := rfl
    have hdateEq : (W z)[(⟨n, hn⟩ : Fin (W z).length)].input.time.val + 1 = t.val + 1 := by
      calc
        (W z)[(⟨n, hn⟩ : Fin (W z).length)].input.time.val + 1 =
            (W z)[n].input.time.val + 1 := by rw [hgetSame]
        _ = t.val + 1 := congrArg (fun time : Fin p.T => time.val + 1) htime
    exact ⟨⟨n, hn⟩, hdateEq, hmissingNonempty, hstrictDateT⟩
  have hdateRow : (W z)[n].input.time.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z := by
    simpa only [htime] using hdate
  have hpending := ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_eq_window_missing
    rate rewards C_star C_h z ⟨n, hn⟩ hdateRow
  have hpending' : P (W z)[n].input.time.val z =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (W z)[n] := by
    simpa only [List.get_eq_getElem, Fin.val_mk] using hpending
  have hiMissing : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (W z)[n] := by
    rw [hmiss]
    exact hipending
  rw [← htime, hpending']
  exact hiMissing

private theorem section_member_pending
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (a : Bool × Fin (M p) × Fin (t.val + 1))
    (ha : z ∈ (if a.1 then
        ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h a.2.1 a.2.2.val t i
      else
        ReferenceFirstLiveHandoverBoundaryFactorization.E_before
          rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
      {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h z}) :
    i ∈ P t.val z := by
  classical
  rcases a with ⟨after, pair⟩
  rcases pair with ⟨q, sf⟩
  cases after <;> simp only [↓reduceIte, Set.mem_inter_iff,
    ReferenceFirstLiveHandoverBoundaryFactorization.E_before,
    ReferenceFirstLiveHandoverBoundaryFactorization.E_after,
    Set.mem_ofPred_eq] at ha
  all_goals
    rcases ha with ⟨⟨_hq, hcross, hphysical, _hs, r, selected,
      hrecord, hwindow, hselection, hipending, _hstage⟩, hstrict⟩
    exact pending_of_section_fields rate rewards C_star C_h t i z sf
      hcross hphysical r selected hrecord hwindow hselection hipending hstrict

/-- At each strict stopped date, every pending follower has exactly one
literal before or after section with its actual selected row and physical
start. Conversely, each such section witness is the pending follower. -/
theorem pending_stopped_section_partition
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    let I := Bool × Fin (M p) × Fin (t.val + 1)
    let S : I → Set (SourceInput p) := fun a =>
      (if a.1 then
        ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h a.2.1 a.2.2.val t i
      else
        ReferenceFirstLiveHandoverBoundaryFactorization.E_before
          rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
        {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z}
    i ∈ P t.val z ↔ ∃! a : I, z ∈ S a := by
  classical
  dsimp only
  constructor
  · intro hi
    have hnonempty : (P t.val z).Nonempty := ⟨i, hi⟩
    have hdate := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
      rate rewards C_star C_h z t.val).mp hnonempty
    obtain ⟨k, hdateEq, _hmissing, hstrict⟩ :=
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
        rate rewards C_star C_h z (t.val + 1)).mp hdate
    let r := (W z)[k.val]
    have htime : r.input.time.val = t.val := by
      change (W z)[k.val].input.time.val = t.val
      omega
    have hrowStage := source_window_stage_partition rate rewards C_star C_h z k
    dsimp only [r, List.get_eq_getElem] at hrowStage
    obtain ⟨selected, hselected, _hpayload, hstages⟩ := hrowStage
    have hcalendar := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k
    have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r := by
      have heq : r.input.time = t := Fin.ext htime
      rw [← heq]
      simpa only [r, List.get_eq_getElem] using hcalendar.2
    have hdateSupported : r.input.time.val + 1 ∈
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z := by
      simpa only [htime] using hdate
    have hmissingEq := ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_eq_window_missing
      rate rewards C_star C_h z k hdateSupported
    have hmissingEq' : P r.input.time.val z =
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r := by
      simpa only [r, List.get_eq_getElem] using hmissingEq
    have hiAtTime : i ∈ P r.input.time.val z := by
      simpa only [htime] using hi
    have hiMissing : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r := by
      rw [hmissingEq'] at hiAtTime
      exact hiAtTime
    have hstartLe : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z ≤ t.val := by
      have hcal : r.input.time.val =
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
            rate rewards C_star C_h z + k.val := by
        simpa only [r, List.get_eq_getElem] using hcalendar.1
      rw [htime] at hcal
      omega
    let q := ActualInitializationPhysicalStep.selectedRowIndex p z
    let sf : Fin (t.val + 1) := ⟨
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z,
      by omega⟩
    have hcross : ReferenceFirstLiveHandoverBoundaryFactorization.crossed
        rate rewards C_star C_h z := by
      have hc := window_crossing rate rewards C_star C_h z (by
        have hk := k.isLt
        omega)
      simpa only [ReferenceFirstLiveHandoverBoundaryFactorization.crossed,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hc
    have hselectedR : r.output.preparation.coordinator.selection = some selected := by
      simpa only [r, List.get_eq_getElem,
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection] using hselected
    have hmissingSelected : i ∈ selected.view.pendingAtChoice := by
      have hmissingSelectedSet : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
          rate r = selected.view.pendingAtChoice := by
        have hselectedEndpoint : ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
            rate r = some selected := by
          change r.output.preparation.coordinator.selection = some selected
          exact hselectedR
        unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        rw [hselectedEndpoint]
        rfl
      rw [hmissingSelectedSet] at hiMissing
      exact hiMissing
    have hwindow : r ∈ ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow
        rate rewards C_star C_h z := by
      simpa only [ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow,
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.window, r] using
          List.getElem_mem k.isLt
    have hmask : z ∈ {z | t.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z} :=
      hstrict
    rcases hstages i with ⟨hbha, hnotboth⟩
    rcases hbha with hb | ha
    · let a : Bool × Fin (M p) × Fin (t.val + 1) := (false, q, sf)
      have hsectionBefore : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_before
          rate rewards C_star C_h q sf.val t i := by
        change ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧
          ReferenceFirstLiveHandoverBoundaryFactorization.crossed rate rewards C_star C_h z ∧
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z = sf.val ∧
          sf.val ≤ t.val ∧
          ∃ r', ∃ selected',
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r' ∧
            r' ∈ ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow rate rewards C_star C_h z ∧
            r'.output.preparation.coordinator.selection = some selected' ∧
            i ∈ selected'.view.pendingAtChoice ∧
            ReferenceFirstLiveHandoverBoundaryFactorization.Before (rate := rate) r' i
        exact ⟨rfl, hcross, rfl, hstartLe, r, selected, hrecord, hwindow,
          hselected, hmissingSelected, hb⟩
      have hmem : z ∈ (if a.1 then
          ReferenceFirstLiveHandoverBoundaryFactorization.E_after
            rate rewards C_star C_h a.2.1 a.2.2.val t i
        else ReferenceFirstLiveHandoverBoundaryFactorization.E_before
            rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
          {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h z} := by
        simpa [a] using And.intro hsectionBefore hmask
      refine ⟨a, hmem, ?_⟩
      intro b hbmem
      rcases b with ⟨tag, pair⟩
      rcases pair with ⟨q', sf'⟩
      by_cases htag : tag
      · simp only [htag, ↓reduceIte, Set.mem_inter_iff,
          ReferenceFirstLiveHandoverBoundaryFactorization.E_after,
          Set.mem_ofPred_eq] at hbmem
        rcases hbmem.1 with ⟨_, _, _, _, r', selected', hr', _, hs', _, hafter'⟩
        have hrecordEq : r' = r := Option.some.inj (hr'.symm.trans hrecord)
        subst r'
        have hselectedEq : selected' = selected := Option.some.inj (hs'.symm.trans hselected)
        subst selected'
        exact False.elim (hnotboth ⟨hb, hafter'⟩)
      · simp only [htag, Set.mem_inter_iff,
          ReferenceFirstLiveHandoverBoundaryFactorization.E_before,
          Set.mem_ofPred_eq] at hbmem
        rcases hbmem.1 with ⟨hq', _, hstart', _, r', selected', hr', _, hs', _, hbefore'⟩
        have hrecordEq : r' = r := Option.some.inj (hr'.symm.trans hrecord)
        subst r'
        have hselectedEq : selected' = selected := Option.some.inj (hs'.symm.trans hselected)
        subst selected'
        have hqEq : q' = q := hq'.symm.trans rfl
        have hsEq : sf'.val = sf.val := hstart'.symm.trans rfl
        apply Prod.ext
        · exact (Bool.eq_false_iff.mpr htag)
        · apply Prod.ext
          · exact hqEq
          · apply Fin.ext
            exact hsEq
    · let a : Bool × Fin (M p) × Fin (t.val + 1) := (true, q, sf)
      have hsectionAfter : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h q sf.val t i := by
        change ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧
          ReferenceFirstLiveHandoverBoundaryFactorization.crossed rate rewards C_star C_h z ∧
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z = sf.val ∧
          sf.val ≤ t.val ∧
          ∃ r', ∃ selected',
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r' ∧
            r' ∈ ReferenceFirstLiveHandoverBoundaryFactorization.firstWindow rate rewards C_star C_h z ∧
            r'.output.preparation.coordinator.selection = some selected' ∧
            i ∈ selected'.view.pendingAtChoice ∧
            ReferenceFirstLiveHandoverBoundaryFactorization.After (rate := rate) r' selected' i
        exact ⟨rfl, hcross, rfl, hstartLe, r, selected, hrecord, hwindow,
          hselected, hmissingSelected, ha⟩
      have hmem : z ∈ (if a.1 then
          ReferenceFirstLiveHandoverBoundaryFactorization.E_after
            rate rewards C_star C_h a.2.1 a.2.2.val t i
        else ReferenceFirstLiveHandoverBoundaryFactorization.E_before
            rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
          {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h z} := by
        simpa [a] using And.intro hsectionAfter hmask
      refine ⟨a, hmem, ?_⟩
      intro b hbmem
      rcases b with ⟨tag, pair⟩
      rcases pair with ⟨q', sf'⟩
      by_cases htag : tag
      · simp only [htag, ↓reduceIte, Set.mem_inter_iff,
          ReferenceFirstLiveHandoverBoundaryFactorization.E_after,
          Set.mem_ofPred_eq] at hbmem
        rcases hbmem.1 with ⟨hq', _, hstart', _, r', selected', hr', _, hs', _, hafter'⟩
        have hrecordEq : r' = r := Option.some.inj (hr'.symm.trans hrecord)
        subst r'
        have hselectedEq : selected' = selected := Option.some.inj (hs'.symm.trans hselected)
        subst selected'
        have hqEq : q' = q := hq'.symm.trans rfl
        have hsEq : sf'.val = sf.val := hstart'.symm.trans rfl
        apply Prod.ext
        · exact htag
        · apply Prod.ext
          · exact hqEq
          · apply Fin.ext
            exact hsEq
      · simp only [htag, Set.mem_inter_iff,
          ReferenceFirstLiveHandoverBoundaryFactorization.E_before,
          Set.mem_ofPred_eq] at hbmem
        rcases hbmem.1 with ⟨_, _, _, _, r', selected', hr', _, hs', _, hbefore'⟩
        have hrecordEq : r' = r := Option.some.inj (hr'.symm.trans hrecord)
        subst r'
        have hselectedEq : selected' = selected := Option.some.inj (hs'.symm.trans hselected)
        subst selected'
        exact False.elim (hnotboth ⟨hbefore', ha⟩)
  · rintro ⟨a, ha, _⟩
    exact section_member_pending rate rewards C_star C_h t i z a ha

/-- The exact pointwise finite strong-indicator identity for the same stopped
sections, with the full unnormalized finite sum. -/
theorem pending_stopped_section_partition_indicator
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    let I := Bool × Fin (M p) × Fin (t.val + 1)
    let S : I → Set (SourceInput p) := fun a =>
      (if a.1 then
        ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h a.2.1 a.2.2.val t i
      else
        ReferenceFirstLiveHandoverBoundaryFactorization.E_before
          rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
        {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z}
    (if i ∈ P t.val z then (1 : ℝ) else 0) =
      ∑ a : I, if z ∈ S a then (1 : ℝ) else 0 := by
  classical
  dsimp only
  let I := Bool × Fin (M p) × Fin (t.val + 1)
  let S : I → Set (SourceInput p) := fun a =>
    (if a.1 then
      ReferenceFirstLiveHandoverBoundaryFactorization.E_after
        rate rewards C_star C_h a.2.1 a.2.2.val t i
    else
      ReferenceFirstLiveHandoverBoundaryFactorization.E_before
        rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
      {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h z}
  change (if i ∈ P t.val z then (1 : ℝ) else 0) =
    ∑ a : I, if z ∈ S a then (1 : ℝ) else 0
  by_cases hi : i ∈ P t.val z
  · simp only [ite_eq_left hi]
    obtain ⟨a, ha, hunique⟩ :=
      (pending_stopped_section_partition rate rewards C_star C_h t i z).mp hi
    symm
    calc
      (∑ b : I, if z ∈ S b then (1 : ℝ) else 0) =
          (if z ∈ S a then (1 : ℝ) else 0) :=
        Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (by
          intro b _hb hne
          have hnot : z ∉ S b := fun hb => hne (hunique b hb)
          simp [hnot])
      _ = 1 := by
        have hza : z ∈ S a := by simpa only using ha
        simp only [ite_eq_left hza]
  · simp only [ite_eq_right hi]
    symm
    apply Finset.sum_eq_zero
    intro a _ha
    have hnot : z ∉ S a := by
      intro hz
      exact hi (section_member_pending rate rewards C_star C_h t i z a hz)
    simp [hnot]

end Bandits.Support.ReferenceFirstLiveHandoverPendingStagePartition

end
