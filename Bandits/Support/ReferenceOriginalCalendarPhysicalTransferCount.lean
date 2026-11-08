/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSignedFirstBadCalendar
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw
public import Bandits.Support.EpisodeStartCount
public import Bandits.Support.ReferenceFixedIDSourceSection

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Physical transfer starts on the original calendar

The count below reads the actual complete physical calendar through the full
horizon.  Its proposal-bit envelope scans every reserved coordinate of the
original selected row, whether or not the coordinator read that coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw
open scoped BigOperators
open scoped Classical

universe u

local instance physicalTransferCountOptionMeasurableSpace {Y : Type u} [MeasurableSpace Y] :
    MeasurableSpace (Option Y) :=
  Bandits.Support.LaterAssignmentStartMeasurability.optionMeasurableSpace

namespace Bandits.Support.ReferenceOriginalCalendarPhysicalTransferCount

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p
abbrev StateCode {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.StateCode p rate
abbrev LiveObservation {p : Parameters} (rate : RateInput p) :=
  Option (Option (LiveTag p) × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (Fin (p.m - 1) → Option (Fin 3)))
abbrev PhysicalStartObservation {p : Parameters} (rate : RateInput p) :=
  Option (StateCode rate) × LiveObservation rate

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

private theorem measurable_optionElim {α : Type u} {β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (Option α)]
    (he : Measurable (Equiv.optionEquivSumPUnit.{u, u} α))
    (f : α → β) (b : β) (hf : Measurable f) :
    Measurable (fun o : Option α => o.elim b f) := by
  let e : Option α ≃ α ⊕ PUnit.{u + 1} := Equiv.optionEquivSumPUnit.{u, u} α
  have hs : Measurable (Sum.elim f (fun _ : PUnit => b)) :=
    hf.sumElim measurable_const
  have hfun : (fun o : Option α => o.elim b f) = Sum.elim f (fun _ : PUnit => b) ∘ e := by
    funext o
    cases o <;> rfl
  rw [hfun]
  exact hs.comp he

/-- A saved live dispatch tag reports the literal successful `StartRound`
command, including its value on the checked-failure branches. -/
def liveTagInitializesAt (time : Fin p.T) : LiveTag p → Bool
  | .inl _ => false
  | .inr (.inl (dispatch, _)) =>
      decide (dispatch.1.ledgerCommand = some (.initializeAt time))
  | .inr (.inr (.inl (dispatch, _))) =>
      decide (dispatch.1.ledgerCommand = some (.initializeAt time))
  | .inr (.inr (.inr (dispatch, _))) =>
      decide (dispatch.1.ledgerCommand = some (.initializeAt time))

/-- The first flag reads the canonical incoming state schema.  The live flag
reads the actual retained dispatcher tag, not a request or a sampler result.
-/
def physicalStartObservationFlags {p : Parameters} (rate : RateInput p)
    (time : Fin p.T) (observation : PhysicalStartObservation rate) : Bool × Bool :=
  let first := observation.1.elim false (fun code => match code.1 with
    | .inl _ => true
    | .inr _ => false)
  let live := observation.2.elim false (fun fields =>
    (fields.1).elim false (liveTagInitializesAt time))
  (first, live)

private theorem measurable_liveTagInitializesAt (time : Fin p.T) :
    Measurable (liveTagInitializesAt (p := p) time) := by
  exact measurable_of_countable _

private theorem measurable_firstFlagCode :
    Measurable (fun code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
      match code with | .inl _ => true | .inr _ => false) := by
  let f : Unit → Bool := fun _ => true
  let g : ((ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
      ((ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit)) → Bool :=
    fun _ => false
  change Measurable (Sum.elim f g)
  exact measurable_const.sumElim measurable_const

private theorem measurable_firstFlagState :
    Measurable (fun code : StateCode rate => match code.1 with
      | .inl _ => true | .inr _ => false) := by
  exact measurable_firstFlagCode (p := p) (rate := rate) |>.comp
    measurable_fst

private theorem measurable_firstFlagOptionState :
    Measurable (fun code : Option (StateCode rate) =>
      code.elim false (fun c => match c.1 with | .inl _ => true | .inr _ => false)) := by
  exact measurable_optionElim (comap_measurable _) _ false
    (measurable_firstFlagState (p := p) (rate := rate))

private theorem measurable_liveFlag (time : Fin p.T) :
    Measurable (fun observation : LiveObservation rate =>
      observation.elim false (fun fields =>
        (fields.1).elim false (liveTagInitializesAt (p := p) time))) := by
  have htag : Measurable (fun tags : Option (LiveTag p) =>
      tags.elim false (liveTagInitializesAt (p := p) time)) :=
    measurable_optionElim (measurable_of_countable _)
      _ false
      (measurable_liveTagInitializesAt (p := p) time)
  have hfields : Measurable (fun fields : Option (LiveTag p) ×
      Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (Fin (p.m - 1) → Option (Fin 3)) =>
      (fields.1).elim false (liveTagInitializesAt (p := p) time)) :=
    htag.comp measurable_fst
  exact measurable_optionElim (comap_measurable _) _ false hfields

private theorem measurable_physicalStartObservationFlags (time : Fin p.T) :
    Measurable (physicalStartObservationFlags (p := p) rate time) := by
  have hfirst : Measurable (fun observation : PhysicalStartObservation rate =>
      observation.1.elim false (fun c => match c.1 with | .inl _ => true | .inr _ => false)) :=
    (measurable_firstFlagOptionState (p := p) (rate := rate)).comp measurable_fst
  have hlive : Measurable (fun observation : PhysicalStartObservation rate =>
      observation.2.elim false (fun fields =>
        (fields.1).elim false (liveTagInitializesAt (p := p) time))) :=
    (measurable_liveFlag (p := p) (rate := rate) time).comp measurable_snd
  unfold physicalStartObservationFlags
  exact hfirst.prodMk hlive

private theorem measurable_actualPhysicalStartObserver (time : Fin p.T) :
    Measurable (fun z : SourceInput p =>
      actualObserver rate rewards C_star C_h time z) := by
  exact (ReferenceSourcePrefixHistoryFiltration.measurable_incoming
      rate rewards C_star C_h time).prodMk
    (measurable_actualReadout rate rewards C_star C_h
      (fun r => liveObservation rate r.input)
      (fun k => measurable_liveObservation rate |>.comp
        (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
          rate rewards C_star C_h k)) time)

/-- The generated launch marker at its actual physical launch boundary. -/
def actualPhysicalTransferInitialMarkerAt (time : Fin p.T) (z : SourceInput p) : Prop :=
  (physicalStartObservationFlags rate time
      (actualObserver rate rewards C_star C_h time z)).1 = true ∧
    time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < p.T

/-- A live dispatch retained the actual successful `StartRound.initializeAt`
command, including checked-initializer and downstream local-failure branches. -/
def actualPhysicalTransferLiveStartAt (time : Fin p.T) (z : SourceInput p) : Prop :=
  (physicalStartObservationFlags rate time
    (actualObserver rate rewards C_star C_h time z)).2 = true

theorem actualPhysicalTransferLiveStartAt_after_physicalStart
    (time : Fin p.T) (z : SourceInput p)
    (h : actualPhysicalTransferLiveStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ time.val := by
  unfold actualPhysicalTransferLiveStartAt at h
  cases hr : actualRecordAt rate rewards C_star C_h time z with
  | none => simp [actualObserver, hr, physicalStartObservationFlags] at h
  | some record =>
      have hrecord : actualRecordAt rate rewards C_star C_h time z ≠ none := by
        rw [hr]
        simp
      have hnot : ¬ time.val <
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        intro hlt
        exact hrecord ((actualRecord_none_iff rate rewards C_star C_h time z).2 hlt)
      omega

/-- Literal physical transfer start at a zero-based original calendar date.
The initial marker is attached to the generated launch boundary; later markers
are the actual live `StartRound` collection initializations. -/
def actualPhysicalTransferStartAt (time : Fin p.T) (z : SourceInput p) : Prop :=
  actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z ∨
    actualPhysicalTransferLiveStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z

theorem actualPhysicalTransferStartAt_false_of_physicalStart_eq_T
    (time : Fin p.T) (z : SourceInput p)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z := by
  rintro (⟨_, htime, hbefore⟩ | hlive)
  · omega
  · have hafter := actualPhysicalTransferLiveStartAt_after_physicalStart
      rate rewards C_star C_h time z hlive
    omega

theorem actualPhysicalTransferStartAt_false_of_no_launch
    (time : Fin p.T) (z : SourceInput p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z := by
  apply actualPhysicalTransferStartAt_false_of_physicalStart_eq_T
    rate rewards C_star C_h time z
  exact ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate z rewards C_star C_h hnone

theorem actualPhysicalTransferStartAt_false_of_terminal_crossing
    (time : Fin p.T) (z : SourceInput p)
    (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z := by
  have ⟨_, hsentinel⟩ := ReferenceCompletePhysicalHistory.terminal_crossing_sentinel_round
    rate z rewards C_star C_h active hlaunch hterminal
  exact actualPhysicalTransferStartAt_false_of_physicalStart_eq_T
    rate rewards C_star C_h time z hterminal

theorem actualPhysicalTransferInitialMarkerAt_unique
    (t s : Fin p.T) (z : SourceInput p)
    (ht : actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z)
    (hs : actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) s z) : t = s := by
  rcases ht with ⟨_, htime, _⟩
  rcases hs with ⟨_, htime', _⟩
  apply Fin.ext
  omega

private theorem detectCutoff_cutoff_grid_or_previousTrueProposal
    (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (sigma : Fin p.T) (hsigma : clock.sigma = some sigma)
    (hdetect : CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma)) :
    FollowerCutoffScan.calendarRound time = clock.g ∨
      ∃ stamp : Fin p.T,
        clock.lastProposal = some (stamp, true) ∧ stamp.val + 1 = time.val := by
  classical
  rcases clock with ⟨s, u, g, token⟩
  change s = some sigma at hsigma
  subst s
  cases u with
  | some u => simp [CoordinatorPhaseClock.detectCutoff] at hdetect
  | none =>
      change FollowerCutoffScan.calendarRound time = g ∨
        ∃ stamp : Fin p.T, token = some (stamp, true) ∧ stamp.val + 1 = time.val
      by_cases hgrid : FollowerCutoffScan.calendarRound time = g
      · exact Or.inl hgrid
      · right
        cases htoken : token with
        | none =>
            change token = none at htoken
            subst token
            have herror : CoordinatorPhaseClock.detectCutoff
                ({ sigma := some sigma, u := none, g := g, lastProposal := none } :
                  CoordinatorPhaseClock.ClockRegisters p) time =
                .error .missingPriorProposal := by
              simp [CoordinatorPhaseClock.detectCutoff, hgrid,
                CoordinatorPhaseClock.savedPriorProposal]
              rfl
            rw [herror] at hdetect
            cases hdetect
        | some pair =>
            rcases pair with ⟨stamp, bit⟩
            change token = some (stamp, bit) at htoken
            subst token
            by_cases hstamp : stamp.val + 1 = time.val
            · cases bit
              · have hno : CoordinatorPhaseClock.detectCutoff
                    ({ sigma := some sigma, u := none, g := g, lastProposal := some (stamp, false)} :
                      CoordinatorPhaseClock.ClockRegisters p) time = .ok .noCutoff := by
                  simp [CoordinatorPhaseClock.detectCutoff, hgrid,
                    CoordinatorPhaseClock.savedPriorProposal, hstamp]
                  rfl
                rw [hno] at hdetect
                cases hdetect
              · exact ⟨stamp, rfl, hstamp⟩
            · have herror : CoordinatorPhaseClock.detectCutoff
                  ({ sigma := some sigma, u := none, g := g, lastProposal := some (stamp, bit)} :
                    CoordinatorPhaseClock.ClockRegisters p) time =
                  .error .stalePriorProposal := by
                simp [CoordinatorPhaseClock.detectCutoff, hgrid,
                  CoordinatorPhaseClock.savedPriorProposal, hstamp]
                rfl
              rw [herror] at hdetect
              cases hdetect

/-- A successful physical-clock initialization is either at its absolute
grid boundary or is authorized by the correctly stamped true bit from the
preceding source date. -/
theorem startRound_initializeAt_grid_or_previousTrueProposal
    (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending =
      .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt time)) :
    FollowerCutoffScan.calendarRound time = clock.g ∨
      ∃ stamp : Fin p.T,
        clock.lastProposal = some (stamp, true) ∧ stamp.val + 1 = time.val := by
  classical
  have hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
    by_contra h
    simp [CoordinatorPhaseClock.startRound, h] at hstart
  have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    by_contra h
    simp [CoordinatorPhaseClock.startRound, hparam, h] at hstart
  have htime : CoordinatorPhaseClock.startRoundTimeValid p time clock := by
    by_contra h
    simp [CoordinatorPhaseClock.startRound, hparam, hclock, h] at hstart
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure =>
      simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime, hdetect] at hstart
  | ok decision =>
      cases decision with
      | cutoff sigma hsigma =>
          exact detectCutoff_cutoff_grid_or_previousTrueProposal
            time clock sigma hsigma hdetect
      | noCutoff =>
          by_cases hready : CoordinatorPhaseClock.sourceStartTest
              clock.sigma clock.u time pending
          · by_cases hboundary : CoordinatorPhaseClock.newGridBoundaryValid p time
                (FollowerCutoffScan.gridBoundary p rate.eta.val time)
            · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hready, hboundary] at hstart
              cases hstart
              simp at hcommand
            · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hready, hboundary] at hstart
          · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
              hdetect, hready] at hstart
            cases hstart
            simp at hcommand

private theorem actualRecord_first_date
    (time : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecordAt rate rewards C_star C_h time z = some record)
    (hfirst : record.input.state.coordinator = .first) :
    time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  change ReferenceSourcePrefixHistoryFiltration.actualRecord
    rate rewards C_star C_h time z = some record at hr
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hr
  have hzero : time.val - start = 0 := by
    by_contra hn
    let j : Fin R.length := ⟨time.val - start - 1, by dsimp only [R]; omega⟩
    have hj : j.val + 1 < R.length := by dsimp only [j, R]; omega
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z j.val hj
    have hphase := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 j
    have hnot := hphase.2.2.2.1
    have hindex : j.val + 1 = time.val - start := by dsimp only [j]; omega
    apply hnot
    have hc := congrArg
      (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hadj
    have hc' : record.input.state.coordinator = R[j.val].output.next.coordinator := by
      simpa only [hindex, start, heq] using hc
    exact hc'.symm.trans hfirst
  dsimp only [start] at hzero
  omega

private theorem firstFlag_iff_record
    (time : Fin p.T) (z : SourceInput p) :
    (physicalStartObservationFlags rate time
      (actualObserver rate rewards C_star C_h time z)).1 = true ↔
      ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        actualRecordAt rate rewards C_star C_h time z = some record ∧
        record.input.state.coordinator = .first := by
  cases hr : actualRecordAt rate rewards C_star C_h time z with
  | none =>
      have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h time z = none := hr
      simp [physicalStartObservationFlags, actualObserver,
        ReferenceSourcePrefixHistoryFiltration.incoming, hr']
  | some record =>
      have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h time z = some record := hr
      cases hc : record.input.state.coordinator <;>
        simp [physicalStartObservationFlags, actualObserver,
          ReferenceSourcePrefixHistoryFiltration.incoming, hr',
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]

/-- The launch-date restriction in the initial marker loses no FIRST event:
connected actual records never return to FIRST after a physical round. -/
theorem actualPhysicalTransferInitialMarkerAt_iff_record_first
    (time : Fin p.T) (z : SourceInput p) :
    actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z ↔
      ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        actualRecordAt rate rewards C_star C_h time z = some record ∧
        record.input.state.coordinator = .first := by
  constructor
  · intro h
    exact (firstFlag_iff_record rate rewards C_star C_h time z).mp h.1
  · rintro ⟨record, hr, hfirst⟩
    have hd := actualRecord_first_date rate rewards C_star C_h time z record hr hfirst
    exact ⟨(firstFlag_iff_record rate rewards C_star C_h time z).mpr
      ⟨record, hr, hfirst⟩, hd, by omega⟩

private theorem dispatchFirst_actualInstallation
    (x : CoordinatorRoundDispatch.FirstInput p) :
    ∃ selection : CoordinatorRoundDispatch.ArmSelection
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput x)).registers.payload
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput x)).startRoundResult
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput x)).registers.time
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput x)).registers.complementWeights x.row,
      CoordinatorRoundDispatch.dispatchFirst x = .chosen
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput x)) selection := by
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · contradiction
  · exact ⟨_, rfl⟩

/-- An initial marker is the generated FIRST dispatch's literal first
installation. Installation precedes arm choice in this operation. -/
theorem actualPhysicalTransferInitialMarkerAt_installation
    (time : Fin p.T) (z : SourceInput p)
    (h : actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z) :
    ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      actualRecordAt rate rewards C_star C_h time z = some record ∧
      record.input.state.coordinator = .first ∧
      ∃ selection : CoordinatorRoundDispatch.ArmSelection
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput record.input))).registers.payload
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput record.input))).startRoundResult
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput record.input))).registers.time
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput record.input))).registers.complementWeights
        record.input.row,
        ReferenceActivePhysicalStep.dispatch record.input = .first (.chosen
          (CoordinatorAssignmentRegisterInstall.installFirst
            (CoordinatorRoundDispatch.firstLaunchInput
              (ReferenceActivePhysicalStep.firstInput record.input))) selection) := by
  obtain ⟨record, hr, hc⟩ :=
    (actualPhysicalTransferInitialMarkerAt_iff_record_first
      rate rewards C_star C_h time z).mp h
  obtain ⟨selected, hselected⟩ :=
    dispatchFirst_actualInstallation (ReferenceActivePhysicalStep.firstInput record.input)
  exact ⟨record, hr, hc, selected, by
    rw [ReferenceActivePhysicalStep.dispatch_first record.input hc, hselected]⟩

/-- A nonterminal generated launch has its actual FIRST record and initial
transfer marker at the launch boundary. -/
theorem actualPhysicalTransferInitialMarkerAt_of_launch
    (time : Fin p.T) (z : SourceInput p)
    (htime : time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h) :
    actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z := by
  apply (actualPhysicalTransferInitialMarkerAt_iff_record_first
    rate rewards C_star C_h time z).mpr
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hl
      omega
  | some active =>
      have hfirst : active.coordinator = .first := by
        unfold ReferenceCorrectedInitializationLaunch.correctedLaunch at hl
        dsimp only at hl
        split at hl
        · exact congrArg ReferenceActivePhysicalStep.State.coordinator
            (Option.some.inj hl.symm)
        · cases hl
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate z rewards C_star C_h active hl
      have hn : actualRecordAt rate rewards C_star C_h time z ≠ none := by
        intro hn
        have hs := (actualRecord_none_iff rate rewards C_star C_h time z).mp hn
        omega
      cases hr : actualRecordAt rate rewards C_star C_h time z with
      | none => exact (hn hr).elim
      | some record =>
          refine ⟨record, rfl, ?_⟩
          have hhead : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[0]? = some record := by
            change ReferenceSourcePrefixHistoryFiltration.actualRecord
              rate rewards C_star C_h time z = some record at hr
            simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
              htime, le_refl, ite_true, Nat.sub_self] using hr
          cases he : ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h with
          | nil => simp [he] at hhead
          | cons head rest =>
              have hh : head = record := by simpa only
                [he, List.getElem?_cons_zero, Option.some.injEq] using hhead
              rw [he] at hconnected
              have hstate : record.input.state = active := hh ▸ hconnected.1
              rw [hstate]
              exact hfirst

private theorem actualRecord_clockAt
    (time : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecordAt rate rewards C_star C_h time z = some record) :
    ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      record.input.time.val record.input.state := by
  obtain ⟨k, hk⟩ := actualRecord_suffix_index rate rewards C_star C_h time z record hr
  have hmem : record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h := by
    rw [← hk]
    exact List.getElem_mem k.isLt
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl] at hmem
  | some active =>
      have hfirst : active.coordinator = .first := by
        unfold ReferenceCorrectedInitializationLaunch.correctedLaunch at hl
        dsimp only at hl
        split at hl
        · exact congrArg ReferenceActivePhysicalStep.State.coordinator
            (Option.some.inj hl.symm)
        · cases hl
      have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z)
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          active := by
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h active hl] at hmem
      exact (ReferenceRunClockPreservation.run_clockAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate z rewards C_star C_h
            omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hl) hseed).2.2.2 record hmem |>.1

private theorem liveTag_startRound_witness
    (x : CoordinatorRoundDispatch.LiveInput p) (time : Fin p.T)
    (out : CoordinatorRoundDispatch.LiveOutcome x)
    (h : liveTagInitializesAt time
      (eraseArm (ReferenceLiveDispatchOutputMeasurability.outcomeData out)) = true) :
    ∃ started : CoordinatorPhaseClock.StartRoundResult p,
      CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
        x.registers.priorClock x.registers.clockPending = .ok started ∧
      started.ledgerCommand = some (.initializeAt time) := by
  cases out with
  | clockFailure failure heq =>
      simp [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
        liveTagInitializesAt] at h
  | initializerFailure dispatched hstart checked hchecked =>
      exact ⟨dispatched.startResult, hstart, by simpa
        [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
          ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt]
        using h⟩
  | localFailure dispatched hstart reason =>
      exact ⟨dispatched.startResult, hstart, by simpa
        [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
          ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt]
        using h⟩
  | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hassign selected =>
      exact ⟨dispatched.startResult, hstart, by simpa
        [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
          ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt]
        using h⟩
  | continuingChosen dispatched hstart continuation selected =>
      exact ⟨dispatched.startResult, hstart, by simpa
        [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
          ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt]
        using h⟩

private theorem liveTagInitializesAt_of_startRound
    (x : CoordinatorRoundDispatch.LiveInput p) (time : Fin p.T)
    (out : CoordinatorRoundDispatch.LiveOutcome x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok started)
    (hc : started.ledgerCommand = some (.initializeAt time)) :
    liveTagInitializesAt time
      (eraseArm (ReferenceLiveDispatchOutputMeasurability.outcomeData out)) = true := by
  cases out with
  | clockFailure failure hd =>
      unfold CoordinatorStartRoundCutoffDispatch.dispatch at hd
      rw [hs] at hd
      cases hd
  | initializerFailure dispatched hstart checked hchecked =>
      have heq := Except.ok.inj (hstart.symm.trans hs)
      simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
        ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt,
        heq, hc, decide_true]
  | localFailure dispatched hstart reason =>
      have heq := Except.ok.inj (hstart.symm.trans hs)
      simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
        ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt,
        heq, hc, decide_true]
  | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hassign selected =>
      have heq := Except.ok.inj (hstart.symm.trans hs)
      simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
        ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt,
        heq, hc, decide_true]
  | continuingChosen dispatched hstart continuation selected =>
      have heq := Except.ok.inj (hstart.symm.trans hs)
      simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm,
        ReferenceLiveDispatchOutputMeasurability.dispatchData, liveTagInitializesAt,
        heq, hc, decide_true]

/-- Every retained live start is the actual clock call on that record's
incoming live registers. Checked initialization and local rejection are kept. -/
theorem actualPhysicalTransferLiveStartAt_witness
    (time : Fin p.T) (z : SourceInput p)
    (h : actualPhysicalTransferLiveStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
      (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p),
      actualRecordAt rate rewards C_star C_h time z = some record ∧
      record.input.state.coordinator = .live regs owned base ∧
      CoordinatorPhaseClock.startRound p rate.eta.val time regs.priorClock
        regs.clockPending = .ok started ∧
      started.ledgerCommand = some (.initializeAt time) := by
  unfold actualPhysicalTransferLiveStartAt at h
  cases hr : actualRecordAt rate rewards C_star C_h time z with
  | none => simp [actualObserver, hr, physicalStartObservationFlags] at h
  | some record =>
      have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h time z record hr).2.2.1
      have hobs : (liveObservation rate record.input).elim false (fun fields =>
          fields.1.elim false (liveTagInitializesAt time)) = true := by
        simpa only [actualObserver, hr, Option.bind_some, physicalStartObservationFlags]
          using h
      unfold liveObservation at hobs
      split_ifs at hobs with hlive
      · obtain ⟨v, hv⟩ := hlive
        cases hc : record.input.state.coordinator with
        | first =>
            simp [ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hv
        | dagger =>
            simp [ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hv
        | collection payload ledger saved =>
            simp [ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc] at hv
        | live regs owned base =>
            rw [dispatchTag_live record.input regs owned base hc] at hobs
            obtain ⟨started, hstart, hcommand⟩ := liveTag_startRound_witness
              (ReferenceActivePhysicalStep.liveInput record.input regs owned base)
              time _ hobs
            refine ⟨record, regs, owned, base, started, rfl, hc, ?_, hcommand⟩
            simpa only [ReferenceActivePhysicalStep.liveInput,
              CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
              ReferenceActivePhysicalStep.liveRegistersAt, ht] using hstart
      · simp at hobs

/-- Exact operation characterization of the live start flag. In particular,
no successful collection initializer or successful sampler is required. -/
theorem actualPhysicalTransferLiveStartAt_iff
    (time : Fin p.T) (z : SourceInput p) :
    actualPhysicalTransferLiveStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z ↔
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
      (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p),
      actualRecordAt rate rewards C_star C_h time z = some record ∧
      record.input.state.coordinator = .live regs owned base ∧
      CoordinatorPhaseClock.startRound p rate.eta.val time regs.priorClock
        regs.clockPending = .ok started ∧
      started.ledgerCommand = some (.initializeAt time) := by
  constructor
  · exact actualPhysicalTransferLiveStartAt_witness rate rewards C_star C_h time z
  · rintro ⟨record, regs, owned, base, started, hr, hc, hs, hcommand⟩
    have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h time z record hr).2.2.1
    have htag := liveTagInitializesAt_of_startRound
      (ReferenceActivePhysicalStep.liveInput record.input regs owned base) time
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput record.input regs owned base)) started
      (by simpa only [ReferenceActivePhysicalStep.liveInput,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq,
          ReferenceActivePhysicalStep.liveRegistersAt, ht] using hs) hcommand
    have hset : record.input ∈ ReferenceFirstLiveCoordinatorStepMeasurability.liveSet := by
      refine ⟨(regs.payload, ReferenceActivePhysicalStepMeasurability.encodeLive
        regs owned base), ?_⟩
      simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]
    unfold actualPhysicalTransferLiveStartAt
    simpa only [actualObserver, hr, Option.bind_some, physicalStartObservationFlags,
      liveObservation, ite_eq_left hset, Option.elim_some,
      dispatchTag_live record.input regs owned base hc] using htag

/-- Collection's later assignment installation completes an existing transfer.
Its actual collection branch contributes no new transfer-start marker. -/
theorem actualPhysicalTransferStartAt_false_of_collection
    (time : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecordAt rate rewards C_star C_h time z = some record)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hc : record.input.state.coordinator = .collection payload ledger saved) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z := by
  rintro (hfirst | hlive)
  · obtain ⟨other, ho, hco⟩ :=
      (actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h time z).mp hfirst
    have heq : other = record := Option.some.inj (ho.symm.trans hr)
    subst other
    rw [hc] at hco
    cases hco
  · obtain ⟨other, regs, owned, base, started, ho, hco, _, _⟩ :=
      actualPhysicalTransferLiveStartAt_witness rate rewards C_star C_h time z hlive
    have heq : other = record := Option.some.inj (ho.symm.trans hr)
    subst other
    rw [hc] at hco
    cases hco

theorem actualPhysicalTransferStartAt_false_of_absent_record
    (time : Fin p.T) (z : SourceInput p)
    (hn : actualRecordAt rate rewards C_star C_h time z = none) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z := by
  rintro (hfirst | hlive)
  · obtain ⟨record, hr, _⟩ :=
      (actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h time z).mp hfirst
    rw [hn] at hr
    cases hr
  · obtain ⟨record, regs, owned, base, started, hr, _, _, _⟩ :=
      actualPhysicalTransferLiveStartAt_witness rate rewards C_star C_h time z hlive
    rw [hn] at hr
    cases hr

theorem actualPhysicalTransferStartAt_false_of_dagger
    (time : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecordAt rate rewards C_star C_h time z = some record)
    (hc : record.input.state.coordinator = .dagger) :
    ¬ actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z := by
  rintro (hfirst | hlive)
  · obtain ⟨other, ho, hco⟩ :=
      (actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h time z).mp hfirst
    have heq : other = record := Option.some.inj (ho.symm.trans hr)
    subst other
    rw [hc] at hco
    cases hco
  · obtain ⟨other, regs, owned, base, started, ho, hco, _, _⟩ :=
      actualPhysicalTransferLiveStartAt_witness rate rewards C_star C_h time z hlive
    have heq : other = record := Option.some.inj (ho.symm.trans hr)
    subst other
    rw [hc] at hco
    cases hco

/-- An actual noninitial start lies at an absolute grid multiple, or follows
the same original selected row's true proposal coordinate on the preceding date. -/
theorem actualPhysicalTransferLiveStartAt_grid_or_reservedProposal
    (time : Fin p.T) (z : SourceInput p)
    (h : actualPhysicalTransferLiveStartAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z) :
    ReplayWeightStability.episodeHorizon rate.eta.val ∣ time.val + 1 ∨
      ∃ stamp : Fin p.T, stamp.val + 1 = time.val ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) stamp = true := by
  obtain ⟨record, regs, owned, base, started, hr, hc, hs, hcommand⟩ :=
    actualPhysicalTransferLiveStartAt_witness rate rewards C_star C_h time z h
  have hclock := actualRecord_clockAt rate rewards C_star C_h time z record hr
  rw [ReferenceCoordinatorClockDomains.clockAt, hc] at hclock
  rcases hclock with ⟨hdate, hvalid, hsigma, hu, hgrid, hbirth, hbefore, htoken⟩
  rcases startRound_initializeAt_grid_or_previousTrueProposal rate time regs.priorClock
      regs.clockPending started hs hcommand with hboundary | ⟨stamp, hstamp, hprev⟩
  · left
    have hg : regs.priorClock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val regs.payload.sigma := by
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
    have hsmall : regs.priorClock.g ≤ p.T := by
      rw [← hboundary]
      exact Nat.succ_le_of_lt time.isLt
    rw [hg, FollowerCutoffScan.gridBoundary] at hsmall
    have hmin : min (p.T + 1)
        (ReplayWeightStability.episodeHorizon rate.eta.val *
          ((regs.payload.sigma.val + 1) /
            ReplayWeightStability.episodeHorizon rate.eta.val + 1)) =
        ReplayWeightStability.episodeHorizon rate.eta.val *
          ((regs.payload.sigma.val + 1) /
            ReplayWeightStability.episodeHorizon rate.eta.val + 1) := by
      apply min_eq_right
      omega
    change time.val + 1 = regs.priorClock.g at hboundary
    rw [hboundary, hg, FollowerCutoffScan.gridBoundary, hmin]
    exact dvd_mul_right _ _
  · right
    rw [htoken] at hstamp
    have heq := Option.some.inj hstamp
    have htime : regs.time = stamp := congrArg Prod.fst heq
    have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) stamp = true := by
      simpa only [htime] using congrArg Prod.snd heq
    exact ⟨stamp, hprev, hbit⟩

theorem measurableSet_actualPhysicalTransferStartAt (time : Fin p.T) :
    MeasurableSet {z : SourceInput p | actualPhysicalTransferStartAt
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) time z} := by
  let observation := fun z : SourceInput p => actualObserver rate rewards C_star C_h time z
  let flags := fun z => physicalStartObservationFlags rate time (observation z)
  have hflags : Measurable flags :=
    (measurable_physicalStartObservationFlags (p := p) (rate := rate) time).comp
      (measurable_actualPhysicalStartObserver rate rewards C_star C_h time)
  have hfirst : MeasurableSet {z : SourceInput p | (flags z).1 = true} :=
    (measurableSet_singleton true).preimage (measurable_fst.comp hflags)
  have hlive : MeasurableSet {z : SourceInput p | (flags z).2 = true} :=
    (measurableSet_singleton true).preimage (measurable_snd.comp hflags)
  have hphysicalStart :=
    ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h
  have hdate : MeasurableSet {z : SourceInput p |
      time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h} :=
    measurableSet_eq_fun measurable_const hphysicalStart
  have hbefore : MeasurableSet {z : SourceInput p |
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < p.T} :=
    measurableSet_lt hphysicalStart measurable_const
  change MeasurableSet
    (({z | (flags z).1 = true} ∩ ({z | time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h} ∩
      {z | ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < p.T})) ∪
      {z | (flags z).2 = true})
  exact (hfirst.inter (hdate.inter hbefore)).union hlive

/-- The all-horizon physical transfer-start count in the literal complete
calendar. No first-bad-date truncation is applied. -/
def actualPhysicalTransferCount (z : SourceInput p) : ℕ :=
  ∑ time : Fin p.T,
    if actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z then 1 else 0

/-- The literal reserved proposal-bit sum over every date of the same
original selected complete row.  This is only an upper-bound observation; it
does not say how many proposal coordinates were read. -/
def reservedProposalBitCount (z : SourceInput p) : ℕ :=
  ∑ time : Fin p.T,
    if FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) time
    then 1 else 0

/-- Distinct noninitial physical starts inject into distinct absolute grid
or preceding reserved-bit dates. The extra constant also covers the single
initial installation and the manuscript's endpoint allowance. -/
theorem actualPhysicalTransferCount_le_reservedProposalBitCount_grid
    (z : SourceInput p) :
    actualPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤
      reservedProposalBitCount (rate := rate) z +
        p.T / ReplayWeightStability.episodeHorizon rate.eta.val + 2 := by
  classical
  let initial : Finset (Fin p.T) := Finset.univ.filter fun time =>
    actualPhysicalTransferInitialMarkerAt (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) time z
  let grid : Finset (Fin p.T) := Finset.univ.filter fun time =>
    ReplayWeightStability.episodeHorizon rate.eta.val ∣ time.val + 1
  let proposals : Finset (Fin p.T) := Finset.univ.filter fun time =>
    ∃ stamp : Fin p.T, stamp.val + 1 = time.val ∧
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) stamp = true
  let bits : Finset (Fin p.T) := Finset.univ.filter fun stamp =>
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) stamp = true
  have hinitial : initial.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht s hs
    exact actualPhysicalTransferInitialMarkerAt_unique rate rewards C_star C_h t s z
      (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hs).2
  have hgrid : grid.card ≤ p.T / ReplayWeightStability.episodeHorizon rate.eta.val := by
    rw [← Nat.card_multiples]
    apply Finset.card_le_card_of_injOn Fin.val
    · intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr t.isLt,
        (Finset.mem_filter.mp ht).2⟩
    · intro t ht s hs heq
      exact Fin.ext heq
  let previous : Fin p.T → Fin p.T := fun time =>
    ⟨time.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) time.isLt⟩
  have hproposals : proposals.card ≤ bits.card := by
    apply Finset.card_le_card_of_injOn previous
    · intro t ht
      obtain ⟨stamp, hstamp, hbit⟩ := (Finset.mem_filter.mp ht).2
      have heq : previous t = stamp := by
        apply Fin.ext
        dsimp only [previous]
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm ▸ hbit⟩
    · intro t ht s hs heq
      obtain ⟨a, ha, hbitA⟩ := (Finset.mem_filter.mp ht).2
      obtain ⟨b, hb, hbitB⟩ := (Finset.mem_filter.mp hs).2
      have hv := congrArg Fin.val heq
      apply Fin.ext
      dsimp only [previous] at hv
      omega
  have hbits : bits.card = reservedProposalBitCount (rate := rate) z := by
    simp only [bits, reservedProposalBitCount, Finset.card_eq_sum_ones,
      Finset.sum_filter]
  have hsubset : (Finset.univ.filter fun time =>
      actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z) ⊆ initial ∪ (grid ∪ proposals) := by
    intro time htime
    rcases (Finset.mem_filter.mp htime).2 with hfirst | hlive
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩)
    · apply Finset.mem_union_right
      rcases actualPhysicalTransferLiveStartAt_grid_or_reservedProposal
          rate rewards C_star C_h time z hlive with hg | hp
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  have hcount : actualPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z =
      (Finset.univ.filter fun time => actualPhysicalTransferStartAt
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) time z).card := by
    simp only [actualPhysicalTransferCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcount]
  have hunion := Finset.card_le_card hsubset
  have hleft := Finset.card_union_le initial (grid ∪ proposals)
  have hright := Finset.card_union_le grid proposals
  omega

/-- Literal inclusive subset through the first decoder failure or overflow
update. The physical calendar itself continues unchanged after this date. -/
def actualStoppedPhysicalTransferCount (z : SourceInput p) : ℕ :=
  ∑ time : Fin p.T,
    if actualPhysicalTransferStartAt (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) time z ∧
      time.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z then 1 else 0

theorem actualStoppedPhysicalTransferCount_le_full (z : SourceInput p) :
    actualStoppedPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤
      actualPhysicalTransferCount (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
  unfold actualStoppedPhysicalTransferCount actualPhysicalTransferCount
  apply Finset.sum_le_sum
  intro time htime
  split_ifs <;> simp_all

theorem actualStoppedPhysicalTransferCount_le_reservedProposalBitCount_grid
    (z : SourceInput p) :
    actualStoppedPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤
      reservedProposalBitCount (rate := rate) z +
        p.T / ReplayWeightStability.episodeHorizon rate.eta.val + 2 :=
  (actualStoppedPhysicalTransferCount_le_full rate rewards C_star C_h z).trans
    (actualPhysicalTransferCount_le_reservedProposalBitCount_grid rate rewards C_star C_h z)

theorem actualPhysicalTransferCount_nonnegative (z : SourceInput p) :
    0 ≤ (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z : ℝ) := by
  exact_mod_cast Nat.zero_le (actualPhysicalTransferCount
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z)

theorem actualPhysicalTransferCount_le_horizon (z : SourceInput p) :
    actualPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤ p.T := by
  unfold actualPhysicalTransferCount
  calc
    _ ≤ ∑ _time : Fin p.T, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro time htime
      split <;> omega
    _ = p.T := by simp

theorem reservedProposalBitCount_le_horizon (z : SourceInput p) :
    reservedProposalBitCount (rate := rate) z ≤ p.T := by
  unfold reservedProposalBitCount
  calc
    _ ≤ ∑ _time : Fin p.T, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro time htime
      split <;> omega
    _ = p.T := by simp

theorem measurable_actualPhysicalTransferCount_nat :
    Measurable (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) : SourceInput p → ℕ) := by
  unfold actualPhysicalTransferCount
  apply Finset.measurable_fun_sum (Finset.univ : Finset (Fin p.T))
  intro time htime
  exact Measurable.ite (measurableSet_actualPhysicalTransferStartAt
    rate rewards C_star C_h time) measurable_const measurable_const

theorem actualPhysicalTransferCount_integrable_fixedID (ids : CompletePublicTable.IDArray p) :
    Integrable (fun z : SourceInput p =>
      (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z : ℝ))
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hm : Measurable (fun z : SourceInput p =>
      (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_actualPhysicalTransferCount_nat rate rewards C_star C_h)
  apply Integrable.of_mem_Icc 0 (p.T : ℝ) hm.aemeasurable
  exact ae_of_all _ fun z => by
    constructor
    · exact_mod_cast Nat.zero_le (actualPhysicalTransferCount
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z)
    · exact_mod_cast actualPhysicalTransferCount_le_horizon
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z

/-- Every fixed-ID law has a finite mean for the literal physical count,
bounded by the full number of original calendar dates. -/
theorem actualPhysicalTransferCount_fixedID_mean_le_horizon
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p,
      (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤ (p.T : ℝ) := by
  have hcount := actualPhysicalTransferCount_integrable_fixedID
    (p := p) rate rewards C_star C_h ids
  have hconst : Integrable (fun _ : SourceInput p => (p.T : ℝ))
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) :=
    integrable_const _
  calc
    _ ≤ ∫ _ : SourceInput p, (p.T : ℝ)
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids :=
      integral_mono_ae hcount hconst (ae_of_all _ fun z => by
        change (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z : ℝ) ≤ (p.T : ℝ)
        exact_mod_cast actualPhysicalTransferCount_le_horizon
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z)
    _ = (p.T : ℝ) := by simp

private theorem measurable_originalSelectedCompleteRow :
    Measurable (fun z : SourceInput p =>
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) := by
  have hJ : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) :=
    BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  exact (measurable_from_prod_countable_right
      (f := fun v : Fin (M p) × SourceInput p => v.2.1.2 v.1)
      (fun q => (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst))).comp
    (hJ.prodMk measurable_id)

theorem measurable_reservedProposalBitCount :
    Measurable (reservedProposalBitCount (rate := rate) : SourceInput p → ℕ) := by
  unfold reservedProposalBitCount
  have hrow := measurable_originalSelectedCompleteRow (p := p)
  apply Finset.measurable_fun_sum (Finset.univ : Finset (Fin p.T))
  intro time htime
  have hbit : Measurable (fun z : SourceInput p =>
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) time) :=
    (FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
      p rate.eta.val).comp (hrow.prodMk measurable_const)
  exact Measurable.ite ((measurableSet_singleton true).preimage hbit)
    measurable_const measurable_const

theorem reservedProposalBitCount_integrable_fixedID (ids : CompletePublicTable.IDArray p) :
    Integrable (fun z : SourceInput p =>
      (reservedProposalBitCount (rate := rate) z : ℝ))
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) := by
  have hm : Measurable (fun z : SourceInput p =>
      (reservedProposalBitCount (rate := rate) z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_reservedProposalBitCount rate)
  apply Integrable.of_mem_Icc 0 (p.T : ℝ) hm.aemeasurable
  exact ae_of_all _ fun z => by
    constructor
    · exact_mod_cast Nat.zero_le (reservedProposalBitCount (rate := rate) z)
    · exact_mod_cast reservedProposalBitCount_le_horizon (rate := rate) z

private theorem proposalHazard_pos_lt_one :
    0 < FollowerCutoffScan.proposalHazard p rate.eta.val ∧
      FollowerCutoffScan.proposalHazard p rate.eta.val < 1 := by
  have hm1 : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide) p.two_le_m)
  have hm : 0 < (p.m : ℝ) := lt_of_lt_of_le (by norm_num) hm1
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide)
      (Nat.le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K)))
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) :=
    by exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hden : (1024 : ℝ) * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      _ = 1024 * (p.m : ℝ) * 1 * 1 := by ring
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
        gcongr
  have hetaSmall : rate.eta.val ≤ 1 / ((1024 : ℝ) * (p.m : ℝ)) := by
    calc
      rate.eta.val ≤
          1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        rate.sourceCap
      _ ≤ 1 / ((1024 : ℝ) * (p.m : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hden
  have hupper : FollowerCutoffScan.proposalHazard p rate.eta.val ≤ 1 / 256 := by
    rw [FollowerCutoffScan.proposalHazard]
    calc
      4 * (p.m : ℝ) * rate.eta.val ≤
          4 * (p.m : ℝ) * (1 / ((1024 : ℝ) * (p.m : ℝ))) :=
        mul_le_mul_of_nonneg_left hetaSmall (by positivity)
      _ = 1 / 256 := by field_simp [ne_of_gt hm]; norm_num
  constructor
  · rw [FollowerCutoffScan.proposalHazard]
    exact mul_pos (mul_pos (by norm_num) hm) rate.eta.property
  · exact lt_of_le_of_lt hupper (by norm_num)

private theorem scalarProposalIndicator_integral :
    (∫ x : ContinuousControlSlice.Scalar,
      if FollowerCutoffScan.thresholdProposalBit x
          (FollowerCutoffScan.proposalHazard p rate.eta.val)
      then (1 : ℝ) else 0 ∂ContinuousControlSlice.scalarLaw) =
      FollowerCutoffScan.proposalHazard p rate.eta.val := by
  let h := FollowerCutoffScan.proposalHazard p rate.eta.val
  let A : Set ContinuousControlSlice.Scalar := {x | x.val < h}
  have hh := proposalHazard_pos_lt_one (p := p) (rate := rate)
  have hA : MeasurableSet A := measurableSet_lt measurable_subtype_coe measurable_const
  have himage : Subtype.val '' A = Set.Ico 0 h := by
    ext y
    simp only [Set.mem_image, Set.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property.1, hx⟩
    · rintro ⟨hy0, hyh⟩
      exact ⟨⟨y, ⟨hy0, lt_trans hyh hh.2⟩⟩, hyh, rfl⟩
  have hfun : (fun x : ContinuousControlSlice.Scalar =>
      if FollowerCutoffScan.thresholdProposalBit x h then (1 : ℝ) else 0) =
      Set.indicator A (fun _ => (1 : ℝ)) := by
    funext x
    simp [A, Set.indicator, FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq]
  rw [hfun]
  calc
    _ = ContinuousControlSlice.scalarLaw.real A := integral_indicator_one hA
    _ = h := by
      rw [measureReal_def, ContinuousControlSlice.scalarLaw_apply, himage,
        Real.volume_Ico]
      simp [h, hh.1.le]

private theorem completeRows_selectedProposalBit_integral
    (j : Fin (M p)) (time : Fin p.T) :
    (∫ rows : CompleteRows p,
      if FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows j) time
      then (1 : ℝ) else 0 ∂completeRowsMeasure p) =
      FollowerCutoffScan.proposalHazard p rate.eta.val := by
  let scalar := fun rows : CompleteRows p =>
    ContinuousLearningRows.scalarAt time ContinuousControlSlice.Label.prop
      (CompletePublicTable.completeRowLearning p (rows j))
  let indicator := fun x : ContinuousControlSlice.Scalar =>
    if FollowerCutoffScan.thresholdProposalBit x
        (FollowerCutoffScan.proposalHazard p rate.eta.val)
    then (1 : ℝ) else 0
  have hmp : MeasurePreserving scalar (completeRowsMeasure p)
      ContinuousControlSlice.scalarLaw := by
    dsimp [scalar]
    exact (ContinuousLearningRows.measurePreserving_scalarAt time
        ContinuousControlSlice.Label.prop).comp
      ((CompletePublicTable.measurePreserving_completeRowLearning p).comp
        (CompletePublicTable.measurePreserving_completeRowProjection p j))
  have hcomp : (fun rows : CompleteRows p => indicator (scalar rows)) =
      (fun rows => if FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (rows j) time then (1 : ℝ) else 0) := by
    funext rows
    by_cases hp : (((rows j).2 time).1 ContinuousControlSlice.Label.prop).val <
        FollowerCutoffScan.proposalHazard p rate.eta.val
    · simp [FollowerCutoffScan.completeRowProposalBit,
        FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq, indicator, scalar,
        ContinuousLearningRows.scalarAt, CompletePublicTable.completeRowLearning, hp]
    · simp [FollowerCutoffScan.completeRowProposalBit,
        FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq, indicator, scalar,
        ContinuousLearningRows.scalarAt, CompletePublicTable.completeRowLearning, hp]
  have hindicator : Measurable indicator := by
    have heq : indicator = (fun x : ContinuousControlSlice.Scalar =>
        if x.val < FollowerCutoffScan.proposalHazard p rate.eta.val
        then (1 : ℝ) else 0) := by
      funext x
      simp [indicator, FollowerCutoffScan.thresholdProposalBit]
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
      measurable_const measurable_const
  have hfm : AEStronglyMeasurable indicator
      (Measure.map scalar (completeRowsMeasure p)) := by
    rw [hmp.map_eq]
    exact hindicator.aestronglyMeasurable
  rw [← hcomp]
  calc
    _ = ∫ x, indicator x ∂ContinuousControlSlice.scalarLaw := by
      rw [← hmp.map_eq]
      exact (integral_map hmp.measurable.aemeasurable hfm).symm
    _ = _ := scalarProposalIndicator_integral (p := p) (rate := rate)

theorem reservedProposalBitCount_fixedID_mean (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p,
      (reservedProposalBitCount (rate := rate) z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) =
      FollowerCutoffScan.proposalHazard p rate.eta.val * (p.T : ℝ) := by
  let insertion := ReferenceFixedIDSourceSection.fixedIDSourceInsertion (p := p) ids
  have hWint := reservedProposalBitCount_integrable_fixedID rate ids
  rw [ReferenceFixedIDSourceSection.fixedIDSourceLaw_integral_eq_insertion
    (p := p) ids _ hWint]
  have hmeas : Measurable (fun w : CompleteRows p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (reservedProposalBitCount (rate := rate) (insertion w) : ℝ)) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_reservedProposalBitCount rate)).comp
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceInsertion (p := p) ids)
  have hinsertInt : Integrable (fun w : CompleteRows p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (reservedProposalBitCount (rate := rate) (insertion w) : ℝ))
      ((completeRowsMeasure p).prod (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
    apply Integrable.of_mem_Icc 0 (p.T : ℝ) hmeas.aemeasurable
    exact ae_of_all _ fun w => by
      constructor
      · exact_mod_cast Nat.zero_le (reservedProposalBitCount (rate := rate) (insertion w))
      · exact_mod_cast reservedProposalBitCount_le_horizon (rate := rate) (insertion w)
  rw [integral_prod_symm _ hinsertInt]
  have hinner (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
      (∫ rows : CompleteRows p,
        (reservedProposalBitCount (rate := rate) ((ids, rows), e) : ℝ)
        ∂completeRowsMeasure p) =
        (p.T : ℝ) * FollowerCutoffScan.proposalHazard p rate.eta.val := by
    let j := PrivateSourceStreams.coordinatorIndex p e.1.2
    have hJ (rows : CompleteRows p) :
        ActualInitializationPhysicalStep.selectedRowIndex p ((ids, rows), e) = j := by
      simp [j, ActualInitializationPhysicalStep.selectedRowIndex,
        PrivateSourceStreams.coordinatorIndex]
    have htermInt (time : Fin p.T) : Integrable
        (fun rows : CompleteRows p =>
          if FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows j) time
          then (1 : ℝ) else 0) (completeRowsMeasure p) := by
      have hbit : Measurable (fun rows : CompleteRows p =>
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows j) time) :=
        (FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
          p rate.eta.val).comp
          ((CompletePublicTable.measurable_completeRowProjection p j).prodMk measurable_const)
      have hm : Measurable (fun rows : CompleteRows p =>
          if FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows j) time
          then (1 : ℝ) else 0) :=
        Measurable.ite ((measurableSet_singleton true).preimage hbit)
          measurable_const measurable_const
      apply Integrable.of_mem_Icc 0 1 hm.aemeasurable
      exact ae_of_all _ fun rows => by split <;> norm_num
    have hsum : (∫ rows : CompleteRows p,
        (reservedProposalBitCount (rate := rate) ((ids, rows), e) : ℝ)
        ∂completeRowsMeasure p) =
        ∑ time : Fin p.T, FollowerCutoffScan.proposalHazard p rate.eta.val := by
      simp_rw [reservedProposalBitCount, hJ, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      rw [integral_finsetSum (Finset.univ : Finset (Fin p.T))
        (fun time _ => htermInt time)]
      apply Finset.sum_congr rfl
      intro time htime
      exact completeRows_selectedProposalBit_integral (p := p) (rate := rate) j time
    rw [hsum]
    simp
  simp_rw [insertion, ReferenceFixedIDSourceSection.fixedIDSourceInsertion]
  simp_rw [hinner]
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- Every original fixed-ID source law satisfies the physical all-horizon
transfer envelope. The full run is counted even after decoder failure or overflow. -/
theorem actualPhysicalTransferCount_fixedID_mean_le
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p,
      (actualPhysicalTransferCount (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z : ℝ)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      (4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2 := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H := EpisodeStartCount.episodeHorizon_pos p
    rate.eta.property rate.sourceCap
  have hHreal : 0 < (H : ℝ) := by exact_mod_cast hH
  have hHlower : 1 / (128 * rate.eta.val) ≤ (H : ℝ) :=
    EpisodeStartCount.episodeHorizon_cast_lower p rate.eta.property rate.sourceCap
  have hprod : (1 : ℝ) ≤ (H : ℝ) * (128 * rate.eta.val) :=
    (div_le_iff₀ (mul_pos (by norm_num) rate.eta.property)).mp hHlower
  have hdiv : ((p.T / H : ℕ) : ℝ) ≤ 128 * rate.eta.val * (p.T : ℝ) := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ hHreal).mpr
    calc
      (p.T : ℝ) ≤ (p.T : ℝ) * ((H : ℝ) * (128 * rate.eta.val)) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg p.T)
      _ = 128 * rate.eta.val * (p.T : ℝ) * (H : ℝ) := by ring
  have hW := reservedProposalBitCount_integrable_fixedID rate ids
  have hM := actualPhysicalTransferCount_integrable_fixedID
    rate rewards C_star C_h ids
  have hbound : Integrable (fun z : SourceInput p =>
      (reservedProposalBitCount (rate := rate) z : ℝ) + (p.T / H : ℕ) + 2)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) :=
    (hW.add (integrable_const _)).add (integrable_const _)
  calc
    _ ≤ ∫ z : SourceInput p,
        (reservedProposalBitCount (rate := rate) z : ℝ) + (p.T / H : ℕ) + 2
        ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
      apply integral_mono hM hbound
      intro z
      dsimp only [H]
      exact_mod_cast actualPhysicalTransferCount_le_reservedProposalBitCount_grid
        rate rewards C_star C_h z
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val * (p.T : ℝ) +
        (p.T / H : ℕ) + 2 := by
      rw [integral_add (f := fun z : SourceInput p =>
          (reservedProposalBitCount (rate := rate) z : ℝ) + (p.T / H : ℕ))
          (g := fun _ : SourceInput p => (2 : ℝ))
          (hW.add (integrable_const _)) (integrable_const _),
        integral_add (f := fun z : SourceInput p =>
          (reservedProposalBitCount (rate := rate) z : ℝ))
          (g := fun _ : SourceInput p => ((p.T / H : ℕ) : ℝ))
          hW (integrable_const _),
        reservedProposalBitCount_fixedID_mean rate ids]
      simp
    _ ≤ (4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2 := by
      rw [FollowerCutoffScan.proposalHazard]
      nlinarith only [hdiv]

end Bandits.Support.ReferenceOriginalCalendarPhysicalTransferCount

end
