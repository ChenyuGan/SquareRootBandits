/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstComplementReplay
import Lean.Elab.Tactic.Omega

/-!
# Actual first-cutoff outside-register initialization

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,246-269,294`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-53`, and
`sources/zip4/manuscript/05_binary_transport.tex:354-396`.

This module selects the first actual cutoff record in the original physical
run and identifies the outside-register initializer computed at that record.
The diagnostic queue seed is the zero-seeded replay on the retained records
strictly before the chosen cutoff. It is an internal pathwise result; it does
not identify these diagnostics with the common analytical `RecordedQueueRun`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceFirstCutoffOutsideInitialization

abbrev Parameters := ReferenceFirstComplementReplay.Parameters
abbrev RateInput := ReferenceFirstComplementReplay.RateInput
abbrev State := ReferenceFirstComplementReplay.State
abbrev RoundRecord := ReferenceFirstComplementReplay.RoundRecord

variable {p : Parameters} {rate : RateInput p}

private theorem takeWhile_firstFailure {α : Type} (predicate : α → Bool)
    (records : List α)
    (hshort : (records.takeWhile predicate).length < records.length) :
    ∃ record suffix,
      records = records.takeWhile predicate ++ record :: suffix ∧
        predicate record = false := by
  induction records with
  | nil => simp at hshort
  | cons head tail ih =>
      cases hhead : predicate head with
      | true =>
        have htail : (tail.takeWhile predicate).length < tail.length := by
          simp only [List.takeWhile_cons_of_pos hhead, List.length_cons] at hshort
          omega
        obtain ⟨record, suffix, hsplit, hfailed⟩ := ih htail
        refine ⟨record, suffix, ?_, hfailed⟩
        rw [List.takeWhile_cons_of_pos hhead]
        calc
          head :: tail = head :: (tail.takeWhile predicate ++ record :: suffix) :=
            congrArg (List.cons head) hsplit
          _ = (head :: tail.takeWhile predicate) ++ record :: suffix := by
            simp only [List.cons_append]
      | false =>
        have hnot : ¬ predicate head := by simp [hhead]
        refine ⟨head, tail, ?_, hhead⟩
        simp [List.takeWhile_cons_of_neg hnot]

private theorem first_live_actual_cutoff_record
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := firstLiveWindow execution.records
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
        cut = execution.records[window.length]'(by
          rw [ReferenceActivePhysicalHorizon.run_record_count]
          omega) ∧
        cut.input.time.val = start + window.length ∧
        ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := firstLiveWindow execution.records
  have hrecords : execution.records.length = count := by
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
      start count hspan active
  have hwindowShort : window.length < execution.records.length := by
    rw [hrecords]
    exact hshort
  obtain ⟨cut, suffix, hsplit, hfailed⟩ :=
    takeWhile_firstFailure
      (fun record : RoundRecord p rate =>
        !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
      execution.records (by simpa [window, firstLiveWindow] using hwindowShort)
  have hwindowLength : window.length < count := by
    simpa [window, execution] using hshort
  have hcutIndex :
      cut = execution.records[window.length]'(by omega) := by
    have hget : execution.records[window.length]? = some cut := by
      rw [hsplit]
      simp [window, firstLiveWindow]
    have hgetIndex : execution.records[window.length]? =
        some (execution.records[window.length]'hwindowShort) := by
      simp [hwindowShort]
    exact Option.some.inj (hget.symm.trans hgetIndex)
  have htimeList :
      (execution.records.map fun record => record.input.time.val)[window.length]? =
        some (start + window.length) := by
    rw [ReferenceActivePhysicalHorizon.run_time_values]
    simp [ReferenceActivePhysicalHorizon.calendar, hwindowLength]
  have hmapIndex : window.length <
      (execution.records.map fun record => record.input.time.val).length := by
    rw [List.length_map, hrecords]
    exact hwindowLength
  have hmapValue :
      (execution.records.map fun record => record.input.time.val)[window.length]'hmapIndex =
        start + window.length := by
    obtain ⟨_, hvalue⟩ := List.getElem_of_getElem? htimeList
    exact hvalue
  have htimeIndex :
      (execution.records.map fun record => record.input.time.val)[window.length]'hmapIndex =
        cut.input.time.val := by
    calc
      _ = (execution.records[window.length]'hwindowShort).input.time.val := by simp
      _ = cut.input.time.val :=
        congrArg (fun record : RoundRecord p rate => record.input.time.val) hcutIndex.symm
  have hcutTime := htimeIndex.symm.trans hmapValue
  have hcutChosen : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
    cases hchosen : ReferenceCollectionPhaseHistory.cutoffChosen cut.input with
    | false => simp [hchosen] at hfailed
    | true => rfl
  exact ⟨cut, suffix, hsplit, hcutIndex,
    hcutTime, hcutChosen⟩

private theorem mem_foldCalendar_of_mem
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (active : allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial)
    {record : RoundRecord p rate} (hrecord : record ∈ acc.records) :
    record ∈ (ReferenceActivePhysicalHorizon.foldCalendar initial rows J rewards origin
      intervalStart count horigin hspan active acc).records := by
  unfold ReferenceActivePhysicalHorizon.foldCalendar
  let step := ReferenceActivePhysicalHorizon.foldRound initial rows J rewards origin active
  have hkeep : ∀ (entries : List
      (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
      (acc : ReferenceActivePhysicalHorizon.Run initial),
      record ∈ acc.records → record ∈ (entries.foldl step acc).records := by
    intro entries
    induction entries with
    | nil =>
        intro acc hrecord
        simpa using hrecord
    | cons entry rest ih =>
        intro acc hrecord
        change record ∈ (rest.foldl step (step acc entry)).records
        apply ih
        simp [step, ReferenceActivePhysicalHorizon.foldRound, hrecord]
  exact hkeep _ _ hrecord

private theorem first_cut_actualRunRecordAt_eq
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count k : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hprefix : k + 1 ≤ count)
    (cut : RoundRecord p rate)
    (hcutMem : cut ∈
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)
    (htime : cut.input.time.val = start + k) :
    cut = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
      start k (by omega) active := by
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
    (by omega) active
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
    start k (by omega) active
  have hactualPrefix : actual ∈ prefixRun.records := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
    simp [actual]
  let rest := count - (k + 1)
  have hcount : (k + 1) + rest = count := by
    dsimp [rest]
    omega
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows J rewards
    start (k + 1) rest (by omega) active
  have happendRecords := congrArg ReferenceActivePhysicalHorizon.Run.records happend
  have hrecords :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records =
        (ReferenceActivePhysicalHorizon.foldCalendar initial rows J rewards start
          (start + (k + 1)) rest (by omega) (by omega) active prefixRun).records := by
    simpa only [hcount, prefixRun] using happendRecords
  have hactualFull : actual ∈
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records := by
    rw [hrecords]
    exact mem_foldCalendar_of_mem initial rows J rewards start (start + (k + 1)) rest
      (by omega) (by omega) active prefixRun hactualPrefix
  have hactualTime : actual.input.time.val = start + k := by
    dsimp [actual, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows J
    rewards start count hspan active hcutMem hactualFull (htime.trans hactualTime.symm)

private theorem startRound_update_detectCutoff
    (eta : ℝ) (time : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (sigma : Fin p.T)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p eta)
    (hvalid : CoordinatorPhaseClock.clockRegistersValid p eta clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hstart : CoordinatorPhaseClock.startRound p eta time clock pending = .ok result)
    (hresultClock : result.clock = { clock with u := some time })
    (hnoAssignment : result.assignmentStart = none) :
    CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma) := by
  classical
  have hstart' := hstart
  simp only [CoordinatorPhaseClock.startRound, if_pos hparam,
    dif_pos hvalid, dif_pos htime] at hstart'
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure => simp [hdetect] at hstart'
  | ok decision =>
      cases decision with
      | cutoff actualSigma hactualSigma =>
          have hsame : actualSigma = sigma :=
            Option.some.inj (hactualSigma.symm.trans hsigma)
          subst actualSigma
          have hproof : hactualSigma = hsigma := Subsingleton.elim _ _
          cases hproof
          rfl
      | noCutoff =>
          by_cases hready : CoordinatorPhaseClock.sourceStartTest
              clock.sigma clock.u time pending
          · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p time
                (FollowerCutoffScan.gridBoundary p eta time)
            · simp [hdetect, hready, hgrid] at hstart'
              have hassignment :=
                congrArg CoordinatorPhaseClock.StartRoundResult.assignmentStart
                  (Except.ok.inj hstart')
              rw [hnoAssignment] at hassignment
              simp at hassignment
            · simp [hdetect, hready, hgrid] at hstart'
          · simp [hdetect, hready] at hstart'
            have hclockEq := congrArg CoordinatorPhaseClock.StartRoundResult.clock
              (Except.ok.inj hstart')
            rw [hresultClock] at hclockEq
            have huEq := congrArg CoordinatorPhaseClock.ClockRegisters.u hclockEq
            rw [hu] at huEq
            simp at huEq

private theorem detectCutoff_first_cause
    (clock : CoordinatorPhaseClock.ClockRegisters p) (time sigma : Fin p.T)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hdetect : CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma)) :
    FollowerCutoffScan.calendarRound time = clock.g ∨
      ∃ stamp, clock.lastProposal = some (stamp, true) ∧
        stamp.val + 1 = time.val := by
  classical
  cases clock with
  | mk savedSigma savedCutoff boundary savedProposal =>
    cases savedSigma with
    | none => simp at hsigma
    | some clockSigma =>
      have hsame : clockSigma = sigma := Option.some.inj hsigma
      subst clockSigma
      cases savedCutoff with
      | some oldCutoff => simp at hu
      | none =>
        by_cases hgrid : FollowerCutoffScan.calendarRound time = boundary
        · exact Or.inl hgrid
        · right
          cases savedProposal with
          | none =>
              simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
                CoordinatorPhaseClock.savedPriorProposal] at hdetect
              change Except.error CoordinatorPhaseClock.ClockFailure.missingPriorProposal =
                Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma hsigma) at hdetect
              cases hdetect
          | some pair =>
              rcases pair with ⟨stamp, bit⟩
              by_cases hstamp : stamp.val + 1 = time.val
              · cases bit with
                | false =>
                    simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
                      CoordinatorPhaseClock.savedPriorProposal, hstamp] at hdetect
                    change Except.ok CoordinatorPhaseClock.CutoffDecision.noCutoff =
                      Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma hsigma)
                        at hdetect
                    cases hdetect
                | true =>
                    exact ⟨stamp, rfl, hstamp⟩
              · simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
                  CoordinatorPhaseClock.savedPriorProposal, hstamp] at hdetect
                change Except.error CoordinatorPhaseClock.ClockFailure.stalePriorProposal =
                  Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma hsigma) at hdetect
                cases hdetect

private theorem liveDispatch_state_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x = .live r q base outcome) :
    x.state.coordinator = .live r q base := by
  cases hstate : x.state.coordinator with
  | first =>
      simp [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hdispatch
      cases hdispatch
  | live r' q' base' =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hdispatch
      cases hdispatch
      rfl
  | collection payload ledger proposal =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      split at hdispatch
      · simp only [CoordinatorRoundDispatch.dispatch] at hdispatch
        cases hdispatch
      · cases hdispatch
  | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch

private theorem cutoffChosen_liveOutcome
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ)
      (outcome : CoordinatorRoundDispatch.LiveOutcome
        (ReferenceActivePhysicalStep.liveInput x r q base)),
      x.state.coordinator = .live r q base ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base outcome := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcutoff
  cases hprep : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first firstOutcome => simp [hprep] at hcutoff
  | live r q base outcome =>
      cases outcome with
      | clockFailure failure heq => simp [hprep] at hcutoff
      | initializerFailure dispatched hstart checked heq => simp [hprep] at hcutoff
      | localFailure dispatched hstart reason => simp [hprep] at hcutoff
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hno selected =>
          have hdispatch : ReferenceActivePhysicalStep.dispatch x =
              .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
                hclock hpending hno selected) := by
            simpa only [ReferenceActivePhysicalStep.prepare] using hprep
          have hstate := liveDispatch_state_eq x r q base _ hdispatch
          exact ⟨r, q, base, .cutoffChosen dispatched hstart ledger hinit hledger hdomain
            hclock hpending hno selected, hstate, rfl⟩
      | continuingChosen dispatched hstart continuation selected => simp [hprep] at hcutoff
  | collection payload ledger clock cutoff outcome => simp [hprep] at hcutoff
  | invalidCollectionCutoff => simp [hprep] at hcutoff
  | dagger => simp [hprep] at hcutoff

private theorem firstCutoff_eq_actualEndpoint
    (eta : ℝ) (sigma time : Fin p.T) (start index : ℕ)
    (bits : Fin p.T → Bool)
    (hsigma : sigma.val = start)
    (hindexPositive : 0 < index)
    (htime : time.val = start + index)
    (hgridBound : FollowerCutoffScan.calendarRound time ≤
      FollowerCutoffScan.gridBoundary p eta sigma)
    (hcause : FollowerCutoffScan.calendarRound time =
        FollowerCutoffScan.gridBoundary p eta sigma ∨
      ∃ stamp, bits stamp = true ∧ stamp.val + 1 = time.val)
    (hproposalHistory : ∀ i : Fin p.T, start ≤ i.val →
      i.val + 1 < start + index → bits i = false) :
    FollowerCutoffScan.firstCutoff p eta sigma bits = time.val + 1 := by
  let endpoint := time.val + 1
  have hendpointGrid : endpoint ≤ FollowerCutoffScan.gridBoundary p eta sigma := by
    simpa [endpoint, FollowerCutoffScan.calendarRound] using hgridBound
  have hmem : endpoint ∈ FollowerCutoffScan.firstCutoffCarrier p eta sigma bits := by
    rcases hcause with hgrid | ⟨stamp, hbit, hstamp⟩
    · apply Finset.mem_insert.mpr
      left
      dsimp [endpoint]
      simpa [FollowerCutoffScan.calendarRound] using hgrid
    · apply Finset.mem_insert_of_mem
      unfold FollowerCutoffScan.trueProposalEndpoints
      apply Finset.mem_image.mpr
      have hstampEndpoint : stamp.val + 1 = start + index := hstamp.trans htime
      refine ⟨stamp, Finset.mem_filter.mpr ⟨?_, hbit⟩, ?_⟩
      · simp [FollowerCutoffScan.proposalCoordinates]
        constructor
        · apply Fin.le_iff_val_le_val.mpr
          omega
        · have htimeLt := time.isLt
          omega
      · simp [FollowerCutoffScan.proposalEndpoint, endpoint]
        omega
  have hleast : ∀ value,
      value ∈ FollowerCutoffScan.firstCutoffCarrier p eta sigma bits → endpoint ≤ value := by
    intro value hvalue
    simp only [FollowerCutoffScan.firstCutoffCarrier, Finset.mem_insert] at hvalue
    rcases hvalue with hgrid | hevent
    · rw [hgrid]
      exact hendpointGrid
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hevent
      have hi' := Finset.mem_filter.mp hi
      have hiCoord : sigma.val ≤ i.val ∧ i.val + 1 < p.T := by
        simpa [FollowerCutoffScan.proposalCoordinates] using hi'.1
      have heq' : i.val + 2 = value := by
        simpa [FollowerCutoffScan.proposalEndpoint] using heq
      by_cases hle : endpoint ≤ value
      · exact hle
      · have hbefore : i.val + 1 < start + index := by
          dsimp [endpoint] at hle
          rw [← heq', htime] at hle
          omega
        have hfalse := hproposalHistory i (by rw [← hsigma]; exact hiCoord.1) hbefore
        rw [hi'.2] at hfalse
        cases hfalse
  unfold FollowerCutoffScan.firstCutoff
  apply (Finset.min'_eq_iff _ _ endpoint).2
  exact ⟨hmem, hleast⟩

/-- Produce the actual first cutoff initializer at the first failed predicate
of the original first-live window. The output retains the exact physical
record, the prior computed run endpoint, the accepted dispatcher constructor,
the whole installed payload, and the diagnostic replay which seeds its
outside registers. These pathwise diagnostics are not identified here with an
analytical recorded queue run.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,246-269,294`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-53`, and
`sources/zip4/manuscript/05_binary_transport.tex:354-396`. -/
theorem run_first_cutoff_outside_initializer
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let k := window.length
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start k
      (by
        have hwindowShort : window.length < count := hshort
        exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hwindowShort) start) hspan) active
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[window.length]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
      cut.input.time.val = start + k ∧
      cut = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k
        (by
          have hwindowShort : window.length < count := hshort
          exact le_trans
            (Nat.add_le_add_left (Nat.succ_le_of_lt hwindowShort) start) hspan) active ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state = prefixRun.finalState ∧
        prefixRun.finalState.coordinator = .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val callInput.registers.time
            callInput.registers.priorClock callInput.registers.clockPending =
              .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            { callInput.registers.priorClock with u := some callInput.registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection callInput.registers.payload
            dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights callInput.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          k > 0 ∧
          r.payload.sigma.val = start ∧
          (∀ i, base i = 0) ∧
          (∃ birth, birth ∈ prefixRun.records ∧
            ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
            birth.input.time.val = start ∧
            ∃ installed birthSelection,
              birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
              installed.registers.payload = r.payload) ∧
          (∀ i : Fin p.T, start ≤ i.val → i.val + 1 < start + k →
            FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) i = false) ∧
          (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
            let D := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1
              window k
            D.length = k ∧
            (∀ d ∈ D, d.1 = true) ∧
            (r.complementScores a, q.queue a) =
              QueueReplay.replay (4 * r.payload.n) (0, 0) D ∧
            q.previousService a =
              CollectionKnownQueueContinuation.replayLastService
                (4 * r.payload.n) (0, 0) 0 D) ∧
          let u := cut.input.time.val + 1
          u = start + k + 1 ∧
          r.payload.sigma.val + 1 < u ∧
          u ≤ p.T ∧
          u ≤ r.gridBoundary ∧
          r.gridBoundary ≤ p.T + 1 ∧
          ledger.sigma = r.payload.sigma.val + 1 ∧
          ledger.cutoff = u ∧
          ledger.freezeAt = r.gridBoundary ∧
          FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = u ∧
          (∀ a, a ∉ CanonicalFastSampling.fastArmFinset r.payload.slowSet →
            CoordinatorStartRoundCutoffDispatch.outsideRegisters callInput.registers
              callInput.ownedRegisters a = none) ∧
          (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
            let D := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1
              window k
            CoordinatorStartRoundCutoffDispatch.outsideRegisters callInput.registers
              callInput.ownedRegisters a.1 = some {
                score := (QueueReplay.replay (4 * r.payload.n) (0, 0) D).1
                queue := (QueueReplay.replay (4 * r.payload.n) (0, 0) D).2
                lastService := CollectionKnownQueueContinuation.replayLastService
                  (4 * r.payload.n) (0, 0) 0 D }) ∧
          ledger.cutoffRegisters = CoordinatorStartRoundCutoffDispatch.outsideRegisters
            callInput.registers callInput.ownedRegisters ∧
          ledger.currentRegisters = (fun a =>
            (CoordinatorStartRoundCutoffDispatch.outsideRegisters
              callInput.registers callInput.ownedRegisters a).map
                (fun reg => ⟨reg.queue, reg.lastService⟩)) ∧
          ledger.baseScore = base ∧
          ledger.pending = Finset.univ ∧
          ledger.increment = (fun _ : Fin p.K => 0) ∧
          ledger.gammaLoc = (fun _ : Fin p.K => 0) ∧
          ledger.rawBuffer = (fun _ _ => none) ∧
          ledger.enabledHistory = (fun _ => none) ∧
          ledger.cursor = u ∧
          ledger.phase = .ready ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).cutoffRegisters = ledger.cutoffRegisters ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).currentRegisters = ledger.currentRegisters ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).increment = ledger.increment ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).gammaLoc = ledger.gammaLoc ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).rawBuffer = ledger.rawBuffer ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).enabledHistory = ledger.enabledHistory ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).cursor = ledger.cursor ∧
          (ReferenceActivePhysicalStep.sharedLedger ledger).phase = ledger.phase ∧
          ∃ (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
            (choice : ReferenceCollectionSegmentExtraction.Choice rate),
            initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
              callInput.registers callInput.ownedRegisters base callInput.registers.time ∧
            ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
            choice.initializer = some initializer ∧
            initializer.checkedStart rate = .success
              (ReferenceActivePhysicalStep.sharedLedger ledger) := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let k := window.length
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start k
    (by
      have hwindowShort : window.length < count := by
        simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hwindowShort) start) hspan) active
  obtain ⟨cut, suffix, hsplit, hindex, htime, hcutChosen⟩ :=
    first_live_actual_cutoff_record initial rows J rewards start count hspan active hshort
  have hcutMem : cut ∈ execution.records := by
    rw [hsplit]
    simp
  have hwindowShort : window.length < count := hshort
  have hactual := first_cut_actualRunRecordAt_eq initial rows J rewards start count k
    hspan active (Nat.succ_le_of_lt hwindowShort)
    cut hcutMem htime
  have hinputState : cut.input.state = prefixRun.finalState := by
    rw [hactual]
    rfl
  rcases cutoffChosen_liveOutcome cut.input hcutChosen with
    ⟨r, q, base, outcome, hstate, hprep⟩
  have htag : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := hcutChosen
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at htag
  rw [hprep] at htag
  cases outcome with
  | clockFailure failure heq => simp at htag
  | initializerFailure dispatched hstart checked heq => simp at htag
  | localFailure dispatched hstart reason => simp at htag
  | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected =>
      let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
      have hstateEndpoint : prefixRun.finalState.coordinator = .live r q base := by
        rw [← hinputState]
        exact hstate
      have hkcount : k ≤ count := by
        exact Nat.le_of_lt hwindowShort
      have hkwindow : k ≤ window.length := by rfl
      have hreplay := ReferenceFirstComplementReplay.run_first_complement_replay
        initial rows J rewards start count hspan active hfirst k hkcount hkwindow
        r q base hstateEndpoint
      rcases hreplay with ⟨hkpos, hsigma, hbase, hbirth, hproposalHistory, hqueues⟩
      have hclockSeed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start count hspan active hclockSeed
      have hclockRecord := (hclockRun.2.2.2 cut hcutMem).1
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclockRecord
      rcases hclockRecord with ⟨hclockTime, hclockValid, hpriorSigma, hpriorU, hgrid,
        hsourceTime, htimeBeforeGrid, hproposalToken⟩
      have hcalendarBound : FollowerCutoffScan.calendarRound cut.input.time ≤
          r.priorClock.g := by
        rw [← hgrid]
        simp only [FollowerCutoffScan.calendarRound]
        omega
      have hstartValid : CoordinatorPhaseClock.startRoundTimeValid p cut.input.time
          r.priorClock := by
        simp only [CoordinatorPhaseClock.startRoundTimeValid, hpriorSigma, hpriorU]
        exact ⟨hsourceTime, hcalendarBound⟩
      have hclockGrid : r.priorClock.g =
          FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        simpa [CoordinatorPhaseClock.boundaryFromSigma, hpriorSigma] using hclockValid.1
      have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
      have hdetect := startRound_update_detectCutoff rate.eta.val cut.input.time
        r.priorClock r.clockPending dispatched.startResult r.payload.sigma hparam
        hclockValid hstartValid hpriorSigma hpriorU hstart hclock hnoAssignment
      have hcauseRaw := detectCutoff_first_cause r.priorClock cut.input.time
        r.payload.sigma hpriorSigma hpriorU hdetect
      have hcause : FollowerCutoffScan.calendarRound cut.input.time =
          FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∨
        ∃ stamp, FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) stamp = true ∧
          stamp.val + 1 = cut.input.time.val := by
        rcases hcauseRaw with hgridCause | ⟨stamp, htoken, hstamp⟩
        · left
          calc
            FollowerCutoffScan.calendarRound cut.input.time = r.priorClock.g := hgridCause
            _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := hclockGrid
        · right
          have hpair := Option.some.inj (htoken.symm.trans hproposalToken)
          have hstampEq : stamp.val = r.time.val := congrArg Fin.val (congrArg Prod.fst hpair)
          have hbitEq : true =
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) r.time :=
            congrArg Prod.snd hpair
          refine ⟨r.time, hbitEq.symm, ?_⟩
          omega
      have hgridBound : FollowerCutoffScan.calendarRound cut.input.time ≤
          FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        calc
          FollowerCutoffScan.calendarRound cut.input.time ≤ r.priorClock.g := hcalendarBound
          _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := hclockGrid
      have huFirstCutoff := firstCutoff_eq_actualEndpoint rate.eta.val r.payload.sigma
        cut.input.time start k (FollowerCutoffScan.completeRowProposalBit
          p rate.eta.val (rows J)) hsigma hkpos htime hgridBound hcause hproposalHistory
      let u := cut.input.time.val + 1
      have huValue : u = start + k + 1 := by
        dsimp [u]
        rw [htime]
      have hdomainForBounds := hdomain
      rcases hdomainForBounds with ⟨_, _, hsourceLess, _, hgridBoundT, _, _, _, _, _, _, _⟩
      have hsourceBeforeU : r.payload.sigma.val + 1 < u := by
        dsimp [u]
        rw [hsigma, htime]
        omega
      have huLeT : u ≤ p.T := by
        dsimp [u]
        omega
      have huLeGrid : u ≤ r.gridBoundary := by
        rw [hgrid]
        simpa [u, FollowerCutoffScan.calendarRound] using hcalendarBound
      have hgridLeT : r.gridBoundary ≤ p.T + 1 := by
        simpa [callInput, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt] using hgridBoundT
      have hledgerSigma : ledger.sigma = r.payload.sigma.val + 1 := by
        rw [hledger]
        rfl
      have hledgerCutoff : ledger.cutoff = u := by
        rw [hledger]
        rfl
      have hledgerFreeze : ledger.freezeAt = r.gridBoundary := by
        rw [hledger]
        rfl
      have hfields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
        callInput.registers callInput.ownedRegisters base callInput.registers.time
      rcases hfields with ⟨_, _, _, _, hbaseLedger, hpendingLedger, _, hcutoffRegisters,
        hcurrentRegisters, hincrement, hgamma, hraw, henabled, hcursor, hphase⟩
      have houtsideSlow : ∀ a,
          a ∉ CanonicalFastSampling.fastArmFinset r.payload.slowSet →
          CoordinatorStartRoundCutoffDispatch.outsideRegisters callInput.registers
            callInput.ownedRegisters a = none := by
        intro a ha
        simp [CoordinatorStartRoundCutoffDispatch.outsideRegisters, callInput,
          ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt,
          ReferenceActivePhysicalStep.liveOwnedAt, ha]
      have houtsideFast : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
          let D := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1
            window k
          CoordinatorStartRoundCutoffDispatch.outsideRegisters callInput.registers
            callInput.ownedRegisters a.1 = some {
              score := (QueueReplay.replay (4 * r.payload.n) (0, 0) D).1
              queue := (QueueReplay.replay (4 * r.payload.n) (0, 0) D).2
              lastService := CollectionKnownQueueContinuation.replayLastService
                (4 * r.payload.n) (0, 0) 0 D } := by
        intro a
        rcases hqueues a with ⟨_, _, hscoreQueue, hlastService⟩
        have hscore := congrArg Prod.fst hscoreQueue
        have hqueue := congrArg Prod.snd hscoreQueue
        change CoordinatorStartRoundCutoffDispatch.outsideRegisters r q a.1 = some {
          score := (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window k)).1
          queue := (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window k)).2
          lastService := CollectionKnownQueueContinuation.replayLastService
            (4 * r.payload.n) (0, 0) 0
            (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window k) }
        unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters
        rw [dif_pos a.property]
        dsimp
        simp only [Option.some.injEq]
        rw [CoordinatorCollectionLedger.CutoffRegister.mk.injEq]
        exact ⟨by simpa [window, execution] using hscore,
          by simpa [window, execution] using hqueue,
          by simpa [window, execution] using hlastService⟩
      have hledgerFields :
          ledger.cutoffRegisters = CoordinatorStartRoundCutoffDispatch.outsideRegisters
              callInput.registers callInput.ownedRegisters ∧
          ledger.currentRegisters = (fun a =>
            (CoordinatorStartRoundCutoffDispatch.outsideRegisters
              callInput.registers callInput.ownedRegisters a).map
                (fun reg => ⟨reg.queue, reg.lastService⟩)) ∧
          ledger.baseScore = base ∧ ledger.pending = Finset.univ ∧
          ledger.increment = (fun _ : Fin p.K => 0) ∧
          ledger.gammaLoc = (fun _ : Fin p.K => 0) ∧
          ledger.rawBuffer = (fun _ _ => none) ∧
          ledger.enabledHistory = (fun _ => none) ∧
          ledger.cursor = u ∧ ledger.phase = .ready := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hledger]
          exact hcutoffRegisters
        · rw [hledger]
          exact hcurrentRegisters
        · rw [hledger]
          exact hbaseLedger
        · rw [hledger]
          exact hpendingLedger
        · rw [hledger]
          exact hincrement
        · rw [hledger]
          exact hgamma
        · rw [hledger]
          exact hraw
        · rw [hledger]
          exact henabled
        · rw [hledger]
          simpa [u, callInput, ReferenceActivePhysicalStep.liveInput,
            ReferenceActivePhysicalStep.liveRegistersAt] using hcursor
        · rw [hledger]
          exact hphase
      rcases ReferenceActivePhysicalStep.sharedLedger_fields ledger with
        ⟨_, _, _, _, _, _, hsharedCutoff, hsharedCurrent, hsharedIncrement,
          hsharedGamma, hsharedRaw, hsharedEnabled, hsharedCursor, hsharedPhase⟩
      let initializer := ReferenceCollectionSegmentExtraction.cutoffInitializer
        callInput.registers callInput.ownedRegisters base callInput.registers.time
      let choice : ReferenceCollectionSegmentExtraction.Choice rate :=
        ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
          callInput.registers.complementWeights, some initializer⟩
      have hchoice : ReferenceCollectionSegmentExtraction.choice cut.input = some choice := by
        simp [ReferenceCollectionSegmentExtraction.choice,
          ReferenceCollectionSegmentExtraction.choiceOfCut, hprep,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, initializer, choice]
        rfl
      have hchecked := ReferenceCollectionSegmentExtraction.choice_initializer cut.input choice
        initializer hchoice rfl
      refine ⟨cut, suffix, hsplit, hindex, htime, hactual,
        r, q, base, hinputState, hstateEndpoint, ?_⟩
      refine ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
        hnoAssignment, selected, ?_⟩
      have hprepOutput : cut.output.preparation.coordinator =
          .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
            hpending hnoAssignment selected) := by
        rw [cut.output_eq]
        simpa [ReferenceActivePhysicalStep.step] using hprep
      refine ⟨hprepOutput, hkpos, hsigma, hbase, hbirth, hproposalHistory, hqueues,
        huValue, hsourceBeforeU, huLeT, huLeGrid, hgridLeT, hledgerSigma,
        hledgerCutoff, hledgerFreeze, huFirstCutoff, houtsideSlow, houtsideFast,
        hledgerFields.1, hledgerFields.2.1, hledgerFields.2.2.1,
        hledgerFields.2.2.2.1, hledgerFields.2.2.2.2.1,
        hledgerFields.2.2.2.2.2.1, hledgerFields.2.2.2.2.2.2.1,
        hledgerFields.2.2.2.2.2.2.2.1, hledgerFields.2.2.2.2.2.2.2.2.1,
        hledgerFields.2.2.2.2.2.2.2.2.2, hsharedCutoff, hsharedCurrent,
        hsharedIncrement, hsharedGamma, hsharedRaw, hsharedEnabled, hsharedCursor,
        hsharedPhase, ⟨initializer, choice, rfl, hchoice, rfl,
          by simpa [choice] using hchecked⟩⟩
  | continuingChosen dispatched hstart continuation selected => simp at htag

end Bandits.Support.ReferenceFirstCutoffOutsideInitialization

end
