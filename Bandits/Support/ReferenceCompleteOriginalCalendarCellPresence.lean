/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionKnownQueueSource

import Mathlib.Tactic

/-!
# Numerical cells on the actual original-calendar suffix

Every actual record of the complete physical suffix has a literal live or
collection numerical cell. On launch, one common numerical word supplies every
original-date optional prefix. No-launch retains literal absence.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceLaterLiveNumericalReadout
open ReferenceLaterCollectionArrivalReadout
open ReferenceFirstCollectionCurrentRetainedGate
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open scoped Classical

namespace Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence

variable {p : ConstructorDimensions.Parameters}

/-- With no actual initialization crossing, the complete physical suffix is
empty, its origin is the terminal calendar coordinate, and the literal
optional numerical prefix remains absent at every date. -/
theorem no_launch_complete_original_calendar_cell_presence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h = [] ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T ∧
    (∀ n, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z = none) := by
  obtain ⟨hstart, hrecords, _hterminal, _hhistory⟩ :=
    ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hlaunch
  have hcross :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome ≠ true := by
    intro hc
    have hs := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).2 hc
    rw [hlaunch] at hs
    cases hs
  refine ⟨hrecords, hstart, ?_⟩
  intro n
  have hnotLaunch :
      ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h n z := by
    intro hby
    change (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true ∧ _ at hby
    apply hcross
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hby.1
  exact (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_no_launch
    rate rewards C_star C_h n z hnotLaunch).1

/-- A genuine crossing at the terminal date has an empty physical suffix.
Its one available numerical boundary is the empty prefix, and the per-record
phase classification is vacuous because there are no suffix records. -/
theorem terminal_launch_complete_original_calendar_cell_presence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      L.length = (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some ∧
      (∀ h, h ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
            some (L.take h)) ∧
      (∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
        ReferenceLaterLiveNumericalReadout.laterLiveDomain 0
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h).get k) ∨
          ∃ d, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h).get k) = some d) := by
  have hcross :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).1 (by rw [hlaunch]; rfl)
  obtain ⟨hrecords, _hterminal, _hhistory⟩ :=
    ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
      rate z rewards C_star C_h active hlaunch hstart
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp [hrecords]
  · simp [hrecords]
  · intro h hh
    have hzero : h = 0 := by simp [hrecords] at hh; omega
    subst h
    have hlaunchBy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h (ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h) z := by
      refine ⟨?_, le_rfl⟩
      simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcross
    simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      hlaunchBy, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
      hrecords, List.take_nil]
  · intro k
    have hk := k.isLt
    simp [hrecords] at hk

/-- On every nonempty actual launch, the first physical suffix record is
already a live numerical cell from the genuine initialization seed. -/
theorem nonempty_launch_first_original_calendar_cell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hnonempty : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h ≠ []) :
    ∃ c, ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[0]'(by
            cases hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h with
            | nil => exact (hnonempty hR).elim
            | cons r rs => simp)) = some c ∧
      ReferenceLaterLiveNumericalReadout.laterLiveDomain 0
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[0]'(by
            cases hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h with
            | nil => exact (hnonempty hR).elim
            | cons r rs => simp)) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hcross :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).1 (by rw [hlaunch]; rfl)
  have hlenPos : 0 < R.length := by
    cases hR : R with
    | nil => exact (hnonempty (by simpa [R] using hR)).elim
    | cons r rs => simp
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let hspan := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let execution := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z rewards C_star C_h hcross count hspan
  have hrecords : R = execution.records := by
    simpa only [R, execution, count, hspan,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
      ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
        rate rewards C_star C_h z hcross
  have hrunNonempty : execution.records ≠ [] := by
    intro hnil
    apply hnonempty
    simpa [R] using hrecords.trans hnil
  cases hr : execution.records with
  | nil => exact (hrunNonempty hr).elim
  | cons first rest =>
      have hRcons : R = first :: rest := hrecords.trans hr
      have hseed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
        rate z rewards C_star C_h hcross
      dsimp only at hseed
      rcases hseed with ⟨_, _, _, hfirstCoordinator, _, _, _, _⟩
      have hconnected := execution.connected
      rw [hr] at hconnected
      change first.input.state =
        ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross ∧ _ at hconnected
      have hfirstState : first.input.state.coordinator = .first := by
        rw [hconnected.1]
        exact hfirstCoordinator
      have hprepared : (ReferenceActivePhysicalStep.prepare first.input).coordinator =
          .first (CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput first.input)) := by
        simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          CoordinatorRoundDispatch.dispatch, hfirstState]
        rfl
      have hnotCutoff : ReferenceCollectionPhaseHistory.cutoffChosen first.input = false := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprepared]
      let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hcross count hspan
      have hWrecords : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := by
        dsimp [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
        rw [← hrecords]
      have hWcons : W = first ::
          ReferenceFirstLiveConfirmationHistory.firstLiveWindow rest := by
        calc
          W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := hWrecords
          _ = ReferenceFirstLiveConfirmationHistory.firstLiveWindow (first :: rest) :=
            congrArg ReferenceFirstLiveConfirmationHistory.firstLiveWindow hRcons
          _ = first :: ReferenceFirstLiveConfirmationHistory.firstLiveWindow rest := by
            simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hnotCutoff]
      have hWpos : 0 < W.length := by rw [hWcons]; simp
      obtain ⟨_seed, _hstart, hcells⟩ :=
        ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
          rate rewards C_star C_h z hcross
      let k : Fin W.length := ⟨0, hWpos⟩
      let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hcross count hspan
      have hcellsLength := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
        rate z rewards C_star C_h hcross count hspan
      let c := cells[0]'(by rw [hcellsLength]; exact hWpos)
      have hcellFacts := hcells k
      rcases hcellFacts with ⟨_, _, _, _, _, _, hread, _, _, _, _, _, _, _, _, _⟩
      change ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
        (W[0]'hWpos) = some c at hread
      have hWfirst? : W[0]? = some first := by
        simp [hWcons]
      have hWfirst : W[0]'hWpos = first := by
        apply Option.some.inj
        calc
          some (W[0]'hWpos) = W[0]? := (List.getElem?_eq_getElem hWpos).symm
          _ = some first := hWfirst?
      have hreadFirst : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 first = some c := by
        rw [← hWfirst]
        exact hread
      have hRpos : 0 < R.length := hlenPos
      have hRfirst : R[0]'(by omega) = first := by
        simp [hRcons]
      have hOriginalFirst :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[0]'(by
            cases hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h with
            | nil => exact (hnonempty hR).elim
            | cons r rs => simp) = first := by
        simpa [R] using hRfirst
      refine ⟨c, ?_, ?_⟩
      · simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hOriginalFirst, hreadFirst]
      · apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
          0 (R[0]'hRpos)).mp
        rw [hRfirst, hreadFirst]
        rfl

private theorem prepared_unoccupied_of_actual_cutoff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselection : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some selected)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : selected.view.payload = payload)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  obtain ⟨states, memories, hstates, hdown, _hinputFields, _houtputFields⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h source k selected hselection
  intro i
  change match (ReferenceFollowerFixedReply.actualChoice record i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False
  rw [hstates i]
  by_contra hbusy
  have hcurrent := hdown i hbusy
  rw [hpayload] at hcurrent
  obtain ⟨before, memory, choice, hbefore, _hdomain, hstart, hchoice,
      _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source k i
  have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hstates i))
  have hchoiceDown : choice.lastDown = some (payload.downRecord i) := by
    rw [hchoiceEq.1]
    exact hcurrent
  have hbeforeDown : before.lastDown = some (payload.downRecord i) :=
    (ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time before
      choice memory memory hstart).1.symm.trans hchoiceDown
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h source k i before memory hbefore
      (payload.downRecord i) hbeforeDown
  have htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = record.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ := by
    intro hoccupied
    exact ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h source k i before memory hbefore hoccupied
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    (rate := rate) record.input.time record.input.row before choice memory memory
      (payload.downRecord i) hbeforeDown hphase htoken hstart
  have hstartPayload : ActiveFollowerDownAcceptance.downStart p rate
      (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
      (payload.downRecord i)
    rw [payload.downRecord_fields i] at hval
    exact Nat.add_right_cancel hval
  have hchoiceUnoccupied : choice.status = .unoccupied :=
    hstatus.mpr (by rw [hstartPayload]; exact hcut)
  exact hbusy (hchoiceEq.1 ▸ hchoiceUnoccupied)

private theorem collection_choice_selection {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ctx : ReferenceCollectionSegmentExtraction.Choice rate) (hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some ctx) :
    ∃ v : Selection r.input,
      r.output.preparation.coordinator.selection = some v ∧ v.view.payload = ctx.payload := by
  classical
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  next => contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice hn
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | dagger => simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
      all_goals try contradiction
      next core snapshot hboundary hchecked =>
        rw [← Option.some.inj hchoice]
        exact ⟨_, rfl, rfl⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        simp only [DispatchCut.selection, selectionAt, dite_true]
        exact ⟨_, rfl, rfl⟩

section ActualSuffix

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h

private theorem actual_prepared_ordinary (k : Fin (R).length) :
    preparedOrdinary R[k.val] := by
  intro i
  obtain ⟨before, memory, choice, _, _, _, hchoice, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z k i
  change (ordinaryData (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration).isSome = true
  rw [hchoice]
  rfl

private theorem actual_record_time (k : Fin (R).length) :
    R[k.val].input.time.val = s + k.val :=
  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k.val R[k.val] (List.getElem?_eq_getElem k.isLt)

private theorem actual_record_row (k : Fin (R).length) :
    R[k.val].input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
  obtain ⟨hc, span, hr⟩ := source_record_prefix rate rewards C_star C_h z k
  change R[k.val] = _ at hr
  rw [hr]
  rfl

private theorem actual_start_positive (k : Fin (R).length) : 0 < s := by
  obtain ⟨hc, _, _⟩ := source_record_prefix rate rewards C_star C_h z k
  obtain ⟨_, hs, _⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hc
  exact hs

private theorem actual_birth_positive (k : Fin (R).length) (payload : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[k.val] payload) :
    0 < payload.sigma.val := by
  have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[k.val] payload hbirth
  rw [ht, actual_record_time rate rewards C_star C_h z k]
  exact Nat.lt_of_lt_of_le (actual_start_positive rate rewards C_star C_h z k)
    (Nat.le_add_right _ _)

private theorem actual_live_positive (k : Fin (R).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hstate : R[k.val].input.state.coordinator = .live r q base) :
    0 < r.payload.sigma.val := by
  have h := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z k
  dsimp only at h
  rw [hstate] at h
  obtain ⟨⟨b, _, hb, _⟩, _⟩ := h
  exact actual_birth_positive rate rewards C_star C_h z b r.payload hb

private theorem actual_live_tail (k : Fin (R).length)
    (v : Selection R[k.val].input)
    (hv : R[k.val].output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      R[k.val].input.time) :
    R[k.val].output.coordinator.failure = none ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
        R[k.val].output.next.coordinator = .live r q base := by
  obtain ⟨a, q, base, started, _, valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      (rate := rate) rewards C_star C_h z k v hv hlive
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpost, hout, hnext, _⟩
  constructor
  · rw [hout]
  · rw [hnext, hpost]
    exact ⟨_, _, base, rfl⟩

private theorem choice_cutoff_bound
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some call) :
    call.preLedger.cutoff ≤ record.input.time.val + 1 := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next =>
    cases hc : (prepare record.input).coordinator with
    | first outcome => cases outcome <;>
        simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | invalidCollectionCutoff =>
        simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | dagger => simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals try contradiction
        next core snapshot boundary checked =>
          cases Option.some.inj hchoice
          have hv := core.ledger_valid
          have hcursor := core.ledger_cursor_eq
          simp only [CoordinatorCollectionLedger.validLedger,
            CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true,
            decide_eq_true_eq] at hv
          change ledger.cursor = record.input.time.val + 1 at hcursor
          have hle : ledger.cutoff ≤ ledger.cursor := by tauto
          exact hle.trans hcursor.le
    | live registers owned base outcome =>
        cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals try contradiction
        next dispatched hs ledger hi he hd hclock hp hn selected =>
          cases Option.some.inj hchoice
          rw [(sharedLedger_fields ledger).2.2.1, he]
          exact (CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
            (liveRegistersAt registers record.input.time)
            (liveOwnedAt registers owned record.input.time) base record.input.time).2.2.1.le

private theorem actual_collection_choice_present (k : Fin (R).length)
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice R[k.val].input = some call) :
    ∃ d, laterCollectionReadout 0 R[k.val] = some d := by
  obtain ⟨b, _, hbirth, _, _, hcutoff, _⟩ :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h z k call hchoice
  have hpos := actual_birth_positive rate rewards C_star C_h z b call.payload hbirth
  have hbound := choice_cutoff_bound rate R[k.val] call hchoice
  have hcut : FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[k.val].input.row) ≤
      R[k.val].input.time.val + 1 := by
    rw [actual_record_row rate rewards C_star C_h z k, ← hcutoff]
    exact hbound
  obtain ⟨selected, hselection, hpayload⟩ := collection_choice_selection R[k.val] call hchoice
  have ho := prepared_unoccupied_of_actual_cutoff rate rewards C_star C_h z k
    selected hselection call.payload hpayload hcut
  apply Option.isSome_iff_exists.mp
  apply (laterCollectionReadout_domain 0 R[k.val]).mpr
  refine ⟨ho, ?_⟩
  have hprep : (prepare R[k.val].input).coordinator = R[k.val].output.preparation.coordinator := by
    rw [R[k.val].output_eq]; rfl
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next =>
    rw [hprep] at hchoice
    cases hc : R[k.val].output.preparation.coordinator with
    | first outcome => cases outcome <;>
        simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | invalidCollectionCutoff =>
        simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | dagger => simp [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals first | contradiction | trivial
    | live registers owned base outcome =>
        cases outcome <;> simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals try contradiction
        have heq := congrArg ReferenceCollectionSegmentExtraction.Choice.payload (Option.some.inj hchoice)
        change registers.payload = call.payload at heq
        simpa only [← heq] using hpos

private theorem actual_live_record (k : Fin (R).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : R[k.val].input.state.coordinator = .live registers owned base) :
    (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d) ∧
      R[k.val].output.coordinator.failure = none ∧
      R[k.val].output.next.coordinator ≠ .first ∧
      R[k.val].output.next.coordinator ≠ .dagger := by
  have hpos := actual_live_positive rate rewards C_star C_h z k registers owned base hstate
  obtain ⟨hprep, hbranch⟩ :=
    ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
      rate rewards C_star C_h z k registers owned base hstate
  have hactual : R[k.val].output.preparation = prepare R[k.val].input := by
    rw [R[k.val].output_eq]; rfl
  cases hd : CoordinatorRoundDispatch.dispatchLive
      (liveInput R[k.val].input registers owned base) with
  | continuingChosen dispatched hstart continuation selection =>
      rw [hd] at hbranch hprep
      obtain ⟨_, hu, _, _, _, v, hv, hp, _, hcut, _⟩ := hbranch
      have hvout : R[k.val].output.preparation.coordinator.selection = some v := by
        rw [hactual]; exact hv
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive
          v.view.payload v.view.cutoff R[k.val].input.time := by
        refine ⟨(selection_choiceValid v).time.assignment_started, ?_⟩
        rw [hcut, hu]
        change R[k.val].input.time.val + 1 < p.T + 1
        omega
      have hdomain : laterLiveDomain 0 R[k.val] :=
        ⟨v, hvout, by simpa only [hp] using hpos, hlive,
          actual_prepared_ordinary rate rewards C_star C_h z k⟩
      obtain ⟨hfail, r, q, beta, hnext⟩ :=
        actual_live_tail rate rewards C_star C_h z k v hvout hlive
      refine ⟨Or.inl hdomain, hfail, ?_, ?_⟩ <;> simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
  | cutoffChosen dispatched hstart ledger hinit hcandidate hvalid hclock hpending hno selected =>
      rw [hd] at hprep
      have hchoice : ∃ call, ReferenceCollectionSegmentExtraction.choice R[k.val].input = some call := by
        simp only [ReferenceCollectionSegmentExtraction.choice, hprep,
          DispatchCut.selection, selectionAt, dite_true, reduceCtorEq, ite_false,
          ReferenceCollectionSegmentExtraction.choiceOfCut]
        exact ⟨_, rfl⟩
      obtain ⟨call, hcall⟩ := hchoice
      have hcell := actual_collection_choice_present rate rewards C_star C_h z k call hcall
      obtain ⟨_, hpost⟩ :=
        Bandits.Support.complete_live_cutoff_post_choice
          rate rewards C_star C_h z k registers owned base hstate
      rw [hd] at hpost
      dsimp only at hpost
      rcases hpost with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, physical,
          _, _, _, _, _, _, _, _, _, recording, _, startedLedger,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, decoded, bank, _, _, _,
          finishedLedger, finished, diagnostic,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, hnext, _⟩
      refine ⟨Or.inr hcell, ?_, ?_, ?_⟩
      · rw [hout]
      · simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
  | clockFailure => rw [hd] at hbranch; exact False.elim hbranch
  | initializerFailure => rw [hd] at hbranch; exact False.elim hbranch
  | localFailure => rw [hd] at hbranch; exact False.elim hbranch

private theorem prepare_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (u : Fin p.T) (hu : u.val + 1 = ledger.cutoff) :
    (prepare x).coordinator = .collection payload ledger
      (collectionClock payload ledger saved u) u
      (CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x payload ledger (collectionClock payload ledger saved u) u)) := by
  have hcutoffRange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    constructor <;> have := u.isLt <;> omega
  have hcutoffVal : ledger.cutoff - 1 = u.val := by omega
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hcutoff : cutoff = u := Fin.ext hcutoffVal
  simp only [prepare, dispatch, hstate, dite_eq_left hcutoffRange,
    CoordinatorRoundDispatch.dispatch]
  change DispatchCut.collection payload ledger (collectionClock payload ledger saved cutoff) cutoff
    (CoordinatorRoundDispatch.dispatchCollection
      (collectionInput x payload ledger (collectionClock payload ledger saved cutoff) cutoff)) = _
  rw [hcutoff]

private theorem actual_pending_collection_record (k : Fin (R).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : R[k.val].input.state.coordinator = .collection payload ledger saved)
    (hpending : ledger.pending.Nonempty) :
    (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d) ∧
      R[k.val].output.coordinator.failure = none ∧
      R[k.val].output.next.coordinator ≠ .first ∧
      R[k.val].output.next.coordinator ≠ .dagger := by
  obtain ⟨_u, _, _core, _scores, _started, _, _, _valid, _snapshot, _boundary,
    _, _, _, _, call, hcall, _, _, _, _o, _startedLedger, finished, _bank, clockFinished,
    _, hfail, hconfig, _⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h z k payload ledger saved hstate hpending
  have hcell := actual_collection_choice_present rate rewards C_star C_h z k call hcall
  have hnext : R[k.val].output.next.coordinator =
      .collection payload finished clockFinished.clock.lastProposal := by
    rw [R[k.val].output_eq]
    exact hconfig
  refine ⟨Or.inr hcell, ?_, ?_, ?_⟩
  · rw [R[k.val].output_eq]
    exact hfail
  · simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem actual_empty_collection_later_chosen (k : Fin (R).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : R[k.val].input.state.coordinator = .collection payload ledger saved)
    (hpending : ledger.pending = ∅) :
    ReferenceCollectionPhaseHistory.laterChosen R[k.val].input = true := by
  by_cases hf : R[k.val].input.time.val + 1 < ledger.freezeAt
  · obtain ⟨u, hu, _core, _started, _hstart, _instruction, _hassignment,
      _, _, _, _, _consistent, _output, _hlocal, _, _clockData, _installation, _selected,
      _, _, _, _, hdispatch, _⟩ :=
      ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
        rate rewards C_star C_h z k payload ledger saved hstate hpending hf
    simp only [ReferenceCollectionPhaseHistory.laterChosen,
      prepare_collection rate R[k.val].input payload ledger saved hstate u hu, hdispatch]
  · obtain ⟨u, hu, _core, _, _started, _hstart, _instruction, _hassignment,
      _htime, _hrenewal, _output, _hlocal, _, _, _, _, _, _, _, _, _, _mass,
      _sampled, _, _, _, _selection, hdispatch, _⟩ :=
      ReferenceCompleteEmptyCollectionRenewalChoiceDomains.complete_empty_collection_renewal_choice_domains
        rate rewards C_star C_h z k payload ledger saved hstate hpending (by omega)
    simp only [ReferenceCollectionPhaseHistory.laterChosen,
      prepare_collection rate R[k.val].input payload ledger saved hstate u hu, hdispatch]

private theorem actual_collection_record (k : Fin (R).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : R[k.val].input.state.coordinator = .collection payload ledger saved) :
    (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d) ∧
      R[k.val].output.coordinator.failure = none ∧
      R[k.val].output.next.coordinator ≠ .first ∧
      R[k.val].output.next.coordinator ≠ .dagger := by
  by_cases hpending : ledger.pending = ∅
  · have hb := actual_empty_collection_later_chosen
      rate rewards C_star C_h z k payload ledger saved hstate hpending
    obtain ⟨_P0, rb, _qb, _beta, _cell, native, _, _, _, _, _, _, hpos, _, _, _, hp, _⟩ :=
      ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
        rate rewards C_star C_h z k hb
    have hdomain : laterLiveDomain 0 R[k.val] :=
      ⟨native.selected, native.selection_actual, by rw [hp]; omega,
        native.assignment_live, actual_prepared_ordinary rate rewards C_star C_h z k⟩
    obtain ⟨hfail, r, q, beta, hnext⟩ :=
      actual_live_tail rate rewards C_star C_h z k native.selected
        native.selection_actual native.assignment_live
    refine ⟨Or.inl hdomain, hfail, ?_, ?_⟩ <;>
      simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
  · exact actual_pending_collection_record rate rewards C_star C_h z k payload ledger saved
      hstate (Finset.nonempty_iff_ne_empty.mpr hpending)

private theorem actual_records_phase_and_successor :
    ∀ k : Fin (R).length,
      (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d) ∧
        R[k.val].output.coordinator.failure = none ∧
        R[k.val].output.next.coordinator ≠ .first ∧
        R[k.val].output.next.coordinator ≠ .dagger := by
  have hall : ∀ n (hn : n < (R).length),
      (laterLiveDomain 0 (R[n]'hn) ∨ ∃ d, laterCollectionReadout 0 (R[n]'hn) = some d) ∧
        (R[n]'hn).output.coordinator.failure = none ∧
        (R[n]'hn).output.next.coordinator ≠ .first ∧
        (R[n]'hn).output.next.coordinator ≠ .dagger := by
    intro n
    induction n with
    | zero =>
        intro hn
        let k : Fin (R).length := ⟨0, hn⟩
        obtain ⟨hc, _, _⟩ := source_record_prefix rate rewards C_star C_h z k
        have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate z rewards C_star C_h hc
        have hne : R ≠ [] := by intro hnil; simp only [hnil, List.length_nil] at hn; omega
        obtain ⟨_c, _, hdomain⟩ := nonempty_launch_first_original_calendar_cell
          rate rewards C_star C_h z _ hlaunch hne
        obtain ⟨v, hv, _hpos, hlive, _ho⟩ := hdomain
        obtain ⟨hfail, r, q, beta, hnext⟩ :=
          actual_live_tail rate rewards C_star C_h z k v hv hlive
        dsimp only [k] at hnext
        refine ⟨Or.inl ⟨v, hv, _hpos, hlive, _ho⟩, hfail, ?_, ?_⟩ <;>
          simp only [hnext, ne_eq, reduceCtorEq, not_false_eq_true]
    | succ n ih =>
        intro hn
        have hn' : n < (R).length := by omega
        obtain ⟨_, _, hfirst, hdagger⟩ := ih hn'
        have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z n hn
        have hcoord := congrArg ReferenceActivePhysicalStep.State.coordinator hadj
        let k : Fin (R).length := ⟨n + 1, hn⟩
        cases hstate : (R[n + 1]'hn).input.state.coordinator with
        | first => exact False.elim (hfirst (hcoord.symm.trans hstate))
        | dagger => exact False.elim (hdagger (hcoord.symm.trans hstate))
        | live r q base =>
            exact actual_live_record rate rewards C_star C_h z k r q base hstate
        | collection payload ledger saved =>
            exact actual_collection_record rate rewards C_star C_h z k payload ledger saved hstate
  intro k
  exact hall k.val k.isLt

/-- Every actual physical suffix record has a literal live or collection
numerical phase, and its coordinator operation completes without failure.
All PREPARE and successor invariants are derived from the actual run. -/
theorem complete_original_calendar_phase_exhaustion (k : Fin (R).length) :
    R[k.val].output.coordinator.failure = none ∧
      (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d) := by
  obtain ⟨hphase, hfail, _, _⟩ := actual_records_phase_and_successor
    rate rewards C_star C_h z k
  exact ⟨hfail, hphase⟩

private theorem total_option_word {α β : Type*} (records : List α) (f : α → Option β)
    (htotal : ∀ r ∈ records, (f r).isSome = true) :
    ∃ L : List β, L.length = records.length ∧ records.map f = L.map some := by
  induction records with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons r rest ih =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (htotal r (List.mem_cons_self ..))
      obtain ⟨L, hlen, hmap⟩ := ih (fun a ha => htotal a (List.mem_cons_of_mem r ha))
      refine ⟨c :: L, by simp only [List.length_cons, hlen], ?_⟩
      simp only [List.map_cons, hc, hmap]

private theorem mapM_map_some {α : Type*} (L : List α) :
    (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.map_cons, List.mapM_cons, ih, id_eq]
      rfl

private theorem actual_cell_word :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      L.length = (R).length ∧ (R).map (cell0 rate) = L.map some := by
  apply total_option_word (R) (cell0 rate)
  intro r hr
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
  subst r
  obtain ⟨_, hphase⟩ := complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z k
  rcases hphase with hlive | ⟨d, hd⟩
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((laterLiveReadout_domain 0 R[k.val]).mpr hlive)
    simp only [List.get_eq_getElem, cell0, hc, Option.some_or, Option.isSome_some]
  · cases hl : laterLiveReadout 0 R[k.val] with
    | none => simp only [List.get_eq_getElem, cell0, hl, Option.none_or, hd, Option.isSome_some]
    | some c => simp only [List.get_eq_getElem, cell0, hl, Option.some_or, Option.isSome_some]

/-- Total original-date numerical presence on the same complete physical
suffix. No-launch retains literal absence. A launch supplies one word whose
every prefix is the existing optional prefix at the original calendar date,
with the actual live/collection phase and absence of coordinator failure. -/
theorem complete_original_calendar_cells :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none => R = [] ∧ s = p.T ∧
        (∀ n, prefixInputs rate rewards C_star C_h n z = none)
    | some _ => ∃ L : List (RecordedQueueRun.RoundInput p.K),
        L.length = (R).length ∧ (R).map (cell0 rate) = L.map some ∧
        (∀ h, h ≤ (R).length →
          prefixInputs rate rewards C_star C_h (s + h) z = some (L.take h)) ∧
        (∀ k : Fin (R).length,
          R[k.val].output.coordinator.failure = none ∧
            (laterLiveDomain 0 R[k.val] ∨ ∃ d, laterCollectionReadout 0 R[k.val] = some d)) := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      exact no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
  | some active =>
      obtain ⟨L, hlen, hmap⟩ := actual_cell_word rate rewards C_star C_h z
      refine ⟨L, hlen, hmap, ?_, complete_original_calendar_phase_exhaustion
        rate rewards C_star C_h z⟩
      intro h _hh
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).1 (by rw [hlaunch]; rfl)
      have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h (s + h) z := by
        refine ⟨?_, Nat.le_add_right _ _⟩
        simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hcross
      unfold prefixInputs
      rw [ite_eq_left hby]
      change (((R).take (s + h - s)).map (cell0 rate)).mapM id = _
      rw [Nat.add_sub_cancel_left, List.map_take, hmap, ← List.map_take]
      exact mapM_map_some (L.take h)

end ActualSuffix

end Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence

end
