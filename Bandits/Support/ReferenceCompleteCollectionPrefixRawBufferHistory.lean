/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory

import Bandits.Support.ReferenceCollectionRawBufferHistory
import Bandits.Support.ReferenceCollectionPrefixLedgerHistory
import Lean.Elab.Tactic.Omega

/-!
# Actual clipped collection-prefix registers and raw-buffer history

For every clipped prefix of an actual, nonempty, cutoff-chosen collection
segment, the physical recorder history agrees with the checked ledger prefix.
The recorder outputs and their guards are recovered from the original physical
records. This is an internal execution result, not a global queue or regret
claim.

Mathematical evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-188`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCollectionPrefixRawBufferHistory

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open CoordinatorCollectionLedger
open CollectionCheckedExecution

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem allFin_eq_true_iff_local {length : ℕ}
    (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    exact h i

private theorem armPendingCheck_eq_true_iff_local
    (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem armPendingCheck_eq_false_of_not
    (l : Ledger rate) (a : Fin p.K)
    (h : ¬ CoordinatorCollectionLedger.armPending l a) :
    CoordinatorCollectionLedger.armPendingCheck l a = false := by
  cases hp : CoordinatorCollectionLedger.armPendingCheck l a with
  | false => rfl
  | true =>
      have hpending := (armPendingCheck_eq_true_iff_local l a).mp hp
      exact False.elim (h hpending)

private theorem startCollectionChecked_success_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger rate)
    (h : startCollectionChecked p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      assignment sigma cutoff freezeAt baseScore outside = .success initial) :
    validLedgerCheck initial = true := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem finishRound_success_valid
    (l result : Ledger rate)
    (h : finishRound l = .success result) : validLedgerCheck result = true := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem checkedRounds_success_valid
    (l final : Ledger rate)
    (inputs : List (RoundInput (p := p) (eta := rate.eta.val)))
    (accepted : List Bool)
    (hvalid : validLedgerCheck l = true)
    (hfold : checkedRounds l inputs = some (accepted, final)) :
    validLedgerCheck final = true := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp only [checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      exact hvalid
  | cons input rest ih =>
      cases hstart : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hstart] at hfold
      | rejected bad => simp [checkedRounds, hstart] at hfold
      | success started =>
          cases hdecode : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hstart, hdecode] at hfold
          | rejected decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : false :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail
          | success decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : true :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail

private theorem validLedgerCheck_arm_fields
    (l : Ledger rate) (hvalid : validLedgerCheck l = true) :
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.currentRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.cutoffRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck l a) || decide (l.gammaLoc a = 0)) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck l a) || decide (l.increment a = 0)) = true ∧
    CoordinatorCollectionLedger.rawEntryDomainsCheck l = true := by
  have h := hvalid
  unfold validLedgerCheck at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  have hcurrent := h.1.1.1.1.1.2
  have hcutoff := h.1.1.1.1.2
  have hgamma := h.1.1.1.2
  have hincrement := h.1.1.2
  have hraw := h.2
  exact ⟨hcurrent, hcutoff, hgamma, hincrement, hraw⟩

private theorem rawBuffer_none_of_not_armPending
    (l : Ledger rate) (hvalid : validLedgerCheck l = true)
    (a : Fin p.K) (hnot : ¬ CoordinatorCollectionLedger.armPending l a)
    (r : Fin p.T) : l.rawBuffer a r = none := by
  have hfields := validLedgerCheck_arm_fields l hvalid
  have harm : CoordinatorCollectionLedger.armPendingCheck l a = false :=
    armPendingCheck_eq_false_of_not l a hnot
  have hcolumn := (allFin_eq_true_iff_local _).mp hfields.2.2.2.2 a
  have hcell := (allFin_eq_true_iff_local _).mp hcolumn r
  cases hraw : l.rawBuffer a r with
  | none => rfl
  | some amount =>
      have hfalse : False := by
        have hcell' := hcell
        simp [hraw, harm] at hcell'
      exact hfalse.elim

private theorem retained_completed_input_of_records
    (records : List (RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ record ∈ records, (extractRound record).isSome = true)
    (record : RoundRecord (p := p) (rate := rate)) (hrecord : record ∈ records) :
    ∃ done, extractRound record = some done ∧
      done.input ∈ inputs records ∧
      done.input.round = record.input.time ∧
      done.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
      done.input.enabled = ReferenceActivePhysicalStep.collectionEnabled
        done.context.preLedger record.input.time := by
  cases hextract : extractRound record with
  | none =>
      have hfalse := hgood record hrecord
      simp [hextract] at hfalse
  | some done =>
      have hround := (actual_collection_round_checked record done hextract).2.1
      have hrawEnabled :=
        ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
          record done hextract
      have hmemCompleted : done ∈ completed records :=
        List.mem_filterMap.mpr ⟨record, hrecord, hextract⟩
      have hmemInput : done.input ∈ inputs records := by
        change done.input ∈ (completed records).map CompletedRound.input
        exact List.mem_map.mpr ⟨done, hmemCompleted, rfl⟩
      exact ⟨done, rfl, hmemInput, hround, hrawEnabled.1, hrawEnabled.2⟩

private theorem retained_record_of_prefix_input
    (records : List (RoundRecord (p := p) (rate := rate)))
    (input : RoundInput (p := p) (eta := rate.eta.val))
    (hinput : input ∈ inputs records) :
    ∃ record ∈ records, ∃ done,
      extractRound record = some done ∧ done.input = input := by
  change input ∈ (completed records).map CompletedRound.input at hinput
  obtain ⟨done, hdone, hinputEq⟩ := List.mem_map.mp hinput
  obtain ⟨record, hrecord, hextract⟩ := List.mem_filterMap.mp hdone
  refine ⟨record, hrecord, done, hextract, ?_⟩
  exact hinputEq

private theorem run_segment_record_time_injective
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (offset : ℕ) (segment : Segment rate)
    (hsegment : segmentAt
      (run initial rows selected rewards start count span active).records offset = some segment)
    (left right : RoundRecord (p := p) (rate := rate))
    (hleft : left ∈ segment.records) (hright : right ∈ segment.records)
    (htime : left.input.time = right.input.time) : left = right := by
  let actualRun := run initial rows selected rewards start count span active
  have hbranch := (segmentAt_branch actualRun.records offset segment hsegment).1
  have hpartition := segment_partition (actualRun.records.drop offset) segment hbranch
  have hleftDrop : left ∈ actualRun.records.drop offset := by
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hleft)
  have hrightDrop : right ∈ actualRun.records.drop offset := by
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hright)
  have hleftRun : left ∈ actualRun.records := List.mem_of_mem_drop hleftDrop
  have hrightRun : right ∈ actualRun.records := List.mem_of_mem_drop hrightDrop
  have hrunTimes := ReferenceActivePhysicalHorizon.run_time_values
    initial rows selected rewards start count span active
  have htimesNodup :
      (actualRun.records.map fun record => record.input.time.val).Nodup := by
    rw [hrunTimes]
    simp [ReferenceActivePhysicalHorizon.calendar, List.nodup_range']
  apply List.inj_on_of_nodup_map htimesNodup hleftRun hrightRun
  exact congrArg Fin.val htime

/-! The caller supplies only the actual source run and its branch selectors.
The checked prefix, initializer, recorder outputs, and register facts are
derived below from those physical data. -/

/-- Every clipped prefix of an actual nonempty cutoff-chosen collection
segment has the checked ledger endpoint, exact pending-arm registers, and the
raw-buffer history of its actual physical recorder outputs. `count = 0` and
`count = segment.records.length` are included; the latter returns the literal
original `segment.final`. -/
theorem run_segment_prefix_raw_buffer_history
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (segment : Segment rate)
    (hsegment : segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e = some segment)
    (hnonempty : segment.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen segment.entry.input = true)
    (count : ℕ) (hcount : count ≤ segment.records.length) :
    let Q := segment.records.take count
    let ln := endpointLedger segment.context.preLedger Q
    ∃ initializer : Initializer p,
      segment.context.initializer = some initializer ∧
      initializer.checkedStart rate = .success segment.context.preLedger ∧
      ∃ accepted,
        checkedRounds segment.context.preLedger (segment.inputs.take count) =
          some (accepted, ln) ∧
        ln.phase = .ready ∧
        ln.cursor = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          e + count + 1 ∧
        ln.assignment = initializer.assignment ∧
        ln.sigma = initializer.sigma ∧
        ln.cutoff = initializer.cutoff ∧
        ln.freezeAt = initializer.freezeAt ∧
        ln.baseScore = initializer.base ∧
        validLedgerCheck ln = true ∧
        (∀ i, i ∈ ln.pending →
          let a := ln.assignment.arm i
          ln.cutoffRegisters a = none ∧
          ln.currentRegisters a = none ∧
          ln.increment a = 0 ∧
          ln.gammaLoc a = 0 ∧
          ln.baseScore i = initializer.base i ∧
          (∀ r amount,
            ln.rawBuffer a r = some amount ↔
              ∃ record ∈ Q, record.input.time = r ∧
                ∃ output,
                  record.output.coordinator.recording = some output ∧
                  output.gateArm = some a ∧
                  output.rawArrival = amount ∧
                  0 < amount ∧
                  r.val + 1 < segment.context.preLedger.freezeAt) ∧
          (∀ r, sourceRound r < segment.context.preLedger.cursor →
            ln.rawBuffer a r = none) ∧
          (∀ r, segment.context.preLedger.freezeAt ≤ sourceRound r →
            ln.rawBuffer a r = none) ∧
          (∀ r, ln.cursor ≤ sourceRound r → ln.rawBuffer a r = none)) ∧
        (∀ a, ¬ armPending ln a → ∀ r, ln.rawBuffer a r = none) ∧
        (count = 0 → ∀ a r, ln.rawBuffer a r = none) ∧
        (count = segment.records.length → ln = segment.final) ∧
        (∀ record ∈ Q, ∃ done,
          extractRound record = some done ∧
          ln.enabledHistory done.input.round = some done.input.enabled) ∧
        (∀ left right, left ∈ Q → right ∈ Q →
          left.input.time = right.input.time → left = right) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hRne : R ≠ [] := by
    intro hnil
    have hp := segmentAt_partition R e segment hsegment
    rw [hnil] at hp
    simp only [List.drop_nil] at hp
    cases hrecords : segment.records with
    | nil => exact hnonempty hrecords
    | cons record rest =>
        have hnil' : (record :: rest) ++ segment.remaining = [] := by
          simpa only [hrecords] using hp
        cases hnil'
  have hlaunchNe :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hnil : R = [] := by
      simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
    exact hRne hnil
  have hlaunchSome :
      (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hlaunchNe hl)
    | some initial => rfl
  have hcrossing :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp hlaunchSome
  obtain ⟨initial, hlaunch, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hcrossing
  have hspan : s + (p.T - s) ≤ p.T := by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  have hactive := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate z rewards C_star C_h initial hlaunch
  have hrun : R = (run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
      hspan hactive).records :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch
  have hsegmentRun : segmentAt (run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
      hspan hactive).records e = some segment := by
    rw [← hrun]
    exact hsegment
  obtain ⟨initializer, hinitializer, hcheckedStart, hwholeRun⟩ :=
    ReferenceCollectionRawBufferHistory.run_collection_raw_buffer_execution
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      s (p.T - s) hspan hactive hfirst e segment hsegmentRun
  have hwholeChron := CollectionCheckedExecution.startAndRunChecked_success_chronology
    p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
    rate.n rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
    initializer.freezeAt initializer.base initializer.outside segment.inputs
    ⟨segment.context.preLedger, segment.accepted, segment.final⟩ hwholeRun
  have hbranch := (segmentAt_branch R e segment hsegment).1
  have hsegmentInputCount := segment_input_count (R.drop e) segment hbranch
  have hstartRaw : startCollectionChecked p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside = .success segment.context.preLedger := by
    simpa only [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hcheckedStart
  have hboundary :=
    ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
      rate rewards C_star C_h z e segment hsegment hnonempty hcut
  dsimp only at hboundary
  rcases hboundary with ⟨_, _, _, saved, _, hboundaryCursor, _⟩
  have hpreCursor : segment.context.preLedger.cursor = s + e + 1 := by
    have hfullCursor : segment.final.cursor =
        segment.context.preLedger.cursor + segment.inputs.length := hwholeChron.1
    rw [hsegmentInputCount] at hfullCursor
    have hboundaryCursor' : segment.final.cursor = s + (e + segment.records.length) + 1 := by
      simpa [s] using hboundaryCursor
    omega
  have hgood : ∀ record ∈ segment.records, (extractRound record).isSome = true :=
    segment_all_completed (R.drop e) segment hbranch
  have hinputsTake :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_inputs_take
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      s (p.T - s) hspan hactive e segment hsegmentRun count
  obtain ⟨accepted, hfold⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      s (p.T - s) hspan hactive e segment hsegmentRun count hcount
  let Q := segment.records.take count
  let ln := endpointLedger segment.context.preLedger Q
  have hfold' : checkedRounds segment.context.preLedger (segment.inputs.take count) =
      some (accepted, ln) := by
    simpa only [Q, ln] using hfold
  have hQlength : Q.length = count := by
    dsimp only [Q]
    simp only [List.length_take, Nat.min_eq_left hcount]
  have hinputLength : (segment.inputs.take count).length = count := by
    calc
      (segment.inputs.take count).length = min count segment.inputs.length :=
        List.length_take
      _ = count := Nat.min_eq_left (by
        rw [segment_input_count (R.drop e) segment hbranch]
        exact hcount)
  have hprefixRun :
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside (segment.inputs.take count) =
          .success ⟨segment.context.preLedger, accepted, ln⟩ := by
    simp only [CollectionCheckedExecution.startAndRunChecked, hstartRaw, hfold']
  have hvalidStart : validLedgerCheck segment.context.preLedger = true := by
    apply startCollectionChecked_success_valid initializer.assignment initializer.sigma
      initializer.cutoff initializer.freezeAt initializer.base initializer.outside
      segment.context.preLedger
    exact hstartRaw
  have hvalid : validLedgerCheck ln = true :=
    checkedRounds_success_valid segment.context.preLedger ln (segment.inputs.take count)
      accepted hvalidStart hfold'
  have hreadyStart : segment.context.preLedger.phase = .ready := by
    apply CollectionCheckedExecution.startCollectionChecked_success_ready
      p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
      initializer.freezeAt initializer.base initializer.outside segment.context.preLedger
    exact hstartRaw
  have hprefixChron := CollectionCheckedExecution.checkedRounds_success_chronology
    segment.context.preLedger ln hreadyStart (segment.inputs.take count) accepted hfold'
  have hcursor : ln.cursor = s + e + count + 1 := by
    rw [hprefixChron.1, hinputLength, hpreCursor]
    omega
  have hpreserved :=
    CollectionBufferProvenance.checkedRounds_success_preserves_context
      segment.context.preLedger ln (segment.inputs.take count) accepted hfold'
  change CollectionBufferProvenance.collectionContext ln =
    CollectionBufferProvenance.collectionContext segment.context.preLedger at hpreserved
  have hstartContext :=
    CollectionBufferProvenance.startCollectionChecked_success_context
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside segment.context.preLedger (by
        exact hstartRaw)
  have hassignment : ln.assignment = initializer.assignment := by
    have hp := congrArg (fun c : (Assignment p × ℕ × ℕ × ℕ ×
        (Fin (p.m - 1) → ℕ)) => c.1) hpreserved
    exact hp.trans hstartContext.1
  have hsigma : ln.sigma = initializer.sigma := by
    have hp := congrArg (fun c : (Assignment p × ℕ × ℕ × ℕ ×
        (Fin (p.m - 1) → ℕ)) => c.2.1) hpreserved
    exact hp.trans hstartContext.2.1
  have hcutoff : ln.cutoff = initializer.cutoff := by
    have hp := congrArg (fun c : (Assignment p × ℕ × ℕ × ℕ ×
        (Fin (p.m - 1) → ℕ)) => c.2.2.1) hpreserved
    exact hp.trans hstartContext.2.2.2.1
  have hfreeze : ln.freezeAt = initializer.freezeAt := by
    have hp := congrArg (fun c : (Assignment p × ℕ × ℕ × ℕ ×
        (Fin (p.m - 1) → ℕ)) => c.2.2.2.1) hpreserved
    exact hp.trans hstartContext.2.2.2.2.1
  have hbase : ln.baseScore = initializer.base := by
    have hp := congrArg (fun c : (Assignment p × ℕ × ℕ × ℕ ×
        (Fin (p.m - 1) → ℕ)) => c.2.2.2.2) hpreserved
    exact hp.trans hstartContext.2.2.2.2.2
  have hprefixGood : ∀ record ∈ Q, (extractRound record).isSome = true := by
    intro record hrecord
    exact hgood record (List.mem_of_mem_take hrecord)
  have hinputAlignment : segment.inputs.take count = inputs Q := hinputsTake
  have hchronQ : chronologicalFrom segment.context.preLedger.cursor (inputs Q) := by
    rw [← hinputAlignment]
    exact CollectionCheckedExecution.startAndRunChecked_success_input_chronology
      p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
      initializer.freezeAt initializer.base initializer.outside (segment.inputs.take count)
      ⟨segment.context.preLedger, accepted, ln⟩ hprefixRun
  have hfields := validLedgerCheck_arm_fields ln hvalid
  have hpendingRegisters : ∀ i, i ∈ ln.pending →
      let a := ln.assignment.arm i
      ln.cutoffRegisters a = none ∧
      ln.currentRegisters a = none ∧
      ln.increment a = 0 ∧
      ln.gammaLoc a = 0 ∧
      ln.baseScore i = initializer.base i := by
    intro i hi
    let a := ln.assignment.arm i
    have harm : armPending ln a := ⟨i, hi, rfl⟩
    have harmCheck : armPendingCheck ln a = true :=
      (armPendingCheck_eq_true_iff_local ln a).mpr harm
    have hcurrentRow := (allFin_eq_true_iff_local _).mp hfields.1 a
    have hcutoffRow := (allFin_eq_true_iff_local _).mp hfields.2.1 a
    have hgammaRow := (allFin_eq_true_iff_local _).mp hfields.2.2.1 a
    have hincrementRow := (allFin_eq_true_iff_local _).mp hfields.2.2.2.1 a
    have hcurrentNone : ln.currentRegisters a = none := by
      rw [harmCheck] at hcurrentRow
      have hnone : (ln.currentRegisters a).isNone = true := by simpa using hcurrentRow
      cases hreg : ln.currentRegisters a <;> simp [hreg] at hnone ⊢
    have hcutoffNone : ln.cutoffRegisters a = none := by
      rw [harmCheck] at hcutoffRow
      have hnone : (ln.cutoffRegisters a).isNone = true := by simpa using hcutoffRow
      cases hreg : ln.cutoffRegisters a <;> simp [hreg] at hnone ⊢
    have hgammaZero : ln.gammaLoc a = 0 := by
      rw [harmCheck] at hgammaRow
      simpa using hgammaRow
    have hincrementZero : ln.increment a = 0 := by
      rw [harmCheck] at hincrementRow
      simpa using hincrementRow
    have hbaseI : ln.baseScore i = initializer.base i := by rw [hbase]
    exact ⟨hcutoffNone, hcurrentNone, hincrementZero, hgammaZero, hbaseI⟩
  have hnonpendingRaw : ∀ a, ¬ armPending ln a → ∀ r, ln.rawBuffer a r = none := by
    intro a hnot r
    exact rawBuffer_none_of_not_armPending ln hvalid a hnot r
  have hbufferForPending : ∀ (arm : Fin p.K), ln.currentRegisters arm = none →
      (∀ r amount, ln.rawBuffer arm r = some amount ↔
        ∃ record ∈ Q, record.input.time = r ∧
          ∃ output,
            record.output.coordinator.recording = some output ∧
            output.gateArm = some arm ∧ output.rawArrival = amount ∧
            0 < amount ∧ r.val + 1 < segment.context.preLedger.freezeAt) ∧
      (∀ record ∈ Q, ∃ done,
        extractRound record = some done ∧
        ln.enabledHistory done.input.round = some done.input.enabled) ∧
      (∀ r, sourceRound r < segment.context.preLedger.cursor →
        ln.rawBuffer arm r = none) ∧
      (∀ r, segment.context.preLedger.freezeAt ≤ sourceRound r →
        ln.rawBuffer arm r = none) ∧
      (∀ r, ln.cursor ≤ sourceRound r → ln.rawBuffer arm r = none) := by
    intro arm hunknown
    let execution : CollectionCheckedExecution.Execution p rate.eta.val
        rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale :=
      ⟨segment.context.preLedger, accepted, ln⟩
    have hRun : CollectionCheckedExecution.startAndRunChecked p rate.eta.val
        rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n
        rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
        initializer.freezeAt initializer.base initializer.outside (segment.inputs.take count) =
          .success execution := by
      simpa only [execution] using hprefixRun
    have hbuffer := CollectionBufferProvenance.startAndRunChecked_success_unknown_buffer
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside (segment.inputs.take count) execution arm hRun
      (by simpa only [execution] using hunknown)
    rcases hbuffer with ⟨_, hinitialCursor, _, _, _, _, _, henables,
      _, hformula, hfreezeEmpty, houtsideEmpty, _⟩
    have hinitContext :=
      CollectionBufferProvenance.startCollectionChecked_success_context
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside segment.context.preLedger (by
          exact hstartRaw)
    have hpreCursor' : execution.initial.cursor = segment.context.preLedger.cursor := by
      calc
        execution.initial.cursor = initializer.cutoff := hinitialCursor
        _ = segment.context.preLedger.cursor := hinitContext.2.2.1.symm
    have hpreFreeze : segment.context.preLedger.freezeAt = initializer.freezeAt :=
      hinitContext.2.2.2.2.1
    have hrawIff : ∀ r amount, ln.rawBuffer arm r = some amount ↔
        ∃ record ∈ Q, record.input.time = r ∧
          ∃ output,
            record.output.coordinator.recording = some output ∧
            output.gateArm = some arm ∧ output.rawArrival = amount ∧
            0 < amount ∧ r.val + 1 < segment.context.preLedger.freezeAt := by
      intro r amount
      have hcell := hformula r
      constructor
      · intro hsome
        rw [hcell] at hsome
        cases hfind : CollectionBufferProvenance.findRoundInput?
            (segment.inputs.take count) r with
        | none => simp [hfind] at hsome
        | some input =>
            have ⟨hinputMem, hinputRound⟩ :=
              CollectionBufferProvenance.findRoundInput?_spec
                (segment.inputs.take count) r input hfind
            cases hraw : input.raw with
            | none => simp [hfind, hraw] at hsome
            | some pair =>
                rcases pair with ⟨rawArm, rawAmount⟩
                by_cases hcondition : rawArm = arm ∧ 0 < rawAmount ∧
                    sourceRound r < initializer.freezeAt
                · simp [hfind, hraw, hcondition] at hsome
                  have hamount : rawAmount = amount := hsome
                  have hinputMemQ : input ∈ inputs Q := by
                    rw [← hinputAlignment]
                    exact hinputMem
                  obtain ⟨record, hrecord, done, hextract, hcompletedInput⟩ :=
                    retained_record_of_prefix_input Q input hinputMemQ
                  have hcompletedRound :=
                    (actual_collection_round_checked record done hextract).2.1
                  have hround : record.input.time = r := by
                    calc
                      record.input.time = done.input.round := hcompletedRound.symm
                      _ = input.round := congrArg RoundInput.round hcompletedInput
                      _ = r := hinputRound
                  obtain ⟨output, hrecording, hrawInput, _⟩ :=
                    ReferenceCollectionRawBufferHistory.actual_completed_input_recording
                      record done hextract
                  have hrawEq : done.input.raw = input.raw :=
                    congrArg RoundInput.raw hcompletedInput
                  have hgate : output.gateArm.map (fun a => (a, output.rawArrival)) =
                      some (rawArm, rawAmount) := by
                    calc
                      output.gateArm.map (fun a => (a, output.rawArrival)) = done.input.raw :=
                        hrawInput.symm
                      _ = input.raw := hrawEq
                      _ = some (rawArm, rawAmount) := hraw
                  cases hgateArm : output.gateArm with
                  | none => simp [hgateArm] at hgate
                  | some actualArm =>
                      simp [hgateArm] at hgate
                      rcases hgate with ⟨hactualArm, hactualAmount⟩
                      have hgateArm' : output.gateArm = some arm := by
                        rw [hgateArm, hactualArm.trans hcondition.1]
                      have harrival : output.rawArrival = amount := hactualAmount.trans hamount
                      have hpositive : 0 < amount := by omega
                      refine ⟨record, hrecord, hround, output, hrecording, hgateArm',
                        harrival, hpositive, ?_⟩
                      simpa only [CoordinatorCollectionLedger.sourceRound, hpreFreeze] using
                        hcondition.2.2
                · simp [hfind, hraw, hcondition] at hsome
      · rintro ⟨record, hrecord, hround, output, hrecording, hgateArm,
          harrival, hpositive, hbefore⟩
        obtain ⟨done, hextract, hinputMem, hcompletedRound, hraw, henabled⟩ :=
          retained_completed_input_of_records Q hprefixGood record hrecord
        have hfind : CollectionBufferProvenance.findRoundInput? (inputs Q)
            done.input.round = some done.input :=
          CollectionBufferProvenance.chronologicalFrom_findRoundInput?_of_mem
            segment.context.preLedger.cursor (inputs Q) hchronQ done.input hinputMem
        have hfindRound : CollectionBufferProvenance.findRoundInput?
            (segment.inputs.take count) r = some done.input := by
          rw [hinputAlignment]
          have hr : done.input.round = r := hcompletedRound.trans hround
          rw [← hr]
          exact hfind
        have hrawInput : done.input.raw = some (arm, amount) := by
          calc
            done.input.raw =
                ReferenceCollectionRawBufferHistory.rawDiagnostic record := hraw
            _ = output.gateArm.map (fun a => (a, output.rawArrival)) := by
              simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording]
            _ = some (arm, amount) := by simp [hgateArm, harrival]
        have hbeforeInit : sourceRound r < initializer.freezeAt := by
          simpa only [CoordinatorCollectionLedger.sourceRound, hpreFreeze] using hbefore
        rw [hcell, hfindRound]
        simp [hrawInput, hbeforeInit, hpositive]
    have hbeforeInitialEmpty : ∀ r,
        sourceRound r < segment.context.preLedger.cursor → ln.rawBuffer arm r = none := by
      intro r hbefore
      exact houtsideEmpty r (Or.inl (by rw [hpreCursor']; exact hbefore))
    have henablesQ : ∀ record ∈ Q, ∃ done,
        extractRound record = some done ∧
        ln.enabledHistory done.input.round = some done.input.enabled := by
      intro record hrecord
      obtain ⟨done, hextract, hinputMem, _, _, _⟩ :=
        retained_completed_input_of_records Q hprefixGood record hrecord
      have hinputMemPrefix : done.input ∈ segment.inputs.take count := by
        rw [hinputAlignment]
        exact hinputMem
      exact ⟨done, hextract, henables done.input hinputMemPrefix⟩
    refine ⟨hrawIff, henablesQ, hbeforeInitialEmpty, ?_, ?_⟩
    · intro r hafter
      exact hfreezeEmpty r (by simpa only [hpreFreeze] using hafter)
    · intro r hafter
      exact houtsideEmpty r (Or.inr hafter)
  have hpendingData : ∀ i, i ∈ ln.pending →
      let arm := ln.assignment.arm i
      ln.cutoffRegisters arm = none ∧
      ln.currentRegisters arm = none ∧
      ln.increment arm = 0 ∧
      ln.gammaLoc arm = 0 ∧
      ln.baseScore i = initializer.base i ∧
      (∀ r amount, ln.rawBuffer arm r = some amount ↔
        ∃ record ∈ Q, record.input.time = r ∧
          ∃ output,
            record.output.coordinator.recording = some output ∧
            output.gateArm = some arm ∧ output.rawArrival = amount ∧
            0 < amount ∧ r.val + 1 < segment.context.preLedger.freezeAt) ∧
      (∀ r, sourceRound r < segment.context.preLedger.cursor →
        ln.rawBuffer arm r = none) ∧
      (∀ r, segment.context.preLedger.freezeAt ≤ sourceRound r →
        ln.rawBuffer arm r = none) ∧
      (∀ r, ln.cursor ≤ sourceRound r → ln.rawBuffer arm r = none) := by
    intro i hi
    let arm := ln.assignment.arm i
    have hregs := hpendingRegisters i hi
    have hbuffer := hbufferForPending arm hregs.2.1
    exact ⟨hregs.1, hregs.2.1, hregs.2.2.1, hregs.2.2.2.1,
      hregs.2.2.2.2, hbuffer.1, hbuffer.2.2.1,
      hbuffer.2.2.2.1, hbuffer.2.2.2.2⟩
  have hcountZeroEmpty : count = 0 → ∀ a r, ln.rawBuffer a r = none := by
    intro hzero a r
    change (endpointLedger segment.context.preLedger
      (segment.records.take count)).rawBuffer a r = none
    rw [hzero]
    have hstartRaw :=
      CollectionBufferProvenance.startCollectionChecked_success_empty_rawBuffer
        initializer.assignment initializer.sigma initializer.cutoff
        initializer.freezeAt initializer.base initializer.outside segment.context.preLedger
        hstartRaw
    simpa [List.take_zero, endpointLedger,
      ReferenceCollectionSegmentExtraction.completed] using hstartRaw a r
  have hfullEndpoint : count = segment.records.length → ln = segment.final := by
    intro hfull
    change endpointLedger segment.context.preLedger
        (segment.records.take count) = segment.final
    rw [hfull]
    have htake : segment.records.take segment.records.length = segment.records :=
      List.take_of_length_le (Nat.le_refl _)
    simp only [htake, Segment.final]
  have henablesOutput : ∀ record ∈ Q, ∃ done,
      extractRound record = some done ∧
      ln.enabledHistory done.input.round = some done.input.enabled := by
    intro record hrecord
    obtain ⟨done, hextract, hinputMem, _, _, _⟩ :=
      retained_completed_input_of_records Q hprefixGood record hrecord
    have hinputMemPrefix : done.input ∈ segment.inputs.take count := by
      rw [hinputAlignment]
      exact hinputMem
    have hrecordsEnables :=
      CollectionCheckedExecution.startAndRunChecked_success_records_supplied_enables
        p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
        rate.n rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
        initializer.freezeAt initializer.base initializer.outside (segment.inputs.take count)
        ⟨segment.context.preLedger, accepted, ln⟩ hprefixRun
    exact ⟨done, hextract, hrecordsEnables done.input hinputMemPrefix⟩
  have hunique : ∀ left right, left ∈ Q → right ∈ Q →
      left.input.time = right.input.time → left = right := by
    intro left right hleft hright htime
    exact run_segment_record_time_injective initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
      hspan hactive e segment hsegmentRun left right
      (List.mem_of_mem_take hleft) (List.mem_of_mem_take hright) htime
  refine ⟨initializer, hinitializer, hcheckedStart, accepted, hfold',
    hprefixChron.2, hcursor, hassignment, hsigma, hcutoff, hfreeze, hbase,
    hvalid, hpendingData, hnonpendingRaw, hcountZeroEmpty, hfullEndpoint,
    henablesOutput, hunique⟩

end Bandits.Support.ReferenceCompleteCollectionPrefixRawBufferHistory

end
