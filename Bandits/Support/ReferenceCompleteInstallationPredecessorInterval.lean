/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory
public import Bandits.Support.ReferenceCompleteRetainedCollectionSegmentEndpoint
public import Bandits.Support.ReferenceCompleteFirstInstallationSpanCut

/-!
# Installation predecessor and collection interval

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceCompleteInstallationPredecessorInterval

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionPhaseHistory ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Read the retained follower base from the actual successful installation tag.
Failures and continuing operations install no new base. -/
def installationBase? {x : RoundInput p rate} (cut : DispatchCut x) :
    Option (Fin (p.m - 1) → ℕ) :=
  match cut with
  | .first (.chosen installed _) => some installed.followerBaseScore
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      some installed.retainedBaseScore
  | _ => none

private theorem complete_suffix_connected
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ∃ initial final,
      ReferenceActivePhysicalHorizon.Connected initial
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) final := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hrecords := (ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate z rewards C_star C_h hlaunch).2.1
      have hb := b.isLt
      have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length = 0 := by rw [hrecords]; rfl
      omega
  | some active =>
      exact ⟨active,
        (ReferenceActivePhysicalHorizon.run active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate z rewards C_star C_h
            omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate z rewards C_star C_h active hlaunch)).finalState,
        ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate z rewards C_star C_h active hlaunch⟩

private theorem connected_adjacent
    {records : List (RoundRecord (p := p) (rate := rate))}
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    (hconn : ReferenceActivePhysicalHorizon.Connected initial records final)
    (k : ℕ) (hk : k + 1 < records.length) :
    (records[k]'(by omega)).output.next = (records[k + 1]'(by omega)).input.state := by
  induction records generalizing initial k with
  | nil => simp at hk
  | cons record rest ih =>
      cases k with
      | zero =>
          cases rest with
          | nil => simp at hk
          | cons next tail =>
              change record.input.state = initial ∧
                ReferenceActivePhysicalHorizon.Connected record.output.next (next :: tail) final
                at hconn
              rcases hconn with ⟨_, hrest⟩
              change next.input.state = record.output.next ∧
                ReferenceActivePhysicalHorizon.Connected next.output.next tail final at hrest
              exact hrest.1.symm
      | succ k =>
          simp only [List.length_cons] at hk
          have hrest : ReferenceActivePhysicalHorizon.Connected record.output.next rest final :=
            hconn.2
          have h := ih hrest k (by omega)
          simpa using h

private theorem complete_suffix_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have hvalues := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hindex : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h]
    exact k.isLt
  have hget := congrArg (fun values : List ℕ => values[k.val]?) hvalues
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex, Nat.one_mul] at hget
  exact Option.some.inj hget

private theorem installationBirth_output_frame
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    ReferenceAssignmentPayloadPersistence.storedPayload record.output.next.coordinator = none ∨
      ReferenceAssignmentPayloadPersistence.storedPayload record.output.next.coordinator =
        some payload := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, _⟩
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .first (.chosen installed selected) := by
            simpa only [hprepared] using hcoord
          by_cases hselection :
              (ReferenceActivePhysicalStep.DispatchCut.first
                (.chosen installed selected)).selection = none
          · have hnone : record.output.preparation.coordinator.selection = none := by
              rw [hprepared, hcut]
              exact hselection
            exact Or.inl (ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
              record hnone)
          · have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
              (ReferenceActivePhysicalStep.prepare record.input) (.chosen installed selected) hcut
            have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
              (ReferenceActivePhysicalStep.prepare record.input) installed.registers
              installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
            rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
            change ReferenceAssignmentPayloadPersistence.storedPayload
              (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration = none ∨
                ReferenceAssignmentPayloadPersistence.storedPayload
                  (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration =
                    some installed.registers.payload
            rw [hobs]
            simp only [ite_eq_right hselection]
            exact hframe
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output localConsistency_eq clockData installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, _⟩
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .collection old ledger clock cutoff
                (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                  output localConsistency_eq clockData installed selected) := by
            simpa only [hprepared] using hcoord
          by_cases hselection :
              (ReferenceActivePhysicalStep.DispatchCut.collection old ledger clock cutoff
                (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                  output localConsistency_eq clockData installed selected)).selection = none
          · have hnone : record.output.preparation.coordinator.selection = none := by
              rw [hprepared, hcut]
              exact hselection
            exact Or.inl (ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
              record hnone)
          · have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
              (ReferenceActivePhysicalStep.prepare record.input) old ledger clock cutoff
              (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                output localConsistency_eq clockData installed selected) hcut
            have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
              (ReferenceActivePhysicalStep.prepare record.input) installed.registers
              installed.ownedRegisters installed.retainedBaseScore started
            rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
            change ReferenceAssignmentPayloadPersistence.storedPayload
              (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration = none ∨
                ReferenceAssignmentPayloadPersistence.storedPayload
                  (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration =
                    some installed.registers.payload
            rw [hobs]
            simp only [ite_eq_right hselection]
            exact hframe
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

private theorem livePostChoice_stored_is_live
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : Payload rate)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration =
        some payload) :
    ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      ∃ nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next,
        (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration =
          .live next nextOwned base := by
  classical
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none =>
      simp [ReferenceActivePhysicalStep.livePostChoice, hrecord,
        ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceAssignmentPayloadPersistence.storedPayload] at hstored
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason =>
          simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
            ReferenceActivePhysicalStep.coordinatorFailure,
            ReferenceAssignmentPayloadPersistence.storedPayload] at hstored
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
                hconfirmation, ReferenceActivePhysicalStep.coordinatorFailure,
                ReferenceAssignmentPayloadPersistence.storedPayload] at hstored
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
                    hconfirmation, hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                    ReferenceAssignmentPayloadPersistence.storedPayload] at hstored
              | ok finished =>
                  let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
                    payload := registers.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := x.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  let nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next := {
                    queue := serviced.queue
                    previousService := serviced.previousService }
                  exact ⟨next, nextOwned, by
                    simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
                      hconfirmation, hfinish, next, nextOwned]⟩

private theorem installationBirth_next_live
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      record.output.next.coordinator = some payload) :
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
      record.output.next.coordinator = .live registers owned base ∧
      installationBase? record.output.preparation.coordinator = some base := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, _⟩
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .first (.chosen installed selected) := by
            simpa only [hprepared] using hcoord
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            (ReferenceActivePhysicalStep.prepare record.input) (.chosen installed selected) hcut
          have hstoredObs := hstored
          rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
            at hstoredObs
          change ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration =
              some installed.registers.payload at hstoredObs
          rw [hobs] at hstoredObs
          by_cases hselection :
              (ReferenceActivePhysicalStep.DispatchCut.first
                (.chosen installed selected)).selection = none
          · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure,
              ReferenceAssignmentPayloadPersistence.storedPayload] at hstoredObs
          · simp only [ite_eq_right hselection] at hstoredObs
            obtain ⟨next, nextOwned, hnextLive⟩ :=
              livePostChoice_stored_is_live (ReferenceActivePhysicalStep.prepare record.input)
                installed.registers installed.ownedRegisters installed.followerBaseScore
                installed.startRoundResult installed.registers.payload hstoredObs
            have hnext : record.output.next.coordinator = .live next nextOwned installed.followerBaseScore := by
              rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
              rw [hobs]
              simp only [ite_eq_right hselection]
              exact hnextLive
            exact ⟨next, nextOwned, installed.followerBaseScore, hnext, by simp only [installationBase?]⟩
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output localConsistency_eq clockData installed selected =>
          simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
          rcases hbirth with ⟨rfl, _⟩
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .collection old ledger clock cutoff
                (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                  output localConsistency_eq clockData installed selected) := by
            simpa only [hprepared] using hcoord
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare record.input) old ledger clock cutoff
            (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
              output localConsistency_eq clockData installed selected) hcut
          have hstoredObs := hstored
          rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
            at hstoredObs
          change ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration =
              some installed.registers.payload at hstoredObs
          rw [hobs] at hstoredObs
          by_cases hselection :
              (ReferenceActivePhysicalStep.DispatchCut.collection old ledger clock cutoff
                (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                  output localConsistency_eq clockData installed selected)).selection = none
          · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure,
              ReferenceAssignmentPayloadPersistence.storedPayload] at hstoredObs
          · simp only [ite_eq_right hselection] at hstoredObs
            obtain ⟨next, nextOwned, hnextLive⟩ :=
              livePostChoice_stored_is_live (ReferenceActivePhysicalStep.prepare record.input)
                installed.registers installed.ownedRegisters installed.retainedBaseScore started
                installed.registers.payload hstoredObs
            have hnext : record.output.next.coordinator =
                .live next nextOwned installed.retainedBaseScore := by
              rw [record.output_eq, (ReferenceActivePhysicalStep.step_next_fields record.input).1]
              rw [hobs]
              simp only [ite_eq_right hselection]
              exact hnextLive
            exact ⟨next, nextOwned, installed.retainedBaseScore, hnext, by simp only [installationBase?]⟩
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

private theorem predecessor_stored_payload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    (hconn : ReferenceActivePhysicalHorizon.Connected initial
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) final)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hk : k.val + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (payload : Payload rate) (birthIndex : ℕ)
    (hpayloadTime : payload.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + birthIndex)
    (hkBirth : birthIndex < k.val)
    (hnext : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
        ⟨k.val + 1, by omega⟩).input.state.coordinator = some payload) :
    ReferenceAssignmentPayloadPersistence.storedPayload
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
          k).input.state.coordinator = some payload ∧
      (∀ fresh, ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
          k) fresh) := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).get k
  have hadj : record.output.next =
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
        ⟨k.val + 1, by omega⟩).input.state := by
    simpa only [record, List.get_eq_getElem] using connected_adjacent hconn k.val hk
  have hout : ReferenceAssignmentPayloadPersistence.storedPayload
      record.output.next.coordinator = some payload := by
    rw [hadj]
    exact hnext
  have hnotBirth : ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord record.input) payload := by
    intro hb
    have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      (ReferenceAssignmentPayloadChronology.actualStepRecord record.input) payload hb
    have hrecordTime : (ReferenceAssignmentPayloadChronology.actualStepRecord
        record.input).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
      change record.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val
      simpa only [record, List.get_eq_getElem] using
        complete_suffix_record_time rate rewards C_star C_h z k
    omega
  have hrecordTime : record.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
    simpa only [record, List.get_eq_getElem] using
      complete_suffix_record_time rate rewards C_star C_h z k
  have hnotBirthRecord : ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
      record payload := by
    intro hb
    have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      record payload hb
    omega
  have hnoBirth : ∀ fresh, ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth record fresh := by
    intro fresh hfresh
    rcases installationBirth_output_frame record fresh hfresh with hnone | hfreshStored
    · rw [hnone] at hout
      cases hout
    · have hEq : fresh = payload := Option.some.inj (hfreshStored.symm.trans hout)
      subst fresh
      exact hnotBirthRecord hfresh
  have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification record.input
  rw [record.output_eq] at hout
  rcases hclass with hnone | ⟨old, hold, hkeep⟩ | ⟨fresh, hfresh, hnew⟩
  · rw [hnone] at hout
    cases hout
  · have holdEq : old = payload := Option.some.inj (hkeep.symm.trans hout)
    subst old
    exact ⟨hold, hnoBirth⟩
  · have hfreshEq : fresh = payload := Option.some.inj (hnew.symm.trans hout)
    subst fresh
    exact False.elim (hnotBirth hfresh)

private theorem stored_payload_on_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    (hconn : ReferenceActivePhysicalHorizon.Connected initial
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) final)
    (a b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (payload : Payload rate)
    (hcurrent : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
        b).input.state.coordinator = some payload)
    (_hab : a.val < b.val)
    (hpayloadTime : payload.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a.val) :
    ∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, a.val < k.val → k.val ≤ b.val →
      ReferenceAssignmentPayloadPersistence.storedPayload
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
          k).input.state.coordinator = some payload ∧
      (k.val < b.val →
        ∀ fresh, ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
            k) fresh) := by
  have hgo : ∀ n, ∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, a.val < k.val → k.val ≤ b.val →
      b.val - k.val = n →
      ReferenceAssignmentPayloadPersistence.storedPayload
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
            k).input.state.coordinator = some payload ∧
        (k.val < b.val →
          ∀ fresh, ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
              k) fresh) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro k hak hkb hdiff
        by_cases hEq : k.val = b.val
        · have hk : k = b := Fin.ext hEq
          subst k
          exact ⟨hcurrent, by intro h fresh; omega⟩
        · have hkl : k.val < b.val := by omega
          let kNext : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).length := ⟨k.val + 1, by omega⟩
          have hdiffNext : b.val - kNext.val < n := by
            rw [← hdiff]
            dsimp [kNext]
            omega
          have hkNext : kNext.val = k.val + 1 := by simp [kNext]
          have hnext := ih (b.val - kNext.val) hdiffNext kNext
            (by rw [hkNext]; omega) (by rw [hkNext]; omega)
            (by simp [kNext])
          have hstep := predecessor_stored_payload rate rewards C_star C_h z hconn k
            (by omega) payload a.val hpayloadTime (by omega)
            (by simpa [kNext] using hnext.1)
          refine ⟨hstep.1, ?_⟩
          intro _ fresh
          exact hstep.2 fresh
  intro k hak hkb
  exact hgo (b.val - k.val) k hak hkb rfl

/-- An actual later-chosen record has an earlier installation of its retained
payload. The score base is tied to the installation's literal constructor. -/
theorem internal_later_chosen_retained_installation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R : List (RoundRecord (p := p) (rate := rate)) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (payload : Payload rate) (ledger : Ledger rate)
      (saved : Option (Fin p.T × Bool)) (a : Fin R.length)
      (r0 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q0 : CoordinatorLiveServiceFinish.OwnedRegisters r0)
      (beta : Fin (p.m - 1) → ℕ),
      (R[b.val]'b.isLt).input.state.coordinator = .collection payload ledger saved ∧
      ledger.pending = ∅ ∧
      a.val < b.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth
        (R[a.val]'a.isLt) payload ∧
      payload.sigma.val = (R[a.val]'a.isLt).input.time.val ∧
      payload.sigma.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a.val ∧
      (∀ k : Fin R.length, a.val < k.val → k.val ≤ b.val →
        ReferenceAssignmentPayloadPersistence.storedPayload
            (R.get k).input.state.coordinator = some payload ∧
          (k.val < b.val →
            ∀ fresh, ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
              (R.get k) fresh)) ∧
      (R[a.val]'a.isLt).output.next.coordinator = .live r0 q0 beta ∧
      installationBase? (R[a.val]'a.isLt).output.preparation.coordinator = some beta ∧
      r0.payload = payload := by
  intro R
  obtain ⟨payload, ledger, saved, hstate, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty (R[b.val]'b.isLt).input hb
  have hret := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z b
  dsimp only at hret
  rw [hstate] at hret
  rcases hret with ⟨⟨a, hab, hbBirth, _hbase⟩, _, _, _⟩
  have htime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[a.val]'a.isLt) payload hbBirth
  have hvalues := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hindex : a.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h]
    exact a.isLt
  have hget := congrArg (fun values : List ℕ => values[a.val]?) hvalues
  rw [List.getElem?_map, List.getElem?_eq_getElem a.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex, Nat.one_mul] at hget
  have htimeIndex : (R[a.val]'a.isLt).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a.val :=
    Option.some.inj hget
  obtain ⟨initial, final, hconn⟩ := complete_suffix_connected rate rewards C_star C_h z b
  have hcurrent : ReferenceAssignmentPayloadPersistence.storedPayload
      (R.get b).input.state.coordinator = some payload := by
    change ReferenceAssignmentPayloadPersistence.storedPayload
      (R[b.val]'b.isLt).input.state.coordinator = some payload
    rw [hstate]
    rfl
  have hcarry := stored_payload_on_interval rate rewards C_star C_h z hconn a b payload
    hcurrent hab (htime.trans htimeIndex)
  have haNextLt : a.val + 1 < R.length := by
    have hle : a.val + 1 ≤ b.val := by omega
    exact Nat.lt_of_le_of_lt hle b.isLt
  let aNext : Fin R.length := ⟨a.val + 1, haNextLt⟩
  have haNextGt : a.val < aNext.val := by simp [aNext]
  have haNextLe : aNext.val ≤ b.val := by
    simp [aNext]
    omega
  have hcarryNext := hcarry aNext haNextGt haNextLe
  have hadjA := connected_adjacent hconn a.val haNextLt
  have hstoredA : ReferenceAssignmentPayloadPersistence.storedPayload
      ((R[a.val]'a.isLt).output.next.coordinator) = some payload := by
    rw [hadjA]
    simpa only [List.get_eq_getElem, aNext] using hcarryNext.1
  obtain ⟨r0, q0, beta, hnext, hbeta⟩ :=
    installationBirth_next_live (R[a.val]'a.isLt) payload hbBirth hstoredA
  have hpayload : r0.payload = payload := by
    rw [hnext] at hstoredA
    exact Option.some.inj hstoredA
  exact ⟨payload, ledger, saved, a, r0, q0, beta, hstate, hempty, hab, hbBirth,
    htime, htime.trans htimeIndex, hcarry, hnext, hbeta, hpayload⟩

private theorem complete_zero_first
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hzero : 0 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[0]'hzero).input.state.coordinator = .first := by
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).length := ⟨0, hzero⟩
  obtain ⟨hc, span, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  rw [List.get_eq_getElem] at hrecord
  rw [hrecord]
  have hspan0 : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 0 ≤ p.T := by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  have hmode : allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z rewards C_star C_h hc).activeAtStart
  change (ReferenceActivePhysicalHorizon.run
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    0 hspan0 hmode).finalState.coordinator = .first
  rw [ReferenceActivePhysicalHorizon.run_zero_final]
  exact (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc).coordinatorFirst

private theorem first_dispatch_base (x : RoundInput p rate) :
    installationBase? (.first (CoordinatorRoundDispatch.dispatchFirst (firstInput x))) =
      some (fun _ => 0) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  dsimp only
  split
  · contradiction
  · rfl

private theorem first_record_base_zero
    (record : RoundRecord (p := p) (rate := rate))
    (hfirst : record.input.state.coordinator = .first)
    (beta : Fin (p.m - 1) → ℕ)
    (hbase : installationBase? record.output.preparation.coordinator = some beta) :
    beta = (fun _ => 0) := by
  have hprep : record.output.preparation.coordinator =
      (prepare record.input).coordinator := by rw [record.output_eq]; rfl
  have hd := dispatch_first record.input hfirst
  change (prepare record.input).coordinator = _ at hd
  rw [hprep, hd, first_dispatch_base] at hbase
  exact (Option.some.inj hbase).symm

private theorem later_retained_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (r0 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q0 : CoordinatorLiveServiceFinish.OwnedRegisters r0)
    (beta : Fin (p.m - 1) → ℕ)
    (hab : a.val < b.val)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hnext : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[a.val].output.next.coordinator = .live r0 q0 beta)
    (htime : r0.payload.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a.val)
    (hapos : 0 < a.val) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (a.val + 1)
    ∃ (e : ℕ) (seg : Segment rate) (I : Initializer p),
      a.val < e ∧ e < b.val ∧ e = a.val + 1 + W.length ∧
      segmentAt R e = some seg ∧ seg.records ≠ [] ∧ R[e]? = some seg.entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.context.payload = r0.payload ∧ seg.context.initializer = some I ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
      I.assignment.arm = r0.payload.assignment.assigned ∧
      I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧ I.base = beta := by
  classical
  intro R s W
  have hbLt : b.val < R.length := b.isLt
  have haNext : a.val + 1 < R.length := by omega
  let k : Fin R.length := ⟨a.val + 1, haNext⟩
  have hk : k.val = a.val + 1 := rfl
  have hstate : (R[k.val]'k.isLt).input.state.coordinator = .live r0 q0 beta := by
    change (R[a.val + 1]'haNext).input.state.coordinator = .live r0 q0 beta
    rw [ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z a.val haNext]
    exact hnext
  have hlater : s < r0.payload.sigma.val := by dsimp only [s]; omega
  let e := k.val + W.length
  have heb : e < b.val := by
    by_contra h
    have hv : b.val - k.val ≤ W.length := by dsimp only [e, k] at h ⊢; omega
    obtain ⟨rv, qv, _, _, hin⟩ :=
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_live
        rewards C_star C_h z k r0 q0 beta hstate hlater (b.val - k.val) hv
    have heq : k.val + (b.val - k.val) = b.val := by dsimp only [k]; omega
    have hLive := hin (by rw [heq]; exact b.isLt)
    have hLiveB : (R[b.val]'b.isLt).input.state.coordinator = .live rv qv beta := by
      simpa only [heq] using hLive
    obtain ⟨payloadB, ledgerB, savedB, hB, _⟩ := laterChosen_pending_empty (R[b.val]'b.isLt).input hb
    rw [hB] at hLiveB
    cases hLiveB
  have hword := ReferenceCompleteLaterCollectionCalendarWord.complete_later_live_collection_calendar_word
    rate rewards C_star C_h z k
  dsimp only at hword
  split at hword
  next r q base hs =>
    have hfields := CoordinatorConfiguration.live.inj (hs.symm.trans hstate)
    obtain ⟨hr, hq, hbase⟩ := hfields
    subst r
    cases hq
    subst base
    obtain ⟨_, _, rE, qE, _, _, _, _, halt⟩ := hword hlater
    rcases halt with hterminal | ⟨he, chosen, _, _, hcut⟩
    · change e = R.length at hterminal
      omega
    · cases chosen <;> simp only at hcut
      next dispatched consistent ledger hdispatch hlocal hselected hbound hscore hqueue hservice hbase =>
        obtain ⟨_, _, seg, I, Dword, hD, hat, hentry, hp, hpre, hi, _, hchecked,
          harm, hsigma, hdate, _, _, hbeta, hcutoff, htail, _⟩ := hcut
        obtain ⟨tail, hrecords⟩ := htail
        refine ⟨e, seg, I, by dsimp only [e, k]; omega, heb, rfl,
          hat, ?_, ?_, hcutoff, hp, hi, ?_, harm, hsigma, hdate, hbeta⟩
        · rw [hrecords]
          exact List.cons_ne_nil _ _
        · rw [hentry]
          exact List.getElem?_eq_getElem he
        · rw [hpre]
          exact hchecked
  next hnot => exact False.elim (hnot r0 q0 beta hstate)

/-- An actual later installation has an immediate retained predecessor,
its literal live word and cutoff initializer, and the whole collection endpoint
on the same complete physical suffix. The only logical input is the actual
later-chosen branch selector. This is an internal structural result. -/
theorem internal_complete_installation_predecessor_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (a : Fin R.length)
      (r0 : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q0 : CoordinatorLiveServiceFinish.OwnedRegisters r0)
      (beta : Fin (p.m - 1) → ℕ)
      (e : ℕ) (seg : Segment rate) (I : Initializer p)
      (saved : Option (Fin p.T × Bool)),
      let Wlive := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (a.val + 1)
      a.val < e ∧ e < b.val ∧ e = a.val + 1 + Wlive.length ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[a.val]'a.isLt) r0.payload ∧
      r0.payload.sigma.val = s + a.val ∧
      (R[a.val]'a.isLt).output.next.coordinator = .live r0 q0 beta ∧
      installationBase? (R[a.val]'a.isLt).output.preparation.coordinator = some beta ∧
      (∀ k : Fin R.length, a.val < k.val → k.val < b.val →
        ∀ fresh : Payload rate,
          ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth (R[k.val]'k.isLt) fresh) ∧
      segmentAt R e = some seg ∧ seg.records ≠ [] ∧ R[e]? = some seg.entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.context.payload = r0.payload ∧ seg.context.initializer = some I ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
      I.assignment.arm = r0.payload.assignment.assigned ∧
      I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧ I.base = beta ∧
      b.val = e + seg.records.length ∧
      R.take b.val = R.take a.val ++ [(R[a.val]'a.isLt)] ++ Wlive ++ seg.records ∧
      R.drop b.val = seg.remaining ∧ seg.exit = .laterChosen (R[b.val]'b.isLt) ∧
      (R[b.val]'b.isLt).input.state = endpointState seg.entry.input.state seg.records ∧
      (R[b.val]'b.isLt).input.state.coordinator = .collection r0.payload seg.final saved ∧
      seg.final.pending = ∅ ∧ seg.final.cursor = s + b.val + 1 ∧
      (a.val = 0 → ∃ u : Fin p.T, u.val = s + e ∧
        z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u (R[b.val]'b.isLt).input.time) := by
  classical
  intro R s
  obtain ⟨payload, ledger, savedB, a, r0, q0, beta, _hstateB, _hemptyB,
    hab, hbirth, _hdateA, htime, hcarry, hnext, hbeta, hpayload⟩ :=
    internal_later_chosen_retained_installation rate rewards C_star C_h z b hb
  change a.val < b.val at hab
  have htime0 : r0.payload.sigma.val = s + a.val := by rw [hpayload]; exact htime
  have hspan :
      ∃ (e : ℕ) (seg : Segment rate) (I : Initializer p),
        a.val < e ∧ e < b.val ∧
        e = a.val + 1 + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (a.val + 1)).length ∧
        segmentAt R e = some seg ∧ seg.records ≠ [] ∧ R[e]? = some seg.entry ∧
        ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
        seg.context.payload = r0.payload ∧ seg.context.initializer = some I ∧
        I.checkedStart rate = .success seg.context.preLedger ∧
        I.assignment.arm = r0.payload.assignment.assigned ∧
        I.sigma = r0.payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧ I.base = beta ∧
        (a.val = 0 → ∃ u : Fin p.T, u.val = s + e ∧
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u (R[b.val]'b.isLt).input.time) := by
    by_cases ha0 : a.val = 0
    · have hcarry0 : ∀ k : Fin R.length, 0 < k.val → k.val ≤ b.val →
          ReferenceAssignmentPayloadPersistence.storedPayload (R.get k).input.state.coordinator =
            some payload ∧
          (k.val < b.val → ∀ fresh,
            ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth (R.get k) fresh) := by
        intro k hk hkb
        exact hcarry k (by rw [ha0]; exact hk) hkb
      obtain ⟨e, seg, I, rE, qE, u, theta, _hwindow, hepos, heb, _hword,
        he, hat, hentry, hne, hcut, _htimeE, _hstateE, _hpE, hpay, _hchoice,
        hi, _hIE, hchecked, hsigma, hcutoff, hbase, harm, _hfreeze, _hfirstCutoff,
        hu, _hcall, _hearlier, _hfirstCall, hcell⟩ :=
        ReferenceCompleteFirstInstallationSpanCut.internal_complete_first_retained_installation_span_cut
          rate rewards C_star C_h z b hb payload hcarry0
      have hfirst : (R[a.val]'a.isLt).input.state.coordinator = .first := by
        have hz : 0 < R.length := Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
        have hf := complete_zero_first (rate := rate) rewards C_star C_h z hz
        simpa only [ha0] using hf
      have hbeta0 := first_record_base_zero (R[a.val]'a.isLt) hfirst beta hbeta
      refine ⟨e, seg, I, by omega, heb, ?_, hat, hne, hentry, hcut,
        hpay.trans hpayload.symm, hi, hchecked, ?_, ?_, hcutoff, ?_, ?_⟩
      · simpa only [ha0, Nat.zero_add] using he
      · rw [hpayload]
        exact harm
      · rw [hpayload]
        exact hsigma
      · exact hbase.trans hbeta0.symm
      · intro _
        exact ⟨u, hu, hcell⟩
    · obtain ⟨e, seg, I, hae, heb, he, hat, hne, hentry, hcut, hpay,
          hi, hchecked, harm, hsigma, hcutoff, hbase⟩ :=
        later_retained_span rate rewards C_star C_h z a b r0 q0 beta hab hb hnext htime0
          (by omega)
      exact ⟨e, seg, I, hae, heb, he, hat, hne, hentry, hcut, hpay, hi,
        hchecked, harm, hsigma, hcutoff, hbase, by intro h; exact False.elim (ha0 h)⟩
  obtain ⟨e, seg, I, hae, heb, he, hat, hne, hentry, hcut, hpay,
    hi, hchecked, harm, hsigma, hcutoff, hbase, hfirst⟩ := hspan
  have hretain : ∀ k : Fin R.length, e < k.val → k.val ≤ b.val →
      ReferenceAssignmentPayloadPersistence.storedPayload (R[k.val]'k.isLt).input.state.coordinator =
        some seg.context.payload := by
    intro k hek hkb
    rw [hpay, hpayload]
    exact (hcarry k (by omega) hkb).1
  have hnobirth : ∀ k : Fin R.length, e < k.val → k.val < b.val →
      ∀ fresh : Payload rate,
        ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth (R[k.val]'k.isLt) fresh := by
    intro k hek hkb fresh
    exact (hcarry k (by omega) (by omega)).2 hkb fresh
  obtain ⟨hbe, hdrop, hexit, hwhole, ⟨saved, hcoord⟩, hpending, hcursor⟩ :=
    ReferenceCompleteRetainedCollectionSegmentEndpoint.internal_complete_retained_collection_segment_endpoint
      rate rewards C_star C_h z e seg hat hne hcut b heb hb hretain hnobirth
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (a.val + 1)
  have hW : W = (R.drop (a.val + 1)).take W.length :=
    List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
  have htakeE : R.take e = R.take a.val ++ [(R[a.val]'a.isLt)] ++ W := by
    rw [he, List.take_add, ← hW, List.take_succ_eq_append_getElem a.isLt]
  have htakeB : R.take b.val = R.take e ++ seg.records := by
    rw [hbe, List.take_add, ← segmentAt_partition R e seg hat, List.take_left]
  refine ⟨a, r0, q0, beta, e, seg, I, saved, hae, heb, he, ?_, htime0,
    hnext, hbeta, ?_, hat, hne, hentry, hcut, hpay, hi, hchecked, harm,
    hsigma, hcutoff, hbase, hbe, ?_, hdrop, hexit, hwhole, ?_, hpending, hcursor, hfirst⟩
  · rw [hpayload]
    exact hbirth
  · intro k hak hkb fresh
    exact (hcarry k hak (by omega)).2 hkb fresh
  · rw [htakeB, htakeE]
  · rw [← hpay]
    exact hcoord

end Bandits.Support.ReferenceCompleteInstallationPredecessorInterval
