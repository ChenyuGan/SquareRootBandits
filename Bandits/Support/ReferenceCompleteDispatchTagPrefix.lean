/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary

/-!
# Actual dispatch tags on strict numerical prefixes

This module projects the three literal constructor tests from each retained
original round code. The code uses its incoming coordinator phase together
with the original successful choice and its `StartRound` result. The dated map
keeps every observation date, including entries without a numerical readout.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceCompleteDispatchTagPrefix

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The finite tag of the input coordinator phase, read from its existing
lossless state code without making its continuous payload discrete. -/
def coordinatorPhaseCode
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) : ℕ :=
  match code with
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

/-- The finite input-phase projection is Borel in the original sum code. -/
theorem coordinatorPhaseCode_measurable :
    Measurable (coordinatorPhaseCode (p := p) (rate := rate)) := by
  unfold coordinatorPhaseCode
  change Measurable (Sum.elim (fun _ : Unit => (0 : ℕ))
    (Sum.elim (fun _ : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => 1)
      (Sum.elim (fun _ : ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => 2)
        (fun _ : Unit => 3))))
  exact (measurable_const : Measurable (fun _ : Unit => (0 : ℕ))).sumElim
    ((measurable_const : Measurable (fun _ : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => (1 : ℕ))).sumElim
      ((measurable_const : Measurable (fun _ : ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => (2 : ℕ))).sumElim
        (measurable_const : Measurable (fun _ : Unit => (3 : ℕ)))))

/-- Keep only the existing countable `StartRoundResult` from a selected
choice observation. -/
local instance selectedStartMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

local instance selectedStartSingleton :
    MeasurableSingletonClass (CoordinatorPhaseClock.StartRoundResult p) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

local instance selectedStartOptionMeasurableSpace :
    MeasurableSpace (Option (CoordinatorPhaseClock.StartRoundResult p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
    (α := CoordinatorPhaseClock.StartRoundResult p)

local instance selectedStartOptionSingleton :
    MeasurableSingletonClass (Option (CoordinatorPhaseClock.StartRoundResult p)) where
  measurableSet_singleton started := by
    rw [selectedStartOptionMeasurableSpace,
      LaterAssignmentStartMeasurability.optionMeasurableSpace,
      MeasurableSpace.measurableSet_comap]
    let target := (Equiv.optionEquivSumPUnit
      (CoordinatorPhaseClock.StartRoundResult p)).toFun started
    have htarget : MeasurableSet ({target} : Set
        (CoordinatorPhaseClock.StartRoundResult p ⊕ PUnit)) := by
      cases started with
      | none =>
          simpa [target, Equiv.optionEquivSumPUnit, Set.image_singleton] using
            (MeasurableSet.inr_image (α := CoordinatorPhaseClock.StartRoundResult p)
              (β := PUnit) (MeasurableSet.singleton PUnit.unit))
      | some value =>
          simpa [target, Equiv.optionEquivSumPUnit, Set.image_singleton] using
            (MeasurableSet.inl_image (α := CoordinatorPhaseClock.StartRoundResult p)
              (β := PUnit)
              (MeasurableSet.singleton value) :
                MeasurableSet (Sum.inl '' ({value} : Set
                  (CoordinatorPhaseClock.StartRoundResult p))))
    refine ⟨{target}, htarget, ?_⟩
    ext x
    cases x <;> cases started <;> simp [target, Equiv.optionEquivSumPUnit]

local instance selectedStartOptionDiscrete :
    DiscreteMeasurableSpace (Option (CoordinatorPhaseClock.StartRoundResult p)) where
  forall_measurableSet s := (Set.to_countable s).measurableSet

def selectedStartCode
    (choice : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)) :
    Option (CoordinatorPhaseClock.StartRoundResult p) :=
  choice.map fun selected => selected.2.1

/-- Decode the successful choice's clock fields according to its actual
incoming phase tag. -/
def dispatchTagFrom (phase : ℕ)
    (started? : Option (CoordinatorPhaseClock.StartRoundResult p)) :
    Bool × Bool × Bool :=
  match phase with
  | 1 =>
      match started? with
      | none => (false, false, false)
      | some started =>
          let cut := match started.ledgerCommand with
            | some (.initializeAt _) => true
            | _ => false
          (cut, false, !cut)
  | 2 =>
      match started? with
      | none => (false, false, false)
      | some started => (false, started.assignmentStart.isSome, false)
  | _ => (false, false, false)

/-- The phase/clock decoder is Borel: its first coordinate is countable and
its second coordinate is the existing discrete clock-result factor. -/
theorem dispatchTagFrom_measurable :
    Measurable (fun pair : ℕ × Option (CoordinatorPhaseClock.StartRoundResult p) =>
      dispatchTagFrom (p := p) pair.1 pair.2) := by
  apply measurable_from_prod_countable_right
  intro phase
  cases phase with
  | zero => exact measurable_const
  | succ n =>
      cases n with
      | zero => exact Measurable.of_discrete
      | succ n =>
          cases n with
          | zero => exact Measurable.of_discrete
          | succ n => exact measurable_const

/-- The three ordered dispatch tags, decoded only from the original retained
incoming phase and successful choice coordinates. -/
def dispatchTagCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool × Bool × Bool :=
  dispatchTagFrom (coordinatorPhaseCode rate code.2.1.1)
    (selectedStartCode rate code.2.2.1.1)

/-- Apply the actual code decoder to every dated entry, preserving dates and
entries whose numerical branch is absent. -/
def datedDispatchTags
    (omega : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate) :
    List (Fin p.T × (Bool × Bool × Bool)) :=
  omega.map fun entry => (entry.1, dispatchTagCode rate entry.2.1)

/-- The code decoder is Borel in the existing product/sum structure. Only its
finite branch tags and the existing countable clock result are inspected. -/
theorem dispatchTagCode_measurable :
    Measurable (dispatchTagCode rate) := by
  classical
  have hphase : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        coordinatorPhaseCode rate code.2.1.1) := by
    exact coordinatorPhaseCode_measurable rate |>.comp
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_id)))
  have hstart : Measurable (selectedStartCode rate) := by
    unfold selectedStartCode
    have h := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun pair : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
          Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
        pair.1.2.1)
      (measurable_fst.comp (measurable_snd.comp measurable_fst)) id measurable_id
    exact h
  have hselected : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        selectedStartCode rate code.2.2.1.1) := by
    exact hstart.comp
      (measurable_fst.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_id))))
  change Measurable (fun code :
    ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      dispatchTagFrom (coordinatorPhaseCode rate code.2.1.1)
        (selectedStartCode rate code.2.2.1.1))
  exact (dispatchTagFrom_measurable (p := p)).comp
    (hphase.prodMk hselected)

/-- The literal dated tag projection is Borel on the existing observation
space, retaining its original continuous and optional factors. -/
theorem measurable_datedDispatchTags :
    Measurable (datedDispatchTags rate) := by
  have hentry : Measurable
      (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (entry.1, dispatchTagCode rate entry.2.1)) := by
    exact measurable_fst.prodMk
      ((dispatchTagCode_measurable rate).comp
        (measurable_fst.comp measurable_snd))
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (fun omega : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate => omega)
    measurable_id _ hentry

private theorem dispatchLive_cutoff_command
    (input : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output input.registers
      input.ownedRegisters input.followerBaseScore)
    (hs ledger hi he hd hc hp hn selection)
    (h : CoordinatorRoundDispatch.dispatchLive input =
      .cutoffChosen out hs ledger hi he hd hc hp hn selection) :
    out.startResult.ledgerCommand =
      some (.initializeAt input.registers.time) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive at h
  dsimp only at h
  split at h
  · cases h
  · rename_i actual hactual
    have hstart := CoordinatorRoundDispatch.cutoffDispatch_startResult_eq
      input.registers input.ownedRegisters input.followerBaseScore actual hactual
    split at h
    · cases h
    · cases h
    · have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          input.registers actual.startResult := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hframe] at h
      have hpayload : input.registers.priorClock.sigma =
          some input.registers.payload.sigma := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hpayload] at h
      have hgrid : input.registers.gridBoundary = input.registers.priorClock.g := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hgrid] at h
      have hscore : input.registers.scoreDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hscore] at h
      have hqueue : input.ownedRegisters.queueDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hqueue] at h
      have hprevious : input.ownedRegisters.previousServiceDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hprevious] at h
      have hbase : ∀ i, input.followerBaseScore i ≤ p.T * D p := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hbase] at h
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hlive] at h
      have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time input.registers.complementWeights := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hchoice] at h
      have hboundary : actual.startResult.clock.g ≤ p.T + 1 := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hboundary] at h
      have henvelope : input.registers.complementEnvelopeValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left henvelope] at h
      split at h
      · rename_i ha
        exact (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          _ _ _ _ _ _ hchoice ha).elim
      · cases h
    · rename_i candidate hcandidate
      have hcommand := (CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
        input.registers input.ownedRegisters input.followerBaseScore actual candidate
        hactual hcandidate).1
      have hresults := Except.ok.inj (hstart.symm.trans hs)
      exact (congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand hresults).symm.trans
        hcommand

private theorem dispatchLive_continuing_startResult_eq
    (input : CoordinatorRoundDispatch.LiveInput p) :
    match CoordinatorRoundDispatch.dispatchLive input with
    | .continuingChosen dispatched _ continuation _ =>
        continuation.startRoundResult = dispatched.startResult
    | _ => True := by
  generalize hcomputed : CoordinatorRoundDispatch.dispatchLive input = outcome
  unfold CoordinatorRoundDispatch.dispatchLive at hcomputed
  repeat' first
    | (split at hcomputed)
    | (extract_lets at hcomputed)
    | (subst outcome; trivial)
  all_goals
    dsimp +zetaDelta only at hcomputed
    split at hcomputed
    · contradiction
    · subst outcome
      trivial

/-- On every original round record, the code decoder is exactly the three
literal constructor tests, including every unsuccessful dispatcher branch. -/
theorem dispatchTagCode_eq_record
    (record : ReferenceCompletePhysicalHistory.RoundRecord
      (p := p) (rate := rate)) :
    dispatchTagCode rate (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      (ReferenceFirstReplacementCollectionPendingFoundation.isCutoff record,
        ReferenceCollectionPhaseHistory.laterChosen record.input,
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen record) := by
  classical
  have hprep := ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq record
  have hfront := ReferenceActiveHorizonMeasurability.roundRecordCode_front record
  unfold ReferenceFirstReplacementCollectionPendingFoundation.isCutoff
    ReferenceCollectionPhaseHistory.laterChosen
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  rw [hprep]
  simp only [dispatchTagCode, selectedStartCode, dispatchTagFrom]
  -- The retained selector is the selector of the same original dispatch.
  rw [hfront.1]
  cases hcoord : record.input.state.coordinator with
  | first =>
      simp only [ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        coordinatorPhaseCode, hcoord, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchFirst
        (ReferenceActivePhysicalStep.firstInput record.input) <;> rfl
  | live registers owned base =>
      simp only [ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        coordinatorPhaseCode, hcoord, ReferenceActivePhysicalStep.prepare]
      have hcut : ReferenceActivePhysicalStep.dispatch record.input =
          .live registers owned base
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput record.input registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hcoord, CoordinatorRoundDispatch.dispatch]
        cases CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input registers owned base) <;> rfl
      rw [hcut]
      cases hd : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input registers owned base) with
      | clockFailure failure hdispatch =>
          simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      | initializerFailure dispatched hstart checked hchecked =>
          simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      | localFailure dispatched hstart reason =>
          simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hnone selected =>
          have hcommand := dispatchLive_cutoff_command
            (ReferenceActivePhysicalStep.liveInput record.input registers owned base)
            dispatched hstart ledger hinit hledger hdomains hclock hpending hnone selected hd
          simp [hcommand,
            ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt,
            ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      | continuingChosen dispatched hstart continuation selected =>
          have hcontinuation := dispatchLive_continuing_startResult_eq
            (ReferenceActivePhysicalStep.liveInput record.input registers owned base)
          rw [hd] at hcontinuation
          have hnone : dispatched.startResult.ledgerCommand = none := by
            rw [← hcontinuation]
            exact continuation.clockFrame.2.2.1
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt,
            ReferenceLiveDispatchOutputMeasurability.encodeSelection, hnone]
  | collection payload ledger saved =>
      simp only [ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        coordinatorPhaseCode, hcoord, ReferenceActivePhysicalStep.prepare]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
        let localInput := ReferenceActivePhysicalStep.collectionInput
          record.input payload ledger clock cutoff
        have hcut : ReferenceActivePhysicalStep.dispatch record.input =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection localInput) := by
          unfold ReferenceActivePhysicalStep.dispatch
          simp only [hcoord]
          split
          · simp only [CoordinatorRoundDispatch.dispatch]
            cases CoordinatorRoundDispatch.dispatchCollection localInput <;> rfl
          · rename_i hbad
            exact (hbad hc).elim
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchCollection localInput with
        | clockFailure failure hstart =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | localFailure started hstart hcore reason =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | coreFailure core started hstart reason =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | continuing core prepared boundary scores =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceLiveDispatchOutputMeasurability.encodeSelection, prepared.clockStarted_frame.2.2.2]
        | laterReconstructionFailure core consistent started hstart instruction hassignment reason hlater =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | laterPrefixFailure core consistent started hstart instruction hassignment arm reason hlater =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | laterOrientationFailure core consistent started hstart instruction hassignment set hlater =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | laterChoiceFailure core consistent started hstart instruction hassignment output hlocal data installed reason =>
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        | laterChosen core consistent started hstart instruction hassignment output hlocal data installed selected =>
            have heffect := CoordinatorPhaseClock.startRound_assignment_effect p
              localInput.etaReal localInput.time localInput.clock localInput.ledger.pending
              started instruction core.clock_parameter_valid core.clock_registers_valid
              core.clock_start_time_valid hstart hassignment
            have htime : instruction.time = record.input.time := by
              change instruction.time = localInput.time
              exact heffect.1
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt,
              ReferenceLiveDispatchOutputMeasurability.encodeSelection, htime,
              hassignment]
      · have hcut : ReferenceActivePhysicalStep.dispatch record.input =
            .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hcoord, hc]
        rw [hcut]
        simp [ReferenceActivePhysicalStep.DispatchCut.selection]
  | dagger =>
      simp [ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        coordinatorPhaseCode, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hcoord]

/-- The strict dated tag map agrees exactly with the same original suffix's
first `n - physicalStart` records. No numerical-cell success condition is
used. -/
theorem datedDispatchTags_datePrefix_eq_take
    (n : ℕ) (hn : n ≤ p.T) (source : SourceInput p) :
    datedDispatchTags rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source)) =
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).take
        (n - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)).map (fun record =>
            (record.input.time,
              (ReferenceFirstReplacementCollectionPendingFoundation.isCutoff record,
                ReferenceCollectionPhaseHistory.laterChosen record.input,
                ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen record))) := by
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h n hn]
  simp only [datedDispatchTags,
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar]
  rw [← List.map_take]
  rw [List.map_map]
  apply List.map_congr_left
  intro record hrecord
  exact congrArg (fun tags => (record.input.time, tags))
    (dispatchTagCode_eq_record rate record)

/-- The strict dated actual tag prefix factors through the accepted source
prefix, at every calendar index. -/
theorem datedDispatchTags_datePrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (source : SourceInput p) :
    datedDispatchTags rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source)) =
      datedDispatchTags rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source))) := by
  exact congrArg (datedDispatchTags rate)
    (ReferenceCompleteObservationPrefixInformation.datePrefix_factor
      rate rewards C_star C_h control0 n hn source)

/-- The actual strict dated tag prefix is measurable in the source-prefix
filtration at `n + 1`, by composing with the accepted numerical-prefix
measurability result. -/
theorem datedDispatchTags_datePrefix_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)]
      (fun source : SourceInput p => datedDispatchTags rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source))) := by
  exact measurable_datedDispatchTags rate |>.comp
    (ReferenceCompleteObservationPrefixInformation.datePrefix_measurable
      rate rewards C_star C_h control0 n hn)

end Bandits.Support.ReferenceCompleteDispatchTagPrefix

end
