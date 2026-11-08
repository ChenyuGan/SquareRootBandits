/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrdinaryCoordinatorLocalMeasurability

/-!
# Retained-data reconstruction of ordinary coordinator preparation

This module reconstructs the exact dependent preparation retained by the
ordinary coordinator's existing local code. It consumes the original
coordinator code, whole row, bank, time, and O's retained branch observation.
FIRST and COLLECTION pass the received observations to the accepted data
decoders; their image equalities supply only dependent proof certificates.
LIVE uses the accepted fixed-input lossless outcome decoder. Invalid cutoff
and dagger remain distinct constructors.

This is internal data reconstruction only. Global actual selection, arm and
DOWN-view measurability belong to the separate preparation-selection module.
The consumer is ordinary observer composition after independently accepted
selection/readout and collection-tail producers; no observer Borel or
manuscript closure is asserted here.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.OrdinaryCoordinatorPreparationReconstruction

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

abbrev LocalInput (p : Parameters) (rate : RateInput p) :=
  _root_.Bandits.Support.OrdinaryCoordinatorLocalMeasurability.LocalInput p rate

abbrev PreparationObservationCode (p : Parameters) (rate : RateInput p) :=
  _root_.Bandits.Support.OrdinaryCoordinatorLocalMeasurability.PreparationObservationCode p rate

open _root_.Bandits.Support.OrdinaryCoordinatorLocalMeasurability
open OrdinaryCoordinatorPhysicalInterface
open ReferenceFirstDispatchMeasurability
open ReferenceLiveDispatchMeasurability
open ReferenceLiveDispatchOutputMeasurability
open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionOutcomeMeasurability

/-- O's original input/observation product, used only with its exact image
equation. -/
abbrev ActualPreparationCode (p : Parameters) (rate : RateInput p) :=
  _root_.Bandits.Support.OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate

/-- The actual code image at one original root input. -/
def actualPreparationCode (z : LocalInput p rate) : ActualPreparationCode p rate :=
  OrdinaryCoordinatorLocalMeasurability.prepareLocalCode z

/-- Actual FIRST selection certificates transported to the installation
retained by the local first observation. -/
theorem firstActualSelectionFacts (d : FirstDomain p) :
    let installed := CoordinatorAssignmentRegisterInstall.installFirst
      (firstLaunchInputAt rate d)
    CoordinatorLocalArmChoice.ChoiceInputsValid installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        installed.startRoundResult.clock.u)
      installed.registers.time installed.registers.complementWeights ∧
    installed.startRoundResult.clock.g ≤ p.T + 1 ∧
    CoordinatorLocalArmChoice.coordinatorArmChoice installed.registers.payload
      installed.startRoundResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
      installed.registers.time installed.registers.complementWeights d.2 =
        some (firstOutcomeArmAt rate d) := by
  obtain ⟨actualInstall, actualSelection, hchosen⟩ :=
    firstOutcomeAt_chosen (rate := rate) d
  have hactualInstall := firstOutcomeAt_chosen_installation (rate := rate) d
    actualInstall actualSelection hchosen
  have harm : firstOutcomeArmAt rate d = actualSelection.arm := by
    change firstOutcomeArm (firstOutcomeAt rate d) = actualSelection.arm
    rw [hchosen]
    rfl
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate d)).registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        (CoordinatorAssignmentRegisterInstall.installFirst
          (firstLaunchInputAt rate d)).startRoundResult.clock.u)
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate d)).registers.time
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate d)).registers.complementWeights := by
    rw [← hactualInstall]
    exact actualSelection.choiceInputsValid
  have hboundary :
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate d)).startRoundResult.clock.g
        ≤ p.T + 1 := by
    rw [← hactualInstall]
    exact actualSelection.recorderBoundaryValid
  have hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate d)).registers.payload
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate d)).startRoundResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        (CoordinatorAssignmentRegisterInstall.installFirst
          (firstLaunchInputAt rate d)).startRoundResult.clock.u)
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate d)).registers.time
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate d)).registers.complementWeights d.2 =
        some (firstOutcomeArmAt rate d) := by
    rw [← hactualInstall, harm]
    exact actualSelection.armChoice_eq
  exact ⟨hvalid, hboundary, hchoice⟩

/-- Restore the original first outcome from its retained observation. Its
continuous installation data and arm are read from the observation; the
accepted actual-first reconstruction supplies only the dependent Prop
certificates. -/
noncomputable def decodeFirstOutcome
    (d : FirstDomain p) (o : FirstDispatchObservation p rate.eta)
    (ho : o = firstDispatchObservationAt rate d) :
    CoordinatorRoundDispatch.FirstOutcome (firstInputAt rate d) := by
  let decoded := decodeFirstDispatchObservation o
  let launch := firstLaunchInputAt rate d
  have hrestoration := restore_firstDispatchObservationAt (rate := rate) d
  have hstart : decoded.1.start = launch.start := by
    dsimp only [decoded]
    rw [ho]
    exact Classical.choose hrestoration
  have hclock : CoordinatorPhaseClock.startRound p rate.eta.val launch.sigma
      (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok decoded.1.startRoundResult := by
    dsimp only [decoded]
    rw [ho]
    exact Classical.choose (Classical.choose_spec hrestoration)
  let installed := decoded.1.restore launch hstart hclock
  have hdata : decoded.1 = FirstInstallationData.ofInstallation
      (CoordinatorAssignmentRegisterInstall.installFirst launch) := by
    dsimp only [decoded]
    rw [ho]
    exact congrArg Prod.fst (decode_firstDispatchObservationAt (rate := rate) d)
  have hdecodedInstall : installed =
      CoordinatorAssignmentRegisterInstall.installFirst launch :=
    FirstInstallationData.restore_eq_of_data decoded.1 _ hdata hstart hclock
  have harm : decoded.2 = some (firstOutcomeArmAt rate d) := by
    dsimp only [decoded]
    rw [ho]
    rw [decode_firstDispatchObservationAt (rate := rate) d]
  let observedArm := decoded.2.get (by rw [harm]; rfl)
  have hobservedArm : observedArm = firstOutcomeArmAt rate d := by
    simp only [observedArm, harm, Option.get_some]
  have hfacts := firstActualSelectionFacts (rate := rate) d
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
      installed.registers.time installed.registers.complementWeights := by
    rw [hdecodedInstall]
    exact hfacts.1
  have hboundary : installed.startRoundResult.clock.g ≤ p.T + 1 := by
    rw [hdecodedInstall]
    exact hfacts.2.1
  have hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice installed.registers.payload
      installed.startRoundResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
      installed.registers.time installed.registers.complementWeights d.2 = some observedArm := by
    rw [hdecodedInstall, hobservedArm]
    exact hfacts.2.2
  exact .chosen installed {
    arm := observedArm
    choiceInputsValid := hvalid
    recorderBoundaryValid := hboundary
    armChoice_eq := hchoice }

private theorem decodeFirstOutcome_eq_actual (d : FirstDomain p) :
    decodeFirstOutcome (rate := rate) d (firstDispatchObservationAt rate d) rfl =
      firstOutcomeAt rate d := by
  obtain ⟨actualInstall, actualSelection, hchosen⟩ :=
    firstOutcomeAt_chosen (rate := rate) d
  have hactualInstall := firstOutcomeAt_chosen_installation (rate := rate) d
    actualInstall actualSelection hchosen
  have harm : actualSelection.arm = firstOutcomeArmAt rate d := by
    change actualSelection.arm = firstOutcomeArm (firstOutcomeAt rate d)
    rw [hchosen]
    rfl
  rw [hchosen]
  unfold decodeFirstOutcome
  simp only
  have hrestoration := restore_firstDispatchObservationAt (rate := rate) d
  let hstart := Classical.choose hrestoration
  let hclock := Classical.choose (Classical.choose_spec hrestoration)
  have hdecodedInstall :
      (decodeFirstDispatchObservation (firstDispatchObservationAt rate d)).1.restore
          (firstLaunchInputAt rate d) hstart hclock =
        actualInstall := by
    have hdata := congrArg Prod.fst
      (decode_firstDispatchObservationAt (rate := rate) d)
    have hstart' := Classical.choose hrestoration
    have hclock' := Classical.choose (Classical.choose_spec hrestoration)
    rw [FirstInstallationData.restore_eq_of_data _ _ hdata hstart' hclock']
    exact hactualInstall.symm
  cases hdecodedInstall
  congr 1
  cases actualSelection with
  | mk arm hvalid hboundary hchoice =>
      have hselectionArm :
          (decodeFirstDispatchObservation (firstDispatchObservationAt rate d)).2.get
            (by simp [decode_firstDispatchObservationAt]) = arm := by
        simp [decode_firstDispatchObservationAt]
        exact harm.symm
      cases hselectionArm
      rfl

/-- Exact reconstruction of the same C.Preparation from O's actual emitted
preparation code. The image proof is what permits dependent cursor and outcome
proof fields to be transported without a fallback. -/
def decode_prepareLocalCode (z : LocalInput p rate)
    (observation : PreparationObservationCode p rate)
    (observation_eq : observation =
      OrdinaryCoordinatorLocalMeasurability.preparationObservation z) :
    OrdinaryCoordinatorPhysicalInterface.Preparation rate
      (OrdinaryCoordinatorLocalMeasurability.decoderBank z)
      (OrdinaryCoordinatorLocalMeasurability.completeRow z)
      (OrdinaryCoordinatorLocalMeasurability.calendarTime z) := by
  rcases z with ⟨code, bank, row, time⟩
  change OrdinaryCoordinatorPhysicalInterface.Preparation rate bank row time
  cases code with
  | inl _ =>
      have hactual : observation = .inl (firstDispatchObservationAt rate (time, row)) := by
        simpa [OrdinaryCoordinatorLocalMeasurability.preparationObservation,
          OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
          OrdinaryCoordinatorLocalMeasurability.firstDomainOf,
          OrdinaryCoordinatorLocalMeasurability.calendarTime,
          OrdinaryCoordinatorLocalMeasurability.completeRow] using observation_eq
      cases h : observation with
      | inl first =>
          have hfirst : first = firstDispatchObservationAt rate (time, row) :=
            Sum.inl.inj (h.symm.trans hactual)
          exact .first (decodeFirstOutcome (time, row) first hfirst)
      | inr rest =>
          have hfalse : False := by simp [h] at hactual
          exact False.elim hfalse
  | inr rest =>
      cases rest with
      | inl pair =>
          rcases pair with ⟨payload, live⟩
          let registers := ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live
          let owned := ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live
          let base := live.baseScores
          let sourceInput := liveInputOfCoordinates
            (OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf
              ((payload, live), (bank, (row, time))))
          have hactual : observation = .inr (.inl
              (outcomeData (CoordinatorRoundDispatch.dispatchLive sourceInput))) := by
            simpa [sourceInput, OrdinaryCoordinatorLocalMeasurability.preparationObservation,
              OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
              OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf,
              OrdinaryCoordinatorLocalMeasurability.decoderBank,
              OrdinaryCoordinatorLocalMeasurability.completeRow,
              OrdinaryCoordinatorLocalMeasurability.calendarTime] using observation_eq
          cases h : observation with
          | inl first =>
              have hfalse : False := by simp [h] at hactual
              exact False.elim hfalse
          | inr tail =>
              cases ht : tail with
              | inl data =>
                  have hdata : data = outcomeData (CoordinatorRoundDispatch.dispatchLive sourceInput) :=
                    Sum.inl.inj (ht.symm.trans (Sum.inr.inj (h.symm.trans hactual)))
                  let retained : StoredOutcome sourceInput :=
                    ⟨data, ⟨CoordinatorRoundDispatch.dispatchLive sourceInput, hdata.symm⟩⟩
                  let restored := decodeOutcome sourceInput retained
                  have hsource : sourceInput =
                      OrdinaryCoordinatorPhysicalInterface.liveInput row time registers owned base := rfl
                  cases hsource
                  exact .live registers owned base restored
              | inr impossible =>
                  have hfalse : False := by simp [h, ht] at hactual
                  exact False.elim hfalse
      | inr tail =>
          cases tail with
          | inl collection =>
              rcases collection with ⟨payload, ledger, proposal⟩
              let boundary : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
                ((payload, row), ledger, (proposal, (bank, time)))
              by_cases hcutoff : ReferenceCollectionDispatchMeasurability.cutoffValid boundary
              · have hactual : observation = .inr (.inr (.inl
                    (ReferenceCollectionOutcomeMeasurability.collectionFullObservation
                      (ReferenceCollectionDispatchMeasurability.boundaryLocal
                        ⟨boundary, hcutoff⟩)))) := by
                  simpa [OrdinaryCoordinatorLocalMeasurability.preparationObservation,
                    OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                    OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
                    OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
                    OrdinaryCoordinatorLocalMeasurability.decoderBank,
                    OrdinaryCoordinatorLocalMeasurability.completeRow,
                    OrdinaryCoordinatorLocalMeasurability.calendarTime,
                    ReferenceCollectionOutcomeMeasurability.boundaryFullObservation,
                    hcutoff, boundary] using observation_eq
                cases h : observation with
                | inl first =>
                    have hfalse : False := by simp [h] at hactual
                    exact False.elim hfalse
                | inr afterFirst =>
                    cases hfirst : afterFirst with
                    | inl liveData =>
                        have hfalse : False := by simp [h, hfirst] at hactual
                        exact False.elim hfalse
                    | inr afterLive =>
                        cases hsecond : afterLive with
                        | inl full =>
                            have hfull : full =
                                ReferenceCollectionOutcomeMeasurability.collectionFullObservation
                                  (ReferenceCollectionDispatchMeasurability.boundaryLocal
                                    ⟨boundary, hcutoff⟩) := by
                              simp only [h, hfirst, hsecond] at hactual
                              injection hactual with h₁
                              injection h₁ with h₂
                              injection h₂ with h₃
                            let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by
                              have hledger := hcutoff
                              change 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T at hledger
                              rcases hledger with ⟨hlo, hhi⟩
                              omega⟩
                            let clock := collectionClock payload ledger proposal cutoff
                            let collectionLocal :=
                              ReferenceCollectionDispatchMeasurability.boundaryLocal
                                ⟨boundary, hcutoff⟩
                            have hclock : full.1.1.1 =
                                ReferenceCollectionDispatchMeasurability.clockObservation
                                  collectionLocal := by
                              rw [hfull]
                              rfl
                            let decodedOption :=
                              ReferenceCollectionOutcomeMeasurability.decodeCollectionFullObservation
                                collectionLocal full hclock
                            have hdecodedOption : decodedOption = some
                                (CoordinatorRoundDispatch.dispatchCollection
                                  (ReferenceCollectionDispatchMeasurability.assemble collectionLocal)) := by
                              dsimp only [decodedOption]
                              simpa only [hfull] using
                                ReferenceCollectionOutcomeMeasurability.decode_collectionFullObservation_exact
                                  collectionLocal
                            let decodedOutcome := decodedOption.get (by rw [hdecodedOption]; rfl)
                            have hinput :
                                ReferenceCollectionDispatchMeasurability.assemble collectionLocal =
                                  OrdinaryCoordinatorPhysicalInterface.collectionInput
                                    bank row time payload ledger clock cutoff := rfl
                            exact .collection payload ledger clock cutoff
                              (hinput ▸ decodedOutcome)
                        | inr other =>
                            have hfalse : False := by simp [h, hfirst, hsecond] at hactual
                            exact False.elim hfalse
              · exact .invalidCollectionCutoff
          | inr dagger => exact .dagger

/-- Exact equality to the literal C.prepareLocal cut on every original O
input, with no operational success or normalization hypothesis. -/
theorem decode_prepareLocalCode_exact (z : LocalInput p rate) :
    decode_prepareLocalCode z (actualPreparationCode z).2 rfl =
      OrdinaryCoordinatorLocalMeasurability.cut z := by
  rcases z with ⟨code, bank, row, time⟩
  cases code with
  | inl _ =>
      simp [decode_prepareLocalCode, actualPreparationCode,
        OrdinaryCoordinatorLocalMeasurability.preparationObservation,
        OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
        OrdinaryCoordinatorLocalMeasurability.firstDomainOf,
        OrdinaryCoordinatorLocalMeasurability.decoderBank,
        OrdinaryCoordinatorLocalMeasurability.completeRow,
        OrdinaryCoordinatorLocalMeasurability.calendarTime,
        OrdinaryCoordinatorLocalMeasurability.cut,
        OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
        ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
        OrdinaryCoordinatorPhysicalInterface.prepareLocal_first,
        ReferenceFirstDispatchMeasurability.firstOutcomeAt,
        ReferenceFirstDispatchMeasurability.firstInputAt,
        OrdinaryCoordinatorPhysicalInterface.firstInput,
        decodeFirstOutcome_eq_actual]
  | inr rest =>
      cases rest with
      | inl pair =>
          rcases pair with ⟨payload, live⟩
          simp [decode_prepareLocalCode, actualPreparationCode,
            OrdinaryCoordinatorLocalMeasurability.preparationObservation,
            OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
            OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf,
            OrdinaryCoordinatorLocalMeasurability.decoderBank,
            OrdinaryCoordinatorLocalMeasurability.completeRow,
            OrdinaryCoordinatorLocalMeasurability.calendarTime,
            OrdinaryCoordinatorLocalMeasurability.cut,
            OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
            ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
            ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
            ReferenceActivePhysicalStepMeasurability.decodeLiveOwned,
            ReferenceLiveDispatchMeasurability.liveInputOfCoordinates,
            ReferenceLiveDispatchOutputMeasurability.decodeOutcome_outcomeData,
            OrdinaryCoordinatorPhysicalInterface.liveInput,
            OrdinaryCoordinatorPhysicalInterface.prepareLocal_live]
      | inr tail =>
          cases tail with
          | inl collection =>
              rcases collection with ⟨payload, ledger, proposal⟩
              let boundary : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
                ((payload, row), ledger, (proposal, (bank, time)))
              by_cases hcut : ReferenceCollectionDispatchMeasurability.cutoffValid boundary
              · have hgood : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
                  change 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T at hcut
                  exact hcut
                have htag : OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary
                    (ReferenceCollectionOutcomeMeasurability.boundaryFullObservation boundary) =
                    .inr (.inr (.inl
                      (ReferenceCollectionOutcomeMeasurability.collectionFullObservation
                        (ReferenceCollectionDispatchMeasurability.boundaryLocal
                          ⟨boundary, hcut⟩)))) := by
                  simp [OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
                    ReferenceCollectionOutcomeMeasurability.boundaryFullObservation, hcut]
                let input : LocalInput p rate :=
                  (Sum.inr (Sum.inr (Sum.inl (payload, ledger, proposal))), (bank, (row, time)))
                let retained : PreparationObservationCode p rate :=
                  .inr (.inr (.inl
                    (ReferenceCollectionOutcomeMeasurability.collectionFullObservation
                      (ReferenceCollectionDispatchMeasurability.boundaryLocal
                        ⟨boundary, hcut⟩))))
                have hobs : OrdinaryCoordinatorLocalMeasurability.preparationObservation input =
                    retained := by
                  simpa [OrdinaryCoordinatorLocalMeasurability.preparationObservation,
                    OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                    OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
                    OrdinaryCoordinatorLocalMeasurability.decoderBank,
                    OrdinaryCoordinatorLocalMeasurability.completeRow,
                    OrdinaryCoordinatorLocalMeasurability.calendarTime, boundary] using htag
                change decode_prepareLocalCode input
                    (OrdinaryCoordinatorLocalMeasurability.preparationObservation input) rfl =
                  OrdinaryCoordinatorLocalMeasurability.cut input
                have hdecode : decode_prepareLocalCode input
                    (OrdinaryCoordinatorLocalMeasurability.preparationObservation input) rfl =
                    decode_prepareLocalCode input retained hobs.symm := by
                  generalize hretained : retained = retained' at hobs ⊢
                  cases hobs
                  rfl
                rw [hdecode]
                simp [decode_prepareLocalCode,
                  OrdinaryCoordinatorLocalMeasurability.cut,
                  OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
                  OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                  ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
                  ReferenceCollectionOutcomeMeasurability.decode_collectionFullObservation_exact,
                  ReferenceCollectionDispatchMeasurability.assemble,
                  ReferenceCollectionDispatchMeasurability.boundaryLocal,
                  OrdinaryCoordinatorPhysicalInterface.collectionInput,
                  OrdinaryCoordinatorPhysicalInterface.prepareLocal_collection,
                  OrdinaryCoordinatorLocalMeasurability.decoderBank,
                  OrdinaryCoordinatorLocalMeasurability.completeRow,
                  OrdinaryCoordinatorLocalMeasurability.calendarTime,
                  boundary, input, retained, hcut, hgood]
              · have hbad : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) := by
                  intro h
                  apply hcut
                  change 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
                  exact h
                have htag : OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary
                    (ReferenceCollectionOutcomeMeasurability.boundaryFullObservation boundary) =
                    .inr (.inr (.inr (.inl ()))) := by
                  simp [OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
                  ReferenceCollectionOutcomeMeasurability.boundaryFullObservation,
                  ReferenceCollectionDispatchMeasurability.cutoffValid,
                  boundary, hbad]
                let input : LocalInput p rate :=
                  (Sum.inr (Sum.inr (Sum.inl (payload, ledger, proposal))), (bank, (row, time)))
                let retained : PreparationObservationCode p rate :=
                  .inr (.inr (.inr (.inl ())))
                have hobs : OrdinaryCoordinatorLocalMeasurability.preparationObservation input =
                    retained := by
                  simpa [OrdinaryCoordinatorLocalMeasurability.preparationObservation,
                    OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                    OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
                    OrdinaryCoordinatorLocalMeasurability.decoderBank,
                    OrdinaryCoordinatorLocalMeasurability.completeRow,
                    OrdinaryCoordinatorLocalMeasurability.calendarTime, boundary] using htag
                change decode_prepareLocalCode input
                    (OrdinaryCoordinatorLocalMeasurability.preparationObservation input) rfl =
                  OrdinaryCoordinatorLocalMeasurability.cut input
                have hdecode : decode_prepareLocalCode input
                    (OrdinaryCoordinatorLocalMeasurability.preparationObservation input) rfl =
                    decode_prepareLocalCode input retained hobs.symm := by
                  generalize hretained : retained = retained' at hobs ⊢
                  cases hobs
                  rfl
                rw [hdecode]
                simp [decode_prepareLocalCode,
                  OrdinaryCoordinatorLocalMeasurability.cut,
                  OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
                  OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                  OrdinaryCoordinatorLocalMeasurability.decoderBank,
                  OrdinaryCoordinatorLocalMeasurability.completeRow,
                  OrdinaryCoordinatorLocalMeasurability.calendarTime,
                  ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
                  OrdinaryCoordinatorPhysicalInterface.prepareLocal_invalidCollectionCutoff,
                  input, boundary, hcut, hbad]
          | inr _ =>
              simp [decode_prepareLocalCode,
                OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                OrdinaryCoordinatorLocalMeasurability.decoderBank,
                OrdinaryCoordinatorLocalMeasurability.completeRow,
                OrdinaryCoordinatorLocalMeasurability.calendarTime,
                OrdinaryCoordinatorLocalMeasurability.cut,
                OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
                ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
                OrdinaryCoordinatorPhysicalInterface.prepareLocal_dagger]

/-- Reconstruction on an encoded actual configuration, with the same bank,
whole row and actual time. The admitted storage decoder is a left inverse;
no current-payload, clock-alignment or success premise is needed. -/
theorem decode_prepareLocalCode_encodeCoordinator
    (q : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate)
    (bank : _root_.Bandits.Support.OrdinaryCoordinatorLocalMeasurability.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    let z : LocalInput p rate :=
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator q, (bank, (row, time)))
    decode_prepareLocalCode z (actualPreparationCode z).2 rfl =
      OrdinaryCoordinatorPhysicalInterface.prepareLocal q bank row time := by
  dsimp only
  rw [decode_prepareLocalCode_exact]
  change OrdinaryCoordinatorPhysicalInterface.prepareLocal
      (OrdinaryCoordinatorLocalMeasurability.decodedCoordinator
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator q,
          (bank, (row, time)))) bank row time =
    OrdinaryCoordinatorPhysicalInterface.prepareLocal q bank row time
  rw [OrdinaryCoordinatorLocalMeasurability.decodedCoordinator_encodeCoordinator]

end Bandits.Support.OrdinaryCoordinatorPreparationReconstruction
end
