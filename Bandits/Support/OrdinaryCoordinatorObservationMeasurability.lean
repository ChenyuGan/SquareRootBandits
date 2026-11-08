/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrdinaryCoordinatorPreparationSelectionMeasurability
public import Bandits.Support.OrdinaryCoordinatorPreparationReconstruction
public import Bandits.Support.OrdinaryCollectionObservationMeasurability

/-!
# The ordinary coordinator's own-feedback observation code

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

The original coordinator storage, bank, whole continuous row, time and own grid
feedback are the inputs. Retained preparation observations supply branch data;
the accepted selection producer supplies the actual view, start and arm. The
live and ordinary collection tails keep every failure and returned bank.
This is internal Borel composition, not a history, law or regret assertion.
The named next consumer is `ActualPostlaunchStepMeasurability`, together with
`ActualPostlaunchFollowerMeasurability` for heterogeneous player feedback.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.OrdinaryCoordinatorObservationMeasurability

abbrev Parameters := OrdinaryCoordinatorLocalMeasurability.Parameters
abbrev RateInput := OrdinaryCoordinatorLocalMeasurability.RateInput
abbrev LocalInput (p : Parameters) (rate : RateInput p) := OrdinaryCoordinatorLocalMeasurability.LocalInput p rate

variable {p : Parameters} {rate : RateInput p}

local instance failureMeasurableSpace :
    MeasurableSpace ReferenceActivePhysicalStep.CoordinatorFailure := ⊤
local instance clockMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.ClockRegisters p) := ⊤
local instance startMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance optionalCutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

local instance followerSetMeasurableSpace :
    MeasurableSpace (Finset (ActiveRoundActions.Follower p.m)) := ⊤
local instance firstTagMeasurableSpace :
    MeasurableSpace ReferenceFirstDispatchMeasurability.FirstOutcomeTag := ⊤
local instance slowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤
local instance collectionClockObservationMeasurableSpace :
    MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤
local instance collectionClockObservationDiscrete :
    DiscreteMeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
  ⟨fun _ => trivial⟩
local instance collectionInstructionMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤
local instance collectionInstructionDiscrete :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  ⟨fun _ => trivial⟩
local instance retainedFullOutputMeasurableSpace : MeasurableSpace
    (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) := inferInstance
local instance retainedPrefixMeasurableSpace : MeasurableSpace
    (ReferenceCollectionDispatchMeasurability.CollectionPrefixObservation p rate) := inferInstance
local instance retainedInstalledMeasurableSpace : MeasurableSpace
    (ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate) := inferInstance
local instance retainedFullMeasurableSpace : MeasurableSpace
    (ReferenceCollectionOutcomeMeasurability.FullObservation p rate) := inferInstance
local instance retainedObservationMeasurableSpace :
    MeasurableSpace (OrdinaryCoordinatorLocalMeasurability.PreparationObservationCode p rate) :=
  inferInstance
local instance selectionMeasurableSpace : MeasurableSpace
    (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate) := inferInstance
local instance installationMeasurableSpace : MeasurableSpace
    (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate) := inferInstance
local instance observationCodeMeasurableSpace : MeasurableSpace
    (ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) := inferInstance
local instance firstObservationMeasurableSpace : MeasurableSpace
    (ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta) := inferInstance
local instance localInputMeasurableSpace : MeasurableSpace (LocalInput p rate) := inferInstance

/-- Convert the existing live whole code to the existing collection code.
Only the original recorder decoder is applied; UP is absent in a live tail. -/
def liveCollectionCode (code : ReferenceLiveServiceTailMeasurability.LiveServiceTailWholeCode p rate) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  ReferenceFirstLiveCoordinatorStepMeasurability.liftLiveCode code

theorem measurable_liveCollectionCode :
    Measurable (liveCollectionCode (p := p) (rate := rate)) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.fst.prodMk
      (((measurable_of_countable CoordinatorRecordingMeasurability.decodeResult).comp
        measurable_snd.snd.snd).prodMk measurable_const)))

private theorem liveCollectionCode_eq (z : ReferenceActiveLiveTailMeasurability.LivePostChoiceCoordinates p rate) :
    liveCollectionCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode z) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z) := by
  have hup := ReferenceLiveServiceTailMeasurability.liveServiceTailObservation_up_none
    (ReferenceActiveLiveTailMeasurability.liveServiceTailCoordinates z)
  change (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
    (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).configuration,
    (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).upDecoderBank,
    (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).failure,
    CoordinatorRecordingMeasurability.decodeResult
      (CoordinatorRecordingMeasurability.encodeResult
        (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).recording), none) = _
  rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
  unfold ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
  change (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).up = none at hup
  rw [hup]
  rfl

private theorem decodeLiveRuntime_encodeLive
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    ReferenceLiveServiceTailMeasurability.decodeLiveRuntime r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) =
      (⟨r, (owned, base)⟩ : ReferenceLiveServiceTailMeasurability.LiveRuntime (p := p) (rate := rate)) := by
  let parts : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate →
      Option (ReferenceLiveServiceTailMeasurability.LiveRuntime (p := p) (rate := rate)) :=
    fun configuration => match configuration with
    | .live registers queues scores => some ⟨registers, (queues, scores)⟩
    | _ => none
  have h := congrArg parts
    (ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator
      (ReferenceActivePhysicalStep.CoordinatorConfiguration.live r owned base))
  apply Option.some.inj
  simpa only [parts, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
    ReferenceLiveServiceTailMeasurability.decodeLiveRuntime] using h

/-- The unrestricted live tail at literal local coordinates equals C's tail.
The start result is supplied data and is never recomputed. -/
theorem liveCollectionCode_eq_livePostChoice
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (arm : Fin p.K) (Y : Fin (D p + 1))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    liveCollectionCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
      (r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base, started, bank, time, row, arm, Y)) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.livePostChoice bank row time arm Y r owned base started) := by
  rw [liveCollectionCode_eq]
  apply congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
  have hinput : ReferenceLiveRecorderJointMeasurability.recordingInput
      (r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base, started, time, row, arm, Y) =
      OrdinaryCoordinatorPhysicalInterface.liveRecordingInput row time arm Y r started := by
    unfold ReferenceLiveRecorderJointMeasurability.recordingInput
      ReferenceLiveRecorderJointMeasurability.recorderRegisters
    dsimp only [ReferenceLiveRecorderJointMeasurability.recorderPayload,
      ReferenceLiveRecorderJointMeasurability.recorderLiveCode,
      ReferenceLiveRecorderJointMeasurability.recorderTime,
      ReferenceLiveRecorderJointMeasurability.recorderStarted,
      ReferenceLiveRecorderJointMeasurability.recorderRow,
      ReferenceLiveRecorderJointMeasurability.recorderOwnArm,
      ReferenceLiveRecorderJointMeasurability.recorderObservation]
    rw [ReferenceLiveRecorderJointMeasurability.complementWeights_decodeLive_encodeLive]
    rfl
  change ReferenceLiveServiceTailMeasurability.liveServiceTailFromRuntime
    (ReferenceLiveServiceTailMeasurability.decodeLiveRuntime r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base)) bank started time row Y
    (ReferenceLiveRecorderJointMeasurability.runCode
      (r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base, started, time, row, arm, Y)) = _
  rw [decodeLiveRuntime_encodeLive]
  unfold ReferenceLiveServiceTailMeasurability.liveServiceTailFromRuntime
  rw [ReferenceLiveRecorderJointMeasurability.decodeResult_runCode, hinput]
  rfl

/-- Restriction of the accepted full real weight vector recovers every actual
dependent weight. Values outside this complement are never consumed. -/
theorem choiceTimeViewWeightVector_apply
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (a : CanonicalFastSampling.FastArm view.payload.slowSet) :
    ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector view a.val =
      view.complementWeights a := by
  simp only [ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector,
    dite_eq_left a.property]

private theorem measurable_viewPayload : Measurable
    (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload) :=
  (comap_measurable ReferenceDownReceptionMeasurability.choiceTimeViewObservation).fst

/-- The collection tail consumes the same view's full continuous weight vector;
the complement extension obligation is proved here rather than assumed. -/
def collectionCodeAtView (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (Y : Fin (D p + 1)) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (selected : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate) :
      ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  OrdinaryCollectionObservationMeasurability.collectionObservationCodeAtComponents
    bank row time selected.2.2 Y selected.1.payload ledger selected.2.1
    (ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector selected.1)

theorem collectionCodeAtView_eq (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (Y : Fin (D p + 1)) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (selected : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate) :
    collectionCodeAtView bank row time Y ledger selected =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.collectionPostChoice bank row time selected.2.2 Y
        selected.1.payload ledger selected.2.1 selected.1.complementWeights) :=
  OrdinaryCollectionObservationMeasurability.collectionObservationCodeAtComponents_eq_of_complement_extension
    bank row time selected.2.2 Y selected.1.payload ledger selected.2.1
    (ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector selected.1)
    selected.1.complementWeights (choiceTimeViewWeightVector_apply selected.1)

private theorem measurable_sumRead {X A B Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (a : X → A ⊕ B) (ha : Measurable a) :
    Measurable (fun x => Sum.elim (fun v => f (v, x)) (fun v => g (v, x)) (a x)) := by
  have h := (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  convert h.comp (ha.prodMk measurable_id) using 1
  funext x
  change Sum.elim _ _ (a x) = Sum.elim f g ((Equiv.sumProdDistrib A B X) (a x, x))
  cases a x <;> rfl

private theorem measurable_optionRead {X A Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Y]
    (fallback : X → Y) (f : A × X → Y) (hb : Measurable fallback) (hf : Measurable f)
    (a : X → Option A) (ha : Measurable a) :
    Measurable (fun x => ReferenceCollectionOutcomeMeasurability.optionalElim (fallback x) (fun v => f (v, x)) (a x)) :=
      by
  have h := measurable_sumRead f (fun z : PUnit × X => fallback z.2)
    hf (hb.comp measurable_snd) (fun x => (Equiv.optionEquivSumPUnit A) (a x))
    ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ha)
  convert h using 1
  funext x
  cases a x <;> rfl

/-- Literal original local input together with its own grid observation. -/
abbrev ObservationInput (p : Parameters) (rate : RateInput p) :=
  LocalInput p rate × Fin (D p + 1)

local instance observationInputMeasurableSpace :
    MeasurableSpace (ObservationInput p rate) := inferInstance
local instance selectedInputMeasurableSpace : MeasurableSpace
    (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate ×
      ObservationInput p rate) := inferInstance

private def rejectedCode (x : ObservationInput p rate) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode
  p rate :=
  ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (ReferenceActivePhysicalStep.coordinatorFailure x.1.2.1 .dispatchRejected none none)

private theorem measurable_rejectedCode : Measurable (rejectedCode (p := p) (rate := rate)) :=
  measurable_const.prodMk (measurable_fst.snd.fst.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const)))

/-- Retained FIRST installation coordinates. This reads the observed scores,
queues, last services and base scores, without calling any operation. -/
def firstInstallationCode (o : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta) :
    ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate :=
  (o.registers.payload, {
    clockSigma := o.registers.priorClock.sigma
    clockCutoff := o.registers.priorClock.u
    clockBoundary := o.registers.priorClock.g
    clockProposal := o.registers.priorClock.lastProposal
    pending := o.registers.pendingAtChoice
    time := o.registers.time
    gridBoundary := o.registers.gridBoundary
    scores := (ReferenceFirstDispatchMeasurability.firstRegisterObservationCode o.registers).2.2.2.2.2
    queues := o.queue
    previousServices := o.previousService
    baseScores := o.followerBaseScore })

private theorem measurable_firstInstallationCode : Measurable
    (firstInstallationCode (p := p) (rate := rate)) := by
  have ho : Measurable (ReferenceFirstDispatchMeasurability.firstDispatchObservationCode (p := p) (eta := rate.eta)) :=
    comap_measurable _
  have hr := (comap_measurable (ReferenceFirstDispatchMeasurability.firstRegisterObservationCode (p := p) (eta :=
    rate.eta))).comp
    ho.snd.snd.snd.fst
  have hd := hr.snd.prodMk (ho.snd.snd.snd.snd.fst.prodMk
    (ho.snd.snd.snd.snd.snd.fst.prodMk ho.snd.snd.snd.snd.snd.snd.fst))
  exact hr.fst.prodMk ((measurable_of_countable (fun c :
      (CoordinatorPhaseClock.ClockRegisters p × (Finset (ActiveRoundActions.Follower p.m) ×
        (Fin p.T × (ℕ × (Fin p.K → ℕ))))) ×
          ((Fin p.K → ℕ) × ((Fin p.K → ℕ) × (Fin (p.m - 1) → ℕ))) =>
    ({ clockSigma := c.1.1.sigma
       clockCutoff := c.1.1.u
       clockBoundary := c.1.1.g
       clockProposal := c.1.1.lastProposal
       pending := c.1.2.1
       time := c.1.2.2.1
       gridBoundary := c.1.2.2.2.1
       scores := c.1.2.2.2.2
       queues := c.2.1
       previousServices := c.2.2.1
       baseScores := c.2.2.2 } : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p))).comp hd)

private def liveCodeAtInstallation (installation : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates
  p rate)
    (selected : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate) (x : ObservationInput p rate)
      :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  liveCollectionCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
    (installation.1, installation.2, selected.2.1, x.1.2.1,
      x.1.2.2.2, x.1.2.2.1, selected.2.2, x.2))

private theorem measurable_liveAt_comp {Ω : Type*} [MeasurableSpace Ω]
    (installation : Ω → ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate)
    (selected : Ω → OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate)
    (input : Ω → ObservationInput p rate)
    (hi : Measurable installation) (hs : Measurable selected) (hx : Measurable input) :
    Measurable (fun ω => liveCodeAtInstallation (installation ω) (selected ω) (input ω)) := by
  unfold liveCodeAtInstallation
  exact (measurable_liveCollectionCode (p := p) (rate := rate)).comp
    (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp
      (fun ω => (installation ω).1) (fun ω => (installation ω).2)
      (fun ω => (selected ω).2.1) (fun ω => (input ω).1.2.1)
      (fun ω => (input ω).1.2.2.2) (fun ω => (input ω).1.2.2.1)
      (fun ω => (selected ω).2.2) (fun ω => (input ω).2)
      hi.fst hi.snd hs.snd.fst hx.fst.snd.fst hx.fst.snd.snd.snd
      hx.fst.snd.snd.fst hs.snd.snd hx.snd)

private theorem measurable_collectionAt_comp {Ω : Type*} [MeasurableSpace Ω]
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (selected : Ω → OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate)
    (input : Ω → ObservationInput p rate)
    (hl : Measurable ledger) (hs : Measurable selected) (hx : Measurable input) :
    Measurable (fun ω => collectionCodeAtView (input ω).1.2.1 (input ω).1.2.2.1
      (input ω).1.2.2.2 (input ω).2 (ledger ω) (selected ω)) := by
  have h := OrdinaryCollectionObservationMeasurability.measurable_collectionObservationCodeAtComponents_comp
    (fun ω => (input ω).1.2.1) (fun ω => (input ω).1.2.2.1)
    (fun ω => (input ω).1.2.2.2) (fun ω => (selected ω).2.2) (fun ω => (input ω).2)
    (fun ω => (selected ω).1.payload) ledger (fun ω => (selected ω).2.1)
    (fun ω => ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector (selected ω).1)
    hx.fst.snd.fst hx.fst.snd.snd.fst hx.fst.snd.snd.snd hs.snd.snd hx.snd
    (measurable_viewPayload.comp hs.fst) hl hs.snd.fst
    (ReferenceActiveStepCompositionMeasurability.measurable_viewWeights.comp hs.fst)
  convert h using 1
  funext ω
  exact OrdinaryCollectionObservationMeasurability.collectionObservationCodeAtComponents_eq_collectionPostChoice
    _ _ _ _ _ _ _ _ _

private def firstSelectedCode (o : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta)
    (rest : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate) :
      ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  liveCodeAtInstallation (firstInstallationCode o) rest.1 rest.2

private theorem measurable_firstSelectedCode : Measurable
    (fun pair : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate) =>
        firstSelectedCode pair.1 pair.2) := by
  let X := ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta ×
    (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate)
  have ho : Measurable (fun pair : X => pair.1) := measurable_fst
  have hi : Measurable (fun pair : X => firstInstallationCode pair.1) :=
    (measurable_firstInstallationCode (p := p) (rate := rate)).comp ho
  unfold firstSelectedCode liveCodeAtInstallation
  exact (measurable_liveCollectionCode (p := p) (rate := rate)).comp
    (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp
      (fun pair : X => (firstInstallationCode pair.1).1)
      (fun pair => (firstInstallationCode pair.1).2)
      (fun pair => pair.2.1.2.1) (fun pair => pair.2.2.1.2.1)
      (fun pair => pair.2.2.1.2.2.2) (fun pair => pair.2.2.1.2.2.1)
      (fun pair => pair.2.1.2.2) (fun pair => pair.2.2.2)
      hi.fst hi.snd (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop))

private theorem measurable_reindexedLiveCode : Measurable
    (fun pair : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate) =>
      liveCodeAtInstallation (pair.1.1, { pair.1.2 with time := pair.2.2.1.2.2.2 })
        pair.2.1 pair.2.2) := by
  let X := ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
    (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate)
  have hcoords : Measurable (fun pair : X => (pair.1.2, pair.2.2.1.2.2.2)) :=
    measurable_fst.snd.prodMk measurable_snd.snd.fst.snd.snd.snd
  have hcode : Measurable (fun pair : X =>
      ({ pair.1.2 with time := pair.2.2.1.2.2.2 } : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)) :=
    (measurable_of_countable (fun pair : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p × Fin p.T =>
      { pair.1 with time := pair.2 })).comp hcoords
  unfold liveCodeAtInstallation
  exact (measurable_liveCollectionCode (p := p) (rate := rate)).comp
    (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp
      (fun pair : X => pair.1.1)
      (fun pair => { pair.1.2 with time := pair.2.2.1.2.2.2 })
      (fun pair => pair.2.1.2.1) (fun pair => pair.2.2.1.2.1)
      (fun pair => pair.2.2.1.2.2.2) (fun pair => pair.2.2.1.2.2.1)
      (fun pair => pair.2.1.2.2) (fun pair => pair.2.2.2)
      (by fun_prop) hcode (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop))

private def liveSelectedCode (live : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate)
    (outcome : ReferenceLiveDispatchOutputMeasurability.OutcomeData p) (rest :
      OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  match outcome with
  | .continuingChosen _ _ _ =>
      liveCodeAtInstallation (live.1, { live.2 with time := rest.2.1.2.2.2 }) rest.1 rest.2
  | .cutoffChosen _ ledger _ =>
      collectionCodeAtView rest.2.1.2.1 rest.2.1.2.2.1 rest.2.1.2.2.2 rest.2.2
        (ReferenceFirstLiveCoordinatorStepMeasurability.ledgerOfData ledger) rest.1
  | _ => rejectedCode rest.2

private theorem measurable_liveSelectedCode : Measurable
    (fun pair : ReferenceLiveDispatchOutputMeasurability.OutcomeData p ×
      (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate)) =>
        liveSelectedCode pair.2.1 pair.1 pair.2.2) := by
  unfold liveSelectedCode
  apply measurable_from_prod_countable_right
  intro outcome
  cases outcome with
  | continuingChosen dispatched continuation arm => exact measurable_reindexedLiveCode
  | cutoffChosen dispatched ledger arm =>
      exact measurable_collectionAt_comp (p := p) (rate := rate)
        (Ω := ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
          (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate))
        (fun _ => ReferenceFirstLiveCoordinatorStepMeasurability.ledgerOfData (rate := rate) ledger)
        (fun pair => pair.2.1) (fun pair => pair.2.2)
        measurable_const measurable_snd.fst measurable_snd.snd
  | clockFailure reason => exact (measurable_rejectedCode (p := p) (rate := rate)).comp (by fun_prop)
  | initializerFailure dispatched checked => exact (measurable_rejectedCode (p := p) (rate := rate)).comp (by fun_prop)
  | localFailure dispatched reason => exact (measurable_rejectedCode (p := p) (rate := rate)).comp (by fun_prop)

private def collectionSelectedCode (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (obs : ReferenceCollectionOutcomeMeasurability.FullObservation p rate) (rest :
      OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  if obs.2.2.1 = .continuing then
    collectionCodeAtView rest.2.1.2.1 rest.2.1.2.2.1 rest.2.1.2.2.2 rest.2.2 ledger rest.1
  else if obs.2.2.1 = .laterChosen then
    ReferenceCollectionOutcomeMeasurability.optionalElim (rejectedCode rest.2)
      (fun installed => liveCodeAtInstallation installed.1 rest.1 rest.2) obs.2.1
  else rejectedCode rest.2

private theorem measurable_collectionLaterSelectedCode : Measurable (fun pair :
  ReferenceCollectionOutcomeMeasurability.FullObservation p rate ×
      (ReferenceActivePhysicalStep.Ledger rate × (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p
        rate × ObservationInput p rate)) =>
        ReferenceCollectionOutcomeMeasurability.optionalElim (rejectedCode pair.2.2.2)
          (fun installed => liveCodeAtInstallation installed.1 pair.2.2.1 pair.2.2.2) pair.1.2.1) := by
  let X := ReferenceCollectionOutcomeMeasurability.FullObservation p rate ×
    (ReferenceActivePhysicalStep.Ledger rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate))
  have hb : Measurable (fun pair : X => rejectedCode pair.2.2.2) :=
    (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd.snd
  have hf : Measurable (fun pair :
      ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate × X =>
        liveCodeAtInstallation pair.1.1 pair.2.2.2.1 pair.2.2.2.2) := by
    exact measurable_liveAt_comp (p := p) (rate := rate)
      (Ω := ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate × X)
      (fun pair => pair.1.1) (fun pair => pair.2.2.2.1) (fun pair => pair.2.2.2.2)
      measurable_fst.fst measurable_snd.snd.snd.fst measurable_snd.snd.snd.snd
  exact measurable_optionRead (fun pair : X => rejectedCode pair.2.2.2)
    (fun pair : ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate × X =>
      liveCodeAtInstallation pair.1.1 pair.2.2.2.1 pair.2.2.2.2)
    hb hf (fun pair : X => pair.1.2.1) measurable_fst.snd.fst

private theorem measurable_collectionSelectedCode : Measurable
    (fun pair : ReferenceCollectionOutcomeMeasurability.FullObservation p rate × (ReferenceActivePhysicalStep.Ledger
      rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate)) =>
        collectionSelectedCode pair.2.1 pair.1 pair.2.2) := by
  classical
  let X := ReferenceCollectionOutcomeMeasurability.FullObservation p rate ×
    (ReferenceActivePhysicalStep.Ledger rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate))
  unfold collectionSelectedCode
  exact Measurable.ite
    (measurableSet_eq_fun measurable_fst.snd.snd.fst measurable_const)
    (measurable_collectionAt_comp (p := p) (rate := rate) (Ω := X)
      (fun pair => pair.2.1)
      (fun pair => pair.2.2.1) (fun pair => pair.2.2.2)
      measurable_snd.fst measurable_snd.snd.fst measurable_snd.snd.snd)
    (Measurable.ite
      (measurableSet_eq_fun measurable_fst.snd.snd.fst measurable_const)
      (measurable_collectionLaterSelectedCode (p := p) (rate := rate)) ((measurable_rejectedCode (p := p) (rate :=
        rate)).comp measurable_snd.snd.snd))

private theorem measurable_sumReadAt {Z X A B Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (a : Z → A ⊕ B) (ha : Measurable a) (x : Z → X) (hx : Measurable x) :
    Measurable (fun z => Sum.elim (fun v => f (v, x z))
      (fun v => g (v, x z)) (a z)) :=
  measurable_sumRead (fun pair => f (pair.1, x pair.2))
    (fun pair => g (pair.1, x pair.2))
    (hf.comp (measurable_fst.prodMk (hx.comp measurable_snd)))
    (hg.comp (measurable_fst.prodMk (hx.comp measurable_snd))) a ha

private def coordinatorRead {X Y : Type*}
    (first : X → Y) (live : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate × X → Y)
    (collection : (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) × X → Y)
    (dagger : X → Y) (pair : OrdinaryCoordinatorLocalMeasurability.CoordinatorCode p rate × X) : Y :=
  match pair.1 with
  | .inl _ => first pair.2
  | .inr (.inl value) => live (value, pair.2)
  | .inr (.inr (.inl value)) => collection (value, pair.2)
  | .inr (.inr (.inr _)) => dagger pair.2

private theorem measurable_coordinatorRead {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (first : X → Y) (live : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate × X → Y)
    (collection : (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) × X → Y)
    (dagger : X → Y) (hf : Measurable first) (hl : Measurable live)
    (hc : Measurable collection) (hd : Measurable dagger) :
    Measurable (coordinatorRead first live collection dagger) := by
  let Collection := ReferenceActivePhysicalStep.Payload rate ×
    (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))
  let tail : (Collection ⊕ Unit) × X → Y := fun pair =>
    Sum.elim (fun value => collection (value, pair.2)) (fun _ => dagger pair.2) pair.1
  have ht : Measurable tail := measurable_sumReadAt collection
    (fun pair : Unit × X => dagger pair.2) hc (hd.comp measurable_snd)
    Prod.fst measurable_fst Prod.snd measurable_snd
  let rest : (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ⊕ (Collection ⊕ Unit)) × X →
    Y :=
    fun pair => Sum.elim (fun value => live (value, pair.2))
      (fun value => tail (value, pair.2)) pair.1
  have hr : Measurable rest := measurable_sumReadAt live tail hl ht
    Prod.fst measurable_fst Prod.snd measurable_snd
  have hm := measurable_sumReadAt (fun pair : Unit × X => first pair.2) rest
    (hf.comp measurable_snd) hr Prod.fst measurable_fst Prod.snd measurable_snd
  convert hm using 1
  funext pair
  rcases pair with ⟨code, x⟩
  cases code with
  | inl u => rfl
  | inr rest => cases rest with
    | inl live => rfl
    | inr tail => cases tail <;> rfl

private def liveFromCoordinator
    (pair : OrdinaryCoordinatorLocalMeasurability.CoordinatorCode p rate ×
      (ReferenceLiveDispatchOutputMeasurability.OutcomeData p ×
        (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate))) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  coordinatorRead (fun x => rejectedCode x.2.2)
    (fun x => liveSelectedCode x.1 x.2.1 x.2.2)
    (fun x => rejectedCode x.2.2.2) (fun x => rejectedCode x.2.2) pair

private theorem measurable_liveFromCoordinator :
    Measurable (liveFromCoordinator (p := p) (rate := rate)) := by
  unfold liveFromCoordinator
  apply measurable_coordinatorRead
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd
  · exact (measurable_liveSelectedCode (p := p) (rate := rate)).comp
      (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd.snd
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd

private def collectionFromCoordinator
    (pair : OrdinaryCoordinatorLocalMeasurability.CoordinatorCode p rate ×
      (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ×
        (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate))) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  coordinatorRead (fun x => rejectedCode x.2.2)
    (fun x => rejectedCode x.2.2.2)
    (fun x => collectionSelectedCode x.1.2.1 x.2.1 x.2.2)
    (fun x => rejectedCode x.2.2) pair

private theorem measurable_collectionFromCoordinator :
    Measurable (collectionFromCoordinator (p := p) (rate := rate)) := by
  unfold collectionFromCoordinator
  apply measurable_coordinatorRead
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd.snd
  · exact (measurable_collectionSelectedCode (p := p) (rate := rate)).comp
      (measurable_snd.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd.snd))
  · exact (measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd

private def selectedObservationCode
    (pair : OrdinaryCoordinatorLocalMeasurability.PreparationObservationCode p rate ×
      (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate)) :
        ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  match pair.1 with
  | .inl first => firstSelectedCode first pair.2
  | .inr (.inl live) => liveFromCoordinator (pair.2.2.1.1, live, pair.2)
  | .inr (.inr (.inl collection)) =>
      collectionFromCoordinator (pair.2.2.1.1, collection, pair.2)
  | _ => rejectedCode pair.2.2

private theorem measurable_selectedObservationCode :
    Measurable (selectedObservationCode (p := p) (rate := rate)) := by
  let X := OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate × ObservationInput p rate
  let tail : (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ⊕ (Unit ⊕ Unit)) × X →
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
    fun pair => Sum.elim
      (fun full => collectionFromCoordinator (pair.2.2.1.1, full, pair.2))
      (fun _ => rejectedCode pair.2.2) pair.1
  have ht : Measurable tail := measurable_sumReadAt
    (fun pair : ReferenceCollectionOutcomeMeasurability.FullObservation p rate × X =>
      collectionFromCoordinator (pair.2.2.1.1, pair.1, pair.2))
    (fun pair : (Unit ⊕ Unit) × X => rejectedCode pair.2.2)
    ((measurable_collectionFromCoordinator (p := p) (rate := rate)).comp
      (show Measurable (fun pair : ReferenceCollectionOutcomeMeasurability.FullObservation p rate × X =>
        (pair.2.2.1.1, pair.1, pair.2)) from
          measurable_snd.snd.fst.fst.prodMk (measurable_fst.prodMk measurable_snd)))
    ((measurable_rejectedCode (p := p) (rate := rate)).comp measurable_snd.snd)
    Prod.fst measurable_fst Prod.snd measurable_snd
  let rest : (ReferenceLiveDispatchOutputMeasurability.OutcomeData p ⊕
    (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ⊕ (Unit ⊕ Unit))) × X →
      ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate := fun pair => Sum.elim
    (fun live => liveFromCoordinator (pair.2.2.1.1, live, pair.2))
    (fun value => tail (value, pair.2)) pair.1
  have hr : Measurable rest := measurable_sumReadAt
    (fun pair : ReferenceLiveDispatchOutputMeasurability.OutcomeData p × X => liveFromCoordinator (pair.2.2.1.1, pair.1,
      pair.2))
    tail ((measurable_liveFromCoordinator (p := p) (rate := rate)).comp
      (show Measurable (fun pair : ReferenceLiveDispatchOutputMeasurability.OutcomeData p × X =>
        (pair.2.2.1.1, pair.1, pair.2)) from
          measurable_snd.snd.fst.fst.prodMk (measurable_fst.prodMk measurable_snd))) ht
    Prod.fst measurable_fst Prod.snd measurable_snd
  have hm := measurable_sumReadAt
    (fun pair : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta × X => firstSelectedCode pair.1
      pair.2)
    rest (measurable_firstSelectedCode (p := p) (rate := rate)) hr
    Prod.fst measurable_fst Prod.snd measurable_snd
  convert hm using 1
  funext pair
  rcases pair with ⟨observation, rest⟩
  cases observation with
  | inl first => rfl
  | inr rest => cases rest with
    | inl live => rfl
    | inr tail => cases tail <;> rfl

private def absentCode (x : ObservationInput p rate) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p
  rate :=
  coordinatorRead rejectedCode (fun pair => rejectedCode pair.2)
    (fun pair => rejectedCode pair.2)
    (fun x => ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
      ⟨.dagger, x.1.2.1, none, none, none⟩) (x.1.1, x)

private theorem measurable_absentCode : Measurable (absentCode (p := p) (rate := rate)) := by
  have hm := measurable_coordinatorRead (p := p) (rate := rate)
    (X := ObservationInput p rate) (Y := ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate)
    (rejectedCode (p := p) (rate := rate)) (fun pair => rejectedCode pair.2) (fun pair => rejectedCode pair.2)
    (fun x => ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation ⟨.dagger, x.1.2.1, none, none,
      none⟩)
    measurable_rejectedCode (measurable_rejectedCode.comp measurable_snd)
    (measurable_rejectedCode.comp measurable_snd)
    (measurable_const.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_const))))
  exact hm.comp (measurable_fst.fst.prodMk measurable_id)

private def readAt (observation : OrdinaryCoordinatorLocalMeasurability.PreparationObservationCode p rate)
    (selection : Option (OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate))
    (input : ObservationInput p rate) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  ReferenceCollectionOutcomeMeasurability.optionalElim (absentCode input)
    (fun selected => selectedObservationCode (observation, selected, input)) selection

/-- Read only retained preparation data and the original local input. The
selection guard is applied before either post-choice tail. -/
private def observationFromPreparationCode (pair : OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate × Fin (D
  p + 1)) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  readAt pair.1.2
    (OrdinaryCoordinatorPreparationSelectionMeasurability.selectionDataFromObservation (pair.1.2, pair.1.1))
    (pair.1.1, pair.2)

private theorem measurable_observationFromPreparationCode :
    Measurable (observationFromPreparationCode (p := p) (rate := rate)) := by
  unfold observationFromPreparationCode readAt
  exact measurable_optionRead
    (fun pair : OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate × Fin (D p + 1) => absentCode (pair.1.1,
      pair.2))
    (fun pair : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate ×
      (OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate × Fin (D p + 1)) =>
      selectedObservationCode (pair.2.1.2, pair.1, pair.2.1.1, pair.2.2))
    ((measurable_absentCode (p := p) (rate := rate)).comp (by fun_prop))
    ((measurable_selectedObservationCode (p := p) (rate := rate)).comp (by fun_prop))
    (fun pair => OrdinaryCoordinatorPreparationSelectionMeasurability.selectionDataFromObservation (pair.1.2, pair.1.1))
    (OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_selectionDataFromObservation.comp (by fun_prop))

private theorem liveCodeAtInstallation_eq
    (installation : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate)
    (selected : OrdinaryCoordinatorPreparationSelectionMeasurability.SelectionData p rate) (x : ObservationInput p rate)
      :
    liveCodeAtInstallation installation selected x =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.livePostChoice x.1.2.1 x.1.2.2.1 x.1.2.2.2
        selected.2.2 x.2 (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters installation.1 installation.2)
        (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned installation.1 installation.2)
          installation.2.baseScores selected.2.1) := by
  unfold liveCodeAtInstallation
  rw [liveCollectionCode_eq]
  apply congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
  change ReferenceLiveServiceTailMeasurability.liveServiceTailFromRuntime
    (ReferenceLiveServiceTailMeasurability.decodeLiveRuntime installation.1 installation.2)
    x.1.2.1 selected.2.1 x.1.2.2.2 x.1.2.2.1 x.2
    (ReferenceLiveRecorderJointMeasurability.runCode
      (installation.1, installation.2, selected.2.1, x.1.2.2.2,
        x.1.2.2.1, selected.2.2, x.2)) = _
  unfold ReferenceLiveServiceTailMeasurability.decodeLiveRuntime
    ReferenceLiveServiceTailMeasurability.liveServiceTailFromRuntime
  rw [ReferenceLiveRecorderJointMeasurability.decodeResult_runCode]
  rfl

private theorem readAt_first_eq (u : Unit)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) (Y : Fin (D p + 1))
    (outcome : CoordinatorRoundDispatch.FirstOutcome (OrdinaryCoordinatorPhysicalInterface.firstInput rate row time)) :
    readAt (.inl (ReferenceFirstDispatchMeasurability.observeFirstOutcome outcome))
      (OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData (bank := bank) (.first outcome))
      (((.inl u), (bank, (row, time))), Y) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.observeLocal (bank := bank) (.first outcome) Y) := by
  cases outcome with
  | choiceDomainFailure installed => rfl
  | recorderBoundaryFailure installed => rfl
  | choiceRejected installed => rfl
  | chosen installed selected =>
      by_cases ht : installed.registers.time = time
      · have hinstallation : firstInstallationCode
            (ReferenceFirstDispatchMeasurability.observeFirstOutcome (.chosen installed selected)) =
            (installed.registers.payload,
              ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers installed.ownedRegisters
                installed.followerBaseScore) := rfl
        simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
          OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
          dite_eq_left ht, Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim,
            selectedObservationCode,
          firstSelectedCode, hinstallation, OrdinaryCoordinatorPhysicalInterface.observeLocal, Option.some_ne_none,
            ite_false,
          OrdinaryCoordinatorPhysicalInterface.Preparation.arm]
        exact liveCollectionCode_eq_livePostChoice bank row time selected.arm Y
          installed.registers installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
      · simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
        OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
          dite_eq_right ht, Option.map_none, ReferenceCollectionOutcomeMeasurability.optionalElim, absentCode,
            coordinatorRead,
          OrdinaryCoordinatorPhysicalInterface.observeLocal, ite_true, rejectedCode]

private theorem readAt_live_eq
    (payload : ReferenceActivePhysicalStep.Payload rate) (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete
      p)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) (Y : Fin (D p + 1))
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (OrdinaryCoordinatorPhysicalInterface.liveInput row time
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live)
        (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live) live.baseScores)) :
    readAt (.inr (.inl (ReferenceLiveDispatchOutputMeasurability.outcomeData outcome)))
      (OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData (bank := bank) (.live
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live)
          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live) live.baseScores outcome))
      (((.inr (.inl (payload, live))), (bank, (row, time))), Y) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.observeLocal (bank := bank) (.live
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live)
          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live) live.baseScores outcome) Y) := by
  cases outcome with
  | clockFailure reason hclock => rfl
  | initializerFailure dispatched hdispatch checked hchecked => rfl
  | localFailure dispatched hdispatch reason => rfl
  | continuingChosen dispatched hdispatch continuation selected =>
      simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
        OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
        dite_true, Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim, selectedObservationCode,
        liveFromCoordinator, coordinatorRead, ReferenceLiveDispatchOutputMeasurability.outcomeData, liveSelectedCode,
        OrdinaryCoordinatorPhysicalInterface.observeLocal, Option.some_ne_none, ite_false,
          OrdinaryCoordinatorPhysicalInterface.Preparation.arm]
      exact liveCodeAtInstallation_eq _ _ _
  | cutoffChosen dispatched hdispatch ledger hinitial hcutoff hvalid hpayload hweights hchoice selected =>
      simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
        OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
        dite_true, Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim, selectedObservationCode,
        liveFromCoordinator, coordinatorRead, ReferenceLiveDispatchOutputMeasurability.outcomeData, liveSelectedCode,
        OrdinaryCoordinatorPhysicalInterface.observeLocal, Option.some_ne_none, ite_false,
          OrdinaryCoordinatorPhysicalInterface.Preparation.arm]
      exact collectionCodeAtView_eq _ _ _ _ _ _

private theorem observationFromPreparationCode_at (z : LocalInput p rate) (Y : Fin (D p + 1)) :
    observationFromPreparationCode (OrdinaryCoordinatorLocalMeasurability.prepareLocalCode z, Y) =
      readAt (OrdinaryCoordinatorLocalMeasurability.preparationObservation z)
        (OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData
        (OrdinaryCoordinatorLocalMeasurability.cut z)) (z, Y) := by
  change readAt (OrdinaryCoordinatorLocalMeasurability.preparationObservation z)
    (OrdinaryCoordinatorPreparationSelectionMeasurability.prepareLocalSelectionData z) (z, Y) = _
  rw [OrdinaryCoordinatorPreparationSelectionMeasurability.prepareLocalSelectionData_eq_actualCut]

private def collectionLocalInput (q : ReferenceCollectionDispatchMeasurability.LocalInput p rate) :
    LocalInput p rate :=
  (.inr (.inr (.inl (q.1.1, q.2.1, q.2.2.1))),
    q.2.2.2.1, q.1.2, q.2.2.2.2.1)

private theorem readAt_collection_eq
    (q : ReferenceCollectionDispatchMeasurability.LocalInput p rate) (Y : Fin (D p + 1)) :
    let input := ReferenceCollectionDispatchMeasurability.assemble q
    let prepared : OrdinaryCoordinatorPhysicalInterface.Preparation rate input.upDecoderBank input.row input.time :=
      .collection input.payload input.ledger input.clock input.cutoffIndex
        (CoordinatorRoundDispatch.dispatchCollection input)
    readAt (.inr (.inr (.inl (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q))))
      (OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData prepared) (collectionLocalInput q,
        Y) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.observeLocal prepared Y) := by
  classical
  dsimp only
  cases hout : CoordinatorRoundDispatch.dispatchCollection
      (ReferenceCollectionDispatchMeasurability.assemble q) with
  | continuing core prepared boundary hscores =>
      have htag : (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q).2.2.1 = .continuing :=
        (ReferenceCollectionOutcomeMeasurability.collectionFullObservation_exact q).1.trans (by rw [hout]; rfl)
      simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
        OrdinaryCoordinatorPhysicalInterface.Preparation.selection,
        Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim, selectedObservationCode,
          collectionLocalInput,
        collectionFromCoordinator, coordinatorRead, OrdinaryCoordinatorPhysicalInterface.observeLocal,
        Option.some_ne_none, ite_false, OrdinaryCoordinatorPhysicalInterface.Preparation.arm]
      unfold collectionSelectedCode
      rw [ite_eq_left htag]
      exact collectionCodeAtView_eq _ _ _ _ _ _
  | laterChosen core consistent started hstart instruction hinstruction output hlocal
      clockData installed selected =>
      have htag : (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q).2.2.1 = .laterChosen :=
        (ReferenceCollectionOutcomeMeasurability.collectionFullObservation_exact q).1.trans (by rw [hout]; rfl)
      by_cases ht : instruction.time = (ReferenceCollectionDispatchMeasurability.assemble q).time
      · have hchosen : ReferenceActiveStepCompositionMeasurability.outcomeInstallationCoordinates q
            (CoordinatorRoundDispatch.dispatchCollection (ReferenceCollectionDispatchMeasurability.assemble q)) =
            some ((installed.registers.payload,
              ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers installed.ownedRegisters
                installed.retainedBaseScore), started) := by
          rw [hout]
          rfl
        obtain ⟨observed, hobserved, hcoordinates⟩ :=
          ReferenceActiveStepCompositionMeasurability.collection_installed_observation q _ hchosen
        have hi : (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q).2.1 = some observed := hobserved
        simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
          OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
          dite_eq_left ht, Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim,
            selectedObservationCode,
          collectionLocalInput, collectionFromCoordinator, coordinatorRead,
            OrdinaryCoordinatorPhysicalInterface.observeLocal,
          Option.some_ne_none, ite_false, OrdinaryCoordinatorPhysicalInterface.Preparation.arm]
        unfold collectionSelectedCode
        rw [ite_eq_right (by rw [htag]; intro h; cases h), ite_eq_left htag, hi]
        simp only [ReferenceCollectionOutcomeMeasurability.optionalElim]
        rw [congrArg Prod.fst hcoordinates]
        exact liveCollectionCode_eq_livePostChoice _ _ _ _ _ _ _ _ _
      · simp only [readAt, OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData,
        OrdinaryCoordinatorPhysicalInterface.Preparation.selection, OrdinaryCoordinatorPhysicalInterface.selectionAt,
          dite_eq_right ht, Option.map_none, ReferenceCollectionOutcomeMeasurability.optionalElim, absentCode,
            collectionLocalInput,
          coordinatorRead, OrdinaryCoordinatorPhysicalInterface.observeLocal, ite_true, rejectedCode]
        rfl
  | clockFailure reason hstart => rfl
  | localFailure started hstart hcore reason => rfl
  | coreFailure core started hstart reason => rfl
  | laterReconstructionFailure core consistent started hstart instruction hi reason hr => rfl
  | laterPrefixFailure core consistent started hstart instruction hi arm reason hr => rfl
  | laterOrientationFailure core consistent started hstart instruction hi set hr => rfl
  | laterChoiceFailure core consistent started hstart instruction hi output hlocal clockData installed reason => rfl

/-- The readout is compared with the accepted reconstruction only on its
actual image. Reconstruction equality is used solely as proof evidence. -/
private theorem observationFromPreparationCode_exact (z : LocalInput p rate) (Y : Fin (D p + 1)) :
    observationFromPreparationCode (OrdinaryCoordinatorLocalMeasurability.prepareLocalCode z, Y) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (OrdinaryCoordinatorPhysicalInterface.observeLocal
        (OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode z
          (OrdinaryCoordinatorPreparationReconstruction.actualPreparationCode z).2 rfl) Y) := by
  rw [OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode_exact,
    observationFromPreparationCode_at]
  rcases z with ⟨code, bank, row, time⟩
  cases code with
  | inl u => exact readAt_first_eq u bank row time Y _
  | inr rest => cases rest with
    | inl live => exact readAt_live_eq live.1 live.2 bank row time Y _
    | inr rest => cases rest with
      | inl collection =>
          rcases collection with ⟨payload, ledger, proposal⟩
          by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
            let q : ReferenceCollectionDispatchMeasurability.LocalInput p rate :=
              ((payload, row), ledger, proposal, bank, time, cutoff)
            have hobs : OrdinaryCoordinatorLocalMeasurability.preparationObservation
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                .inr (.inr (.inl (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q))) := by
              simp [OrdinaryCoordinatorLocalMeasurability.preparationObservation,
                OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                OrdinaryCoordinatorLocalMeasurability.decoderBank,
                OrdinaryCoordinatorLocalMeasurability.completeRow, OrdinaryCoordinatorLocalMeasurability.calendarTime,
                  OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
                OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
                  ReferenceCollectionOutcomeMeasurability.boundaryFullObservation,
                ReferenceCollectionDispatchMeasurability.boundaryLocal,
                ReferenceCollectionDispatchMeasurability.cutoffValid, hcutoff, q, cutoff]
            have hcut : OrdinaryCoordinatorLocalMeasurability.cut
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                .collection payload ledger
                  (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff
                  (CoordinatorRoundDispatch.dispatchCollection
                    (OrdinaryCoordinatorPhysicalInterface.collectionInput bank row time payload ledger
                      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff)) := by
              exact OrdinaryCoordinatorPhysicalInterface.prepareLocal_collection bank row time payload ledger proposal
                hcutoff
            rw [hobs, hcut]
            exact readAt_collection_eq q Y
          · have hcut : OrdinaryCoordinatorLocalMeasurability.cut
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                .invalidCollectionCutoff :=
              OrdinaryCoordinatorPhysicalInterface.prepareLocal_invalidCollectionCutoff bank row time payload ledger
                proposal hcutoff
            rw [hcut]
            rfl
      | inr dagger => rfl

/-- The literal complete ordinary own-feedback observer, encoded by the
existing retained collection observation schema. -/
def observeLocalCode (z : LocalInput p rate × Fin (D p + 1)) :
  ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (OrdinaryCoordinatorPhysicalInterface.observeLocal (OrdinaryCoordinatorLocalMeasurability.cut z.1) z.2)

/-- Joint Borel measurability on every original raw coordinator code, original
bank, whole continuous row, calendar time and own grid feedback. There is no
validity, alignment, safety, success or measurable-operation premise. -/
theorem measurable_observeLocalCode :
    Measurable (observeLocalCode (p := p) (rate := rate)) := by
  have hargs : Measurable (fun z : LocalInput p rate × Fin (D p + 1) =>
      (OrdinaryCoordinatorLocalMeasurability.prepareLocalCode z.1, z.2)) :=
    (OrdinaryCoordinatorLocalMeasurability.measurable_prepareLocalCode.comp measurable_fst).prodMk measurable_snd
  have hread := (measurable_observationFromPreparationCode (p := p) (rate := rate)).comp hargs
  have heq : observeLocalCode (p := p) (rate := rate) =
      fun z => observationFromPreparationCode (OrdinaryCoordinatorLocalMeasurability.prepareLocalCode z.1, z.2) := by
    funext z
    have h := observationFromPreparationCode_exact z.1 z.2
    rw [OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode_exact] at h
    exact h.symm
  rw [heq]
  exact hread

/-- The retained decoder recovers the exact whole local output, including all
failure, recorder, bank and ordinary UP-result branches. -/
theorem decode_observeLocalCode (z : LocalInput p rate) (Y : Fin (D p + 1)) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation (observeLocalCode (z, Y)) =
      OrdinaryCoordinatorPhysicalInterface.observeLocal (OrdinaryCoordinatorLocalMeasurability.cut z) Y :=
  ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation_encodeCollectionObservation _

/-- Optional substitution corollary. Its only additional proof inputs are
measurability of the primitive original local input and own feedback maps. -/
theorem measurable_observeLocalCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → LocalInput p rate) (feedback : Ω → Fin (D p + 1))
    (hinput : Measurable input) (hfeedback : Measurable feedback) :
    Measurable (fun ω => observeLocalCode (input ω, feedback ω)) :=
  measurable_observeLocalCode.comp (hinput.prodMk hfeedback)

end Bandits.Support.OrdinaryCoordinatorObservationMeasurability

end
