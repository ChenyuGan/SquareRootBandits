/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterCollectionArrivalReadout

import Lean.Elab.Tactic.Omega

/-!
# Exact local constructor domain of the later-collection readout

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The observations below project actual PREPARE configurations and actual
collection/LIVE dispatch outcomes on the existing canonical RoundInput Borel
space. Their finite tags retain the underlying full continuous coordinates.
The guard is the exact option domain, including frozen continuing collection
and strict later cutoff choice, before any recorder or post-choice failure.

These are internal local results. Named remaining consumers are the
source-indexed later-collection domain (by composition with the independently
owned suffix-input Borel producer), then the full optional numerical tuple and
integer-vector calendar Borelness. No source law, total coverage, global
calendar measurability, queue truth, overflow identity, or manuscript closure
is established here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLaterCollectionReadoutDomain

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

local instance : MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
  ReferenceCollectionOutcomeMeasurability.instMeasurableSpaceClockObservation
local instance : DiscreteMeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
  ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤
local instance : DiscreteMeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  ⟨fun _ => trivial⟩
local instance optionDiscrete {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    DiscreteMeasurableSpace (Option A) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit A
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

/-- The finite PREPARE status projection carried by the lossless output code. -/
def preparedFollowerTagFromCode (rate : RateInput p)
    (code : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) :
    Option (Fin 3) :=
  let output : FollowerPrepareJointMeasurability.PrepareOutput p rate code.1 := code.2
  match ReferenceUpReceptionMeasurability.incomingOfferIndex output.2.2 with
  | .dagger => none
  | .ordinary index => some index.1.status

/-- The actual PREPARE follower tag: dagger is absent, and every ordinary
status is retained by its original finite code. -/
def preparedFollowerTag (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    Option (Fin 3) :=
  preparedFollowerTagFromCode rate
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i)

/-- The finite status tag of an actual ordinary/dagger PREPARE configuration. -/
def preparedConfigurationTag :
    DeclaredFollowerLocalRound.LocalConfiguration p rate → Option (Fin 3)
  | .dagger => none
  | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status)

private theorem incomingTag_eq_localConfigurationTag
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    (match ReferenceUpReceptionMeasurability.incomingOfferIndex incoming with
      | .dagger => (none : Option (Fin 3))
      | .ordinary index => some index.1.status) =
      preparedConfigurationTag
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming) := by
  cases incoming with
  | none => rfl
  | some data =>
      rcases data with ⟨carried, memory⟩
      let stateCode := carried.1.1
      have hstatus : ∀ status : Fin 3,
          FollowerDownMeasurability.followerStatusCode
            (FollowerDownMeasurability.followerStatusOfCode status) = status := by
        intro status
        fin_cases status <;> rfl
      simp only [ReferenceUpReceptionMeasurability.incomingOfferIndex,
        FollowerPrepareJointMeasurability.incomingConfigurationToSum,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
        FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
        FollowerDownMeasurability.followerStateOfCode,
        FollowerDownMeasurability.followerStatusOfCode, preparedConfigurationTag]
      change some stateCode.status = some (FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode stateCode.status))
      exact congrArg some (hstatus stateCode.status).symm

private theorem preparedFollowerTagFromCode_eq_configuration (rate : RateInput p)
    (i : Fin (p.m - 1))
    (code : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) :
    preparedFollowerTagFromCode rate code =
      preparedConfigurationTag
        (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i code.1 code.2).configuration := by
  exact incomingTag_eq_localConfigurationTag code.2.2.2

/-- The local PREPARE code reconstructs the very same prepared follower,
including ordinary/dagger and every checked failure branch. -/
theorem preparedFollowerCode_reconstruct
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i
        (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i).1
        (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i).2 =
      (ReferenceActivePhysicalStep.prepare x).followers.followers i :=
  ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct x i

/-- The status tag reconstructs the actual PREPARE configuration on every
canonical round input, including dagger and every checked failure branch. -/
theorem preparedFollowerTag_eq_prepare
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    preparedFollowerTag rate x i = preparedConfigurationTag
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
  have h := preparedFollowerTagFromCode_eq_configuration rate i
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i)
  rw [preparedFollowerCode_reconstruct] at h
  exact h

/-- The lossless code tag equals the literal ordinary/dagger and status tag
stored in the same physical record's PREPARE output. -/
theorem preparedFollowerTag_eq_actualPreparation
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1)) :
    preparedFollowerTag rate record.input i = preparedConfigurationTag
      (record.output.preparation.followers.followers i).configuration := by
  have hprepared : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  rw [preparedFollowerTag_eq_prepare, ← hprepared]

/-- The all-follower PREPARE guard is exactly the finite ordinary/unoccupied
tag test; dagger cannot pass through a default value. -/
theorem preparedFollowersUnoccupied_iff_actualPrepareTag
    (record : RoundRecord (p := p) (rate := rate)) :
    ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ↔
      ∀ i : Fin (p.m - 1), preparedFollowerTag rate record.input i = some 0 := by
  constructor
  · intro hunoccupied i
    cases hconfig : (record.output.preparation.followers.followers i).configuration with
    | dagger =>
        have hi := hunoccupied i
        simp only [hconfig] at hi
    | ordinary state memory =>
        have hstatus : state.status = .unoccupied := by
          simpa [ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied, hconfig]
            using hunoccupied i
        rw [preparedFollowerTag_eq_actualPreparation record i]
        simp [hconfig, preparedConfigurationTag, hstatus,
          FollowerDownMeasurability.followerStatusCode]
  · intro htag i
    cases hconfig : (record.output.preparation.followers.followers i).configuration with
    | dagger =>
        have hi := htag i
        rw [preparedFollowerTag_eq_actualPreparation record i, hconfig] at hi
        simp [preparedConfigurationTag] at hi
    | ordinary state memory =>
        have hi := htag i
        rw [preparedFollowerTag_eq_actualPreparation record i, hconfig] at hi
        have hstatus : state.status = .unoccupied := by
          cases hs : state.status <;>
            simp [preparedConfigurationTag, hs,
              FollowerDownMeasurability.followerStatusCode] at hi ⊢
        exact hstatus

/-- Joint measurability of the finite PREPARE tag, with the original local
buffer and all continuous row coordinates retained. -/
theorem measurable_preparedFollowerTag (rate : RateInput p)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      preparedFollowerTag rate x i) := by
  have htag : Measurable (preparedFollowerTagFromCode rate) := by
    exact measurable_of_sigma_sections (preparedFollowerTagFromCode rate) fun activation => by
      have hconfig : Measurable (fun output :
          FollowerPrepareJointMeasurability.PrepareOutput p rate activation => output.2.2) :=
        measurable_snd.comp (measurable_snd.comp measurable_id)
      have hproject : Measurable (fun offer :
          ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate =>
            match offer with
            | .dagger => (none : Option (Fin 3))
            | .ordinary index => some index.1.status) := measurable_of_countable _
      exact hproject.comp
        ((ReferenceUpReceptionMeasurability.measurable_incomingOfferIndex rate).comp hconfig)
  change Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
    preparedFollowerTagFromCode rate
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i))
  exact htag.comp (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)

/-- Project the tag of an actual collection observation from its canonical
full observation. Absence and invalid-cutoff observations remain absent. -/
def canonicalCollectionTag (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (ReferenceCollectionOutcomeMeasurability.CollectionTag p) :=
  ReferenceCollectionOutcomeMeasurability.optionalElim none
    (fun observation => Sum.elim (fun _ : Unit => (none : Option
      (ReferenceCollectionOutcomeMeasurability.CollectionTag p)))
      (fun full => some full.2.2.1) observation)
    (ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation x)

section CanonicalTag

local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ReferenceCollectionOutcomeMeasurability.instMeasurableSpaceStartRoundResult
local instance (priority := 1200) optionLater {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance (priority := 1300) : MeasurableSpace (Option (Fin p.K)) :=
  FollowerActionMeasurability.optionArmMeasurableSpace p
local instance (priority := 1300) : MeasurableSpace
    (Option (ReferenceCollectionOutcomeMeasurability.CollectionTag p)) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

/-- The stored collection-tag projection is Borel on the original round
input and uses the canonical full observation, including invalid outcomes. -/
theorem measurable_canonicalCollectionTag (rate : RateInput p) :
    Measurable (canonicalCollectionTag rate) := by
  have hfull : Measurable (fun full :
      ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
        (some full.2.2.1 : Option
          (ReferenceCollectionOutcomeMeasurability.CollectionTag p))) := by
    exact (Measurable.of_discrete : Measurable
      (some : ReferenceCollectionOutcomeMeasurability.CollectionTag p →
        Option (ReferenceCollectionOutcomeMeasurability.CollectionTag p))).comp
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have htag : Measurable (fun observation :
      Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
        Sum.elim (fun _ : Unit => (none : Option
          (ReferenceCollectionOutcomeMeasurability.CollectionTag p)))
          (fun full => some full.2.2.1) observation) :=
    measurable_fun_sum measurable_const hfull
  exact (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim none
      (fun observation => Sum.elim (fun _ : Unit => (none : Option
        (ReferenceCollectionOutcomeMeasurability.CollectionTag p)))
        (fun full => some full.2.2.1) observation) htag).comp
    (ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionFullObservation
      (p := p) (rate := rate))

end CanonicalTag

/-- The projected canonical collection tag is the tag of the actual
`dispatchCollection` call on the same complete boundary input. -/
theorem canonicalCollectionTag_eq_actualOutcomeTag (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) :
    canonicalCollectionTag rate x = some
      (ReferenceCollectionOutcomeMeasurability.outcomeTag
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceCollectionDispatchMeasurability.assemble
            (ReferenceCollectionDispatchMeasurability.boundaryLocal
              ⟨((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time), hcutoff⟩)))) := by
  have hvalid : ReferenceCollectionDispatchMeasurability.cutoffValid
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time) := by
    simpa [ReferenceCollectionDispatchMeasurability.cutoffValid] using hcutoff
  rw [canonicalCollectionTag,
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_collection
      x payload ledger proposal hstate]
  simp [ReferenceCollectionOutcomeMeasurability.optionalElim,
    ReferenceCollectionOutcomeMeasurability.boundaryFullObservation, hvalid,
    ReferenceCollectionOutcomeMeasurability.collectionFullObservation]
  rw [ReferenceCollectionOutcomeMeasurability.collectionTag_eq_actual]

/-- Project the actual incoming-LIVE dispatcher outcome. The stored live
coordinate, complete current row, and time are the ones passed to dispatch. -/
def actualLiveOutcomeData (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) :=
  match ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator with
  | .inl _ => none
  | .inr (.inl (payload, live)) =>
      some (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
            (payload, (live, (x.time, x.row))))), payload.sigma)
  | .inr (.inr _) => none

private theorem measurable_sumProdElim {A B X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    : Measurable (fun z : (A ⊕ B) × X =>
      Sum.elim (fun a => f (a, z.2)) (fun b => g (b, z.2)) z.1) := by
  have h := (hf.sumElim hg).comp
    (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  convert h using 1
  funext z
  cases z with
  | mk tag x => cases tag <;> rfl

private def liveOutcomeDataOnCoordinates (rate : RateInput p)
    (z : (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (Fin p.T × CompletePublicTable.CompleteRow p)) :
    Option (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) :=
  some (ReferenceLiveDispatchOutputMeasurability.outcomeData
    (CoordinatorRoundDispatch.dispatchLive
      (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
        (z.1.1, (z.1.2, z.2)))), z.1.1.sigma)

private theorem measurable_liveOutcomeDataOnCoordinates (rate : RateInput p) :
    Measurable (liveOutcomeDataOnCoordinates rate) := by
  let coordinates :
      (ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
          (Fin p.T × CompletePublicTable.CompleteRow p) →
        ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate :=
    fun z => (z.1.1, (z.1.2, z.2))
  have hcoordinates : Measurable coordinates :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hdata : Measurable (fun z :
      ((ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
          (Fin p.T × CompletePublicTable.CompleteRow p)) =>
      ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
            (coordinates z)))) :=
    (ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData
      (p := p) (rate := rate)).comp hcoordinates
  have hpayloadObservation : Measurable
      (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
  have hsigma : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate => z.sigma) :=
    measurable_fst.comp (measurable_snd.comp hpayloadObservation)
  have hpair : Measurable (fun z =>
      (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
        (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates (coordinates z))),
        (coordinates z).1.sigma)) := hdata.prodMk (hsigma.comp (measurable_fst.comp hcoordinates))
  have hsome : Measurable (some :
      (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) →
        Option (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T)) := by
    exact Measurable.of_discrete
  change Measurable (fun z :
    (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (Fin p.T × CompletePublicTable.CompleteRow p) => some
    (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
          (z.1.1, (z.1.2, z.2)))), z.1.1.sigma))
  exact hsome.comp hpair

/-- The incoming live tag and its exact outcome data are jointly Borel on
the original round input. The payload sigma is retained alongside the true
dispatcher outcome so the strict later-start test is observable. -/
theorem measurable_actualLiveOutcomeData (rate : RateInput p) :
    Measurable (actualLiveOutcomeData rate) := by
  let code := fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator
  let roundData := fun x : ReferenceActivePhysicalStep.RoundInput p rate => (x.time, x.row)
  have hcode : Measurable code :=
    ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp
      ReferenceActivePhysicalStepMeasurability.measurable_state
  have hroundData : Measurable roundData :=
    ReferenceActivePhysicalStepMeasurability.measurable_time.prodMk
      ReferenceActivePhysicalStepMeasurability.measurable_row
  let livePair := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  let otherPair :=
    (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit
  let roundDataType := Fin p.T × CompletePublicTable.CompleteRow p
  let innerMap : (livePair ⊕ otherPair) × roundDataType →
      Option (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) :=
    fun z => Sum.elim (fun pair : livePair => liveOutcomeDataOnCoordinates rate (pair, z.2))
      (fun _ : otherPair => none) z.1
  have hInner : Measurable innerMap := by
    exact measurable_sumProdElim
      (fun q : livePair × roundDataType => liveOutcomeDataOnCoordinates rate q)
      (fun _ : otherPair × roundDataType => none)
      (measurable_liveOutcomeDataOnCoordinates rate) measurable_const
  let outerMap : (Unit ⊕ (livePair ⊕ otherPair)) × roundDataType →
      Option (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) :=
    fun z => Sum.elim (fun _ : Unit => none)
      (fun nested => innerMap (nested, z.2)) z.1
  have hOuter : Measurable outerMap := by
    exact measurable_sumProdElim
      (fun _ : Unit × roundDataType => none)
      (fun z : (livePair ⊕ otherPair) × roundDataType => innerMap z)
      measurable_const hInner
  have hcodeData := hcode.prodMk hroundData
  have hmeas := hOuter.comp hcodeData
  have heq : actualLiveOutcomeData rate = fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      outerMap (code x, roundData x) := by
    funext x
    cases hcoord : x.state.coordinator <;>
      simp [actualLiveOutcomeData, code, roundData, outerMap, innerMap,
        liveOutcomeDataOnCoordinates, hcoord,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceLiveDispatchMeasurability.liveInputOfCoordinates]
  rw [heq]
  exact hmeas

/-- The retained LIVE outcome-data tag is the actual dispatcher
`outcomeData`, using the same reindexed registers, full row, and time. -/
theorem actualLiveOutcomeData_eq_liveDispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live registers owned base) :
    actualLiveOutcomeData rate x = some
      (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base)),
        registers.payload.sigma) := by
  unfold actualLiveOutcomeData
  rw [hstate]
  simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    ReferenceLiveDispatchMeasurability.liveInputOfCoordinates]
  exact congrArg (fun data => some (data, registers.payload.sigma))
      (ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput x registers owned base)

/-- Under the literal LIVE dispatch branch, the saved code's outcome-data tag
is exactly the constructor retained by the actual PREPARE observation. -/
theorem actualLiveOutcomeData_eq_actualDispatchOutcome
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hstate : x.state.coordinator = .live registers owned base)
    (hdispatch : ReferenceActivePhysicalStep.dispatch x = .live registers owned base outcome) :
    actualLiveOutcomeData rate x = some
      (ReferenceLiveDispatchOutputMeasurability.outcomeData outcome, registers.payload.sigma) := by
  have hactual : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) = outcome := by
    have h := hdispatch
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at h
    injection h with _ _ _ houtcome
  rw [actualLiveOutcomeData_eq_liveDispatch x registers owned base hstate, hactual]

/-- The literal observable domain: every actual prepared follower is
ordinary/unoccupied, and dispatch is continuing collection or a cutoff choice
whose assignment start is strictly after `s`. -/
def observableReadoutGuard (rate : RateInput p) (s : ℕ)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Prop :=
  (∀ i : Fin (p.m - 1), preparedFollowerTag rate x i = some 0) ∧
    (canonicalCollectionTag rate x = some .continuing ∨
      ∃ result : ReferenceLiveDispatchOutputMeasurability.OutcomeData p,
        ∃ sigma : Fin p.T,
          actualLiveOutcomeData rate x = some (result, sigma) ∧
          (∃ dispatched ledger arm, result = .cutoffChosen dispatched ledger arm) ∧
          s < sigma.val)

/-- Borelness on the canonical input space. Only the countable outcome data
and finite tags are given discrete measurable structures; payloads, rows,
registers and saved real fibres retain their existing spaces. -/
theorem measurableSet_observableReadoutGuard (rate : RateInput p) (s : ℕ) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      observableReadoutGuard rate s x} := by
  have hfollowers : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      ∀ i : Fin (p.m - 1), preparedFollowerTag rate x i = some 0) :=
    Measurable.forall fun i => (measurable_preparedFollowerTag rate i).eq_const (some 0)
  have hcollection := (measurable_canonicalCollectionTag rate).eq_const (some .continuing)
  have htest : Measurable (fun data : Option
      (ReferenceLiveDispatchOutputMeasurability.OutcomeData p × Fin p.T) =>
      ∃ result : ReferenceLiveDispatchOutputMeasurability.OutcomeData p,
        ∃ sigma : Fin p.T,
          data = some (result, sigma) ∧
          (∃ dispatched ledger arm, result = .cutoffChosen dispatched ledger arm) ∧
          s < sigma.val) := Measurable.of_discrete
  exact (hfollowers.and
    (hcollection.or (htest.comp (measurable_actualLiveOutcomeData rate)))).setOf

private theorem liveOutcome_guard_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base)) (s : ℕ) :
    (match (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome :
        ReferenceActivePhysicalStep.DispatchCut x) with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live r _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => s < r.payload.sigma.val
      | _ => False) ↔
      (∃ result : ReferenceLiveDispatchOutputMeasurability.OutcomeData p,
        ∃ sigma : Fin p.T,
          some (ReferenceLiveDispatchOutputMeasurability.outcomeData outcome,
            registers.payload.sigma) = some (result, sigma) ∧
          (∃ dispatched ledger arm, result = .cutoffChosen dispatched ledger arm) ∧
          s < sigma.val) := by
  have heq : (∃ result : ReferenceLiveDispatchOutputMeasurability.OutcomeData p,
      ∃ sigma : Fin p.T,
        some (ReferenceLiveDispatchOutputMeasurability.outcomeData outcome,
          registers.payload.sigma) = some (result, sigma) ∧
        (∃ dispatched ledger arm, result = .cutoffChosen dispatched ledger arm) ∧
        s < sigma.val) ↔
      (∃ dispatched ledger arm,
        ReferenceLiveDispatchOutputMeasurability.outcomeData outcome =
          .cutoffChosen dispatched ledger arm) ∧ s < registers.payload.sigma.val := by
    constructor
    · rintro ⟨result, sigma, hpair, hcutoff, hlt⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpair)
      exact ⟨hcutoff, hlt⟩
    · rintro ⟨hcutoff, hlt⟩
      exact ⟨_, registers.payload.sigma, rfl, hcutoff, hlt⟩
  rw [heq]
  cases outcome <;>
    simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData,
      reduceCtorEq, exists_false, false_and]
  constructor
  · intro hlt
    exact ⟨⟨_, _, _, rfl⟩, hlt⟩
  · exact fun h => h.2

private theorem collectionOutcome_guard_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) (s : ℕ) :
    (match (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome :
        ReferenceActivePhysicalStep.DispatchCut x) with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live r _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => s < r.payload.sigma.val
      | _ => False) ↔
      ReferenceCollectionOutcomeMeasurability.outcomeTag outcome = .continuing := by
  cases outcome <;>
    simp only [ReferenceCollectionOutcomeMeasurability.outcomeTag, reduceCtorEq]

private theorem canonicalCollectionTag_absent
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hphase : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) = none) :
    canonicalCollectionTag rate x = none := by
  have hobs :=
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_absent x hphase
  simp only [canonicalCollectionTag, hobs.1,
    ReferenceCollectionOutcomeMeasurability.optionalElim]

/-- On every canonical input, the collection tag is exactly the tag of
its actual collection dispatch. All other phases and the distinct invalid
collection-cutoff constructor remain absent. -/
theorem canonicalCollectionTag_eq_dispatch (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    canonicalCollectionTag rate x =
      match ReferenceActivePhysicalStep.dispatch x with
      | .collection _ _ _ _ outcome =>
          some (ReferenceCollectionOutcomeMeasurability.outcomeTag outcome)
      | _ => none := by
  cases hstate : x.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate]
      apply canonicalCollectionTag_absent
      simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate]
      apply canonicalCollectionTag_absent
      simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
  | live registers owned base =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch x =
          .live registers owned base (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hdispatch]
      apply canonicalCollectionTag_absent
      simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · have hdispatch := ReferenceCollectionDispatchMeasurability.dispatch_collection x
          payload ledger proposal hstate hvalid
        dsimp only at hdispatch
        rw [hdispatch]
        exact canonicalCollectionTag_eq_actualOutcomeTag rate x
          payload ledger proposal hstate hvalid
      · have hinvalid :=
          ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_invalid
            x payload ledger proposal hstate hvalid
        rw [hinvalid.2]
        simp only [canonicalCollectionTag, hinvalid.1,
          ReferenceCollectionOutcomeMeasurability.optionalElim, Sum.elim_inl]

/-- On every canonical input, the LIVE observation is precisely the actual
LIVE dispatch data and its original assignment start. Clock, initializer and
local failures remain their own stored outcome constructors. -/
theorem actualLiveOutcomeData_eq_dispatch (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    actualLiveOutcomeData rate x =
      match ReferenceActivePhysicalStep.dispatch x with
      | .live registers _ _ outcome =>
          some (ReferenceLiveDispatchOutputMeasurability.outcomeData outcome,
            registers.payload.sigma)
      | _ => none := by
  cases hstate : x.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate]
      simp only [actualLiveOutcomeData, hstate,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate]
      simp only [actualLiveOutcomeData, hstate,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
  | live registers owned base =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch x =
          .live registers owned base (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hdispatch]
      exact actualLiveOutcomeData_eq_liveDispatch x registers owned base hstate
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · have hdispatch := ReferenceCollectionDispatchMeasurability.dispatch_collection x
          payload ledger proposal hstate hvalid
        dsimp only at hdispatch
        rw [hdispatch]
        simp only [actualLiveOutcomeData, hstate,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      · have hdispatch := ReferenceCollectionDispatchMeasurability.dispatch_collection_invalid x
          payload ledger proposal hstate hvalid
        rw [hdispatch.1]
        simp only [actualLiveOutcomeData, hstate,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]

/-- The observable coordinator tests reconstruct exactly the two dispatch
constructors used by the readout. Each failure and each other incoming phase
is handled at its own constructor, independently of all later effects. -/
theorem dispatch_guard_iff (rate : RateInput p) (s : ℕ)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (match ReferenceActivePhysicalStep.dispatch x with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
          s < registers.payload.sigma.val
      | _ => False) ↔
      (canonicalCollectionTag rate x = some .continuing ∨
        ∃ result : ReferenceLiveDispatchOutputMeasurability.OutcomeData p,
          ∃ sigma : Fin p.T,
            actualLiveOutcomeData rate x = some (result, sigma) ∧
            (∃ dispatched ledger arm, result = .cutoffChosen dispatched ledger arm) ∧
            s < sigma.val) := by
  cases hstate : x.state.coordinator with
  | first =>
      have htag : canonicalCollectionTag rate x = none := by
        apply canonicalCollectionTag_absent
        simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
      have hlive : actualLiveOutcomeData rate x = none := by
        simp only [actualLiveOutcomeData, hstate,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate, htag, hlive]
      simp only [reduceCtorEq, false_and, exists_false, false_or]
  | dagger =>
      have htag : canonicalCollectionTag rate x = none := by
        apply canonicalCollectionTag_absent
        simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
      have hlive : actualLiveOutcomeData rate x = none := by
        simp only [actualLiveOutcomeData, hstate,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate, htag, hlive]
      simp only [reduceCtorEq, false_and, exists_false, false_or]
  | live registers owned base =>
      have htag : canonicalCollectionTag rate x = none := by
        apply canonicalCollectionTag_absent
        simp only [hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          ReferenceCollectionDispatchMeasurability.collectionCoordinates?]
      have hlive := actualLiveOutcomeData_eq_liveDispatch x registers owned base hstate
      have hdispatch : ReferenceActivePhysicalStep.dispatch x =
          .live registers owned base (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hdispatch, htag, hlive]
      simp only [reduceCtorEq, false_or]
      exact liveOutcome_guard_iff x registers owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base)) s
  | collection payload ledger proposal =>
      have hlive : actualLiveOutcomeData rate x = none := by
        simp only [actualLiveOutcomeData, hstate,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · have htag := canonicalCollectionTag_eq_actualOutcomeTag rate x
          payload ledger proposal hstate hvalid
        have hdispatch := ReferenceCollectionDispatchMeasurability.dispatch_collection x
          payload ledger proposal hstate hvalid
        dsimp only at hdispatch
        rw [hdispatch, htag, hlive]
        simp only [reduceCtorEq, false_and, exists_false, or_false, Option.some.injEq]
        exact collectionOutcome_guard_iff x payload ledger _ _
          (CoordinatorRoundDispatch.dispatchCollection
            (ReferenceCollectionDispatchMeasurability.assemble
              (ReferenceCollectionDispatchMeasurability.boundaryLocal
                ⟨((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time), hvalid⟩))) s
      · have hinvalid :=
          ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation_invalid
            x payload ledger proposal hstate hvalid
        have htag : canonicalCollectionTag rate x = none := by
          simp only [canonicalCollectionTag, hinvalid.1,
            ReferenceCollectionOutcomeMeasurability.optionalElim, Sum.elim_inl]
        rw [hinvalid.2, htag, hlive]
        simp only [reduceCtorEq, false_and, exists_false, false_or]

/-- For every actual round record, including every post-choice failure, the
later-collection option is present exactly on the literal Borel guard. The
only record evidence used is its existing `output_eq` and PREPARE identity. -/
theorem readout_isSome_iff (rate : RateInput p) (s : ℕ)
    (record : RoundRecord (p := p) (rate := rate)) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome = true ↔
      observableReadoutGuard rate s record.input := by
  rw [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain,
    observableReadoutGuard, preparedFollowersUnoccupied_iff_actualPrepareTag,
    record.output.preparation.coordinator_eq]
  apply and_congr Iff.rfl
  have h := dispatch_guard_iff rate s record.input
  cases hcut : ReferenceActivePhysicalStep.dispatch record.input with
  | first outcome => simpa only [hcut] using h
  | dagger => simpa only [hcut] using h
  | invalidCollectionCutoff => simpa only [hcut] using h
  | live registers owned base outcome =>
      cases outcome <;> simpa only [hcut] using h
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simpa only [hcut] using h

end Bandits.Support.ReferenceLaterCollectionReadoutDomain

end
