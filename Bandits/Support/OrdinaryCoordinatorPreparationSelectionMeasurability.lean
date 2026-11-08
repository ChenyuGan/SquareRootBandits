/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrdinaryCoordinatorLocalMeasurability

/-!
# Borel data for the actual ordinary coordinator selection

The input is the original coordinator code, UP decoder bank, complete public
row, and calendar time.  The selection data is projected from O's retained
branch observation.  It keeps the original choice view, including its payload
and dependent real weights, together with the start result and chosen arm.
The final Borel proof composes a readout of this retained data with
`OrdinaryCoordinatorLocalMeasurability.measurable_prepareLocalCode`; it does
not reproduce the prechoice observation producer. No measurable space is
assigned to the dependent `Preparation` carrier.

The root telescope is only `{p : Parameters} {rate : RateInput p}`, followed
by the original `LocalInput p rate` for pointwise identities. FIRST's actual
installation time, LIVE's reindexed call time and changed cutoff clock, and
COLLECTION's continuing clock/ledger weights and later instruction time are
discharged in branch identities before the final original-sum identity.
The complete Preparation decoder, observation tails, mixed feedback composer,
history/probability laws and manuscript closure remain separate obligations.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.OrdinaryCoordinatorPreparationSelectionMeasurability

abbrev Parameters := OrdinaryCoordinatorLocalMeasurability.Parameters
abbrev RateInput := OrdinaryCoordinatorLocalMeasurability.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance firstSlowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤
local instance firstStartRoundResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance firstClockMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.ClockRegisters p) := ⊤
local instance optionalCutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤
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
local instance collectionOptionalTimeMeasurableSpace :
    MeasurableSpace (Option (Fin p.T)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance selectionOptionCodeMeasurableSpace :
    MeasurableSpace (Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)) := ⊤

local instance optionDiscrete {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    DiscreteMeasurableSpace (Option A) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit A
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

abbrev LocalInput (p : Parameters) (rate : RateInput p) :=
  OrdinaryCoordinatorLocalMeasurability.LocalInput p rate
abbrev SelectionData (p : Parameters) (rate : RateInput p) :=
  ReferenceCollectionDispatchMeasurability.SelectionCoordinates p rate

/-- The literal data projection of the existing dependent preparation
selection. Only its proof fields are omitted. -/
def preparationSelectionData {bank : CoordinatorUpReception.UpDecoderBank p}
    {row : CompletePublicTable.CompleteRow p} {time : Fin p.T}
    (cut : OrdinaryCoordinatorPhysicalInterface.Preparation rate bank row time) :
    Option (SelectionData p rate) :=
  cut.selection.map fun selected => (selected.view, (selected.started, selected.arm))

/-- Project the DOWN view from retained selection data. -/
def selectionDataDownView (code : Option (SelectionData p rate)) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  code.map Prod.fst

/-- Project the selected arm, using the source fallback exactly when the
actual preparation has no selection. -/
def selectionDataArm (code : Option (SelectionData p rate)) : Fin p.K :=
  (code.map (fun selected => selected.2.2)).getD
    (ReferenceActivePhysicalStep.coordinatorFallback p)

theorem measurable_selectionDataDownView : Measurable
    (selectionDataDownView (p := p) (rate := rate)) := by
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap
    Prod.fst measurable_fst id measurable_id

theorem measurable_selectionDataArm : Measurable
    (selectionDataArm (p := p) (rate := rate)) := by
  let : MeasurableSpace (Option (Fin p.K)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hmap : Measurable (fun code : Option (SelectionData p rate) =>
      code.map (fun selected => selected.2.2)) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap
      (fun selected : SelectionData p rate => selected.2.2)
      (measurable_snd.comp measurable_snd) id measurable_id
  have hget : Measurable (fun arm : Option (Fin p.K) =>
      arm.getD (ReferenceActivePhysicalStep.coordinatorFallback p)) := by
    have hsum : Measurable (fun arm : Fin p.K ⊕ PUnit =>
        Sum.elim id (fun _ => ReferenceActivePhysicalStep.coordinatorFallback p) arm) :=
      measurable_fun_sum measurable_id measurable_const
    have hm := hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit (Fin p.K)))
    convert hm using 1
    funext arm
    cases arm <;> rfl
  exact hget.comp hmap

theorem preparationSelectionData_downView
    {bank : CoordinatorUpReception.UpDecoderBank p}
    {row : CompletePublicTable.CompleteRow p} {time : Fin p.T}
    (cut : OrdinaryCoordinatorPhysicalInterface.Preparation rate bank row time) :
    selectionDataDownView (preparationSelectionData cut) = cut.downView := by
  cases hselection : cut.selection <;>
    simp [preparationSelectionData, selectionDataDownView,
      OrdinaryCoordinatorPhysicalInterface.Preparation.downView, hselection]

theorem preparationSelectionData_arm
    {bank : CoordinatorUpReception.UpDecoderBank p}
    {row : CompletePublicTable.CompleteRow p} {time : Fin p.T}
    (cut : OrdinaryCoordinatorPhysicalInterface.Preparation rate bank row time) :
    selectionDataArm (preparationSelectionData cut) = cut.arm := by
  cases hselection : cut.selection <;>
    simp [preparationSelectionData, selectionDataArm,
      OrdinaryCoordinatorPhysicalInterface.Preparation.arm, hselection]

local instance firstOutcomeTagMeasurableSpace :
    MeasurableSpace ReferenceFirstDispatchMeasurability.FirstOutcomeTag := ⊤
local instance firstOptionalArmMeasurableSpace : MeasurableSpace (Option (Fin p.K)) :=
  FollowerActionMeasurability.optionArmMeasurableSpace p

private theorem measurable_some_Option {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] {f : Ω → A} (hf : Measurable f) :
    Measurable (fun ω => some (f ω)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl.comp hf

/-- Read a first choice view from the same retained observation fields used by
the first operation. -/
def firstViewFromObservation
    (o : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta) :
    ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := o.registers.payload
  pendingAtChoice := by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using
      o.startRoundResult.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p o.startRoundResult.clock.u
  complementWeights := o.registers.complementWeights }

private theorem measurable_firstRegisterCoordinates : Measurable
    (fun r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta =>
      (r.payload, r.time,
        (ReferenceFirstDispatchMeasurability.firstRegisterObservationCode r).2.2.2.2.2)) := by
  let : MeasurableSpace (Finset (ActiveRoundActions.Follower p.m)) := ⊤
  have h : Measurable (ReferenceFirstDispatchMeasurability.firstRegisterObservationCode
      (p := p) (eta := rate.eta)) := comap_measurable _
  exact h.fst.prodMk (h.snd.snd.snd.fst.prodMk h.snd.snd.snd.snd.snd)

theorem measurable_firstViewFromObservation : Measurable
    (firstViewFromObservation (p := p) (rate := rate)) := by
  classical
  let Obs := ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta
  have ho : Measurable (ReferenceFirstDispatchMeasurability.firstDispatchObservationCode
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hr : Measurable (fun o : Obs => o.registers) := ho.snd.snd.snd.fst
  have hreg := (measurable_firstRegisterCoordinates (rate := rate)).comp hr
  have hp := hreg.fst
  have hs : Measurable (fun o : Obs => o.startRoundResult) := ho.snd.snd.fst
  have hw : Measurable (fun o : Obs =>
      ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
        (firstViewFromObservation (rate := rate) o)) := by
    apply measurable_pi_iff.mpr
    intro a
    have hpayload : Measurable (fun o : Obs =>
        LaterAssignmentStartMeasurability.payloadObservation o.registers.payload) :=
      (comap_measurable _).comp hp
    have hmem : MeasurableSet {o : Obs |
        a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet} := by
      simpa only [CanonicalFastSampling.fastArmFinset, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Set.preimage_ofPred_eq,
        LaterAssignmentStartMeasurability.payloadObservation] using
        (measurableSet_notMem_finset a).preimage hpayload.snd.snd.fst
    have hscore := (measurable_pi_apply a).comp hreg.snd.snd
    have hweight := (measurable_of_countable (fun n : ℕ =>
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) n)).comp hscore
    have heq : (fun o : Obs =>
        ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
          (firstViewFromObservation (rate := rate) o) a) = fun o =>
        if a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet then
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            ((ReferenceFirstDispatchMeasurability.firstRegisterObservationCode
              o.registers).2.2.2.2.2 a)
        else 0 := by
      funext o
      change (if ha : a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet then
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (o.registers.complementScores ⟨a, ha⟩) else 0) =
        (if a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet then
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (if ha : a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet then
              o.registers.complementScores ⟨a, ha⟩ else 0) else 0)
      by_cases ha : a ∈ CanonicalFastSampling.fastArmFinset o.registers.payload.slowSet
      · simp only [dite_eq_left ha, ite_eq_left ha]
      · simp only [dite_eq_right ha, ite_eq_right ha]
    rw [heq]
    exact hweight.ite hmem measurable_const
  apply measurable_comap_iff.mpr
  exact hp.prodMk (((measurable_of_countable (fun started :
      CoordinatorPhaseClock.StartRoundResult p => started.pending)).comp hs).prodMk
    (((measurable_of_countable (fun started : CoordinatorPhaseClock.StartRoundResult p =>
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)).comp hs).prodMk hw))

/-- FIRST keeps the observation's real weights, start, and arm. The literal
installation-time test mirrors `Preparation.selectionAt`. -/
def firstPreparationSelectionData
    (z : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta ×
      (CompletePublicTable.CompleteRow p × Fin p.T)) : Option (SelectionData p rate) :=
  match z.1.tag, z.1.arm with
  | .chosen, some arm =>
      if z.1.registers.time = z.2.2 then
        some (firstViewFromObservation z.1, (z.1.startRoundResult, arm))
      else none
  | _, _ => none

theorem measurable_firstPreparationSelectionData : Measurable
    (firstPreparationSelectionData (p := p) (rate := rate)) := by
  classical
  let Obs := ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta
  let X := Obs × (CompletePublicTable.CompleteRow p × Fin p.T)
  have ho : Measurable (fun z : X =>
      ReferenceFirstDispatchMeasurability.firstDispatchObservationCode z.1) :=
    (comap_measurable _).comp measurable_fst
  have hr := (measurable_firstRegisterCoordinates (rate := rate)).comp ho.snd.snd.snd.fst
  let key : X → Bool × (Option (Fin p.K) × Bool) := fun z =>
    (decide (z.1.tag = .chosen), z.1.arm, decide (z.1.registers.time = z.2.2))
  have hkey : Measurable key :=
    ((measurable_from_top : Measurable (fun tag :
      ReferenceFirstDispatchMeasurability.FirstOutcomeTag => decide (tag = .chosen))).comp
        ho.fst).prodMk
      (ho.snd.snd.snd.snd.snd.snd.snd.prodMk
        ((measurable_of_countable (fun times : Fin p.T × Fin p.T =>
          decide (times.1 = times.2))).comp
            (hr.snd.fst.prodMk (measurable_snd.comp measurable_snd))))
  let read : (Bool × (Option (Fin p.K) × Bool)) × X → Option (SelectionData p rate) :=
    fun pair => match pair.1 with
    | (true, some arm, true) =>
        some (firstViewFromObservation pair.2.1, (pair.2.1.startRoundResult, arm))
    | _ => none
  have hread : Measurable read := by
    apply measurable_from_prod_countable_right
    rintro ⟨chosen, arm, aligned⟩
    cases chosen <;> cases arm <;> cases aligned <;>
      first
      | exact measurable_const
      | exact measurable_some_Option
          ((measurable_firstViewFromObservation.comp measurable_fst).prodMk
            (ho.snd.snd.fst.prodMk measurable_const))
  have heq : firstPreparationSelectionData (rate := rate) = fun z => read (key z, z) := by
    funext z
    dsimp only [firstPreparationSelectionData, read, key]
    cases z.1.tag <;> cases z.1.arm <;>
      by_cases htime : z.1.registers.time = z.2.2 <;> simp [htime]
  rw [heq]
  exact hread.comp (hkey.prodMk measurable_id)

private theorem firstPreparationSelectionData_actual
    (d : ReferenceFirstDispatchMeasurability.FirstDomain p) :
    firstPreparationSelectionData (rate := rate)
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d, (d.2, d.1)) =
    some (ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d,
      (ReferenceFirstDispatchMeasurability.firstStartResultAt rate d,
        ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate d)) := by
  obtain ⟨installed, selected, hchosen⟩ :=
    ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen (rate := rate) d
  have hview : firstViewFromObservation
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d) =
      ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d := by
    have hinstall := ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen_installation
      (rate := rate) d installed selected hchosen
    have hleft : firstViewFromObservation
        (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d) =
        ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed := by
      rw [ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_eq_data]
      rw [hinstall]
      simp only [ReferenceFirstDispatchMeasurability.firstDispatchDataAt,
        firstViewFromObservation, ReferenceFirstDispatchMeasurability.firstInstalledChoiceView]
      rw [← ReferenceFirstDispatchMeasurability.firstInstalledStartResultAt]
      rfl
    have hraw : ReferenceFirstDispatchMeasurability.firstOutcomeViewAt rate d =
        some (ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed) := by
      change ReferenceFirstDispatchMeasurability.firstOutcomeView
        (ReferenceFirstDispatchMeasurability.firstOutcomeAt rate d) = _
      rw [hchosen]
      rfl
    have hinstalled : ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed =
        ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d :=
      Option.some.inj (hraw.symm.trans
        (ReferenceFirstDispatchMeasurability.firstOutcomeViewAt_eq_firstChoiceViewAt
          (rate := rate) d))
    exact hleft.trans hinstalled
  have harm : (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d).arm =
      some (ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate d) := by
    rw [ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_eq_data]
    simp only [ReferenceFirstDispatchMeasurability.firstDispatchDataAt]
    rw [← ReferenceFirstDispatchMeasurability.firstChoiceAt_eq_some_actual (rate := rate) d]
  have hobsTime :
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d).registers.time = d.1 := by
    rw [ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_eq_data]
    rfl
  have hobsStart :
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d).startRoundResult =
        ReferenceFirstDispatchMeasurability.firstStartResultAt rate d := by
    rw [ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_eq_data]
    rfl
  simp [firstPreparationSelectionData,
    ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_tag,
    hobsTime, hobsStart, harm, hview]

/-- Decode selected LIVE fields only from O's retained outcome data. -/
def livePreparationSelectionData
    (z : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate)
    (data : ReferenceLiveDispatchOutputMeasurability.OutcomeData p) :
    Option (SelectionData p rate) :=
  match ReferenceLiveDispatchOutputMeasurability.selectedData data with
  | none => none
  | some (started, arm) =>
      some (ReferenceLiveDispatchOutputMeasurability.viewAtStart z started,
        (started, arm))

theorem measurable_livePreparationSelectionData : Measurable
    (fun pair : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate ×
      ReferenceLiveDispatchOutputMeasurability.OutcomeData p =>
        livePreparationSelectionData (rate := rate) pair.1 pair.2) := by
  have hcode : Measurable (fun pair :
      ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate ×
        ReferenceLiveDispatchOutputMeasurability.OutcomeData p =>
          ReferenceLiveDispatchOutputMeasurability.selectedData pair.2) :=
    (measurable_of_countable ReferenceLiveDispatchOutputMeasurability.selectedData).comp
      measurable_snd
  have hf (code : Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)) :
      Measurable (fun z : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate =>
        match code with
        | none => (none : Option (SelectionData p rate))
        | some (started, arm) =>
            some (ReferenceLiveDispatchOutputMeasurability.viewAtStart z started,
              (started, arm))) := by
    cases code with
    | none => exact measurable_const
    | some pair =>
        exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
          ((ReferenceLiveDispatchOutputMeasurability.measurable_viewAtStart pair.1).prodMk
            (measurable_const.prodMk measurable_const))
  have hm : Measurable (fun pair :
      Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K) ×
        ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate =>
          match pair.1 with
          | none => (none : Option (SelectionData p rate))
          | some (started, arm) => some
              (ReferenceLiveDispatchOutputMeasurability.viewAtStart pair.2 started,
                (started, arm))) := measurable_from_prod_countable_right hf
  exact hm.comp (hcode.prodMk measurable_fst)

/-- The collection installation's actual stored time, read from the full
retained observation. -/
def collectionLaterInstalledTime?
    (observation : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) :
    Option (Fin p.T) :=
  match observation with
  | .inl _ => none
  | .inr full => full.2.1.map (fun installed => installed.1.2.time)

theorem measurable_collectionLaterInstalledTime? : Measurable
    (collectionLaterInstalledTime? (p := p) (rate := rate)) := by
  have htime : Measurable (fun installed :
      ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate =>
        installed.1.2.time) :=
    (measurable_of_countable (fun code :
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => code.time)).comp
      (measurable_snd.comp measurable_fst)
  have hsome : Measurable (fun full :
      ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
        full.2.1.map (fun installed => installed.1.2.time)) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap
      (fun installed : ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate =>
        installed.1.2.time) htime
      (fun full : ReferenceCollectionOutcomeMeasurability.FullObservation p rate => full.2.1)
      (measurable_fst.comp measurable_snd)
  exact measurable_fun_sum measurable_const hsome

def collectionPreparationSelectionDataRaw
    (observation : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) :
    Option (SelectionData p rate) :=
  ReferenceCollectionOutcomeMeasurability.selectionFromBoundary observation

private theorem measurable_selectionDataIsSome : Measurable
    (fun code : Option (SelectionData p rate) => code.isSome) := by
  have hsum : Measurable
      (fun code : SelectionData p rate ⊕ PUnit => Sum.elim (fun _ => true) (fun _ => false) code) :=
    measurable_fun_sum measurable_const measurable_const
  have hm := hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit (SelectionData p rate)))
  convert hm using 1
  funext code
  cases code <;> rfl

def collectionPreparationLaterChosen
    (observation : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) : Bool :=
  match observation with
  | .inl _ => false
  | .inr full => decide (full.2.2.1 = .laterChosen)

theorem measurable_collectionPreparationLaterChosen : Measurable
    (collectionPreparationLaterChosen (p := p) (rate := rate)) := by
  have htag : Measurable (fun full :
      ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
        decide (full.2.2.1 = ReferenceCollectionOutcomeMeasurability.CollectionTag.laterChosen)) :=
    (measurable_of_countable (fun tag : ReferenceCollectionOutcomeMeasurability.CollectionTag p =>
      decide (tag = .laterChosen))).comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact measurable_fun_sum measurable_const htag

def collectionPreparationTimeGuard
    (pair : Fin p.T ×
      (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate)) : Bool :=
  match collectionPreparationLaterChosen (rate := rate) pair.2,
      collectionPreparationSelectionDataRaw (rate := rate) pair.2,
      collectionLaterInstalledTime? (rate := rate) pair.2 with
  | true, some _, some selectedTime => decide (selectedTime = pair.1)
  | true, some _, none => false
  | _, _, _ => true

theorem measurable_collectionPreparationTimeGuard : Measurable
    (collectionPreparationTimeGuard (p := p) (rate := rate)) := by
  have hselected : Measurable (fun pair : Fin p.T ×
      (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) =>
        Option.isSome (collectionPreparationSelectionDataRaw (rate := rate) pair.2)) :=
    measurable_selectionDataIsSome.comp
      (ReferenceCollectionOutcomeMeasurability.measurable_selectionFromBoundary.comp
        (measurable_snd : Measurable (fun pair : Fin p.T ×
          (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) => pair.2)))
  have hfields : Measurable (fun pair : Fin p.T ×
      (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) =>
        (pair.1, (collectionPreparationLaterChosen (rate := rate) pair.2,
          (Option.isSome (collectionPreparationSelectionDataRaw (rate := rate) pair.2),
            collectionLaterInstalledTime? (rate := rate) pair.2)))) :=
    measurable_fst.prodMk (measurable_collectionPreparationLaterChosen.comp measurable_snd |>.prodMk
      (hselected.prodMk (measurable_collectionLaterInstalledTime?.comp measurable_snd)))
  have hguard : Measurable
      (fun fields : Fin p.T × (Bool × (Bool × Option (Fin p.T))) =>
        match fields.2.1, fields.2.2.1, fields.2.2.2 with
        | true, true, some selectedTime => decide (selectedTime = fields.1)
        | true, true, none => false
        | _, _, _ => true) := measurable_of_countable _
  have heq : collectionPreparationTimeGuard (rate := rate) = fun pair =>
      (fun fields : Fin p.T × (Bool × (Bool × Option (Fin p.T))) =>
        match fields.2.1, fields.2.2.1, fields.2.2.2 with
        | true, true, some selectedTime => decide (selectedTime = fields.1)
        | true, true, none => false
        | _, _, _ => true)
        (pair.1, (collectionPreparationLaterChosen (rate := rate) pair.2,
          (Option.isSome (collectionPreparationSelectionDataRaw (rate := rate) pair.2),
            collectionLaterInstalledTime? (rate := rate) pair.2))) := by
    funext pair
    cases hlater : collectionPreparationLaterChosen (rate := rate) pair.2 <;>
      cases hsel : ReferenceCollectionOutcomeMeasurability.selectionFromBoundary pair.2 <;>
      cases htime : collectionLaterInstalledTime? (rate := rate) pair.2 <;>
      simp [collectionPreparationTimeGuard, collectionPreparationSelectionDataRaw,
        hlater, hsel, htime]
  rw [heq]
  exact hguard.comp hfields

def collectionPreparationSelectionData
    (time : Fin p.T)
    (observation : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) :
    Option (SelectionData p rate) :=
  if collectionPreparationTimeGuard (rate := rate) (time, observation) then
    collectionPreparationSelectionDataRaw (rate := rate) observation
  else none

theorem measurable_collectionPreparationSelectionData : Measurable
    (fun pair : Fin p.T ×
      (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) =>
        collectionPreparationSelectionData (rate := rate) pair.1 pair.2) := by
  exact Measurable.ite
    (measurableSet_eq_fun measurable_collectionPreparationTimeGuard measurable_const)
    (ReferenceCollectionOutcomeMeasurability.measurable_selectionFromBoundary.comp
      (measurable_snd : Measurable (fun pair : Fin p.T ×
        (Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) => pair.2)))
    measurable_const

private theorem measurable_sumElim_prod {Z X A B Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (a : Z → A ⊕ B) (ha : Measurable a) (x : Z → X) (hx : Measurable x) :
    Measurable (fun z => Sum.elim (fun v => f (v, x z))
      (fun v => g (v, x z)) (a z)) := by
  let lift : (A ⊕ B) × X → Y := fun z =>
    Sum.elim (fun a => f (a, z.2)) (fun b => g (b, z.2)) z.1
  have hlift' : Measurable (fun z : (A ⊕ B) × X =>
      Sum.elim f g (Equiv.sumProdDistrib A B X z)) :=
    (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  have hlift : Measurable lift := by
    convert hlift' using 1
    funext z
    cases z with
    | mk s x => cases s <;> rfl
  exact hlift.comp (ha.prodMk hx)

private theorem measurable_liveCoordinatesOf : Measurable
    (OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf (p := p) (rate := rate)) := by
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))

-- These aliases use the admitted product/sum spaces verbatim. Naming the
-- large factors keeps typeclass search from rebuilding the whole nested code.
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

/-- Read the retained observation without invoking any preparation operation.
The LIVE tag uses only the original live coordinates. Invalid cutoff and
all failure/dagger observations retain no selection. -/
def selectionDataFromObservation
    (pair : OrdinaryCoordinatorLocalMeasurability.PreparationObservationCode p rate ×
      LocalInput p rate) : Option (SelectionData p rate) :=
  match pair.1 with
  | .inl first => firstPreparationSelectionData
      (first, (OrdinaryCoordinatorLocalMeasurability.completeRow pair.2,
        OrdinaryCoordinatorLocalMeasurability.calendarTime pair.2))
  | .inr (.inl data) =>
      match OrdinaryCoordinatorLocalMeasurability.coordinatorCode pair.2 with
      | .inr (.inl live) => livePreparationSelectionData
          (OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf (live, pair.2.2)) data
      | _ => none
  | .inr (.inr (.inl full)) => collectionPreparationSelectionData
      (OrdinaryCoordinatorLocalMeasurability.calendarTime pair.2) (.inr full)
  | _ => none

theorem measurable_selectionDataFromObservation : Measurable
    (selectionDataFromObservation (p := p) (rate := rate)) := by
  let aux := OrdinaryCoordinatorLocalMeasurability.UpDecoderBank p ×
    (CompletePublicTable.CompleteRow p × Fin p.T)
  let Data := ReferenceLiveDispatchOutputMeasurability.OutcomeData p
  let Live := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  let Other := (ReferenceActivePhysicalStep.Payload rate ×
    (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit
  let liveFn : Live × (aux × Data) → Option (SelectionData p rate) := fun z =>
    livePreparationSelectionData (OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf (z.1, z.2.1)) z.2.2
  have hlive : Measurable liveFn :=
    measurable_livePreparationSelectionData.comp
      ((measurable_liveCoordinatesOf.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd))
  let restFn : (Live ⊕ Other) × (aux × Data) → Option (SelectionData p rate) :=
    fun z => Sum.elim (fun live => liveFn (live, z.2)) (fun _ => none) z.1
  have hrest : Measurable restFn :=
    measurable_sumElim_prod liveFn (fun _ : Other × (aux × Data) => none)
      hlive measurable_const Prod.fst measurable_fst Prod.snd measurable_snd
  let bodyFn : OrdinaryCoordinatorLocalMeasurability.CoordinatorCode p rate ×
      (aux × Data) → Option (SelectionData p rate) := fun z =>
    Sum.elim (fun _ => none) (fun rest => restFn (rest, z.2)) z.1
  have hbody : Measurable bodyFn :=
    measurable_sumElim_prod (fun _ : Unit × (aux × Data) => none) restFn
      measurable_const hrest Prod.fst measurable_fst Prod.snd measurable_snd
  let liveRead : Data × LocalInput p rate → Option (SelectionData p rate) := fun z =>
    bodyFn (z.2.1, (z.2.2, z.1))
  have hliveRead : Measurable liveRead := hbody.comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  let firstRead : ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta ×
      LocalInput p rate → Option (SelectionData p rate) := fun z =>
    firstPreparationSelectionData (z.1, (z.2.2.2.1, z.2.2.2.2))
  have hfirstRead : Measurable firstRead := measurable_firstPreparationSelectionData.comp
    (measurable_fst.prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  let collectionRead : ReferenceCollectionOutcomeMeasurability.FullObservation p rate ×
      LocalInput p rate → Option (SelectionData p rate) := fun z =>
    collectionPreparationSelectionData z.2.2.2.2 (.inr z.1)
  have hcollectionRead : Measurable collectionRead :=
    measurable_collectionPreparationSelectionData.comp
      ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
        (measurable_inr.comp measurable_fst))
  let tailRead : (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ⊕
      (Unit ⊕ Unit)) × LocalInput p rate → Option (SelectionData p rate) := fun z =>
    Sum.elim (fun full => collectionRead (full, z.2)) (fun _ => none) z.1
  have htailRead : Measurable tailRead :=
    measurable_sumElim_prod collectionRead (fun _ : (Unit ⊕ Unit) × LocalInput p rate => none)
      hcollectionRead measurable_const Prod.fst measurable_fst Prod.snd measurable_snd
  let restRead : (Data ⊕ (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ⊕
      (Unit ⊕ Unit))) × LocalInput p rate → Option (SelectionData p rate) := fun z =>
    Sum.elim (fun data => liveRead (data, z.2)) (fun tail => tailRead (tail, z.2)) z.1
  have hrestRead : Measurable restRead :=
    measurable_sumElim_prod liveRead tailRead hliveRead htailRead
      Prod.fst measurable_fst Prod.snd measurable_snd
  have hm := measurable_sumElim_prod firstRead restRead hfirstRead hrestRead
    Prod.fst measurable_fst Prod.snd measurable_snd
  convert hm using 1
  funext pair
  rcases pair with ⟨observation, code, bank, row, time⟩
  cases observation with
  | inl first => rfl
  | inr rest => cases rest with
    | inl data => cases code with
      | inl u => rfl
      | inr rest => cases rest <;> rfl
    | inr tail => cases tail with
      | inl full => rfl
      | inr failure => cases failure <;> rfl

/-- The original input is paired with O's retained preparation observation;
its selection readout performs no dispatcher, installation, or choice call. -/
def prepareLocalSelectionData (z : LocalInput p rate) : Option (SelectionData p rate) :=
  selectionDataFromObservation
    (OrdinaryCoordinatorLocalMeasurability.preparationObservation z, z)

theorem measurable_prepareLocalSelectionData :
    Measurable (prepareLocalSelectionData (p := p) (rate := rate)) :=
  measurable_selectionDataFromObservation.comp
    (measurable_swap.comp OrdinaryCoordinatorLocalMeasurability.measurable_prepareLocalCode)

private theorem firstPreparationSelectionData_eq_actualCut
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    firstPreparationSelectionData (rate := rate)
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate (time, row),
        (row, time)) =
      preparationSelectionData
        (bank := bank) (row := row) (time := time)
        (.first (CoordinatorRoundDispatch.dispatchFirst
          (OrdinaryCoordinatorPhysicalInterface.firstInput rate row time))) := by
  let d : ReferenceFirstDispatchMeasurability.FirstDomain p := (time, row)
  obtain ⟨installed, selected, hchosen⟩ :=
    ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen (rate := rate) d
  have hinstall := ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen_installation
    (rate := rate) d installed selected hchosen
  have htime : installed.registers.time = time := by
    rw [hinstall]
    rw [CoordinatorAssignmentRegisterInstall.first_registers_time]
    rfl
  have hstart : installed.startRoundResult =
      ReferenceFirstDispatchMeasurability.firstStartResultAt rate d := by
    rw [hinstall]
    exact ReferenceFirstDispatchMeasurability.firstInstalledStartResultAt (rate := rate) d
  have hview : ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed =
      ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d := by
    have hraw : ReferenceFirstDispatchMeasurability.firstOutcomeViewAt rate d =
        some (ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed) := by
      change ReferenceFirstDispatchMeasurability.firstOutcomeView
        (ReferenceFirstDispatchMeasurability.firstOutcomeAt rate d) = _
      rw [hchosen]
      rfl
    exact Option.some.inj (hraw.symm.trans
      (ReferenceFirstDispatchMeasurability.firstOutcomeViewAt_eq_firstChoiceViewAt
        (rate := rate) d))
  have harm : ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate d = selected.arm := by
    rw [ReferenceFirstDispatchMeasurability.firstOutcomeArmAt_eq_firstChoiceAt (rate := rate) d]
    rw [ReferenceFirstDispatchMeasurability.firstChoiceAt_eq_chosen_arm
      (rate := rate) d installed selected hchosen]
    rfl
  have hdispatch : CoordinatorRoundDispatch.dispatchFirst
      (OrdinaryCoordinatorPhysicalInterface.firstInput rate row time) =
        .chosen installed selected := by
    simpa [ReferenceFirstDispatchMeasurability.firstOutcomeAt,
      ReferenceFirstDispatchMeasurability.firstInputAt,
      OrdinaryCoordinatorPhysicalInterface.firstInput] using hchosen
  have hchoiceView : ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d =
      { payload := installed.registers.payload
        pendingAtChoice := installed.startRoundResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
          installed.startRoundResult.clock.u
        complementWeights := installed.registers.complementWeights } := by
    change ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d =
      ReferenceFirstDispatchMeasurability.firstInstalledChoiceView installed
    exact hview.symm
  calc
    firstPreparationSelectionData (rate := rate)
        (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate d, (row, time)) =
        some (ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate d,
          (ReferenceFirstDispatchMeasurability.firstStartResultAt rate d,
            ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate d)) :=
      firstPreparationSelectionData_actual (rate := rate) d
    _ = preparationSelectionData
        (.first (CoordinatorRoundDispatch.dispatchFirst
          (OrdinaryCoordinatorPhysicalInterface.firstInput rate row time))) := by
      simp [preparationSelectionData, OrdinaryCoordinatorPhysicalInterface.Preparation.selection,
        OrdinaryCoordinatorPhysicalInterface.selectionAt, hdispatch, htime, hstart, hchoiceView,
        harm]
      rfl

private theorem livePreparationSelectionData_eq_actualPreparation
    (coords : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (hrow : coords.2.2.2 = row) (htime : coords.2.2.1 = time) :
    livePreparationSelectionData (rate := rate) coords
      (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates coords))) =
      preparationSelectionData (bank := bank) (row := row) (time := time)
        (.live
          (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters coords.1 coords.2.1)
          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned coords.1 coords.2.1)
          coords.2.1.baseScores
          (CoordinatorRoundDispatch.dispatchLive
            (OrdinaryCoordinatorPhysicalInterface.liveInput row time
              (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters coords.1 coords.2.1)
              (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned coords.1 coords.2.1)
              coords.2.1.baseScores))) := by
  cases hrow
  cases htime
  let row : CompletePublicTable.CompleteRow p := coords.2.2.2
  let time : Fin p.T := coords.2.2.1
  let registers := ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters coords.1 coords.2.1
  let owned := ReferenceActivePhysicalStepMeasurability.decodeLiveOwned coords.1 coords.2.1
  let base := coords.2.1.baseScores
  have hin : OrdinaryCoordinatorPhysicalInterface.liveInput row time registers owned base =
      ReferenceLiveDispatchMeasurability.liveInputOfCoordinates coords := by
    rfl
  have hdata : ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates coords)) =
      ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (OrdinaryCoordinatorPhysicalInterface.liveInput row time registers owned base)) := by
    exact (congrArg (fun input => ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive input)) hin).symm
  rw [hdata]
  cases hdispatch : CoordinatorRoundDispatch.dispatchLive
      (OrdinaryCoordinatorPhysicalInterface.liveInput row time registers owned base) <;>
    simp [livePreparationSelectionData, preparationSelectionData,
      OrdinaryCoordinatorPhysicalInterface.Preparation.selection,
      OrdinaryCoordinatorPhysicalInterface.selectionAt,
      ReferenceLiveDispatchOutputMeasurability.outcomeData,
      ReferenceLiveDispatchOutputMeasurability.dispatchData,
      ReferenceLiveDispatchOutputMeasurability.selectedData,
      ReferenceLiveDispatchOutputMeasurability.viewAtStart,
      OrdinaryCoordinatorPhysicalInterface.liveInput,
      ReferenceLiveDispatchMeasurability.liveInputOfCoordinates,
      ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceActivePhysicalStep.liveOwnedAt,
      ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
      registers, owned, base]

private theorem collectionInstalledObservation_time_eq_requested
    (q : ReferenceCollectionDispatchMeasurability.LocalInput p rate)
    {observed : ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate}
    (hobserved : ReferenceCollectionInstallOutputMeasurability.laterInstalledObservation? q =
      some observed) :
    ∃ started instruction,
      ReferenceCollectionDispatchMeasurability.clockObservation q = .inr started ∧
      started.assignmentStart = some instruction ∧
      observed.1.2.time = instruction.time := by
  classical
  by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceCollectionDispatchMeasurability.assemble q)
  · have hclocked : ReferenceCollectionInstallOutputMeasurability.laterInstalledAtClock
        ⟨q, hcore⟩ (ReferenceCollectionDispatchMeasurability.clockObservation q) =
          some observed := by
      simpa [ReferenceCollectionInstallOutputMeasurability.laterInstalledObservation?, hcore]
        using hobserved
    unfold ReferenceCollectionInstallOutputMeasurability.laterInstalledAtClock at hclocked
    cases hclock : ReferenceCollectionDispatchMeasurability.clockObservation q with
    | inl failure => simp [hclock] at hclocked
    | inr started =>
        by_cases hpending : q.2.1.pending.Nonempty
        · simp [hclock, hpending] at hclocked
        · simp only [hclock, ite_eq_right hpending] at hclocked
          cases hrequest : ReferenceCollectionDispatchMeasurability.requestedInstructionAt
              q (.inr started) with
          | none =>
              simp only [hrequest] at hclocked
              simp at hclocked
          | some instruction =>
              have hinstruction : started.assignmentStart = some instruction := by
                simpa [ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
                  hpending] using hrequest
              simp only [hrequest] at hclocked
              unfold ReferenceCollectionInstallOutputMeasurability.laterInstalledObservation at hclocked
              cases hscore : ReferenceCollectionInstallOutputMeasurability.laterPayloadScore?
                  ⟨q, hcore⟩ instruction with
              | none =>
                  rw [hscore] at hclocked
                  simp at hclocked
              | some payloadScore =>
                  rw [hscore] at hclocked
                  simp only [Option.map_some] at hclocked
                  cases hclocked
                  exact ⟨started, instruction, rfl, hinstruction, rfl⟩
  · simp [ReferenceCollectionInstallOutputMeasurability.laterInstalledObservation?, hcore] at hobserved

private theorem collectionPreparationSelectionData_eq_actualPreparation
    (q : ReferenceCollectionDispatchMeasurability.LocalInput p rate) :
    collectionPreparationSelectionData (rate := rate)
        (ReferenceCollectionDispatchMeasurability.assemble q).time
        (.inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) =
      preparationSelectionData
        (.collection (ReferenceCollectionDispatchMeasurability.assemble q).payload
          (ReferenceCollectionDispatchMeasurability.assemble q).ledger
          (ReferenceCollectionDispatchMeasurability.assemble q).clock
          (ReferenceCollectionDispatchMeasurability.assemble q).cutoffIndex
          (CoordinatorRoundDispatch.dispatchCollection
            (ReferenceCollectionDispatchMeasurability.assemble q))) := by
  classical
  cases hout : CoordinatorRoundDispatch.dispatchCollection
      (ReferenceCollectionDispatchMeasurability.assemble q) with
  | continuing core prepared hboundary hscores =>
      have hexact := ReferenceCollectionOutcomeMeasurability.collectionFullObservation_exact q
      have htag : ReferenceCollectionOutcomeMeasurability.collectionTag q = .continuing := by
        exact hexact.1.trans (by simp [ReferenceCollectionOutcomeMeasurability.outcomeTag, hout])
      have hcode := hexact.2.2
      have hguard : collectionPreparationTimeGuard (rate := rate)
          ((ReferenceCollectionDispatchMeasurability.assemble q).time,
            .inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) = true := by
        simp [collectionPreparationTimeGuard, collectionPreparationLaterChosen,
          ReferenceCollectionOutcomeMeasurability.collectionFullObservation, htag]
      rw [collectionPreparationSelectionData, ite_eq_left hguard]
      change ReferenceCollectionOutcomeMeasurability.collectionSelectionCode q = _
      rw [hcode, hout]
      simp [ReferenceCollectionOutcomeMeasurability.outcomeSelectionCode,
        preparationSelectionData, OrdinaryCoordinatorPhysicalInterface.Preparation.selection,
        ReferenceCollectionDispatchMeasurability.continuingView,
        ReferenceCollectionDispatchMeasurability.assemble,
        OrdinaryCoordinatorPhysicalInterface.collectionInput,
        ReferenceActivePhysicalStep.collectionClock]
  | laterChosen core consistent started hstart instruction hinstruction output hlocal
      clockData installed selected =>
      have hexact := ReferenceCollectionOutcomeMeasurability.collectionFullObservation_exact q
      have htag : ReferenceCollectionOutcomeMeasurability.collectionTag q = .laterChosen := by
        exact hexact.1.trans (by simp [ReferenceCollectionOutcomeMeasurability.outcomeTag, hout])
      have hselection := hexact.2.2
      have hchosen : ReferenceActiveStepCompositionMeasurability.outcomeInstallationCoordinates q
          (CoordinatorRoundDispatch.dispatchCollection
            (ReferenceCollectionDispatchMeasurability.assemble q)) =
          some ((installed.registers.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers
              installed.ownedRegisters installed.retainedBaseScore), started) := by
        rw [hout]
        rfl
      have hinstalled := ReferenceActiveStepCompositionMeasurability.collection_installed_observation
        q ((installed.registers.payload,
          ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers
            installed.ownedRegisters installed.retainedBaseScore), started) hchosen
      obtain ⟨observed, hobserved, _hcoordinates⟩ := hinstalled
      have htime : instruction.time =
          (ReferenceCollectionDispatchMeasurability.assemble q).time :=
        (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
          (ReferenceCollectionDispatchMeasurability.assemble q).time
          (ReferenceCollectionDispatchMeasurability.assemble q).clock
          (ReferenceCollectionDispatchMeasurability.assemble q).ledger.pending
          started instruction core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hinstruction).1
      obtain ⟨observedStarted, observedInstruction, hclock, hrequested, htimeObserved⟩ :=
        collectionInstalledObservation_time_eq_requested q hobserved
      have hclockActual : ReferenceCollectionDispatchMeasurability.clockObservation q =
          .inr started := by
        change (match CoordinatorPhaseClock.startRound p rate.eta.val
            (ReferenceCollectionDispatchMeasurability.assemble q).time
            (ReferenceCollectionDispatchMeasurability.assemble q).clock
            (ReferenceCollectionDispatchMeasurability.assemble q).ledger.pending with
          | .error failure => Sum.inl failure
          | .ok result => Sum.inr result) = .inr started
        have hstart' : CoordinatorPhaseClock.startRound p (↑rate.eta)
            (ReferenceCollectionDispatchMeasurability.assemble q).time
            (ReferenceCollectionDispatchMeasurability.assemble q).clock
            (ReferenceCollectionDispatchMeasurability.assemble q).ledger.pending = .ok started := by
          simpa [ReferenceCollectionDispatchMeasurability.assemble] using hstart
        rw [hstart']
      have hsameStarted : observedStarted = started :=
        Sum.inr.inj (hclock.symm.trans hclockActual)
      have hsameInstruction : observedInstruction = instruction := by
        have hrequested' : started.assignmentStart = some observedInstruction := by
          simpa [hsameStarted] using hrequested
        exact Option.some.inj (hrequested'.symm.trans hinstruction)
      have hobservedTime : observed.1.2.time =
          (ReferenceCollectionDispatchMeasurability.assemble q).time := by
        rw [htimeObserved, hsameInstruction]
        exact htime
      have hreadTime : collectionLaterInstalledTime? (rate := rate)
          (.inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) =
          some ((ReferenceCollectionDispatchMeasurability.assemble q).time) := by
        simp [collectionLaterInstalledTime?,
          ReferenceCollectionOutcomeMeasurability.collectionFullObservation,
          hobserved, hobservedTime]
      have hlater : collectionPreparationLaterChosen (rate := rate)
          (.inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) = true := by
        simp [collectionPreparationLaterChosen,
          ReferenceCollectionOutcomeMeasurability.collectionFullObservation, htag]
      have hraw : collectionPreparationSelectionDataRaw (rate := rate)
          (.inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) =
          some ({ payload := installed.registers.payload
                  pendingAtChoice := started.pending
                  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
                  complementWeights := installed.registers.complementWeights },
            (started, selected.arm)) := by
        change ReferenceCollectionOutcomeMeasurability.collectionSelectionCode q = _
        rw [hselection, hout]
        rfl
      have hguard : collectionPreparationTimeGuard (rate := rate)
          ((ReferenceCollectionDispatchMeasurability.assemble q).time,
            .inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) = true := by
        unfold collectionPreparationTimeGuard
        rw [hlater, hraw, hreadTime]
        simp
      rw [collectionPreparationSelectionData, ite_eq_left hguard]
      change ReferenceCollectionOutcomeMeasurability.collectionSelectionCode q = _
      rw [hselection, hout]
      simp [ReferenceCollectionOutcomeMeasurability.outcomeSelectionCode,
        preparationSelectionData, OrdinaryCoordinatorPhysicalInterface.Preparation.selection,
        OrdinaryCoordinatorPhysicalInterface.selectionAt, htime,
        ReferenceCollectionDispatchMeasurability.assemble]
      rfl
  | clockFailure failure hstart
  | localFailure _ hstart _ _
  | coreFailure _ _ hstart _
  | laterReconstructionFailure _ _ _ hstart _ _ _
  | laterPrefixFailure _ _ _ hstart _ _ _ _
  | laterOrientationFailure _ _ _ hstart _ _ _ _
  | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
      have hexact := ReferenceCollectionOutcomeMeasurability.collectionFullObservation_exact q
      have htag := hexact.1
      have hcode := hexact.2.2
      have hguard : collectionPreparationTimeGuard (rate := rate)
          ((ReferenceCollectionDispatchMeasurability.assemble q).time,
            .inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) = true := by
        simp [collectionPreparationTimeGuard, collectionPreparationLaterChosen,
          ReferenceCollectionOutcomeMeasurability.collectionFullObservation,
          ReferenceCollectionOutcomeMeasurability.outcomeTag, hout, htag]
      rw [collectionPreparationSelectionData, ite_eq_left hguard]
      change ReferenceCollectionOutcomeMeasurability.collectionSelectionCode q = _
      rw [hcode, hout]
      simp [ReferenceCollectionOutcomeMeasurability.outcomeSelectionCode,
        preparationSelectionData, OrdinaryCoordinatorPhysicalInterface.Preparation.selection]

/-- The retained branch observation projects to exactly the data projection
of C's actual preparation selection on every original coordinator input. -/
theorem prepareLocalSelectionData_eq_actualCut (z : LocalInput p rate) :
    prepareLocalSelectionData (rate := rate) z =
      preparationSelectionData (OrdinaryCoordinatorLocalMeasurability.cut z) := by
  rcases z with ⟨code, bank, row, time⟩
  cases code with
  | inl u =>
      have hfirst := firstPreparationSelectionData_eq_actualCut (rate := rate) bank row time
      simpa [prepareLocalSelectionData, selectionDataFromObservation,
        OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
        OrdinaryCoordinatorLocalMeasurability.preparationObservation,
        OrdinaryCoordinatorLocalMeasurability.firstDomainOf,
        OrdinaryCoordinatorLocalMeasurability.completeRow,
        OrdinaryCoordinatorLocalMeasurability.calendarTime,
        OrdinaryCoordinatorLocalMeasurability.decoderBank,
        OrdinaryCoordinatorLocalMeasurability.cut,
        OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
        ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
        OrdinaryCoordinatorPhysicalInterface.prepareLocal_first] using hfirst
  | inr rest => cases rest with
    | inl live =>
        rcases live with ⟨payload, live⟩
        let coords := OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf
          ((payload, live), (bank, (row, time)))
        have hlive := livePreparationSelectionData_eq_actualPreparation (rate := rate)
          coords bank row time rfl rfl
        simpa [prepareLocalSelectionData, selectionDataFromObservation,
          OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
          OrdinaryCoordinatorLocalMeasurability.preparationObservation,
          OrdinaryCoordinatorLocalMeasurability.completeRow,
          OrdinaryCoordinatorLocalMeasurability.calendarTime,
          OrdinaryCoordinatorLocalMeasurability.decoderBank,
          OrdinaryCoordinatorLocalMeasurability.liveCoordinatesOf,
          OrdinaryCoordinatorLocalMeasurability.cut,
          OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
          ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
          ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
          ReferenceActivePhysicalStepMeasurability.decodeLiveOwned,
          OrdinaryCoordinatorPhysicalInterface.prepareLocal_live,
          coords] using hlive
    | inr rest => cases rest with
      | inl collection =>
          rcases collection with ⟨payload, ledger, proposal⟩
          by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
            let q : ReferenceCollectionDispatchMeasurability.LocalInput p rate :=
              ((payload, row), ledger, proposal, bank, time, cutoff)
            have hcollection := collectionPreparationSelectionData_eq_actualPreparation
              (rate := rate) q
            have hselectionData : prepareLocalSelectionData (rate := rate)
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                collectionPreparationSelectionData (rate := rate) time
                  (.inr (ReferenceCollectionOutcomeMeasurability.collectionFullObservation q)) := by
              simp [prepareLocalSelectionData, selectionDataFromObservation,
                OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
                OrdinaryCoordinatorLocalMeasurability.preparationObservation,
                OrdinaryCoordinatorLocalMeasurability.completeRow,
                OrdinaryCoordinatorLocalMeasurability.calendarTime,
                OrdinaryCoordinatorLocalMeasurability.decoderBank,
                OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
                OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
                ReferenceCollectionOutcomeMeasurability.boundaryFullObservation,
                ReferenceCollectionDispatchMeasurability.boundaryLocal,
                ReferenceCollectionDispatchMeasurability.cutoffValid,
                cutoff, q, hcutoff]
            have hactual : OrdinaryCoordinatorLocalMeasurability.cut
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                .collection payload ledger
                  (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff)
                  cutoff
                  (CoordinatorRoundDispatch.dispatchCollection
                    (OrdinaryCoordinatorPhysicalInterface.collectionInput bank row time payload
                      ledger
                      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff)
                      cutoff)) := by
              change OrdinaryCoordinatorPhysicalInterface.prepareLocal
                  (.collection payload ledger proposal) bank row time = _
              exact OrdinaryCoordinatorPhysicalInterface.prepareLocal_collection
                bank row time payload ledger proposal hcutoff
            rw [hselectionData, hactual]
            exact hcollection
          · have hselectionData : prepareLocalSelectionData (rate := rate)
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) = none := by
              simp [prepareLocalSelectionData, selectionDataFromObservation,
              OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
              OrdinaryCoordinatorLocalMeasurability.preparationObservation,
              OrdinaryCoordinatorLocalMeasurability.collectionBoundaryObservation,
              OrdinaryCoordinatorLocalMeasurability.tagCollectionBoundary,
              ReferenceCollectionOutcomeMeasurability.boundaryFullObservation,
              ReferenceCollectionDispatchMeasurability.cutoffValid,
              hcutoff]
            have hactual : OrdinaryCoordinatorLocalMeasurability.cut
                ((.inr (.inr (.inl (payload, ledger, proposal)))), (bank, (row, time))) =
                .invalidCollectionCutoff := by
              change OrdinaryCoordinatorPhysicalInterface.prepareLocal
                  (.collection payload ledger proposal) bank row time = _
              exact OrdinaryCoordinatorPhysicalInterface.prepareLocal_invalidCollectionCutoff
                bank row time payload ledger proposal hcutoff
            rw [hselectionData, hactual]
            simp [preparationSelectionData,
              OrdinaryCoordinatorPhysicalInterface.Preparation.selection]
      | inr dagger =>
          let daggerCode : OrdinaryCoordinatorLocalMeasurability.CoordinatorCode p rate :=
            .inr (.inr (.inr dagger))
          have hdagger : OrdinaryCoordinatorLocalMeasurability.cut
              (daggerCode, (bank, (row, time))) =
                (OrdinaryCoordinatorPhysicalInterface.Preparation.dagger :
                  OrdinaryCoordinatorPhysicalInterface.Preparation rate bank row time) := by
            change OrdinaryCoordinatorPhysicalInterface.prepareLocal
                .dagger bank row time = _
            exact OrdinaryCoordinatorPhysicalInterface.prepareLocal_dagger bank row time
          rw [hdagger]
          simp [prepareLocalSelectionData, selectionDataFromObservation,
            OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
            OrdinaryCoordinatorLocalMeasurability.preparationObservation,
            preparationSelectionData,
            OrdinaryCoordinatorPhysicalInterface.Preparation.selection]

/-- Actual configurations specialize through O's lossless coordinator
encoding; no normalization of arbitrary raw coordinator codes is asserted. -/
theorem prepareLocalSelectionData_encodeCoordinator
    (q : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    prepareLocalSelectionData
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator q, (bank, (row, time))) =
      preparationSelectionData
        (OrdinaryCoordinatorPhysicalInterface.prepareLocal q bank row time) := by
  rw [prepareLocalSelectionData_eq_actualCut]
  change preparationSelectionData (OrdinaryCoordinatorPhysicalInterface.prepareLocal
    (OrdinaryCoordinatorLocalMeasurability.decodedCoordinator
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator q, (bank, (row, time))))
    bank row time) = _
  rw [OrdinaryCoordinatorLocalMeasurability.decodedCoordinator_encodeCoordinator]

/-- No selection data means exactly the actual no-selection branch. -/
theorem prepareLocalSelectionData_eq_none_iff (z : LocalInput p rate) :
    prepareLocalSelectionData z = none ↔
      (OrdinaryCoordinatorLocalMeasurability.cut z).selection = none := by
  rw [prepareLocalSelectionData_eq_actualCut]
  cases hselection : (OrdinaryCoordinatorLocalMeasurability.cut z).selection <;>
    simp only [preparationSelectionData, hselection, Option.map_none, Option.map_some,
      Option.some_ne_none, iff_self]

/-- The sole conditional input is the literal result of this selection-data
producer. The actual preparation then uses the source fallback and no DOWN view. -/
theorem prepareLocal_fallback_of_selectionData_none (z : LocalInput p rate)
    (hselection : prepareLocalSelectionData z = none) :
    (OrdinaryCoordinatorLocalMeasurability.cut z).arm =
        ReferenceActivePhysicalStep.coordinatorFallback p ∧
      (OrdinaryCoordinatorLocalMeasurability.cut z).downView = none :=
  OrdinaryCoordinatorPhysicalInterface.Preparation.fallback_of_selection_none
    (OrdinaryCoordinatorLocalMeasurability.cut z)
    ((prepareLocalSelectionData_eq_none_iff z).mp hselection)

/-- Unconditional Borel measurability of the actual prepared arm, including
the source fallback on every branch without a selection. -/
theorem measurable_prepareLocalArm : Measurable
    (fun z : LocalInput p rate =>
      (OrdinaryCoordinatorLocalMeasurability.cut z).arm) := by
  have heq : (fun z : LocalInput p rate =>
      (OrdinaryCoordinatorLocalMeasurability.cut z).arm) =
      fun z => selectionDataArm (prepareLocalSelectionData (rate := rate) z) := by
    funext z
    rw [prepareLocalSelectionData_eq_actualCut]
    exact (preparationSelectionData_arm (OrdinaryCoordinatorLocalMeasurability.cut z)).symm
  rw [heq]
  exact measurable_selectionDataArm.comp measurable_prepareLocalSelectionData

/-- Unconditional Borel measurability of the actual prepared DOWN view. -/
theorem measurable_prepareLocalDownView : Measurable
    (fun z : LocalInput p rate =>
      (OrdinaryCoordinatorLocalMeasurability.cut z).downView) := by
  have heq : (fun z : LocalInput p rate =>
      (OrdinaryCoordinatorLocalMeasurability.cut z).downView) =
      fun z => selectionDataDownView (prepareLocalSelectionData (rate := rate) z) := by
    funext z
    rw [prepareLocalSelectionData_eq_actualCut]
    exact (preparationSelectionData_downView
      (OrdinaryCoordinatorLocalMeasurability.cut z)).symm
  rw [heq]
  exact measurable_selectionDataDownView.comp measurable_prepareLocalSelectionData

end Bandits.Support.OrdinaryCoordinatorPreparationSelectionMeasurability

end
