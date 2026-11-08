/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchPhysicalStep
public import Bandits.Support.ReferenceActiveStepCompositionMeasurability

/-!
# Borel coding of the actual ordinary coordinator's local operations

The input is the existing coordinator storage code, decoder bank, complete
selected row, and current calendar time. The local cut and its own-feedback
observer are the ordinary operations from
`OrdinaryCoordinatorPhysicalInterface`; no reference sent-word filter, actual
follower profile, history, or probability law is introduced here.

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
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.OrdinaryCoordinatorLocalMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance firstSlowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤
local instance firstStartRoundResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
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

abbrev CoordinatorCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate
abbrev UpDecoderBank (p : Parameters) := CoordinatorUpReception.UpDecoderBank p
abbrev CompleteRow (p : Parameters) := CompletePublicTable.CompleteRow p

/-- The complete input to one ordinary coordinator local operation. Every
coordinate uses the existing product and sum Borel spaces. -/
abbrev LocalInput (p : Parameters) (rate : RateInput p) :=
  CoordinatorCode p rate × (UpDecoderBank p × (CompleteRow p × Fin p.T))

def coordinatorCode (z : LocalInput p rate) : CoordinatorCode p rate := z.1
def decoderBank (z : LocalInput p rate) : UpDecoderBank p := z.2.1
def completeRow (z : LocalInput p rate) : CompleteRow p := z.2.2.1
def calendarTime (z : LocalInput p rate) : Fin p.T := z.2.2.2

/-- The exact current coordinator configuration obtained from the admitted
lossless storage decoder. -/
def decodedCoordinator (z : LocalInput p rate) :
    CoordinatorConfiguration p rate :=
  ReferenceActivePhysicalStepMeasurability.decodeCoordinator (coordinatorCode z)

/-- The literal accepted coordinator preparation on the retained storage. -/
def cut (z : LocalInput p rate) :
    OrdinaryCoordinatorPhysicalInterface.Preparation rate (decoderBank z)
      (completeRow z) (calendarTime z) :=
  OrdinaryCoordinatorPhysicalInterface.prepareLocal (decodedCoordinator z)
    (decoderBank z) (completeRow z) (calendarTime z)

/-- Lossless branch observations used by the local preparation decoder. The
five tags distinguish first, live, valid collection, invalid collection
cutoff, and dagger. -/
abbrev PreparationObservationCode (p : Parameters) (rate : RateInput p) :=
  ReferenceFirstDispatchMeasurability.FirstDispatchObservation p rate.eta ⊕
    (ReferenceLiveDispatchOutputMeasurability.OutcomeData p ⊕
      (ReferenceCollectionOutcomeMeasurability.FullObservation p rate ⊕
        (Unit ⊕ Unit)))

/-- Reindex the complete root coordinates to the original first-dispatch
domain without changing the selected row or calendar time. -/
def firstDomainOf (z : LocalInput p rate) :
    ReferenceFirstDispatchMeasurability.FirstDomain p :=
  (calendarTime z, completeRow z)

/-- The live dispatcher receives the same payload, original lossless live
register code, whole row, and time as the stored coordinator branch. -/
def liveCoordinatesOf (z :
    (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (UpDecoderBank p × (CompleteRow p × Fin p.T))) :
    ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate :=
  (z.1.1, (z.1.2, (z.2.2.2, z.2.2.1)))

/-- Collection PREPARE retains its literal cutoff validity result. The
collection boundary producer sees the existing payload, ledger, proposal,
bank, whole row, and time. -/
def collectionBoundaryObservation (z :
    (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ×
        (UpDecoderBank p × (CompleteRow p × Fin p.T))) :
    Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate :=
  ReferenceCollectionOutcomeMeasurability.boundaryFullObservation
    ((z.1.1, z.2.2.1), z.1.2.1, z.1.2.2, z.2.1, z.2.2.2)

/-- Turn the boundary producer's explicit invalid-cutoff arm into its own
source branch tag; valid outcomes retain the complete admitted observation. -/
def tagCollectionBoundary
    (o : Unit ⊕ ReferenceCollectionOutcomeMeasurability.FullObservation p rate) :
  PreparationObservationCode p rate :=
  Sum.elim (fun _ : Unit => .inr (.inr (.inr (.inl ()))))
    (fun full => .inr (.inr (.inl full))) o

/-- The exact transient branch observation generated from the existing
coordinator code. No operation result is assumed measurable in this
definition. -/
def preparationObservation (z : LocalInput p rate) :
    PreparationObservationCode p rate :=
  match coordinatorCode z with
  | .inl _ => .inl
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate
        (firstDomainOf z))
  | .inr (.inl (payload, live)) => .inr (.inl
      (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
            (liveCoordinatesOf ((payload, live), (decoderBank z,
              (completeRow z, calendarTime z))))))))
  | .inr (.inr (.inl (payload, ledger, proposal))) =>
      tagCollectionBoundary
        (collectionBoundaryObservation ((payload, (ledger, proposal)),
          (decoderBank z, (completeRow z, calendarTime z))))
  | .inr (.inr (.inr _)) => .inr (.inr (.inr (.inr ())))

/-- Original input plus the existing branch observation. This code carries
the exact source coordinates needed to restore dependent proof fields. -/
abbrev PreparationCode (p : Parameters) (rate : RateInput p) := LocalInput p rate ×
  PreparationObservationCode p rate

local instance preparationCodeMeasurableSpace :
    MeasurableSpace (PreparationCode p rate) :=
  MeasurableSpace.prod
    (inferInstance : MeasurableSpace (LocalInput p rate))
    (inferInstance : MeasurableSpace (PreparationObservationCode p rate))

def prepareLocalCode (z : LocalInput p rate) : PreparationCode p rate :=
  (z, preparationObservation z)

@[simp] theorem prepareLocalCode_input (z : LocalInput p rate) :
    (prepareLocalCode z).1 = z := rfl

@[simp] theorem prepareLocalCode_observation (z : LocalInput p rate) :
    (prepareLocalCode z).2 = preparationObservation z := rfl

/-- On an encoded actual coordinator, the decoder used by the root is exactly
the admitted lossless coordinator decoder. -/
theorem decodedCoordinator_encodeCoordinator
    (q : CoordinatorConfiguration p rate) (bank : UpDecoderBank p)
    (row : CompleteRow p) (time : Fin p.T) :
    decodedCoordinator
      ((ReferenceActivePhysicalStepMeasurability.encodeCoordinator q,
        (bank, (row, time)))) = q := by
  change ReferenceActivePhysicalStepMeasurability.decodeCoordinator
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator q) = q
  exact ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator q

private theorem measurable_sumElim_comp {X A B Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (a : X → A ⊕ B) (ha : Measurable a) :
    Measurable (fun x => Sum.elim (fun v => f (v, x)) (fun v => g (v, x)) (a x)) := by
  have h := (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  convert h.comp (ha.prodMk measurable_id) using 1
  funext x
  change Sum.elim _ _ (a x) = Sum.elim f g ((Equiv.sumProdDistrib A B X) (a x, x))
  cases a x <;> rfl

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
    (hf.sumElim hg).comp
      (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  have hlift : Measurable lift := by
    convert hlift' using 1
    funext z
    cases z with
    | mk s x => cases s <;> rfl
  have hp : Measurable (fun z => (a z, x z)) := ha.prodMk hx
  have heq : (fun z => Sum.elim (fun v => f (v, x z))
      (fun v => g (v, x z)) (a z)) =
      (fun z => lift (a z, x z)) := by
    funext z
    cases a z <;> rfl
  rw [heq]
  exact hlift.comp hp

private theorem measurable_liveCoordinatesOf : Measurable
    (liveCoordinatesOf (p := p) (rate := rate)) := by
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))

private theorem measurable_collectionBoundaryObservation : Measurable
    (collectionBoundaryObservation (p := p) (rate := rate)) := by
  unfold collectionBoundaryObservation
  let X :=
    (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ×
      (UpDecoderBank p × (CompleteRow p × Fin p.T))
  exact ReferenceCollectionOutcomeMeasurability.measurable_boundaryFullObservation_comp
    (fun z : X => z.1.1) (fun z : X => z.1.2.1) (fun z : X => z.1.2.2)
    (fun z : X => z.2.1) (fun z : X => z.2.2.1) (fun z : X => z.2.2.2)
    (measurable_fst.comp measurable_fst)
    (measurable_fst.comp (measurable_snd.comp measurable_fst))
    (measurable_snd.comp (measurable_snd.comp measurable_fst))
    (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

private theorem measurable_tagCollectionBoundary : Measurable
    (tagCollectionBoundary (p := p) (rate := rate)) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_inr.comp (measurable_inr.comp (measurable_inl.comp measurable_id))

private theorem measurable_preparationObservation : Measurable
    (preparationObservation (p := p) (rate := rate)) := by
  let aux := UpDecoderBank p × (CompleteRow p × Fin p.T)
  let firstFn : Unit × aux → PreparationObservationCode p rate := fun z =>
    .inl (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate
      (z.2.2.2, z.2.2.1))
  have hfirst : Measurable firstFn := by
    have htime : Measurable (fun z : Unit × aux => z.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hrow : Measurable (fun z : Unit × aux => z.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact measurable_inl.comp
      (ReferenceFirstDispatchMeasurability.measurable_firstDispatchObservationAt.comp
        (htime.prodMk hrow))
  let liveFn :
      (ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) × aux →
          PreparationObservationCode p rate := fun z =>
    .inr (.inl (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
          (liveCoordinatesOf z)))))
  have hlive : Measurable liveFn := by
    exact measurable_inr.comp (measurable_inl.comp
      (ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData.comp
        (measurable_liveCoordinatesOf (p := p) (rate := rate))))
  let collectionComponent := ReferenceActivePhysicalStep.Payload rate ×
    (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))
  let collectionFn : collectionComponent × aux → PreparationObservationCode p rate := fun z =>
    tagCollectionBoundary (collectionBoundaryObservation z)
  have hcollection : Measurable collectionFn :=
    (measurable_tagCollectionBoundary (p := p) (rate := rate)).comp
      (measurable_collectionBoundaryObservation (p := p) (rate := rate))
  let daggerFn : Unit × aux → PreparationObservationCode p rate := fun _ =>
    .inr (.inr (.inr (.inr ())))
  have hdagger : Measurable daggerFn := measurable_const
  let tailFn : (collectionComponent ⊕ Unit) × aux → PreparationObservationCode p rate :=
    fun z => Sum.elim (fun d => collectionFn (d, z.2))
      (fun u => daggerFn (u, z.2)) z.1
  have htail : Measurable tailFn :=
    measurable_sumElim_prod
      collectionFn daggerFn hcollection hdagger Prod.fst measurable_fst Prod.snd measurable_snd
  let restFn :
      ((ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
          (collectionComponent ⊕ Unit)) × aux → PreparationObservationCode p rate :=
    fun z => Sum.elim (fun l => liveFn (l, z.2))
      (fun c => tailFn (c, z.2)) z.1
  have hrest : Measurable restFn :=
    measurable_sumElim_prod
      liveFn tailFn hlive htail
      Prod.fst measurable_fst Prod.snd measurable_snd
  let bodyFn : CoordinatorCode p rate × aux → PreparationObservationCode p rate :=
    fun z => Sum.elim (fun u => firstFn (u, z.2))
      (fun r => restFn (r, z.2)) z.1
  have hbody : Measurable bodyFn :=
    measurable_sumElim_prod
      firstFn restFn hfirst hrest
      Prod.fst measurable_fst Prod.snd measurable_snd
  have hEq : (fun z : LocalInput p rate => preparationObservation z) =
      (fun z => bodyFn (z.1, z.2)) := by
    funext z
    rcases z with ⟨code, restInput⟩
    rcases restInput with ⟨bank, restInput⟩
    rcases restInput with ⟨row, time⟩
    cases code with
    | inl _ => simp [preparationObservation, coordinatorCode, firstDomainOf,
        calendarTime, completeRow, bodyFn, firstFn]
    | inr rest => cases rest with
      | inl live => simp [preparationObservation, coordinatorCode,
          calendarTime, completeRow, decoderBank, liveCoordinatesOf,
          bodyFn, restFn, liveFn]
      | inr tail => cases tail with
        | inl collection => simp [preparationObservation, coordinatorCode,
            calendarTime, completeRow, decoderBank, collectionBoundaryObservation,
            tagCollectionBoundary, bodyFn,
            restFn, tailFn, collectionFn]
        | inr _ => simp [preparationObservation, coordinatorCode, bodyFn,
            restFn, tailFn, daggerFn]
  change Measurable (fun z : LocalInput p rate => preparationObservation z)
  rw [hEq]
  exact hbody.comp (measurable_fst.prodMk measurable_snd)

/-- Joint Borel measurability of the stored original input and the complete
first/live/collection/dagger branch observation. -/
theorem measurable_prepareLocalCode :
    Measurable (prepareLocalCode (p := p) (rate := rate)) := by
  change Measurable (fun z : LocalInput p rate =>
    (z, preparationObservation z))
  exact measurable_id.prodMk measurable_preparationObservation

end Bandits.Support.OrdinaryCoordinatorLocalMeasurability
end
