/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionDispatchMeasurability

/-!
# Measurable installation output for the collection dispatcher

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-70,235-260` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,46-64`.

This module observes only the actual later-installation component. It retains
the original payload, ledger-derived live registers, complete row, installed
base scores, and every post-install guard. Invalid or unsuccessful later
operations remain absent. No full-dispatcher gluing or manuscript closure is
claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceCollectionDispatchMeasurability
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CoordinatorLiveChoiceRecorderStep

namespace Bandits.Support.ReferenceCollectionInstallOutputMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : RateInput p}

/-- A measurable dependent version of mapping an option-valued output. The
secondary input is retained only on the `some` branch. -/
theorem measurable_optionMapDependent {X A C : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace C]
    (f : A × X → C) (hf : Measurable f) (g : X → Option A) (hg : Measurable g) :
    Measurable (fun x => (g x).map fun a => f (a, x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => Equiv.optionEquivSumPUnit C
    ((g x).map fun a => f (a, x)))
  have hsource : Measurable (fun x => Equiv.optionEquivSumPUnit A (g x)) :=
    measurable_comap_iff.mp hg
  let distrib := MeasurableEquiv.sumProdDistrib A PUnit X
  let left : A × X → C ⊕ PUnit := fun q => Sum.inl (f q)
  let right : PUnit × X → C ⊕ PUnit := fun _ => Sum.inr PUnit.unit
  have hleft : Measurable left := measurable_inl.comp hf
  have hright : Measurable right := measurable_const
  let lift : (A ⊕ PUnit) × X → C ⊕ PUnit :=
    fun q => Sum.elim left right (distrib q)
  have hlift : Measurable lift := (hleft.sumElim hright).comp distrib.measurable_toFun
  have hpair : Measurable (fun x =>
      (Equiv.optionEquivSumPUnit A (g x), x)) := hsource.prodMk measurable_id
  have heq : (fun x => Equiv.optionEquivSumPUnit C
      ((g x).map fun a => f (a, x))) = lift ∘ fun x =>
        (Equiv.optionEquivSumPUnit A (g x), x) := by
    funext x
    cases hvalue : g x <;> simp [hvalue, lift, left, right, distrib,
      Equiv.optionEquivSumPUnit, MeasurableEquiv.sumProdDistrib,
      Equiv.sumProdDistrib, Sum.map]
  rw [heq]
  exact hlift.comp hpair

local instance installStartResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance installStartResultDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⟨fun _ => trivial⟩
local instance installInstructionMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤
local instance installInstructionDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  ⟨fun _ => trivial⟩
local instance installInstructionOptionMeasurableSpace :
    MeasurableSpace (Option (CoordinatorPhaseClock.AssignmentStartInstruction p)) := ⊤
attribute [local instance]
  ReferenceDownReceptionMeasurability.choiceCutoffMeasurableSpace
local instance installClockFailureMeasurableSpace :
    MeasurableSpace CoordinatorPhaseClock.ClockFailure := ⊤
local instance installClockFailureDiscreteMeasurableSpace :
    DiscreteMeasurableSpace CoordinatorPhaseClock.ClockFailure := ⟨fun _ => trivial⟩
local instance installClockObservationMeasurableSpace :
    MeasurableSpace (ClockObservation p) := ⊤

/-- The literal code for a newly installed assignment: its complete payload
and the existing discrete live-register code. -/
abbrev InstallationCoordinates (p : Parameters) (rate : RateInput p) :=
  Payload rate × LiveDiscrete p

/-- Read all live discrete fields from the same successful reconstruction,
the old collection ledger, the selected instruction, and its started clock. -/
def installationCoordinates
    (payloadScore : Payload rate × (Fin (p.m - 1) → ℕ))
    (ledger : Ledger rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (started : CoordinatorPhaseClock.StartRoundResult p) : InstallationCoordinates p rate :=
  (payloadScore.1, {
    clockSigma := started.clock.sigma
    clockCutoff := started.clock.u
    clockBoundary := started.clock.g
    clockProposal := started.clock.lastProposal
    pending := started.pending
    time := instruction.time
    gridBoundary := started.clock.g
    scores := extendComplement payloadScore.1 (fun a =>
      ((ledger.cutoffRegisters a).map fun r => r.score + ledger.increment a).getD 0)
    queues := extendComplement payloadScore.1 (fun a =>
      ((ledger.currentRegisters a).map fun r => r.queue).getD 0)
    previousServices := extendComplement payloadScore.1 (fun a =>
      ((ledger.currentRegisters a).map fun r => r.lastService).getD 0)
    baseScores := payloadScore.2 })

/-- The code projection is jointly Borel; only the existing discrete register
coordinates are countable, while the complete original payload is retained. -/
theorem measurable_installationCoordinates : Measurable
    (fun z : (Payload rate × (Fin (p.m - 1) → ℕ)) ×
      (Ledger rate × (CoordinatorPhaseClock.AssignmentStartInstruction p ×
        CoordinatorPhaseClock.StartRoundResult p)) =>
      installationCoordinates z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hk : Measurable (fun z : (Payload rate × (Fin (p.m - 1) → ℕ)) ×
      (Ledger rate × (CoordinatorPhaseClock.AssignmentStartInstruction p ×
        CoordinatorPhaseClock.StartRoundResult p)) =>
      ((z.1.1.slowSet, z.1.2), z.2)) :=
    ((measurable_payloadSlowSet.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  let f : (CanonicalOrientedSetLaw.SlowSet p.K p.m × (Fin (p.m - 1) → ℕ)) ×
      (Ledger rate × (CoordinatorPhaseClock.AssignmentStartInstruction p ×
        CoordinatorPhaseClock.StartRoundResult p)) → LiveDiscrete p := fun k => {
    clockSigma := k.2.2.2.clock.sigma
    clockCutoff := k.2.2.2.clock.u
    clockBoundary := k.2.2.2.clock.g
    clockProposal := k.2.2.2.clock.lastProposal
    pending := k.2.2.2.pending
    time := k.2.2.1.time
    gridBoundary := k.2.2.2.clock.g
    scores := fun a => if a ∈ CanonicalFastSampling.fastArmFinset k.1.1 then
      ((k.2.1.cutoffRegisters a).map fun r => r.score + k.2.1.increment a).getD 0 else 0
    queues := fun a => if a ∈ CanonicalFastSampling.fastArmFinset k.1.1 then
      ((k.2.1.currentRegisters a).map fun r => r.queue).getD 0 else 0
    previousServices := fun a => if a ∈ CanonicalFastSampling.fastArmFinset k.1.1 then
      ((k.2.1.currentRegisters a).map fun r => r.lastService).getD 0 else 0
    baseScores := k.1.2 }
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_of_countable f).comp hk)

/-- The selected view decodes the installed live weights and keeps the whole
continuous payload anchor in its original Borel carrier. -/
def installedView (c : InstallationCoordinates p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := c.1
  pendingAtChoice := started.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  complementWeights :=
    (decodeLiveRegisters c.1 c.2).complementWeights }

/-- Joint Borel measurability of the retained payload and installed choice
view, including the exact complement weights decoded from the live code. -/
theorem measurable_installedView : Measurable
    (fun z : InstallationCoordinates p rate × CoordinatorPhaseClock.StartRoundResult p =>
      installedView z.1 z.2) := by
  apply measurable_comap_iff.mpr
  have hp : Measurable (fun z : InstallationCoordinates p rate ×
      CoordinatorPhaseClock.StartRoundResult p => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hk : Measurable (fun z : InstallationCoordinates p rate ×
      CoordinatorPhaseClock.StartRoundResult p => (z.1.1.slowSet, z.1.2, z.2)) :=
    (measurable_payloadSlowSet.comp hp).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  let f : CanonicalOrientedSetLaw.SlowSet p.K p.m ×
      (LiveDiscrete p × CoordinatorPhaseClock.StartRoundResult p) →
      Finset (ActiveRoundActions.Follower p.m) ×
        (Option (CoordinatorLocalArmChoice.Cutoff p) × (Fin p.K → ℝ)) := fun k =>
    (k.2.2.pending, CoordinatorLiveChoiceRecorderStep.cutoffFromClock p k.2.2.clock.u,
      fun a => if a ∈ CanonicalFastSampling.fastArmFinset k.1 then
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (k.2.1.scores a) else 0)
  have hf : Measurable f := by
    apply measurable_of_countable
  exact hp.prodMk (hf.comp hk)

/-- Evaluate the actual coordinator choice only on a nonempty pending set.
This wrapper is a total observation, not a supplied successful choice. -/
def pendingChoice (z : ReferenceDownReception.ChoiceTimeView p rate.eta ×
    (CompletePublicTable.CompleteRow p × Fin p.T)) : Option (Fin p.K) := by
  classical
  exact if z.1.pendingAtChoice.Nonempty then
    CoordinatorLocalArmChoice.coordinatorArmChoice z.1.payload z.1.pendingAtChoice
      z.1.cutoff z.2.2 z.1.complementWeights z.2.1 else none

/-- The pending coordinator choice is jointly Borel in the complete view,
whole public row, and instruction time. -/
theorem measurable_pendingChoice : Measurable (pendingChoice (p := p) (rate := rate)) := by
  classical
  let s : Set (ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompletePublicTable.CompleteRow p × Fin p.T)) :=
    {z | z.1.pendingAtChoice.Nonempty}
  have hpendingView : Measurable
      (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp
      (comap_measurable
        ReferenceDownReceptionMeasurability.choiceTimeViewObservation))
  have hpending : Measurable (fun z : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompletePublicTable.CompleteRow p × Fin p.T) => z.1.pendingAtChoice) :=
    hpendingView.comp measurable_fst
  have hset : MeasurableSet s :=
    (Set.to_countable
      {v : Finset (ActiveRoundActions.Follower p.m) | v.Nonempty}).measurableSet.preimage
      hpending
  have hchoice : Measurable (fun z : s =>
      CoordinatorLocalArmChoice.coordinatorArmChoice z.1.1.payload
        z.1.1.pendingAtChoice z.1.1.cutoff z.1.2.2
        z.1.1.complementWeights z.1.2.1) :=
    ReferenceCollectionDispatchMeasurability.measurable_pendingArmChoice_comp
      (fun z : s => z.1.1) (fun z : s => z.1.2.1) (fun z : s => z.1.2.2)
      (measurable_fst.comp measurable_subtype_coe)
      (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
      (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe))
      (fun z => z.2)
  unfold pendingChoice
  exact Measurable.dite hchoice measurable_const hset

/-- The literal complement-envelope guard reconstructed from the installed
scores and the original continuous anchor. -/
def installedEnvelopeBit (c : InstallationCoordinates p rate) : Bool :=
  by classical
    let pred : Prop := ∀ j : CanonicalFastSampling.FastArm c.1.slowSet,
      c.1.anchor j.1 ≤ ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p) (c.2.scores j.1) ∧
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (c.2.scores j.1) ≤ 2 * c.1.anchor j.1
    letI : Decidable pred := Classical.propDecidable pred
    exact if h : pred then true else false

/-- The envelope guard is Borel on the whole payload anchor and the genuine
countable slow-set/register skeleton. -/
theorem measurable_installedEnvelopeBit :
    Measurable (installedEnvelopeBit (p := p) (rate := rate)) := by
  classical
  let key : InstallationCoordinates p rate →
      CanonicalOrientedSetLaw.SlowSet p.K p.m × LiveDiscrete p :=
    fun c => (c.1.slowSet, c.2)
  let anchor : InstallationCoordinates p rate → Fin p.K → ℝ := fun c => c.1.anchor
  let f : (Fin p.K → ℝ) ×
      (CanonicalOrientedSetLaw.SlowSet p.K p.m × LiveDiscrete p) → Bool := fun z => by
    let pred : Prop := ∀ j : CanonicalFastSampling.FastArm z.2.1,
      z.1 j.1 ≤ ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (z.2.2.scores j.1) ∧
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (z.2.2.scores j.1) ≤ 2 * z.1 j.1
    letI : Decidable pred := Classical.propDecidable pred
    exact if h : pred then true else false
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro k
    let s : Set (Fin p.K → ℝ) := {a | ∀ j :
        CanonicalFastSampling.FastArm k.1,
        a j.1 ≤ ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (k.2.scores j.1) ∧
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (k.2.scores j.1) ≤ 2 * a j.1}
    have hset : MeasurableSet s := by
      change MeasurableSet {a : Fin p.K → ℝ | ∀ j :
          CanonicalFastSampling.FastArm k.1,
          a j.1 ≤ ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (k.2.scores j.1) ∧
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (k.2.scores j.1) ≤ 2 * a j.1}
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro j
      have ha : Measurable (fun a : Fin p.K → ℝ => a j.1) := measurable_pi_apply j.1
      exact (measurableSet_le ha measurable_const).inter
        (measurableSet_le measurable_const (measurable_const.mul ha))
    have hfiber : Measurable (fun a : Fin p.K → ℝ =>
        if ha : a ∈ s then true else false) := Measurable.ite hset
          measurable_const measurable_const
    have heq : (fun a : Fin p.K → ℝ => f (a, k)) =
        (fun a => if ha : a ∈ s then true else false) := by
      funext a
      by_cases h : ∀ j : CanonicalFastSampling.FastArm k.1,
          a j.1 ≤ ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (k.2.scores j.1) ∧
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (k.2.scores j.1) ≤ 2 * a j.1
      · simp [f, s]
      · simp [f, s]
    rw [heq]
    exact hfiber
  have hobs : Measurable (fun c : InstallationCoordinates p rate =>
      LaterAssignmentStartMeasurability.payloadObservation c.1) :=
    measurable_payloadObservation.comp measurable_fst
  have hanchor : Measurable anchor :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp hobs)))
  have hkey : Measurable key :=
    (measurable_payloadSlowSet.comp measurable_fst).prodMk measurable_snd
  have heq : installedEnvelopeBit = fun c => f (anchor c, key c) := by
    funext c
    rfl
  rw [heq]
  exact hf.comp (hanchor.prodMk hkey)

/-- The actual base-score guard carried by the installed successful output. -/
def installedBaseScoreBit (c : InstallationCoordinates p rate) : Bool :=
  decide (∀ i, c.2.baseScores i ≤ p.T * D p)

/-- The actual choice-domain guard, evaluated on the installed view and time. -/
def installedChoiceInputsBit (c : InstallationCoordinates p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) : Bool :=
  ReferenceDownReceptionMeasurability.choiceInputsValidBit
    (installedView c started) c.2.time

/-- The original clock's grid-boundary guard, retained as an explicit bit. -/
def installedGridBoundaryBit (started : CoordinatorPhaseClock.StartRoundResult p) : Bool :=
  decide (started.clock.g ≤ p.T + 1)

/-- Return an arm only on the same guard branch where the dispatcher reaches
its arm-choice operation. -/
def installedSelectedArm (c : InstallationCoordinates p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (row : CompletePublicTable.CompleteRow p) : Option (Fin p.K) :=
  if installedBaseScoreBit c && installedChoiceInputsBit c started &&
      installedGridBoundaryBit started && installedEnvelopeBit c then
    pendingChoice (installedView c started, (row, c.2.time))
  else none

/-- One complete installation observation. Its four guard bits and optional
arm are retained beside the full installed code and actual choice view. -/
abbrev InstalledObservation (p : Parameters) (rate : RateInput p) :=
  InstallationCoordinates p rate ×
    (ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CoordinatorPhaseClock.StartRoundResult p ×
        (Bool × (Bool × (Bool × (Bool × Option (Fin p.K)))))))

/-- Assemble the actual installed coordinates, view, guard bits, and arm
observation without rerunning the later sampler or dispatcher. -/
def installedObservation (c : InstallationCoordinates p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (row : CompletePublicTable.CompleteRow p) : InstalledObservation p rate :=
  (c, (installedView c started, (started,
    (installedBaseScoreBit c, (installedChoiceInputsBit c started,
      (installedGridBoundaryBit started,
        (installedEnvelopeBit c, installedSelectedArm c started row)))))))

/-- The joint installation observation is Borel, including each guard and
the optional selected arm. -/
theorem measurable_installedObservation : Measurable
    (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedObservation z.1 z.2.1 z.2.2) := by
  have hv : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedView z.1 z.2.1) :=
    measurable_installedView.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hb : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedBaseScoreBit z.1) :=
    (measurable_of_countable (fun d : LiveDiscrete p =>
      decide (∀ i, d.baseScores i ≤ p.T * D p))).comp
        (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedChoiceInputsBit z.1 z.2.1) :=
    ReferenceDownReceptionMeasurability.measurable_choiceInputsValid.comp
      (hv.prodMk ((measurable_of_countable (fun c : LiveDiscrete p => c.time)).comp
        (measurable_snd.comp measurable_fst)))
  have hg : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedGridBoundaryBit z.2.1) :=
    (measurable_of_countable installedGridBoundaryBit).comp
      (measurable_fst.comp measurable_snd)
  have he : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      installedEnvelopeBit z.1) :=
    measurable_installedEnvelopeBit.comp measurable_fst
  have ht : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      z.2.1) := measurable_fst.comp measurable_snd
  have hr : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      z.2.2) := measurable_snd.comp measurable_snd
  have htime : Measurable (fun z : InstallationCoordinates p rate ×
      (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
      z.1.2.time) :=
    (measurable_of_countable (fun c : LiveDiscrete p => c.time)).comp
      (measurable_snd.comp measurable_fst)
  have hpendingChoice : Measurable
      (fun z : InstallationCoordinates p rate ×
        (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
        pendingChoice (installedView z.1 z.2.1, (z.2.2, z.1.2.time))) :=
    measurable_pendingChoice.comp (hv.prodMk (hr.prodMk htime))
  have hguards : Measurable
      (fun z : InstallationCoordinates p rate ×
        (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
        installedBaseScoreBit z.1 && installedChoiceInputsBit z.1 z.2.1 &&
          installedGridBoundaryBit z.2.1 && installedEnvelopeBit z.1) :=
    (measurable_of_countable (fun b : Bool × (Bool × (Bool × Bool)) =>
      b.1 && b.2.1 && b.2.2.1 && b.2.2.2)).comp
      (hb.prodMk (hc.prodMk (hg.prodMk he)))
  have hselected : Measurable
      (fun z : InstallationCoordinates p rate ×
        (CoordinatorPhaseClock.StartRoundResult p × CompletePublicTable.CompleteRow p) =>
        installedSelectedArm z.1 z.2.1 z.2.2) :=
    Measurable.ite (hguards (measurableSet_singleton true)) hpendingChoice measurable_const
  exact measurable_fst.prodMk (hv.prodMk (ht.prodMk
    (hb.prodMk (hc.prodMk (hg.prodMk (he.prodMk hselected))))))

/-- The original local-ledger projection used by the accepted later-start
operation. -/
def operationLedger (z : CoreInput p rate) :
    LaterAssignmentStartOperation.LocalLedger z.val.1.1 :=
  CoordinatorRoundDispatch.collectionOperationLedger (assemble z.val) z.property.payload_n_eq

/-- The existing successful-output payload/base-score projection for the
same original input, instruction, and whole row. -/
def laterPayloadScore? (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  LaterAssignmentFullOutputMeasurability.actualPayloadScore?
    (laterInput z instruction, z.val.1.2)

/-- The actual output projection is jointly Borel in the checked core and the
original instruction. -/
theorem measurable_laterPayloadScore? : Measurable
    (fun z : CoreInput p rate × CoordinatorPhaseClock.AssignmentStartInstruction p =>
      laterPayloadScore? z.1 z.2) :=
  LaterAssignmentFullOutputMeasurability.measurable_actualPayloadScore?.comp
    (measurable_laterInput.prodMk
      (measurable_snd.comp (measurable_fst.comp
        (measurable_subtype_coe.comp measurable_fst))))

/-- Install only a payload and base-score pair actually returned by the
accepted later operation. -/
def laterInstalledObservation (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    Option (InstalledObservation p rate) :=
  (laterPayloadScore? z instruction).map fun ps =>
    installedObservation (installationCoordinates ps z.val.2.1 instruction started)
      started z.val.1.2

/-- Measurability of installation from the accepted actual output projection,
separating the original ledger, instruction, clock result, and complete row. -/
theorem measurable_laterInstalledObservation : Measurable
    (fun z : CoreInput p rate ×
      (CoordinatorPhaseClock.AssignmentStartInstruction p ×
        CoordinatorPhaseClock.StartRoundResult p) =>
      laterInstalledObservation z.1 z.2.1 z.2.2) := by
  let X := CoreInput p rate ×
    (CoordinatorPhaseClock.AssignmentStartInstruction p × CoordinatorPhaseClock.StartRoundResult p)
  have hcore : Measurable (fun z : X => z.1) := measurable_fst
  have hinstruction : Measurable (fun z : X => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hstarted : Measurable (fun z : X => z.2.2) := measurable_snd.comp measurable_snd
  have hps : Measurable (fun z : X => laterPayloadScore? z.1 z.2.1) :=
    measurable_laterPayloadScore?.comp (measurable_fst.prodMk hinstruction)
  have hledger : Measurable (fun z : X => z.1.val.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_subtype_coe.comp hcore))
  have hrow : Measurable (fun z : X => z.1.val.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_subtype_coe.comp hcore))
  let f : (Payload rate × (Fin (p.m - 1) → ℕ)) × X → InstalledObservation p rate :=
    fun q => installedObservation
      (installationCoordinates q.1 q.2.1.val.2.1 q.2.2.1 q.2.2.2)
      q.2.2.2 q.2.1.val.1.2
  have hf : Measurable f := by
    have hcoordinates : Measurable (fun q : (Payload rate × (Fin (p.m - 1) → ℕ)) × X =>
        installationCoordinates q.1 q.2.1.val.2.1 q.2.2.1 q.2.2.2) :=
      measurable_installationCoordinates.comp
        (measurable_fst.prodMk ((hledger.comp measurable_snd).prodMk
          ((hinstruction.comp measurable_snd).prodMk (hstarted.comp measurable_snd))))
    exact measurable_installedObservation.comp
      (hcoordinates.prodMk ((hstarted.comp measurable_snd).prodMk (hrow.comp measurable_snd)))
  exact measurable_optionMapDependent f hf
    (fun z : X => laterPayloadScore? z.1 z.2.1) hps

/-- Test the actual original pending set, clock observation, and requested
instruction before producing an installation observation. -/
def laterInstalledAtClock (z : CoreInput p rate)
    (clock : ClockObservation p) : Option (InstalledObservation p rate) := by
  classical
  match clock with
  | .inl _ => exact none
  | .inr started =>
      exact if z.val.2.1.pending.Nonempty then none else
        match requestedInstructionAt z.val clock with
        | none => none
        | some instruction => laterInstalledObservation z instruction started

/-- Joint Borel measurability of the checked-clock installation producer. -/
theorem measurable_laterInstalledAtClock : Measurable
    (fun z : CoreInput p rate × ClockObservation p =>
      laterInstalledAtClock z.1 z.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro clock
  cases clock with
  | inl _ => exact measurable_const
  | inr started =>
      let f : CoreInput p rate ×
          Option (CoordinatorPhaseClock.AssignmentStartInstruction p) →
          Option (InstalledObservation p rate) := fun z =>
        match z.2 with
        | none => none
        | some instruction => laterInstalledObservation z.1 instruction started
      have hf : Measurable f := by
        apply measurable_from_prod_countable_left
        intro instruction
        cases instruction with
        | none => exact measurable_const
        | some instruction =>
            have hp : Measurable (fun x : CoreInput p rate =>
                (x, (instruction, started))) :=
              measurable_id.prodMk
                (measurable_const.prodMk measurable_const)
            exact measurable_laterInstalledObservation.comp hp
      have hrequest : Measurable (fun z : CoreInput p rate =>
          requestedInstructionAt z.val (.inr started)) := by
        have hledger : Measurable (fun z : CoreInput p rate => z.val.2.1) :=
          measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
        let g : Ledger rate → Option (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
          fun ledger => if ledger.pending.Nonempty then none else started.assignmentStart
        have heq : (fun z : CoreInput p rate =>
            requestedInstructionAt z.val (.inr started)) = g ∘ fun z => z.val.2.1 := by
          funext z
          rfl
        rw [heq]
        exact (measurable_of_countable g).comp hledger
      have hset : MeasurableSet {z : CoreInput p rate | z.val.2.1.pending.Nonempty} :=
        (Set.to_countable {ledger : Ledger rate | ledger.pending.Nonempty}).measurableSet.preimage
          (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
      exact Measurable.ite hset measurable_const
        (hf.comp (measurable_id.prodMk hrequest))

/-- The unrestricted producer tests the actual collection core and clock
inside the function; no successful-output or Borel premise is supplied. -/
def laterInstalledObservation? (z : LocalInput p rate) :
    Option (InstalledObservation p rate) := by
  classical
  exact if hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z) then
    laterInstalledAtClock ⟨z, hcore⟩ (clockObservation z) else none

/-- The unrestricted actual installation component is Borel on the full
continuous local input product. -/
theorem measurable_laterInstalledObservation? :
    Measurable (laterInstalledObservation? (p := p) (rate := rate)) := by
  classical
  let s : Set (LocalInput p rate) :=
    {z | CoordinatorRoundDispatch.CollectionCoreValid (assemble z)}
  have hs : MeasurableSet s := measurableSet_coreChecks
  have hsuccess : Measurable (fun z : s =>
      laterInstalledAtClock ⟨z.1, z.2⟩ (clockObservation z.1)) := by
    exact measurable_laterInstalledAtClock.comp
      (measurable_id.prodMk (measurable_clockObservation.comp measurable_subtype_coe))
  change Measurable (fun z => if hcore : z ∈ s then
    laterInstalledAtClock ⟨z, hcore⟩ (clockObservation z) else none)
  exact Measurable.dite hsuccess measurable_const hs

/-- Composition with any separately measurable map to the existing local
input remains Borel. -/
theorem measurable_laterInstalledObservation?_comp {X : Type*} [MeasurableSpace X]
    (input : X → LocalInput p rate) (hinput : Measurable input) :
    Measurable (fun x => laterInstalledObservation? (input x)) :=
  measurable_laterInstalledObservation?.comp hinput

/-- Composition from separate original payload, row, ledger, proposal,
decoder-bank, time, and cutoff maps. The continuous payload and whole row are
not discretized. -/
theorem measurable_laterInstalledObservation?_separate {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (row : X → CompletePublicTable.CompleteRow p)
    (ledger : X → Ledger rate) (proposal : X → Option (Fin p.T × Bool))
    (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (time cutoff : X → Fin p.T)
    (hpayload : Measurable payload) (hrow : Measurable row)
    (hledger : Measurable ledger) (hproposal : Measurable proposal)
    (hbank : Measurable bank) (htime : Measurable time) (hcutoff : Measurable cutoff) :
    Measurable (fun x => laterInstalledObservation?
      ((payload x, row x), (ledger x, (proposal x, (bank x, (time x, cutoff x)))))) := by
  apply measurable_laterInstalledObservation?_comp
  exact (hpayload.prodMk hrow).prodMk
    (hledger.prodMk (hproposal.prodMk (hbank.prodMk (htime.prodMk hcutoff))))

/-- Decode soundness for the accepted later-start decoder, with its exact
code-result equation exposed as an input to this local helper. -/
theorem decodeLaterAssignmentStart_sound (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p)
    (result : LaterAssignmentStartOperation.Result z.val.1.1
      (operationLedger z) instruction z.val.1.2 (localConsistency z))
    (hdecoded : LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
      z.val.1.1 (operationLedger z) instruction z.val.1.2
        (localConsistency z) code = some result) :
    LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
      (operationLedger z) instruction z.val.1.2 (localConsistency z) = result := by
  classical
  unfold LaterAssignmentStartMeasurability.decodeLaterAssignmentStart at hdecoded
  unfold LaterAssignmentStartOperation.laterAssignmentStart
  cases hd : LaterAssignmentStartOperation.decideReconstruction
      z.val.1.1 (operationLedger z) instruction with
  | failure reason =>
      rw [hd] at hdecoded
      cases code <;>
        simp only [LaterAssignmentStartMeasurability.decodeAfterReconstruction] at hdecoded
        <;> try contradiction
      split at hdecoded
      · rename_i heq
        subst reason
        exact Option.some.inj hdecoded
      · contradiction
  | success out hcall =>
      rw [hd] at hdecoded
      cases code <;>
        simp only [LaterAssignmentStartMeasurability.decodeAfterReconstruction,
          LaterAssignmentStartMeasurability.decodeAfterSuccessful] at hdecoded
        <;> try contradiction
      all_goals
        split at hdecoded
        · exact Option.some.inj hdecoded
        · contradiction

/-- Recover every live score, queue, and previous service from the very same
successful collection reconstruction. -/
theorem ledger_coordinates_of_reconstruction (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart (operationLedger z) instruction)
    (a : Fin p.K) :
    ((z.val.2.1.cutoffRegisters a).map fun r => r.score + z.val.2.1.increment a).getD 0 =
        AssignmentScoreReconstruction.sourceScore out a ∧
      ((z.val.2.1.currentRegisters a).map fun r => r.queue).getD 0 =
        AssignmentScoreReconstruction.initialQueue out a ∧
      ((z.val.2.1.currentRegisters a).map fun r => r.lastService).getD 0 =
        (out.registers.current a).lastService := by
  have hc := out.registers.cutoff_eq a
  have hr := out.registers.current_eq a
  change z.val.2.1.cutoffRegisters a = some (out.registers.cutoff a) at hc
  change z.val.2.1.currentRegisters a = some (out.registers.current a) at hr
  simp only [hc, hr, Option.map_some, Option.getD_some,
    AssignmentScoreReconstruction.sourceScore,
    AssignmentScoreReconstruction.initialQueue]
  exact ⟨rfl, trivial, trivial⟩

/-- Every encoded installation field is the corresponding original
`installLater` field, including owned queues, prior services, and base scores. -/
theorem installationCoordinates_eq_actual (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output) :
    let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
    installationCoordinates (output.payload, output.baseScore) z.val.2.1 instruction
        clockData.result =
      (installed.registers.payload,
        encodeLive installed.registers installed.ownedRegisters installed.retainedBaseScore) := by
  dsimp only
  have hs : (fun a =>
      ((z.val.2.1.cutoffRegisters a).map fun r => r.score + z.val.2.1.increment a).getD 0) =
      AssignmentScoreReconstruction.sourceScore output.reconstruction :=
    funext fun a => (ledger_coordinates_of_reconstruction z instruction
      output.reconstruction a).1
  have hq : (fun a =>
      ((z.val.2.1.currentRegisters a).map fun r => r.queue).getD 0) =
      AssignmentScoreReconstruction.initialQueue output.reconstruction :=
    funext fun a => (ledger_coordinates_of_reconstruction z instruction
      output.reconstruction a).2.1
  have hp : (fun a =>
      ((z.val.2.1.currentRegisters a).map fun r => r.lastService).getD 0) =
      (fun a => (output.reconstruction.registers.current a).lastService) :=
    funext fun a => (ledger_coordinates_of_reconstruction z instruction
      output.reconstruction a).2.2
  dsimp only [installationCoordinates,
    CoordinatorAssignmentRegisterInstall.installLater, encodeLive]
  have hs' : (fun a : CanonicalFastSampling.FastArm output.payload.slowSet =>
      ((z.val.2.1.cutoffRegisters a.val).map fun r =>
        r.score + z.val.2.1.increment a.val).getD 0) =
      (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a.val) :=
    funext fun a => congrFun hs a.val
  have hq' : (fun a : CanonicalFastSampling.FastArm output.payload.slowSet =>
      ((z.val.2.1.currentRegisters a.val).map fun r => r.queue).getD 0) =
      (fun a => AssignmentScoreReconstruction.initialQueue output.reconstruction a.val) :=
    funext fun a => congrFun hq a.val
  have hp' : (fun a : CanonicalFastSampling.FastArm output.payload.slowSet =>
      ((z.val.2.1.currentRegisters a.val).map fun r => r.lastService).getD 0) =
      (fun a => (output.reconstruction.registers.current a.val).lastService) :=
    funext fun a => congrFun hp a.val
  simp only [hs', hq', hp']

/-- Decode the exact existing live-register and owned-queue code while
retaining the original successful assignment vector and reconstruction. -/
def restoreInstallation (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (c : InstallationCoordinates p rate) :
    CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData := {
  registers := decodeLiveRegisters c.1 c.2
  ownedRegisters := decodeLiveOwned c.1 c.2
  retainedBaseScore := c.2.baseScores
  assignmentVector := output.assignmentVector
  reconstruction := output.reconstruction }

/-- Restoring the original live code gives the exact same `installLater`
registers, owned queues, base score, assignment vector, and reconstruction. -/
theorem restoreInstallation_exact (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output) :
    restoreInstallation z instruction output clockData
      (installationCoordinates (output.payload, output.baseScore) z.val.2.1
        instruction clockData.result) =
      CoordinatorAssignmentRegisterInstall.installLater output clockData := by
  rw [installationCoordinates_eq_actual]
  have hs : (fun a : CanonicalFastSampling.FastArm output.payload.slowSet =>
      extendComplement output.payload
        (fun j => AssignmentScoreReconstruction.sourceScore output.reconstruction j.1) a.1) =
      (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a.1) :=
    funext fun a => extendComplement_apply _ _ a
  dsimp only [restoreInstallation, decodeLiveRegisters, decodeLiveOwned, encodeLive,
    CoordinatorAssignmentRegisterInstall.installLater]
  simp only [extendComplement_apply]
  rw [hs]

/-- The installed view is exactly the actual installer's view, with the
original full payload and decoded complement weights. -/
theorem installedView_eq_actual (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output) :
    let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
    installedView (installationCoordinates (output.payload, output.baseScore) z.val.2.1
        instruction clockData.result) clockData.result =
      ({ payload := installed.registers.payload
         pendingAtChoice := clockData.result.pending
         cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clockData.result.clock.u
         complementWeights := installed.registers.complementWeights } :
        ReferenceDownReception.ChoiceTimeView p rate.eta) := by
  have hr := congrArg (fun i => i.registers)
    (restoreInstallation_exact z instruction output clockData)
  change decodeLiveRegisters _ _ = _ at hr
  let f : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta →
      ReferenceDownReception.ChoiceTimeView p rate.eta := fun r => {
    payload := r.payload
    pendingAtChoice := clockData.result.pending
    cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clockData.result.clock.u
    complementWeights := r.complementWeights }
  exact congrArg f hr

/-- A successful clock start at the selected assignment instruction has a
nonempty new pending set. -/
theorem pending_new_start (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction) : started.pending.Nonempty := by
  have heffect := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
    (assemble z.val).time (assemble z.val).clock (assemble z.val).ledger.pending started
    instruction z.property.clock_parameter_valid z.property.clock_registers_valid
    z.property.clock_start_time_valid hstart hi
  rw [heffect.2.2.2.2.2.2.1]
  have hpos : 0 < p.m - 1 := by
    have h := p.two_le_m
    omega
  exact ⟨⟨0, hpos⟩, Finset.mem_univ _⟩

/-- The successful payload/score code equation produced by the accepted
later-output decoder, with the exact result equation explicit. -/
theorem laterPayloadScore?_of_decoded_success (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (hlocal : output.localConsistency = localConsistency z)
    (hdecoded : LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
      z.val.1.1 (operationLedger z) instruction z.val.1.2 (localConsistency z)
        (laterObservation z instruction).1 = some (.success output hlocal)) :
    laterPayloadScore? z instruction = some (output.payload, output.baseScore) := by
  have hresult := decodeLaterAssignmentStart_sound z instruction
    (laterObservation z instruction).1 (.success output hlocal) hdecoded
  change LaterAssignmentStartMeasurability.resultPayloadScore?
      (LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
        (operationLedger z) instruction z.val.1.2 (localConsistency z)) = _
  rw [hresult]
  rfl

/-- The admitted full-output decoder gives the exact success code whenever
the original operation at this instruction returns this successful output. -/
theorem laterObservation_code_of_success (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (hlocal : output.localConsistency = localConsistency z)
    (hresult : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
      (operationLedger z) instruction z.val.1.2 (localConsistency z) =
        .success output hlocal) :
    LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
      z.val.1.1 (operationLedger z) instruction z.val.1.2 (localConsistency z)
        (laterObservation z instruction).1 = some (.success output hlocal) := by
  exact (laterObservation_decode z instruction).trans (congrArg some hresult)

/-- When the original later operation at this instruction returns this
successful output, the optional component equals the installed coordinates
and full view/guard/arm observation derived from this output. -/
theorem laterInstalledObservation?_of_actual_success (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (hpending : ¬ z.val.2.1.pending.Nonempty)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (hlocal : output.localConsistency = localConsistency z)
    (hresult : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
      (operationLedger z) instruction z.val.1.2 (localConsistency z) =
        .success output hlocal) :
    laterInstalledObservation? z.val = some (installedObservation
      (installationCoordinates (output.payload, output.baseScore) z.val.2.1 instruction started)
      started z.val.1.2) := by
  have hclock : clockObservation z.val = .inr started := by
    unfold clockObservation
    rw [hstart]
  have hrequest : requestedInstructionAt z.val (.inr started) = some instruction := by
    simp [requestedInstructionAt, hpending, hi]
  have hdecoded := laterObservation_code_of_success z instruction output hlocal hresult
  have hps := laterPayloadScore?_of_decoded_success z instruction output hlocal hdecoded
  classical
  simp [laterInstalledObservation?, z.property, laterInstalledAtClock, hclock,
    hpending, hrequest, laterInstalledObservation, hps]

end Bandits.Support.ReferenceCollectionInstallOutputMeasurability

end
