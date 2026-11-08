/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLiveDispatchMeasurability

/-!
# Lossless observations of the actual live dispatcher

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-60`.

Internal local mathematics for the canonical whole-step Borel composer, after
acceptance of every branch and tail. No physical producer or manuscript
closure is asserted. The original input coordinate module is unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLiveDispatchOutputMeasurability

open ReferenceActivePhysicalStepMeasurability
open ReferenceLiveDispatchMeasurability
open CoordinatorRoundDispatch

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Every runtime ledger field, including raw arrivals and enabled history.
Its rate and integer-scale indices occur only in proof fields. -/
abbrev LedgerData (p : Parameters) :=
  CoordinatorCollectionLedger.Assignment p × ℕ × ℕ × ℕ ×
    (Fin (p.m - 1) → ℕ) × Finset (Fin (p.m - 1)) ×
    (Fin p.K → Option CoordinatorCollectionLedger.CutoffRegister) ×
    (Fin p.K → Option CoordinatorCollectionLedger.CurrentRegister) ×
    (Fin p.K → ℕ) × (Fin p.K → ℕ) ×
    (Fin p.K → Fin p.T → Option ℕ) × (Fin p.T → Option Bool) ×
    ℕ × CoordinatorCollectionLedger.Phase

/-- Literal storage of the complete ledger, with no initialization call. -/
def ledgerData {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger r) : LedgerData p :=
  CoordinatorUpMeasurability.ledgerCode ledger

theorem ledgerData_injective {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta} :
    Function.Injective (ledgerData (r := r)) :=
  CoordinatorUpMeasurability.ledgerCode_injective

/-- Preserve invalid, rejected, and successful checked constructors. -/
def checkedData {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta} :
    CoordinatorCollectionLedger.Checked
        (Option (CoordinatorStartRoundCutoffDispatch.NewLedger r)) →
      Option (Bool × Option (LedgerData p))
  | .invalid => none
  | .rejected value => some (false, value.map ledgerData)
  | .success value => some (true, value.map ledgerData)

theorem checkedData_injective {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta} :
    Function.Injective (checkedData (r := r)) := by
  intro a b h
  cases a <;> cases b <;> simp only [checkedData, Option.some.injEq,
    Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
    reduceCtorEq] at h
  all_goals
    first
    | rfl
    | exact congrArg _ (Option.map_injective ledgerData_injective h.2)

abbrev DispatchData (p : Parameters) :=
  CoordinatorPhaseClock.StartRoundResult p × Option (Bool × Option (LedgerData p))

def dispatchData {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : CoordinatorLiveServiceFinish.OwnedRegisters r} {base : Fin (p.m - 1) → ℕ}
    (out : CoordinatorStartRoundCutoffDispatch.Output r q base) : DispatchData p :=
  (out.startResult, checkedData out.collectionInitialization)

theorem dispatchData_injective {eta : ReferencePrelaunchFollower.LearningRate}
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {q : CoordinatorLiveServiceFinish.OwnedRegisters r} {base : Fin (p.m - 1) → ℕ} :
    Function.Injective (dispatchData (r := r) (q := q) (base := base)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨rfl, h⟩ := Prod.mk.inj h
  have hbd := checkedData_injective h
  cases hbd
  rfl

deriving instance Countable for CoordinatorPhaseClock.ClockRegisters
deriving instance Countable for CoordinatorPhaseClock.AssignmentStartKind
deriving instance Countable for CoordinatorPhaseClock.AssignmentStartInstruction
deriving instance Countable for CoordinatorPhaseClock.CollectionLedgerCommand
deriving instance Countable for CoordinatorPhaseClock.ClockFailure
deriving instance Countable for CoordinatorPhaseClock.StartRoundResult
deriving instance Countable for LiveFailure

/-- All outcome constructors and their stored runtime data. Continuation
control and mode are determined by the original row and pending set; the
injectivity proof below checks these equalities explicitly. -/
inductive OutcomeData (p : Parameters) where
  | clockFailure (reason : CoordinatorPhaseClock.ClockFailure)
  | initializerFailure (dispatched : DispatchData p)
      (checked : Option (Bool × Option (LedgerData p)))
  | localFailure (dispatched : DispatchData p) (reason : LiveFailure)
  | cutoffChosen (dispatched : DispatchData p) (ledger : LedgerData p) (arm : Fin p.K)
  | continuingChosen (dispatched : DispatchData p)
      (continuationStart : CoordinatorPhaseClock.StartRoundResult p) (arm : Fin p.K)
  deriving Countable

def outcomeData {x : LiveInput p} : LiveOutcome x → OutcomeData p
  | .clockFailure reason _ => .clockFailure reason
  | .initializerFailure out _ checked _ =>
      .initializerFailure (dispatchData out) (checkedData checked)
  | .localFailure out _ reason => .localFailure (dispatchData out) reason
  | .cutoffChosen out _ ledger _ _ _ _ _ _ selected =>
      .cutoffChosen (dispatchData out) (ledgerData ledger) selected.arm
  | .continuingChosen out _ continuation selected =>
      .continuingChosen (dispatchData out) continuation.startRoundResult selected.arm

theorem continuation_eq_of_start_eq {x : LiveInput p}
    (a b : CoordinatorLiveChoiceRecorderStep.Continuation x.registers x.row)
    (h : a.startRoundResult = b.startRoundResult) : a = b := by
  have hc : a.currentControl = b.currentControl :=
    a.currentControl_eq.trans b.currentControl_eq.symm
  have hm : a.preChoiceMode = b.preChoiceMode :=
    a.preChoiceMode_eq.trans b.preChoiceMode_eq.symm
  cases a
  cases b
  cases h
  cases hc
  cases hm
  rfl

theorem armSelection_eq_of_arm_eq {x : LiveInput p}
    {started : CoordinatorPhaseClock.StartRoundResult p}
    (a b : ArmSelection x.registers.payload started x.registers.time
      x.registers.complementWeights x.row) (h : a.arm = b.arm) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Whole dependent outcomes are recovered at the SAME original input.
Only proof fields and fields forced equal by checked equations are omitted. -/
theorem outcomeData_injective (x : LiveInput p) :
    Function.Injective (outcomeData (x := x)) := by
  intro a b h
  cases a <;> cases b <;> simp only [outcomeData, reduceCtorEq] at h
  case clockFailure.clockFailure =>
    have hr := OutcomeData.clockFailure.inj h
    cases hr
    rfl
  case initializerFailure.initializerFailure =>
    have h := OutcomeData.initializerFailure.inj h
    have ho := dispatchData_injective h.1
    have hc := checkedData_injective h.2
    subst_vars
    rfl
  case localFailure.localFailure =>
    have h := OutcomeData.localFailure.inj h
    have ho := dispatchData_injective h.1
    have hr := h.2
    subst_vars
    rfl
  case cutoffChosen.cutoffChosen =>
    have h := OutcomeData.cutoffChosen.inj h
    have ho := dispatchData_injective h.1
    have hledger := ledgerData_injective h.2.1
    have ha := h.2.2
    subst_vars
    congr 1
    exact armSelection_eq_of_arm_eq _ _ ha
  case continuingChosen.continuingChosen =>
    have h := OutcomeData.continuingChosen.inj h
    have ho := dispatchData_injective h.1
    have hcont := continuation_eq_of_start_eq _ _ h.2.1
    have ha := h.2.2
    subst_vars
    congr 1
    exact armSelection_eq_of_arm_eq _ _ ha

/-- Valid stored observations are the range of the lossless encoder at the
original input, not an assumption that the dispatcher succeeds. -/
abbrev StoredOutcome (x : LiveInput p) := Set.range (outcomeData (x := x))

/-- Decode the unique outcome represented by the stored runtime data. This
uses the encoder's proved injectivity and never calls any dispatcher, clock,
initializer, or arm sampler. -/
def decodeOutcome (x : LiveInput p) (code : StoredOutcome x) : LiveOutcome x :=
  Classical.choose code.property

theorem decodeOutcome_outcomeData (x : LiveInput p) (out : LiveOutcome x) :
    decodeOutcome x ⟨outcomeData out, out, rfl⟩ = out := by
  apply outcomeData_injective x
  exact Classical.choose_spec (show ∃ a, outcomeData a = outcomeData out from ⟨out, rfl⟩)

theorem decodeOutcome_dispatchLive (z : LiveDispatchCoordinates p rate) :
    decodeOutcome (liveInputOfCoordinates z)
      ⟨outcomeData (dispatchLive (liveInputOfCoordinates z)),
        dispatchLive (liveInputOfCoordinates z), rfl⟩ =
      dispatchLive (liveInputOfCoordinates z) :=
  decodeOutcome_outcomeData _ _

instance outcomeDataMeasurableSpace : MeasurableSpace (OutcomeData p) := ⊤
instance outcomeDataDiscrete : DiscreteMeasurableSpace (OutcomeData p) :=
  ⟨fun _ => trivial⟩

open CanonicalFastSampling FastComplementLocality
open LaterAssignmentAnchorMeasurability

local instance downRecordMeasurableSpace : MeasurableSpace
    (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) := ⊤
local instance downRecordDiscrete : DiscreteMeasurableSpace
    (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
  ⟨fun _ => trivial⟩

local instance cutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

/-- A conditional arithmetic helper: positive anchors, positive complement
weights, and both envelope inequalities are explicit. In the dispatcher these
conditions are obtained by restricting to its actual Borel validity check. -/
theorem measurable_sampleLocalFast_varying {α : Type*} [MeasurableSpace α]
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (v : α → Fin p.K → ℝ) (hv : Measurable v)
    (w : FastArm U → ℝ) (hw : ∀ j, 0 < w j)
    (hpos : ∀ x i, 0 < v x i)
    (hlow : ∀ x j, v x j.1 ≤ w j)
    (hhigh : ∀ x j, w j ≤ 2 * v x j.1)
    (u : α → ContinuousCategorical.Scalar) (hu : Measurable u) :
    Measurable (fun x => sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap (v x) (hpos x) U w hw (hlow x) (hhigh x) (u x)) := by
  classical
  have hc (j : FastArm U) : Measurable (fun x => localFastCandidateMass (v x) U w j) := by
    unfold localFastCandidateMass FiniteOrientationDisintegration.inverseAnchorSum
    exact measurable_const.div (measurable_const.add
      ((Finset.measurable_fun_sum U.val fun i _ =>
        measurable_const.div ((measurable_pi_apply i).comp hv)).mul
          ((measurable_pi_apply j.1).comp hv)))
  have hn : Measurable (fun x => localFastNormalizer (v x) U w) :=
    Finset.measurable_fun_sum Finset.univ fun j _ => hc j
  let masses (x : α) (k : Fin (p.K - p.m + 1)) :=
    localFastLaw p rate.eta.val rate.eta.property rate.sourceCap
      (v x) U w (hpos x) hw (hlow x) (hhigh x) (fastArmOrderIso U k)
  have hm (k : Fin (p.K - p.m + 1)) : Measurable (fun x => masses x k) :=
    (measurable_const.mul ((hc _).div hn)).add measurable_const
  have hsum (x : α) : ∑ k, masses x k = 1 := by
    change (∑ k, localFastLaw p rate.eta.val rate.eta.property rate.sourceCap
      (v x) U w (hpos x) hw (hlow x) (hhigh x) (fastArmOrderIso U k)) = 1
    calc
      _ = ∑ j : FastArm U, localFastLaw p rate.eta.val rate.eta.property
          rate.sourceCap (v x) U w (hpos x) hw (hlow x) (hhigh x) j :=
        Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := localFastLaw_sum_eq_one p rate.eta.property rate.sourceCap
        (v x) (hpos x) U w hw (hlow x) (hhigh x)
  have hnonneg (x : α) (k : Fin (p.K - p.m + 1)) : 0 ≤ masses x k :=
    (localFastLaw_pos p rate.eta.property rate.sourceCap
      (v x) (hpos x) U w hw (hlow x) (hhigh x) _).le
  apply measurable_to_countable'
  intro j
  have hfiber : {x | sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap (v x) (hpos x) U w hw (hlow x) (hhigh x) (u x) = j} =
      {x | ContinuousCategorical.lower (masses x) ((fastArmOrderIso U).symm j) ≤
          (u x).val ∧ (u x).val <
            ContinuousCategorical.upper (masses x) ((fastArmOrderIso U).symm j)} := by
    ext x
    change fastArmOrderIso U (ContinuousCategorical.sample _ (masses x) (hsum x) (u x)) = j ↔ _
    rw [← OrderIso.eq_symm_apply]
    exact ContinuousCategorical.sample_eq_iff _ (hnonneg x) (hsum x) _ _
  change MeasurableSet {x | sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap (v x) (hpos x) U w hw (hlow x) (hhigh x) (u x) = j}
  rw [hfiber]
  exact (measurableSet_le
    (Finset.measurable_fun_sum _ fun k _ => hm k)
    (measurable_subtype_coe.comp hu)).inter
      (measurableSet_lt (measurable_subtype_coe.comp hu)
        (Finset.measurable_fun_sum _ fun k _ => hm k))

/-- The original payload with only its positive anchor allowed to vary. -/
abbrev SliceCoordinates (p : Parameters) := PositiveAnchor p × CompletePublicTable.CompleteRow p

def sliceInput (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) (z : SliceCoordinates p) : LiveInput p :=
  liveInputOfCoordinates (payloadWithAnchor old z.1, code, t, z.2)

private theorem measurable_reanchoredPayload (old : ReferenceActivePhysicalStep.Payload rate) :
    Measurable (fun z : SliceCoordinates p => payloadWithAnchor old z.1) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z : SliceCoordinates p =>
    (old.n, old.sigma, old.slowSet.1, z.1.val, old.queues))
  exact measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk ((measurable_subtype_coe.comp measurable_fst).prodMk
      measurable_const)))

private def downCoordinates (r : OrdinaryMessageCodec.DownFields) :=
  (r.sigma, r.a, r.e, r.h, r.q)

private theorem downCoordinates_injective : Function.Injective downCoordinates := by
  rintro ⟨a, b, c, d, e⟩ ⟨f, g, h, i, j⟩ heq
  simpa only [downCoordinates, Prod.mk.injEq, OrdinaryMessageCodec.DownFields.mk.injEq] using heq

private theorem measurable_sliceDownWord (old : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) : Measurable (fun z : SliceCoordinates p =>
      CoordinatorLocalArmChoice.storedDownFlatWord (payloadWithAnchor old z.1) i) := by
  have hp := measurable_reanchoredPayload old
  have he := AssignmentPayloadDerivedMeasurability.measurable_inputExponent.comp hp
  have ha := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp hp
  have haux : Measurable (fun z : SliceCoordinates p =>
      (payloadWithAnchor old z.1).assignment.auxiliary.val + 1) :=
    (measurable_of_countable (fun a : Fin p.K => a.val + 1)).comp ha
  have hexp : Measurable (fun z : SliceCoordinates p =>
      (payloadWithAnchor old z.1).exponent (old.assignment.assigned i)) :=
    (measurable_pi_apply (old.assignment.assigned i)).comp he
  have hcoordinates : Measurable (fun z : SliceCoordinates p =>
      downCoordinates
        ((payloadWithAnchor old z.1).downRecord i).val) := by
    change Measurable (fun z : SliceCoordinates p =>
      (old.sigma.val + 1, (old.assignment.assigned i).val + 1,
        (payloadWithAnchor old z.1).assignment.auxiliary.val + 1,
        (payloadWithAnchor old z.1).exponent (old.assignment.assigned i),
        old.queues (old.assignment.assigned i)))
    exact measurable_const.prodMk (measurable_const.prodMk
      (haux.prodMk (hexp.prodMk measurable_const)))
  have hrecord : Measurable (fun z : SliceCoordinates p =>
      (payloadWithAnchor old z.1).downRecord i) := by
    apply measurable_to_countable'
    intro r
    have hfiber : {z : SliceCoordinates p | (payloadWithAnchor old z.1).downRecord i = r} =
        (fun z => downCoordinates
          ((payloadWithAnchor old z.1).downRecord i).val) ⁻¹'
          {downCoordinates r.val} := by
      ext z
      constructor
      · intro h
        exact congrArg (fun r => downCoordinates r.val) h
      · intro h
        exact Subtype.ext (downCoordinates_injective h)
    change MeasurableSet {z : SliceCoordinates p | (payloadWithAnchor old z.1).downRecord i = r}
    rw [hfiber]
    exact hcoordinates (measurableSet_singleton _)
  exact (measurable_of_countable (fun r : OrdinaryMessageCodec.DownRecord
    (ReferencePrelaunchFollower.codecParams p rate.eta) =>
      OrdinaryMessageCodec.wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)
        (OrdinaryMessageCodec.encodeDown (ReferencePrelaunchFollower.codecParams p rate.eta) r))).comp hrecord

def sliceView (old : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p)
    (t : Fin p.T) (started : CoordinatorPhaseClock.StartRoundResult p)
    (z : SliceCoordinates p) : ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := payloadWithAnchor old z.1
  pendingAtChoice := started.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  complementWeights := (sliceInput old code t z).registers.complementWeights }

private theorem measurable_sliceView (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) (started : CoordinatorPhaseClock.StartRoundResult p) :
    Measurable (sliceView old code t started) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z : SliceCoordinates p =>
    (payloadWithAnchor old z.1, started.pending,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u,
      fun a : Fin p.K => if ha : a ∈ fastArmFinset old.slowSet then
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (code.scores a) else 0))
  exact (measurable_reanchoredPayload old).prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const))

private theorem measurableSet_sliceChoice (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) (started : CoordinatorPhaseClock.StartRoundResult p) :
    MeasurableSet {z : SliceCoordinates p | CoordinatorLocalArmChoice.ChoiceInputsValid
      (payloadWithAnchor old z.1)
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
      (sliceInput old code t z).registers.complementWeights} := by
  classical
  have hm := ReferenceDownReceptionMeasurability.measurable_choiceInputsValid.comp
    ((measurable_sliceView old code t started).prodMk (measurable_const (a := t)))
  have h := hm (measurableSet_singleton true)
  change MeasurableSet {z : SliceCoordinates p | decide
    (CoordinatorLocalArmChoice.ChoiceInputsValid (payloadWithAnchor old z.1)
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
      (sliceInput old code t z).registers.complementWeights) = true} at h
  simpa only [decide_eq_true_eq] using h

private theorem measurableSet_sliceEnvelope (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) :
    MeasurableSet {z : SliceCoordinates p |
      (sliceInput old code t z).registers.complementEnvelopeValid} := by
  change MeasurableSet {z : SliceCoordinates p | ∀ j : FastArm old.slowSet,
    z.1.val j.1 ≤ ScoreWeights.scoreWeight
      (AssignmentScoreReconstruction.sourceWeightBase p) (code.scores j.1) ∧
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (code.scores j.1) ≤ 2 * z.1.val j.1}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  have ha : Measurable (fun z : SliceCoordinates p => z.1.val j.1) :=
    (measurable_pi_apply j.1).comp (measurable_subtype_coe.comp measurable_fst)
  exact (measurableSet_le ha measurable_const).inter
    (measurableSet_le measurable_const (measurable_const.mul ha))

open PublicDiscreteDraws ActiveRoundActions

/-- The non-fast part of the actual arm formula, on the actual current row. -/
def sliceTransportArm (old : ReferenceActivePhysicalStep.Payload rate)
    (t : Fin p.T) (pending : Finset (Fin (p.m - 1))) (z : SliceCoordinates p) : Fin p.K := by
  classical
  exact
     let control := z.2.2 t
    if slotDraw control.1 = dataSlot then
      pilotDraw (K_pos p) (coordinator p.two_le_m) control.1
    else if slotDraw control.1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K control.1 ∈ pending then
      let i := selectedFollowerDraw p.two_le_m p.m_lt_K control.1
      let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1
      sendArm (CoordinatorLocalArmChoice.currentDownHash (payloadWithAnchor old z.1) control i)
        (tuple.val (coordinator p.two_le_m)) (tuple.val (followerPlayer p.two_le_m i))
    else (OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1).val
      (coordinator p.two_le_m)

private theorem measurable_sliceTransportArm (old : ReferenceActivePhysicalStep.Payload rate)
    (t : Fin p.T) (pending : Finset (Fin (p.m - 1))) :
    Measurable (sliceTransportArm old t pending) := by
  classical
  have hcontrol : Measurable (fun z : SliceCoordinates p => z.2.2 t) :=
    (measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)
  have hwords : Measurable (fun z : SliceCoordinates p => fun i : Fin (p.m - 1) =>
      CoordinatorLocalArmChoice.storedDownFlatWord (payloadWithAnchor old z.1) i) :=
    measurable_pi_iff.mpr (measurable_sliceDownWord old)
  have hread := hwords.prodMk
    ((measurable_slotDraw.comp (measurable_fst.comp hcontrol)).prodMk
      (((measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
        (measurable_fst.comp hcontrol)).prodMk
        (((measurable_pilotDraw (K_pos p) (coordinator p.two_le_m)).comp
          (measurable_fst.comp hcontrol)).prodMk
          ((measurable_subtype_coe.comp
            ((OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp
              (measurable_fst.comp hcontrol))).prodMk (measurable_snd.comp hcontrol)))))
  have hm := (measurable_of_countable (fun data =>
    if data.2.1 = dataSlot then data.2.2.2.1
    else if data.2.1 = downSlot ∧ data.2.2.1 ∈ pending then
      sendArm (AffineChannelLaw.affineHash
        (data.2.2.2.2.2 (CoordinatorLocalArmChoice.downChannel data.2.2.1))
        (data.1 data.2.2.1))
        (data.2.2.2.2.1 (coordinator p.two_le_m))
        (data.2.2.2.2.1 (followerPlayer p.two_le_m data.2.2.1))
    else data.2.2.2.2.1 (coordinator p.two_le_m))).comp hread
  convert hm using 1
  funext z
  simp only [Function.comp_def, sliceTransportArm, CoordinatorLocalArmChoice.currentDownHash]
  dsimp only [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] at *

/-- The actual arm sampler on a varying positive anchor and whole row;
validity is tested, rather than supplied as a premise. -/
theorem measurable_sliceArmChoice (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) (started : CoordinatorPhaseClock.StartRoundResult p) :
    Measurable (fun z : SliceCoordinates p => CoordinatorLocalArmChoice.coordinatorArmChoice
      (payloadWithAnchor old z.1) started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
      (sliceInput old code t z).registers.complementWeights z.2) := by
  classical
  let good : Set (SliceCoordinates p) := {z | CoordinatorLocalArmChoice.ChoiceInputsValid
    (payloadWithAnchor old z.1)
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
    (sliceInput old code t z).registers.complementWeights}
  have hg : MeasurableSet good := measurableSet_sliceChoice old code t started
  apply measurable_of_restrict_of_restrict_compl hg
  · by_cases hfast : CoordinatorLocalArmChoice.assignmentIsLive old
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t ∧
        started.pending = ∅
    · have heq : good.domRestrict (fun z => CoordinatorLocalArmChoice.coordinatorArmChoice
          (payloadWithAnchor old z.1) started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
          (sliceInput old code t z).registers.complementWeights z.2) =
          fun z : good => some ((sampleLocalFast p rate.eta.val rate.eta.property
            rate.sourceCap z.1.1.val z.1.1.property old.slowSet
            (decodeLiveRegisters old code).complementWeights
            (decodeLiveRegisters old code).complementWeights_pos
            (fun j => z.2.anchor_le_current j)
            (fun j => z.2.current_le_twice_anchor j)
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
              (z.1.2.2 t).1)).val) := by
        funext z
        have hz : CoordinatorLocalArmChoice.ChoiceInputsValid
            (payloadWithAnchor old z.1.1)
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
            (sliceInput old code t z.1).registers.complementWeights := z.property
        have hf : CoordinatorLocalArmChoice.assignmentIsLive (payloadWithAnchor old z.1.1)
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t ∧
            started.pending = ∅ := hfast
        change CoordinatorLocalArmChoice.coordinatorArmChoiceCore
          (payloadWithAnchor old z.1.1) started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
          (sliceInput old code t z.1).registers.complementWeights (z.1.2.2 t) = _
        exact (CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty _ _ _ _ _ _
          hz hf.1 hf.2).trans (by rfl)
      rw [heq]
      have ha : Measurable (fun z : good => z.1.1.val) :=
        measurable_subtype_coe.comp (measurable_fst.comp measurable_subtype_coe)
      have hu : Measurable (fun z : good => ContinuousControlSlice.coordinate
          ContinuousControlSlice.Label.fast (z.1.2.2 t).1) :=
        (ContinuousControlSlice.measurable_coordinate _).comp
          (measurable_fst.comp ((measurable_pi_apply t).comp
            (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe))))
      exact (measurable_of_countable (fun j : FastArm old.slowSet => some j.val)).comp
        (measurable_sampleLocalFast_varying old.slowSet _ ha
          (decodeLiveRegisters old code).complementWeights
          (decodeLiveRegisters old code).complementWeights_pos
          (fun z => z.1.1.property) (fun z j => z.2.anchor_le_current j)
          (fun z j => z.2.current_le_twice_anchor j) _ hu)
    · have heq : good.domRestrict (fun z => CoordinatorLocalArmChoice.coordinatorArmChoice
          (payloadWithAnchor old z.1) started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
          (sliceInput old code t z).registers.complementWeights z.2) =
          fun z : good => some (sliceTransportArm old t started.pending z.1) := by
        funext z
        have hz : CoordinatorLocalArmChoice.ChoiceInputsValid
            (payloadWithAnchor old z.1.1)
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
            (sliceInput old code t z.1).registers.complementWeights := z.property
        have hf : ¬ (CoordinatorLocalArmChoice.assignmentIsLive (payloadWithAnchor old z.1.1)
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t ∧
            started.pending = ∅) := hfast
        change CoordinatorLocalArmChoice.coordinatorArmChoiceCore
          (payloadWithAnchor old z.1.1) started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
          (sliceInput old code t z.1).registers.complementWeights (z.1.2.2 t) = _
        unfold sliceTransportArm
        dsimp only
        split_ifs with hd hdown
        · exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data _ _ _ _ _ _ hz hf hd
        · exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down _ _ _ _ _ _
            hz hf hd hdown.1 hdown.2
        · exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other _ _ _ _ _ _
            hz hf hd hdown
      rw [heq]
      exact (measurable_of_countable (fun a : Fin p.K => some a)).comp
        ((measurable_sliceTransportArm old t started.pending).comp measurable_subtype_coe)
  · have heq : goodᶜ.domRestrict (fun z => CoordinatorLocalArmChoice.coordinatorArmChoice
        (payloadWithAnchor old z.1) started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
        (sliceInput old code t z).registers.complementWeights z.2) =
        fun _ : (goodᶜ : Set (SliceCoordinates p)) => none := by
      funext z
      have hz : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid
          (payloadWithAnchor old z.1.1)
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
          (sliceInput old code t z.1).registers.complementWeights := z.property
      simp only [Set.domRestrict_apply, CoordinatorLocalArmChoice.coordinatorArmChoice,
        CoordinatorLocalArmChoice.coordinatorArmChoiceCore]
      rw [dite_eq_right hz]
    rw [heq]
    exact measurable_const

/-- Administrative observation of the checked choice. The default arm is
used only to totalize `Option.getD`; the equality theorem below proves that
an actual checked chosen branch has a `some` result. -/
def choiceData (x : LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (chosen : Fin p.K → OutcomeData p) : OutcomeData p := by
  classical
  exact if CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
      x.registers.time x.registers.complementWeights then
    if out.startResult.clock.g ≤ p.T + 1 then
      if x.registers.complementEnvelopeValid then
        chosen ((CoordinatorLocalArmChoice.coordinatorArmChoice x.registers.payload
          out.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
          x.registers.time x.registers.complementWeights x.row).getD ⟨0, K_pos p⟩)
      else .localFailure (dispatchData out) .recorderBoundaryFailure
    else .localFailure (dispatchData out) .recorderBoundaryFailure
  else .localFailure (dispatchData out) .choiceDomainFailure

/-- Literal proof-free observation formula for the existing dispatcher.
It retains the new cutoff ledger; it performs no second clock call. -/
def dataFormula (x : LiveInput p) : OutcomeData p := by
  classical
  exact match CoordinatorStartRoundCutoffDispatch.dispatch x.registers
      x.ownedRegisters x.followerBaseScore with
  | .error reason => .clockFailure reason
  | .ok out =>
    match out.collectionInitialization with
    | .invalid => .initializerFailure (dispatchData out) none
    | .rejected value => .initializerFailure (dispatchData out) (checkedData (.rejected value))
    | .success (some ledger) => choiceData x out
        (OutcomeData.cutoffChosen (dispatchData out) (ledgerData ledger))
    | .success none =>
      if CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame x.registers out.startResult then
        if x.registers.priorClock.sigma = some x.registers.payload.sigma then
          if x.registers.gridBoundary = x.registers.priorClock.g then
            if x.registers.scoreDomainValid then
              if x.ownedRegisters.queueDomainValid then
                if x.ownedRegisters.previousServiceDomainValid then
                  if ∀ i, x.followerBaseScore i ≤ p.T * D p then
                    if CoordinatorLocalArmChoice.assignmentIsLive x.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
                        x.registers.time then
                      choiceData x out
                        (OutcomeData.continuingChosen (dispatchData out) out.startResult)
                    else .localFailure (dispatchData out) .choiceDomainFailure
                  else .localFailure (dispatchData out) .baseScoreDomainFailure
                else .localFailure (dispatchData out) .previousServiceDomainFailure
              else .localFailure (dispatchData out) .queueDomainFailure
            else .localFailure (dispatchData out) .scoreDomainFailure
          else .localFailure (dispatchData out) .gridBoundaryMismatch
        else .localFailure (dispatchData out) .payloadClockMismatch
      else .localFailure (dispatchData out) .frameMismatch

/-- Equality on ALL inputs, including every checked and clock failure. -/
theorem outcomeData_dispatchLive (x : LiveInput p) :
    outcomeData (dispatchLive x) = dataFormula x := by
  classical
  unfold dispatchLive dataFormula
  dsimp only
  split
  · rename_i reason hd
    simp only [hd, outcomeData]
  · rename_i out hd
    simp only [hd]
    split
    · rename_i hi
      simp only [hi, outcomeData, checkedData]
    · rename_i value hi
      simp only [hi, outcomeData]
    · rename_i hi
      simp only [hi]
      unfold choiceData
      by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame x.registers out.startResult
      swap
      · rw [dite_eq_right hframe, ite_eq_right hframe]
        rfl
      rw [dite_eq_left hframe, ite_eq_left hframe]
      by_cases hpayload : x.registers.priorClock.sigma = some x.registers.payload.sigma
      swap
      · rw [dite_eq_right hpayload, ite_eq_right hpayload]
        rfl
      rw [dite_eq_left hpayload, ite_eq_left hpayload]
      by_cases hgrid : x.registers.gridBoundary = x.registers.priorClock.g
      swap
      · rw [dite_eq_right hgrid, ite_eq_right hgrid]
        rfl
      rw [dite_eq_left hgrid, ite_eq_left hgrid]
      by_cases hscore : x.registers.scoreDomainValid
      swap
      · rw [dite_eq_right hscore, ite_eq_right hscore]
        rfl
      rw [dite_eq_left hscore, ite_eq_left hscore]
      by_cases hqueue : x.ownedRegisters.queueDomainValid
      swap
      · rw [dite_eq_right hqueue, ite_eq_right hqueue]
        rfl
      rw [dite_eq_left hqueue, ite_eq_left hqueue]
      by_cases hprevious : x.ownedRegisters.previousServiceDomainValid
      swap
      · rw [dite_eq_right hprevious, ite_eq_right hprevious]
        rfl
      rw [dite_eq_left hprevious, ite_eq_left hprevious]
      by_cases hbase : ∀ i, x.followerBaseScore i ≤ p.T * D p
      swap
      · rw [dite_eq_right hbase, ite_eq_right hbase]
        rfl
      rw [dite_eq_left hbase, ite_eq_left hbase]
      by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive x.registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u) x.registers.time
      swap
      · rw [dite_eq_right hlive, ite_eq_right hlive]
        rfl
      rw [dite_eq_left hlive, ite_eq_left hlive]
      by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u) x.registers.time x.registers.complementWeights
      swap
      · rw [dite_eq_right hchoice, ite_eq_right hchoice]
        rfl
      rw [dite_eq_left hchoice, ite_eq_left hchoice]
      by_cases hboundary : out.startResult.clock.g ≤ p.T + 1
      swap
      · rw [dite_eq_right hboundary, ite_eq_right hboundary]
        rfl
      rw [dite_eq_left hboundary, ite_eq_left hboundary]
      by_cases henvelope : x.registers.complementEnvelopeValid
      swap
      · rw [dite_eq_right henvelope, ite_eq_right henvelope]
        rfl
      rw [dite_eq_left henvelope, ite_eq_left henvelope]
      split
      · rename_i hs
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          x.registers.payload out.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
          x.registers.time x.registers.complementWeights x.row hchoice hs)
      · rename_i arm hs
        have ha := congrArg (fun result : Option (Fin p.K) => result.getD ⟨0, K_pos p⟩) hs
        change OutcomeData.continuingChosen (dispatchData out) out.startResult arm = _
        exact congrArg (OutcomeData.continuingChosen (dispatchData out) out.startResult) ha.symm
    · rename_i ledger hi
      simp only [hi]
      unfold choiceData
      by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u) x.registers.time x.registers.complementWeights
      swap
      · rw [dite_eq_right hchoice, ite_eq_right hchoice]
        rfl
      rw [dite_eq_left hchoice, ite_eq_left hchoice]
      by_cases hboundary : out.startResult.clock.g ≤ p.T + 1
      swap
      · rw [dite_eq_right hboundary, ite_eq_right hboundary]
        rfl
      rw [dite_eq_left hboundary, ite_eq_left hboundary]
      by_cases henvelope : x.registers.complementEnvelopeValid
      swap
      · rw [dite_eq_right henvelope, ite_eq_right henvelope]
        rfl
      rw [dite_eq_left henvelope, ite_eq_left henvelope]
      split
      · rename_i hs
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          x.registers.payload out.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
          x.registers.time x.registers.complementWeights x.row hchoice hs)
      · rename_i arm hs
        have ha := congrArg (fun result : Option (Fin p.K) => result.getD ⟨0, K_pos p⟩) hs
        change OutcomeData.cutoffChosen (dispatchData out) (ledgerData ledger) arm = _
        exact congrArg (OutcomeData.cutoffChosen (dispatchData out) (ledgerData ledger)) ha.symm

/-- The carried registers with the actual current time; no dispatch is run. -/
def sliceRegisters (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) :=
  ReferenceActivePhysicalStep.liveRegistersAt (decodeLiveRegisters old code) t

def sliceOwned (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) :
    CoordinatorLiveServiceFinish.OwnedRegisters (sliceRegisters old code t) :=
  ReferenceActivePhysicalStep.liveOwnedAt (decodeLiveRegisters old code)
    (decodeLiveOwned old code) t

/-- Transport only the ledger's proof indices when reanchoring. Every
runtime field of the stored one-call result is retained literally. -/
def sliceOutput (old : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p)
    (t : Fin p.T)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      (sliceRegisters old code t) (sliceOwned old code t) code.baseScores)
    (z : SliceCoordinates p) : CoordinatorStartRoundCutoffDispatch.Output
      (sliceInput old code t z).registers (sliceInput old code t z).ownedRegisters
      (sliceInput old code t z).followerBaseScore :=
  ⟨out.startResult, out.collectionInitialization⟩

/-- The cutoff dispatcher's literal formulas read no anchor coordinate.
The checked ledger and every clock failure are transported unchanged. -/
theorem dispatch_sliceInput (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) (z : SliceCoordinates p) :
    CoordinatorStartRoundCutoffDispatch.dispatch (sliceInput old code t z).registers
      (sliceInput old code t z).ownedRegisters (sliceInput old code t z).followerBaseScore =
    (CoordinatorStartRoundCutoffDispatch.dispatch (sliceRegisters old code t)
      (sliceOwned old code t) code.baseScores).map (fun out => sliceOutput old code t out z) := by
  unfold CoordinatorStartRoundCutoffDispatch.dispatch
  dsimp only [sliceInput, liveInputOfCoordinates, sliceRegisters, sliceOwned,
    decodeLiveRegisters, decodeLiveOwned, ReferenceActivePhysicalStep.liveRegistersAt,
    ReferenceActivePhysicalStep.liveOwnedAt, payloadWithAnchor,
    CoordinatorLiveChoiceRecorderStep.Registers.clockPending]
  split <;> rfl

theorem dispatchData_sliceOutput (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      (sliceRegisters old code t) (sliceOwned old code t) code.baseScores)
    (z : SliceCoordinates p) :
    dispatchData (sliceOutput old code t out z) = dispatchData out := by
  rcases out with ⟨started, checked⟩
  cases checked with
  | invalid => rfl
  | success value => cases value <;> rfl
  | rejected value => cases value <;> rfl

private theorem measurable_choiceData_slice (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      (sliceRegisters old code t) (sliceOwned old code t) code.baseScores)
    (chosen : Fin p.K → OutcomeData p) :
    Measurable (fun z : SliceCoordinates p =>
      choiceData (sliceInput old code t z) (sliceOutput old code t out z) chosen) := by
  classical
  have ha := (measurable_of_countable (fun arm : Option (Fin p.K) =>
    chosen (arm.getD ⟨0, K_pos p⟩))).comp
      (measurable_sliceArmChoice old code t out.startResult)
  change Measurable (fun z : SliceCoordinates p => chosen
    ((CoordinatorLocalArmChoice.coordinatorArmChoice (sliceInput old code t z).registers.payload
      (sliceOutput old code t out z).startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        (sliceOutput old code t out z).startResult.clock.u)
      (sliceInput old code t z).registers.time
      (sliceInput old code t z).registers.complementWeights (sliceInput old code t z).row).getD
        ⟨0, K_pos p⟩)) at ha
  have he := measurableSet_sliceEnvelope old code t
  have hc := measurableSet_sliceChoice old code t out.startResult
  change MeasurableSet {z : SliceCoordinates p |
    CoordinatorLocalArmChoice.ChoiceInputsValid (sliceInput old code t z).registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        (sliceOutput old code t out z).startResult.clock.u)
      (sliceInput old code t z).registers.time
      (sliceInput old code t z).registers.complementWeights} at hc
  have hb : MeasurableSet {z : SliceCoordinates p |
      (sliceOutput old code t out z).startResult.clock.g ≤ p.T + 1} := by
    change MeasurableSet {z : SliceCoordinates p | out.startResult.clock.g ≤ p.T + 1}
    exact MeasurableSet.const _
  unfold choiceData
  simp_rw [dispatchData_sliceOutput]
  exact ((ha.ite he measurable_const).ite hb measurable_const).ite hc measurable_const

/-- On a countable discrete-register fibre, all remaining nonconstant tests
are the actual Borel choice/envelope comparisons. -/
theorem measurable_outcomeData_slice (old : ReferenceActivePhysicalStep.Payload rate)
    (code : LiveDiscrete p) (t : Fin p.T) :
    Measurable (fun z : SliceCoordinates p => outcomeData (dispatchLive (sliceInput old code t z))) := by
  classical
  simp_rw [outcomeData_dispatchLive]
  simp only [dataFormula, dispatch_sliceInput]
  cases hd : CoordinatorStartRoundCutoffDispatch.dispatch (sliceRegisters old code t)
      (sliceOwned old code t) code.baseScores with
  | error reason => simp only [Except.map]; exact measurable_const
  | ok out =>
    rcases out with ⟨started, checked⟩
    simp only [Except.map, sliceOutput]
    cases checked with
    | invalid => simp only [dispatchData, checkedData]; exact measurable_const
    | rejected value =>
      change Measurable (fun _ : SliceCoordinates p => OutcomeData.initializerFailure
        (started, some (false, value.map (ledgerData (r := sliceRegisters old code t))))
        (some (false, value.map (ledgerData (r := sliceRegisters old code t)))))
      exact measurable_const
    | success value =>
      cases value with
      | some ledger =>
        exact measurable_choiceData_slice old code t ⟨started, .success (some ledger)⟩
          (OutcomeData.cutoffChosen (started, checkedData (.success (some ledger)))
            (ledgerData ledger))
      | none =>
        simp only [sliceInput, liveInputOfCoordinates, decodeLiveRegisters, decodeLiveOwned,
          ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.liveOwnedAt,
          payloadWithAnchor, CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending,
          CoordinatorLiveChoiceRecorderStep.Registers.scoreDomainValid,
          CoordinatorLiveServiceFinish.OwnedRegisters.queueDomainValid,
          CoordinatorLiveServiceFinish.OwnedRegisters.previousServiceDomainValid,
          CoordinatorLocalArmChoice.assignmentIsLive, CoordinatorLocalArmChoice.assignmentStart,
          dispatchData, checkedData]
        have hm := measurable_choiceData_slice old code t ⟨started, .success none⟩
          (OutcomeData.continuingChosen (started, some (true, none)) started)
        repeat' first
          | apply Measurable.ite (MeasurableSet.const _)
          | exact hm
          | (dsimp only [Option.map]; exact measurable_const)

/-- Countable fibre keys contain only the existing payload's discrete fields,
the accepted live register code, and the actual time. -/
abbrev InputDiscrete (p : Parameters) :=
  (ℕ × Fin p.T × Finset (Fin p.K) × (Fin p.K → ℕ)) × (LiveDiscrete p × Fin p.T)

def inputDiscrete (z : LiveDispatchCoordinates p rate) : InputDiscrete p :=
  ((z.1.n, z.1.sigma, z.1.slowSet.1, z.1.queues), z.2.1, z.2.2.1)

private theorem measurable_inputDiscrete : Measurable (inputDiscrete (p := p) (rate := rate)) := by
  have hp : Measurable (fun z : LiveDispatchCoordinates p rate =>
      LaterAssignmentStartMeasurability.payloadObservation z.1) :=
    (comap_measurable _).comp measurable_fst
  apply measurable_to_countable'
  rintro ⟨⟨n, sigma, slow, queues⟩, code, time⟩
  change MeasurableSet {z : LiveDispatchCoordinates p rate |
    ((z.1.n, z.1.sigma, z.1.slowSet.1, z.1.queues), z.2.1, z.2.2.1) =
      ((n, sigma, slow, queues), code, time)}
  simp only [Prod.mk.injEq, Set.ofPred_and]
  exact ((measurableSet_eq_fun hp.fst measurable_const).inter
    ((measurableSet_eq_fun hp.snd.fst measurable_const).inter
      ((measurableSet_eq_fun hp.snd.snd.fst measurable_const).inter
        (measurableSet_eq_fun hp.snd.snd.snd.snd measurable_const)))).inter
    ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const))

abbrev InputDiscreteRange (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Set.range (inputDiscrete (p := p) (rate := rate))

def discreteRange (z : LiveDispatchCoordinates p rate) : InputDiscreteRange p rate :=
  ⟨inputDiscrete z, z, rfl⟩

def sliceRepresentative (c : InputDiscreteRange p rate) : LiveDispatchCoordinates p rate :=
  Classical.choose c.property

private theorem payload_reanchor_eq (a b : ReferenceActivePhysicalStep.Payload rate)
    (h : (a.n, a.sigma, a.slowSet.1, a.queues) = (b.n, b.sigma, b.slowSet.1, b.queues)) :
    payloadWithAnchor a ⟨b.anchor, b.anchor_pos⟩ = b := by
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, hslow, rfl⟩
  have hs := Subtype.ext hslow
  cases hs
  rfl

/-- Original coordinates are restored with their original WHOLE row. -/
theorem sliceRepresentative_reconstruction (z : LiveDispatchCoordinates p rate) :
    (payloadWithAnchor (sliceRepresentative (discreteRange z)).1 ⟨z.1.anchor, z.1.anchor_pos⟩,
      (sliceRepresentative (discreteRange z)).2.1,
      (sliceRepresentative (discreteRange z)).2.2.1, z.2.2.2) = z := by
  have h : inputDiscrete (sliceRepresentative (discreteRange z)) = inputDiscrete z :=
    Classical.choose_spec (discreteRange z).property
  have hp := payload_reanchor_eq _ _ (congrArg Prod.fst h)
  have hd := congrArg (fun c : InputDiscrete p => c.2.1) h
  have ht := congrArg (fun c : InputDiscrete p => c.2.2) h
  change (sliceRepresentative (discreteRange z)).2.1 = z.2.1 at hd
  change (sliceRepresentative (discreteRange z)).2.2.1 = z.2.2.1 at ht
  rw [hp, hd, ht]

private theorem measurable_positiveAnchor : Measurable
    (fun z : LiveDispatchCoordinates p rate => (⟨z.1.anchor, z.1.anchor_pos⟩ : PositiveAnchor p)) :=
  (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp measurable_fst).subtype_mk

/-- Direct JOINT result on the accepted payload/register/time/whole-row
product. No successful-domain, clock-match, score-truth, or overflow premise. -/
theorem measurable_dispatchLive_outcomeData : Measurable
    (fun z : LiveDispatchCoordinates p rate => outcomeData (dispatchLive (liveInputOfCoordinates z))) := by
  have hkey : Measurable (discreteRange (p := p) (rate := rate)) :=
    measurable_inputDiscrete.subtype_mk
  have hf (c : InputDiscreteRange p rate) : Measurable
      (fun z : LiveDispatchCoordinates p rate => outcomeData (dispatchLive
        (sliceInput (sliceRepresentative c).1 (sliceRepresentative c).2.1
          (sliceRepresentative c).2.2.1 (⟨z.1.anchor, z.1.anchor_pos⟩, z.2.2.2)))) :=
    (measurable_outcomeData_slice _ _ _).comp
      (measurable_positiveAnchor.prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have h := CoordinatorCollectionRunMeasurabilityRepair.measurable_of_countable_cases
    discreteRange hkey _ hf
  convert h using 1
  funext z
  dsimp only [sliceInput]
  rw [sliceRepresentative_reconstruction]

/-- A lossless joint observation: the unmodified continuous input and the
entire proof-free runtime output code. Its decoder above uses stored data. -/
def dispatchObservation (z : LiveDispatchCoordinates p rate) :=
  (z, outcomeData (dispatchLive (liveInputOfCoordinates z)))

theorem measurable_dispatchObservation : Measurable
    (dispatchObservation (p := p) (rate := rate)) :=
  measurable_id.prodMk measurable_dispatchLive_outcomeData

/-- Component composition requires measurability only of the original
primitive coordinates; it assumes no measurable output operation. -/
theorem measurable_dispatchObservation_comp {Ω : Type*} [MeasurableSpace Ω]
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (registers : Ω → LiveDiscrete p) (time : Ω → Fin p.T)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (hp : Measurable payload) (hr : Measurable registers)
    (ht : Measurable time) (hw : Measurable row) :
    Measurable (fun ω => dispatchObservation (payload ω, registers ω, time ω, row ω)) :=
  measurable_dispatchObservation.comp (hp.prodMk (hr.prodMk (ht.prodMk hw)))

/-- The WHOLE complement-weight vector, extended only by zero on slow arms.
Every actual complement entry is unchanged. -/
def weightVector (z : LiveDispatchCoordinates p rate) (a : Fin p.K) : ℝ :=
  if ha : a ∈ fastArmFinset z.1.slowSet then
    (liveInputOfCoordinates z).registers.complementWeights ⟨a, ha⟩ else 0

/-- Joint measurability retains the complete ordinary real weight vector. -/
theorem measurable_weightVector : Measurable (weightVector (p := p) (rate := rate)) := by
  classical
  have hp : Measurable (fun z : LiveDispatchCoordinates p rate =>
      LaterAssignmentStartMeasurability.payloadObservation z.1) :=
    (comap_measurable _).comp measurable_fst
  apply measurable_pi_iff.mpr
  intro a
  have hs : MeasurableSet {z : LiveDispatchCoordinates p rate |
      a ∈ fastArmFinset z.1.slowSet} := by
    simpa only [fastArmFinset, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.preimage_ofPred_eq, LaterAssignmentStartMeasurability.payloadObservation] using
      (measurableSet_notMem_finset a).preimage hp.snd.snd.fst
  have hw : Measurable (fun z : LiveDispatchCoordinates p rate =>
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (z.2.1.scores a)) :=
    (measurable_of_countable (fun code : LiveDiscrete p =>
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (code.scores a))).comp (measurable_fst.comp measurable_snd)
  have heq : (fun z : LiveDispatchCoordinates p rate => weightVector z a) =
      fun z => if a ∈ fastArmFinset z.1.slowSet then
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (z.2.1.scores a) else 0 := by
    funext z
    unfold weightVector
    split <;> rfl
  rw [heq]
  exact hw.ite hs measurable_const

instance startResultMeasurableSpace : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
instance startResultDiscrete : DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

/-- The actual choice-time view derived from the retained start result. -/
def viewAtStart (z : LiveDispatchCoordinates p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := z.1
  pendingAtChoice := started.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  complementWeights := (liveInputOfCoordinates z).registers.complementWeights }

theorem measurable_viewAtStart (started : CoordinatorPhaseClock.StartRoundResult p) :
    Measurable (fun z : LiveDispatchCoordinates p rate => viewAtStart z started) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z : LiveDispatchCoordinates p rate =>
    (z.1, started.pending,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u, weightVector z))
  exact measurable_fst.prodMk (measurable_const.prodMk
    (measurable_const.prodMk measurable_weightVector))

local instance selectedOptionMeasurableSpace : MeasurableSpace
    (Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)) := ⊤
local instance selectedOptionDiscrete : DiscreteMeasurableSpace
    (Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)) := ⟨fun _ => trivial⟩

/-- Successful branch projection; failures retain their codes in the full
observation but have no successful selection. -/
def selectedData : OutcomeData p → Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)
  | .cutoffChosen out _ arm => some (out.1, arm)
  | .continuingChosen out _ arm => some (out.1, arm)
  | _ => none

abbrev SelectionData (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceDownReception.ChoiceTimeView p rate.eta ×
    (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)

/-- Observe every runtime field of a canonical dependent selection. -/
def encodeSelection {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x) : SelectionData p rate :=
  (selected.view, selected.started, selected.arm)

theorem encodeSelection_injective (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Function.Injective (encodeSelection (x := x)) := by
  intro a b h
  cases a
  cases b
  simp only [encodeSelection, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- The full selection observation, retaining the actual payload, complete
weights, pending set, cutoff, original start result and arm. -/
def selectionObservation (z : LiveDispatchCoordinates p rate) : Option (SelectionData p rate) :=
  match selectedData (outcomeData (dispatchLive (liveInputOfCoordinates z))) with
  | none => none
  | some (started, arm) => some (viewAtStart z started, started, arm)

theorem measurable_selectionObservation : Measurable
    (selectionObservation (p := p) (rate := rate)) := by
  have hcode := (measurable_of_countable (selectedData (p := p))).comp
    (measurable_dispatchLive_outcomeData (rate := rate))
  have hs : Measurable (some : SelectionData p rate → Option (SelectionData p rate)) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hf (code : Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)) :
      Measurable (fun z : LiveDispatchCoordinates p rate =>
        match code with
        | none => (none : Option (SelectionData p rate))
        | some (started, arm) => some (viewAtStart z started, started, arm)) := by
    cases code with
    | none => exact measurable_const
    | some pair => exact hs.comp ((measurable_viewAtStart pair.1).prodMk measurable_const)
  have hm : Measurable (fun pair :
      Option (CoordinatorPhaseClock.StartRoundResult p × Fin p.K) × LiveDispatchCoordinates p rate =>
      match pair.1 with
      | none => (none : Option (SelectionData p rate))
      | some (started, arm) => some (viewAtStart pair.2 started, started, arm)) :=
    measurable_from_prod_countable_right hf
  exact hm.comp (hcode.prodMk measurable_id)

def downViewObservation (z : LiveDispatchCoordinates p rate) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  (selectionObservation z).map Prod.fst

theorem measurable_downViewObservation : Measurable
    (downViewObservation (p := p) (rate := rate)) := by
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap Prod.fst measurable_fst
    selectionObservation measurable_selectionObservation

/-- The actual source fallback is used on every failure. -/
def armObservation (z : LiveDispatchCoordinates p rate) : Fin p.K :=
  ((selectedData (outcomeData (dispatchLive (liveInputOfCoordinates z)))).map Prod.snd).getD
    (ReferenceActivePhysicalStep.coordinatorFallback p)

theorem measurable_armObservation : Measurable (armObservation (p := p) (rate := rate)) :=
  (measurable_of_countable (fun data : OutcomeData p =>
    ((selectedData data).map Prod.snd).getD (ReferenceActivePhysicalStep.coordinatorFallback p))).comp
      measurable_dispatchLive_outcomeData

theorem measurable_selectionObservation_comp {Ω : Type*} [MeasurableSpace Ω]
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (registers : Ω → LiveDiscrete p) (time : Ω → Fin p.T)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (hp : Measurable payload) (hr : Measurable registers)
    (ht : Measurable time) (hw : Measurable row) :
    Measurable (fun ω => selectionObservation (payload ω, registers ω, time ω, row ω)) :=
  measurable_selectionObservation.comp (hp.prodMk (hr.prodMk (ht.prodMk hw)))

/-- Same-original-input whole-outcome reconstruction after both the lossless
input decoder and the lossless output decoder. -/
theorem canonical_decodeOutcome_reconstruction
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ) :
    (liveInputOfCoordinates_liveDispatchCoordinatesOfRound x r q base) ▸
      decodeOutcome (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base))
        ⟨(dispatchObservation (liveDispatchCoordinatesOfRound x r q base)).2,
          dispatchLive (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base)), rfl⟩ =
      dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) := by
  exact (congrArg (fun out =>
    (liveInputOfCoordinates_liveDispatchCoordinatesOfRound x r q base) ▸ out)
      (decodeOutcome_dispatchLive (liveDispatchCoordinatesOfRound x r q base))).trans
        (dispatchLive_coordinates_reconstruction x r q base)

theorem outcomeData_originalInput
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ) :
    outcomeData (dispatchLive (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base))) =
      outcomeData (dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base)) :=
  congrArg (fun input : LiveInput p => outcomeData (dispatchLive input))
    (liveInputOfCoordinates_liveDispatchCoordinatesOfRound x r q base)

theorem viewAtStart_originalInput
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    viewAtStart (liveDispatchCoordinatesOfRound x r q base) started = {
      payload := r.payload, pendingAtChoice := started.pending,
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u,
      complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights } := by
  unfold viewAtStart
  dsimp only [liveInputOfCoordinates, liveDispatchCoordinatesOfRound,
    ReferenceActivePhysicalStep.liveRegistersAt, decodeLiveRegisters, encodeLive,
    CoordinatorLiveChoiceRecorderStep.Registers.complementWeights]
  congr 1
  funext j
  exact congrArg (ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p))
    (extendComplement_apply r.payload r.complementScores j)

/-- The measured selection is the actual dependent canonical selection at the
SAME original x, with no success or clock restriction. -/
theorem canonical_selectionObservation
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    (ReferenceActivePhysicalStep.dispatch x).selection.map encodeSelection =
      selectionObservation (liveDispatchCoordinatesOfRound x r q base) := by
  classical
  rw [canonicalDispatch_live_reconstruction x r q base hstate]
  unfold selectionObservation
  rw [outcomeData_originalInput]
  cases h : dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) <;>
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, dite_true,
      outcomeData, selectedData, dispatchData, Option.map_none, Option.map_some,
      encodeSelection, viewAtStart_originalInput]

/-- The down-facing view is the actual dispatch projection, including none
on failures and the changed cutoff on a cutoff start. -/
theorem canonical_downViewObservation
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    (ReferenceActivePhysicalStep.dispatch x).downView =
      downViewObservation (liveDispatchCoordinatesOfRound x r q base) := by
  have h := congrArg (Option.map Prod.fst) (canonical_selectionObservation x r q base hstate)
  simpa only [ReferenceActivePhysicalStep.DispatchCut.downView, downViewObservation,
    Option.map_map, Function.comp_def, encodeSelection] using h

/-- Every failure has the original fallback arm, and both successful branches
have exactly the arm in the original dispatch selection. -/
theorem canonical_armObservation
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    (ReferenceActivePhysicalStep.dispatch x).arm =
      armObservation (liveDispatchCoordinatesOfRound x r q base) := by
  classical
  rw [canonicalDispatch_live_reconstruction x r q base hstate]
  unfold armObservation
  rw [outcomeData_originalInput]
  cases h : dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) <;>
    simp only [ReferenceActivePhysicalStep.DispatchCut.arm,
      ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
      dite_true, outcomeData, selectedData, Option.map_none,
      Option.map_some, Option.getD_none, Option.getD_some]

/-- Composition for the ACTUAL canonical live selection, down-view and arm
at the same original round. The only branch premise is the explicit live
coordinator tag. The four measurability inputs concern primitive coordinates:
the full payload, lossless live register code, actual time, and whole row. -/
theorem measurable_canonical_live_projections_comp {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (r : Ω → CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : ∀ ω, CoordinatorLiveServiceFinish.OwnedRegisters (r ω))
    (base : Ω → Fin (p.m - 1) → ℕ)
    (hstate : ∀ ω, (x ω).state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live (r ω) (q ω) (base ω))
    (hp : Measurable (fun ω => (r ω).payload))
    (hr : Measurable (fun ω => encodeLive (r ω) (q ω) (base ω)))
    (ht : Measurable (fun ω => (x ω).time))
    (hw : Measurable (fun ω => (x ω).row)) :
    Measurable (fun ω =>
      ((ReferenceActivePhysicalStep.dispatch (x ω)).selection.map encodeSelection,
        (ReferenceActivePhysicalStep.dispatch (x ω)).downView,
        (ReferenceActivePhysicalStep.dispatch (x ω)).arm)) := by
  have heq : (fun ω =>
      ((ReferenceActivePhysicalStep.dispatch (x ω)).selection.map encodeSelection,
        (ReferenceActivePhysicalStep.dispatch (x ω)).downView,
        (ReferenceActivePhysicalStep.dispatch (x ω)).arm)) =
      fun ω => (selectionObservation (liveDispatchCoordinatesOfRound (x ω) (r ω) (q ω) (base ω)),
        downViewObservation (liveDispatchCoordinatesOfRound (x ω) (r ω) (q ω) (base ω)),
        armObservation (liveDispatchCoordinatesOfRound (x ω) (r ω) (q ω) (base ω))) := by
    funext ω
    rw [canonical_selectionObservation (x ω) (r ω) (q ω) (base ω) (hstate ω),
      canonical_downViewObservation (x ω) (r ω) (q ω) (base ω) (hstate ω),
      canonical_armObservation (x ω) (r ω) (q ω) (base ω) (hstate ω)]
  rw [heq]
  exact (measurable_selectionObservation.prodMk
    (measurable_downViewObservation.prodMk measurable_armObservation)).comp
      (hp.prodMk (hr.prodMk (ht.prodMk hw)))

end Bandits.Support.ReferenceLiveDispatchOutputMeasurability

end
