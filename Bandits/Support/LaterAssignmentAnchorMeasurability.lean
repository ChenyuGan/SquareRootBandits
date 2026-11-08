/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LaterAssignmentStartMeasurability

/-!
# Joint measurability for a varying retained assignment payload

The local later-start operation is considered with its actual dependent
payload and local reconstruction input. The input sigma algebra is pulled
back from the existing payload observation and local-input code, retaining
the real anchor with its product Borel structure.

Sources: `sources/zip4/manuscript/06_interruptions.tex:16-61,80-100`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.LaterAssignmentAnchorMeasurability

variable {p : ConstructorDimensions.Parameters}
abbrev LearningRate := Bandits.Support.ReferencePrelaunchFollower.LearningRate
variable {eta : LearningRate}

/-- The actual dependent local input when the retained old payload varies. -/
abbrev JointLocalStartInput (p : ConstructorDimensions.Parameters)
    (eta : LearningRate) :=
  Σ old : AssignmentStartPayload.Input p eta,
    LaterAssignmentStartMeasurability.LocalStartInput old

/-- The discrete ledger, instruction and consistency coordinates emitted by
the existing `localStartInputCode`. -/
abbrev LedgerObservableCode (p : ConstructorDimensions.Parameters) :=
  Bandits.Support.CoordinatorCollectionLedger.Assignment p × ℕ × ℕ × ℕ ×
    (Fin (p.m - 1) → ℕ) × Finset (Fin (p.m - 1)) ×
    (Fin p.K → Option Bandits.Support.CoordinatorCollectionLedger.CutoffRegister) ×
    (Fin p.K → Option Bandits.Support.CoordinatorCollectionLedger.CurrentRegister) ×
    (Fin p.K → ℕ) × (Fin p.K → ℕ) ×
    (Fin p.K → Fin p.T → Option ℕ) × (Fin p.T → Option Bool) × ℕ ×
    Bandits.Support.CoordinatorCollectionLedger.Phase

/-- A fixed target type for the existing faithful local-start input code. -/
abbrev LocalStartObservableCode (p : ConstructorDimensions.Parameters) :=
  LedgerObservableCode p × ((Fin p.T × Fin 3) × ℕ)

private def assignmentObservableCode
    (a : Bandits.Support.CoordinatorCollectionLedger.Assignment p) := a.arm

private theorem assignmentObservableCode_injective :
    Function.Injective (assignmentObservableCode (p := p)) := by
  intro a b h
  cases a with
  | mk aa ha =>
    cases b with
    | mk ba hb =>
      simp only [assignmentObservableCode] at h
      cases h
      rfl

private instance assignmentObservableCountable :
    Countable (Bandits.Support.CoordinatorCollectionLedger.Assignment p) :=
  assignmentObservableCode_injective.countable

private def cutoffRegisterObservableCode
    (r : Bandits.Support.CoordinatorCollectionLedger.CutoffRegister) :=
  (r.score, (r.queue, r.lastService))

private theorem cutoffRegisterObservableCode_injective :
    Function.Injective cutoffRegisterObservableCode := by
  intro a b h
  cases a with
  | mk ascore aqueue alast =>
    cases b with
    | mk bscore bqueue blast =>
      simp only [cutoffRegisterObservableCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

private instance cutoffRegisterObservableCountable :
    Countable Bandits.Support.CoordinatorCollectionLedger.CutoffRegister :=
  cutoffRegisterObservableCode_injective.countable

private def currentRegisterObservableCode
    (r : Bandits.Support.CoordinatorCollectionLedger.CurrentRegister) :=
  (r.queue, r.lastService)

private theorem currentRegisterObservableCode_injective :
    Function.Injective currentRegisterObservableCode := by
  intro a b h
  cases a with
  | mk aqueue alast =>
    cases b with
    | mk bqueue blast =>
      simp only [currentRegisterObservableCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

private instance currentRegisterObservableCountable :
    Countable Bandits.Support.CoordinatorCollectionLedger.CurrentRegister :=
  currentRegisterObservableCode_injective.countable

private def phaseObservableCode :
    Bandits.Support.CoordinatorCollectionLedger.Phase → Fin 3
  | .ready => 0
  | .started => 1
  | .decoded => 2

private theorem phaseObservableCode_injective :
    Function.Injective phaseObservableCode := by
  intro a b h
  cases a <;> cases b <;> simp [phaseObservableCode] at h ⊢

private instance phaseObservableCountable :
    Countable Bandits.Support.CoordinatorCollectionLedger.Phase :=
  phaseObservableCode_injective.countable

private instance ledgerObservableCodeCountable : Countable (LedgerObservableCode p) := by
  dsimp [LedgerObservableCode]
  infer_instance

instance localStartObservableCodeCountable :
    Countable (LocalStartObservableCode p) := by
  dsimp [LocalStartObservableCode]
  infer_instance

instance localStartObservableCodeMeasurableSpace :
    MeasurableSpace (LocalStartObservableCode p) := ⊤

instance localStartObservableCodeDiscrete :
    DiscreteMeasurableSpace (LocalStartObservableCode p) :=
  ⟨fun _ => trivial⟩

/-- The countable part of the old payload observation, excluding its real
anchor coordinate. -/
abbrev PayloadDiscreteObservation (p : ConstructorDimensions.Parameters) :=
  ℕ × (Fin p.T × (Finset (Fin p.K) × (Fin p.K → ℕ)))

instance payloadDiscreteObservationMeasurableSpace :
    MeasurableSpace (PayloadDiscreteObservation p) := ⊤

instance payloadDiscreteObservationDiscrete :
    DiscreteMeasurableSpace (PayloadDiscreteObservation p) :=
  ⟨fun _ => trivial⟩

/-- All varying local coordinates except the positive real anchor. -/
abbrev JointDiscreteObservation (p : ConstructorDimensions.Parameters) :=
  PayloadDiscreteObservation p × LocalStartObservableCode p

instance jointDiscreteObservationMeasurableSpace :
    MeasurableSpace (JointDiscreteObservation p) := ⊤

instance jointDiscreteObservationDiscrete :
    DiscreteMeasurableSpace (JointDiscreteObservation p) :=
  ⟨fun _ => trivial⟩

private instance payloadDiscreteObservationCountable :
    Countable (PayloadDiscreteObservation p) := by
  dsimp [PayloadDiscreteObservation]
  infer_instance

instance jointDiscreteObservationCountable :
    Countable (JointDiscreteObservation p) := by
  dsimp [JointDiscreteObservation]
  infer_instance

/-- The open anchor domain already imposed by the old payload type. -/
abbrev PositiveAnchor (p : ConstructorDimensions.Parameters) :=
  {a : Fin p.K → ℝ // ∀ i, 0 < a i}

/-- The literal observable coordinates of the full dependent input: the
existing real-valued payload observation and existing local-input code. -/
def jointLocalStartObservation (z : JointLocalStartInput (p := p) (eta := eta)) :
    PayloadObservation p × LocalStartObservableCode p :=
  (payloadObservation z.1,
    localStartInputCode (p := p) (eta := eta) z.2)

/-- The joint input uses exactly the sigma algebra induced by its observable
payload and local-code coordinates. The anchor coordinate of
`payloadObservation` therefore keeps the ordinary product Borel sigma
algebra. -/
instance jointLocalStartInputMeasurableSpace :
    MeasurableSpace (JointLocalStartInput (p := p) (eta := eta)) :=
  (inferInstance : MeasurableSpace
    (PayloadObservation p × LocalStartObservableCode p)).comap
      (jointLocalStartObservation (p := p) (eta := eta))

private theorem payloadObservation_injective :
    Function.Injective (payloadObservation (p := p) (eta := eta)) := by
  intro a b h
  cases a with
  | mk ac an ane asigma aslow aanchor apos aqueues aqle =>
    cases b with
    | mk bc bn bne bsigma bslow banchor bpos bqueues bqle =>
      simp only [payloadObservation, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hslow, rfl, rfl⟩
      have hslow' : aslow = bslow := Subtype.ext hslow
      cases hslow'
      rfl

private theorem localCode_injective {old : AssignmentStartPayload.Input p eta} :
    Function.Injective
      (localStartInputCode (p := p) (eta := eta) (old := old)) :=
  localStartInputCode_injective

/-- Equality of the observable coordinates forces equality of the complete
dependent input. Thus the code omits proof fields only. -/
theorem jointLocalStartObservation_injective :
    Function.Injective (jointLocalStartObservation (p := p) (eta := eta)) := by
  intro a b h
  rcases a with ⟨oldA, inputA⟩
  rcases b with ⟨oldB, inputB⟩
  change (payloadObservation oldA, localStartInputCode inputA) =
    (payloadObservation oldB, localStartInputCode inputB) at h
  rcases Prod.mk.inj h with ⟨hobs, hcode⟩
  have hold : oldA = oldB := payloadObservation_injective hobs
  cases hold
  have hinput := localCode_injective hcode
  cases hinput
  rfl

/-- Measurability of the literal observable map follows from the defining
comap sigma algebra. -/
theorem measurable_jointLocalStartObservation :
    Measurable (jointLocalStartObservation (p := p) (eta := eta)) :=
  comap_measurable _

/-- The observable payload coordinates are measurable on the joint carrier. -/
theorem measurable_jointPayloadObservation :
    Measurable (fun z : JointLocalStartInput (p := p) (eta := eta) =>
      payloadObservation z.1) := by
  exact measurable_fst.comp measurable_jointLocalStartObservation

/-- The existing discrete local-start code remains a measurable coordinate
of the varying dependent input. -/
theorem measurable_jointLocalStartInputCode :
    Measurable (fun z : JointLocalStartInput (p := p) (eta := eta) =>
      localStartInputCode z.2) := by
  exact measurable_snd.comp measurable_jointLocalStartObservation

/-- The discrete payload and local ledger/instruction coordinates. -/
def jointDiscreteObservation
    (z : JointLocalStartInput (p := p) (eta := eta)) :
    JointDiscreteObservation p :=
  ((z.1.n, (z.1.sigma, (z.1.slowSet.1, z.1.queues))),
    localStartInputCode z.2)

private def payloadDiscreteProjection (o : PayloadObservation p) :
    PayloadDiscreteObservation p :=
  (o.1, (o.2.1, (o.2.2.1, o.2.2.2.2)))

private theorem measurable_payloadDiscreteProjection :
    Measurable (payloadDiscreteProjection (p := p)) := by
  apply measurable_to_countable'
  intro c
  have hset :
      {o : PayloadObservation p | payloadDiscreteProjection o = c} =
        {o | o.1 = c.1} ∩ ({o | o.2.1 = c.2.1} ∩
          ({o | o.2.2.1 = c.2.2.1} ∩ {o | o.2.2.2.2 = c.2.2.2})) := by
    ext o
    change payloadDiscreteProjection o = c ↔
      (o.1 = c.1 ∧ o.2.1 = c.2.1 ∧
        o.2.2.1 = c.2.2.1 ∧ o.2.2.2.2 = c.2.2.2)
    rw [payloadDiscreteProjection]
    constructor
    · intro h
      rcases Prod.mk.inj h with ⟨h1, htail⟩
      rcases Prod.mk.inj htail with ⟨h2, htail⟩
      rcases Prod.mk.inj htail with ⟨h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      apply Prod.ext h1
      apply Prod.ext h2
      exact Prod.ext h3 h4
  change MeasurableSet {o : PayloadObservation p | payloadDiscreteProjection o = c}
  rw [hset]
  have h1 : MeasurableSet {o : PayloadObservation p | o.1 = c.1} :=
    (measurableSet_singleton c.1).preimage measurable_fst
  have h2 : MeasurableSet {o : PayloadObservation p | o.2.1 = c.2.1} :=
    (measurableSet_singleton c.2.1).preimage (measurable_fst.comp measurable_snd)
  have h3 : MeasurableSet {o : PayloadObservation p | o.2.2.1 = c.2.2.1} :=
    (measurableSet_singleton c.2.2.1).preimage
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have h4 : MeasurableSet {o : PayloadObservation p | o.2.2.2.2 = c.2.2.2} :=
    (measurableSet_singleton c.2.2.2).preimage
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact h1.inter (h2.inter (h3.inter h4))

/-- This derived coordinate map is measurable because its codomain records
only the existing discrete payload and local-code fields. -/
theorem measurable_jointDiscreteObservation :
    Measurable (jointDiscreteObservation (p := p) (eta := eta)) :=
  by
    apply measurable_to_countable'
    intro c
    have hset :
        {z : JointLocalStartInput (p := p) (eta := eta) |
          jointDiscreteObservation z = c} =
          {z | payloadDiscreteProjection (payloadObservation z.1) = c.1} ∩
            {z | localStartInputCode z.2 = c.2} := by
      ext z
      change ((z.1.n, (z.1.sigma, (z.1.slowSet.1, z.1.queues))),
          localStartInputCode z.2) = c ↔
        (payloadDiscreteProjection (payloadObservation z.1) = c.1 ∧
          localStartInputCode z.2 = c.2)
      constructor
      · intro h
        rcases Prod.mk.inj h with ⟨hpayload, hcode⟩
        exact ⟨by simpa [payloadDiscreteProjection, payloadObservation] using hpayload,
          hcode⟩
      · rintro ⟨hpayload, hcode⟩
        apply Prod.ext
        · simpa [payloadDiscreteProjection, payloadObservation] using hpayload
        · exact hcode
    change MeasurableSet {z : JointLocalStartInput (p := p) (eta := eta) |
      jointDiscreteObservation z = c}
    rw [hset]
    exact ((measurableSet_singleton c.1).preimage
      (measurable_payloadDiscreteProjection.comp measurable_jointPayloadObservation)).inter
      ((measurableSet_singleton c.2).preimage measurable_jointLocalStartInputCode)

/-- The positive anchor carried by the original payload, with its genuine
product-Borel value and positivity proof. -/
def jointPositiveAnchor
    (z : JointLocalStartInput (p := p) (eta := eta)) : PositiveAnchor p :=
  ⟨z.1.anchor, z.1.anchor_pos⟩

/-- The positive-anchor projection is measurable into the inherited subtype
sigma algebra. -/
theorem measurable_jointPositiveAnchor :
    Measurable (jointPositiveAnchor (p := p) (eta := eta)) := by
  have hpayload : Measurable (fun z : JointLocalStartInput (p := p) (eta := eta) =>
      payloadObservation z.1) := measurable_jointPayloadObservation
  have hanchor : Measurable (fun z : JointLocalStartInput (p := p) (eta := eta) =>
      z.1.anchor) := by
    change Measurable (fun z : JointLocalStartInput (p := p) (eta := eta) =>
      (payloadObservation z.1).2.2.2.1)
    exact measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hpayload)))
  exact hanchor.subtype_mk (h := fun z => z.1.anchor_pos)

/-- The same old payload fields with a supplied positive anchor. This is the
source payload constructor used to analyze one fixed discrete ledger slice. -/
def payloadWithAnchor (old : AssignmentStartPayload.Input p eta)
    (anchor : PositiveAnchor p) : AssignmentStartPayload.Input p eta := {
  eta_le_source_cap := old.eta_le_source_cap
  n := old.n
  n_eq_eta_mul_D := old.n_eq_eta_mul_D
  sigma := old.sigma
  slowSet := old.slowSet
  anchor := anchor.1
  anchor_pos := anchor.2
  queues := old.queues
  queues_le_TD := old.queues_le_TD
}

/-- Transport a typed local input to the payload with a changed real anchor.
The ledger's proof indices and consistency proof move along the unchanged
runtime fields. -/
def transportLocalStartInput
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) : LocalStartInput (payloadWithAnchor old anchor) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  let old' := payloadWithAnchor old anchor
  let ledger' : LaterAssignmentStartOperation.LocalLedger old' := {
      assignment := ledger.assignment
      sigma := ledger.sigma
      cutoff := ledger.cutoff
      freezeAt := ledger.freezeAt
      baseScore := ledger.baseScore
      pending := ledger.pending
      cutoffRegisters := ledger.cutoffRegisters
      currentRegisters := ledger.currentRegisters
      increment := ledger.increment
      gammaLoc := ledger.gammaLoc
      rawBuffer := ledger.rawBuffer
      enabledHistory := ledger.enabledHistory
      cursor := ledger.cursor
      phase := ledger.phase
    }
  have consistent' : LaterAssignmentStartOperation.LocalConsistency old' ledger' := by
    refine ⟨?_, ?_, consistent.oldFreezeAt, ?_⟩
    · simpa [old', payloadWithAnchor, ledger'] using consistent.oldStart_eq
    · intro i
      simpa [old', payloadWithAnchor, ledger',
        AssignmentStartPayload.Input.assignment] using
        consistent.oldAssignment_eq i
    · simpa [ledger'] using consistent.oldFreezeAt_eq
  exact ⟨ledger', (instruction, consistent')⟩

private theorem transportLocalStartInput_code
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    localStartInputCode (transportLocalStartInput old anchor input) =
      localStartInputCode input := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  simp [transportLocalStartInput, localStartInputCode, ledgerCode,
    instructionCode, consistencyCode, payloadWithAnchor]

private theorem reconstructLaterStart_transport
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    AssignmentScoreReconstruction.reconstructLaterStart
        (transportLocalStartInput old anchor input).1
        (transportLocalStartInput old anchor input).2.1 =
      AssignmentScoreReconstruction.reconstructLaterStart input.1 input.2.1 := by
  rfl

/-- The countable range of the exact discrete payload and local-code
coordinates. -/
abbrev JointDiscreteObservationRange (p : ConstructorDimensions.Parameters)
    (eta : LearningRate) :=
  Set.range (jointDiscreteObservation (p := p) (eta := eta))

instance jointDiscreteObservationRangeMeasurableSpace :
    MeasurableSpace (JointDiscreteObservationRange p eta) := ⊤

instance jointDiscreteObservationRangeDiscrete :
    DiscreteMeasurableSpace (JointDiscreteObservationRange p eta) :=
  ⟨fun _ => trivial⟩

private instance jointDiscreteObservationRangeCountable :
    Countable (JointDiscreteObservationRange p eta) := by
  dsimp [JointDiscreteObservationRange]
  infer_instance

/-- A representative typed input for one attained discrete observation. -/
noncomputable def jointInputRepresentative
    (c : JointDiscreteObservationRange p eta) :
    JointLocalStartInput p eta :=
  Classical.choose c.property

theorem jointDiscreteObservation_representative
    (c : JointDiscreteObservationRange p eta) :
    jointDiscreteObservation (jointInputRepresentative c) = c.1 :=
  Classical.choose_spec c.property

private theorem payloadWithAnchor_eq_of_discreteObservation_eq
    (a b : AssignmentStartPayload.Input p eta)
    (hdiscrete : (a.n, (a.sigma, (a.slowSet.1, a.queues))) =
      (b.n, (b.sigma, (b.slowSet.1, b.queues)))) :
    payloadWithAnchor a ⟨b.anchor, b.anchor_pos⟩ = b := by
  apply payloadObservation_injective
  rcases Prod.mk.inj hdiscrete with ⟨hn, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hsigma, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hslow, hqueues⟩
  simp [payloadObservation, payloadWithAnchor, hn, hsigma, hslow, hqueues]

private theorem payloadWithAnchor_input_eq
    (a b : JointLocalStartInput p eta)
    (hdiscrete : jointDiscreteObservation a = jointDiscreteObservation b) :
    (⟨payloadWithAnchor a.1 (jointPositiveAnchor b),
      transportLocalStartInput a.1 (jointPositiveAnchor b) a.2⟩ :
        JointLocalStartInput p eta) = b := by
  rcases a with ⟨oldA, inputA⟩
  rcases b with ⟨oldB, inputB⟩
  rcases Prod.mk.inj hdiscrete with ⟨hpayload, hcode⟩
  have hold : payloadWithAnchor oldA (jointPositiveAnchor ⟨oldB, inputB⟩) = oldB :=
    payloadWithAnchor_eq_of_discreteObservation_eq oldA oldB hpayload
  let constructed : JointLocalStartInput p eta :=
    ⟨payloadWithAnchor oldA (jointPositiveAnchor ⟨oldB, inputB⟩),
      transportLocalStartInput oldA (jointPositiveAnchor ⟨oldB, inputB⟩) inputA⟩
  have hpayload' : payloadObservation constructed.1 = payloadObservation oldB := by
    exact congrArg payloadObservation hold
  have hcode' : localStartInputCode constructed.2 = localStartInputCode inputB := by
    dsimp [constructed]
    rw [transportLocalStartInput_code]
    exact hcode
  apply jointLocalStartObservation_injective
  change (payloadObservation constructed.1, localStartInputCode constructed.2) =
    (payloadObservation oldB, localStartInputCode inputB)
  exact Prod.ext hpayload' hcode'

/-- The actual operation domain pairs the full varying local input with one
untouched complete row. -/
abbrev JointOperationInput (p : ConstructorDimensions.Parameters) (eta : LearningRate) :=
  JointLocalStartInput (p := p) (eta := eta) × CompletePublicTable.CompleteRow p

/-- Exact code of the existing operation on the original dependent inputs. -/
noncomputable def operationCodeForInput
    (input : JointLocalStartInput p eta) (row : CompletePublicTable.CompleteRow p) :
      LaterAssignmentStartMeasurability.LaterAssignmentStartCode p :=
  LaterAssignmentStartMeasurability.laterAssignmentStartCode
    input.1 input.2.1 input.2.2.1 row input.2.2.2

noncomputable def laterAssignmentStartCodeMap
    (z : JointOperationInput (p := p) (eta := eta)) :
      LaterAssignmentStartMeasurability.LaterAssignmentStartCode p :=
  operationCodeForInput z.1 z.2

/-- The exact operation viewed on one attained discrete slice and the
original positive-anchor/complete-row coordinates. -/
noncomputable def operationCodeOnDiscreteSlice
    (c : JointDiscreteObservationRange p eta)
    (z : PositiveAnchor p × CompletePublicTable.CompleteRow p) :
    LaterAssignmentStartMeasurability.LaterAssignmentStartCode p := by
  let representative := jointInputRepresentative c
  let old' := payloadWithAnchor representative.1 z.1
  let input' := transportLocalStartInput representative.1 z.1 representative.2
  exact LaterAssignmentStartMeasurability.laterAssignmentStartCode
    old' input'.1 input'.2.1 z.2 input'.2.2

/-- The slice representation changes only the old positive anchor; its
ledger, instruction, consistency witness and complete row stay the original
runtime values. -/
theorem laterAssignmentStartCode_eq_discreteSlice
    (z : JointOperationInput p eta) :
    laterAssignmentStartCodeMap z =
      operationCodeOnDiscreteSlice
        ⟨jointDiscreteObservation z.1, ⟨z.1, rfl⟩⟩
        (jointPositiveAnchor z.1, z.2) := by
  let c : JointDiscreteObservationRange p eta :=
    ⟨jointDiscreteObservation z.1, ⟨z.1, rfl⟩⟩
  have hdiscrete :
      jointDiscreteObservation (jointInputRepresentative c) =
        jointDiscreteObservation z.1 := by
    rw [jointDiscreteObservation_representative]
  have hin := payloadWithAnchor_input_eq (jointInputRepresentative c) z.1 hdiscrete
  change operationCodeForInput z.1 z.2 =
    operationCodeForInput
      ⟨payloadWithAnchor (jointInputRepresentative c).1 (jointPositiveAnchor z.1),
        transportLocalStartInput (jointInputRepresentative c).1
          (jointPositiveAnchor z.1) (jointInputRepresentative c).2⟩ z.2
  exact (congrArg (fun input => operationCodeForInput input z.2) hin).symm

/-- The existing exact decoder remains valid for every original varying
input; success retains the original full assignment vector, payload and base
scores, up to proof irrelevance. -/
theorem decodeLaterAssignmentStart_exact
    (z : JointOperationInput (p := p) (eta := eta)) :
    LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2
        (laterAssignmentStartCodeMap z) =
      some (LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2) := by
  exact LaterAssignmentStartMeasurability.decodeLaterAssignmentStart_exact
    z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2

end Bandits.Support.LaterAssignmentAnchorMeasurability

end
