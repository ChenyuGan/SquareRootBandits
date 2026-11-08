/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapObservedFollower
public import Bandits.Support.BootstrapPrivateRoundStreams

/-!
# Measurable code for actual bootstrap observations

This module adapts the existing all-candidate bootstrap observer to countable
observable inputs.  It retains the original `SourceInput`, including the full
ID array, complete continuous row family, every private stream, and the
coordinator's original `J` scalar.  A denominator-`D` observation is an
explicit input.  The adapter does not generate physical play or observations.

The startup state and candidate registers are already the required discrete
carriers, so their codes are aliases of those carriers.  Complete rows remain
continuous; the only row observables used here are each candidate's DATA bit
and forward bit at the supplied private ID and time.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,55-114` and
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.BootstrapAllCandidateController
open Bandits.Support.BootstrapObservedFollower

namespace Bandits.Support.ActualBootstrapObservationCode

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {s : Fin (n_boot p)}

private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (f : α → γ)
    (hf : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro t ht
  have hpre : f ⁻¹' t = key ⁻¹' (key '' (f ⁻¹' t)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      change f x ∈ t
      rw [hf x y heq.symm]
      exact hy
  rw [hpre]
  exact hkey (Set.to_countable _).measurableSet

/-! ## The unchanged source and direct observable carriers -/

/-- The actual source carrier, with all published and private coordinates. -/
abbrev ActualSource (p : Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

/-- The source ID array, without restricting its row-index or time coordinates. -/
def sourceIDs (p : Parameters) (x : ActualSource p) : IDArray p := x.1.1

/-- The entire family of complete rows, retaining every continuous coordinate. -/
def sourceRows (p : Parameters) (x : ActualSource p) : CompleteRows p := x.1.2

/-- All original private coordinates, including the original coordinator `J`. -/
def sourcePrivate (p : Parameters) (x : ActualSource p) :
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p := x.2

theorem measurable_sourceIDs (p : Parameters) : Measurable (sourceIDs p) := by
  exact measurable_fst.comp measurable_fst

theorem measurable_sourceRows (p : Parameters) : Measurable (sourceRows p) := by
  exact measurable_snd.comp measurable_fst

theorem measurable_sourcePrivate (p : Parameters) : Measurable (sourcePrivate p) :=
  measurable_snd

/-- Assemble the original source product from its three literal components. -/
def assembleActualSource (p : Parameters) (ids : IDArray p) (rows : CompleteRows p)
    (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : ActualSource p :=
  ((ids, rows), privateCoords)

@[simp] theorem assembleActualSource_ids (p : Parameters) (ids : IDArray p)
    (rows : CompleteRows p) (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    sourceIDs p (assembleActualSource p ids rows privateCoords) = ids := rfl

@[simp] theorem assembleActualSource_rows (p : Parameters) (ids : IDArray p)
    (rows : CompleteRows p) (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    sourceRows p (assembleActualSource p ids rows privateCoords) = rows := rfl

@[simp] theorem assembleActualSource_private (p : Parameters) (ids : IDArray p)
    (rows : CompleteRows p) (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    sourcePrivate p (assembleActualSource p ids rows privateCoords) = privateCoords := rfl

@[simp] theorem assembleActualSource_components (p : Parameters) (source : ActualSource p) :
    assembleActualSource p (sourceIDs p source) (sourceRows p source)
      (sourcePrivate p source) = source := rfl

theorem measurable_assembleActualSource {Ω : Type*} [MeasurableSpace Ω]
    (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hids : Measurable ids) (hrows : Measurable rows) (hprivate : Measurable privateCoords) :
    Measurable (fun ω => assembleActualSource p (ids ω) (rows ω) (privateCoords ω)) := by
  exact (hids.prodMk hrows).prodMk hprivate

/-- A lossless code for the existing all-candidate candidate registers. -/
abbrev RegistersCode (p : Parameters) := BootstrapAllCandidateController.Registers p

/-- A lossless code for the existing observer state. Its dependent cursor,
weight-validity proof, and gain-prefix proof are retained. -/
abbrev StartupCode (p : Parameters) (s : Fin (n_boot p)) :=
  BootstrapObservedFollower.StartupState p s

private theorem countable_finArrow (k : ℕ) {α : Type*} [Countable α] :
    Countable (Fin k → α) := by
  let encα : Encodable α := Encodable.ofCountable α
  let encFunction : Encodable (Fin k → α) :=
    @Encodable.fintypeArrowOfEncodable (Fin k) α inferInstance inferInstance encα
  exact @Encodable.countable (Fin k → α) encFunction

private instance finArrowCountable (k : ℕ) {α : Type*} [Countable α] :
    Countable (Fin k → α) := countable_finArrow k

instance registersCodeCountable (p : Parameters) : Countable (RegistersCode p) := by
  apply Function.Injective.countable (f := fun r : RegistersCode p =>
    (r.count, r.dead, r.pending))
  intro a b h
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

instance registersCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (RegistersCode p) := ⊤

instance registersCodeMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (RegistersCode p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

private def startupBlockCaseKey (p : Parameters)
    (c : BootstrapObservedFollower.StartupBlockCase p) :
    Option (Fin p.K × Fin (A_id p) × ℕ × RegistersCode p) :=
  match c with
  | .inactive => none
  | .active held privateID gain registers => some (held, privateID, gain, registers)

private theorem startupBlockCaseKey_injective (p : Parameters) :
    Function.Injective (startupBlockCaseKey p) := by
  intro a b h
  cases a <;> cases b <;> simp_all [startupBlockCaseKey]

instance startupBlockCaseCountable (p : Parameters) :
    Countable (BootstrapObservedFollower.StartupBlockCase p) := by
  exact (startupBlockCaseKey_injective p).countable

instance startupCodeCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (StartupCode p s) := by
  apply Function.Injective.countable (f := fun x : StartupCode p s =>
    (x.numerators, (x.processed, x.blockCase)))
  intro a b h
  cases a
  cases b
  injection h with hnum hrest
  injection hrest with hprocessed hcase
  subst hnum
  subst hprocessed
  subst hcase
  rfl

instance startupCodeMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (StartupCode p s) := ⊤

instance startupCodeMeasurableSingletonClass (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSingletonClass (StartupCode p s) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

private def roundFailureKey {p : Parameters} {s : Fin (n_boot p)}
    (error : BootstrapObservedFollower.RoundFailure p s) :
    Sum (Fin p.T) (Sum (Fin p.T) (ℕ × ℕ)) :=
  match error with
  | .outsideBlock time => .inl time
  | .blockComplete time => .inr (.inl time)
  | .outOfOrder expected actual => .inr (.inr (expected, actual))

private theorem roundFailureKey_injective {p : Parameters}
    {s : Fin (n_boot p)} :
    Function.Injective (roundFailureKey (p := p) (s := s)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [roundFailureKey]

instance roundFailureCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (BootstrapObservedFollower.RoundFailure p s) := by
  exact (roundFailureKey_injective (p := p) (s := s)).countable

private def observeResultKey {p : Parameters} {s : Fin (n_boot p)}
    (result : BootstrapObservedFollower.ObserveResult p s) :
    Sum (BootstrapObservedFollower.RoundFailure p s) (StartupCode p s) :=
  match result with
  | .rejected error => .inl error
  | .accepted state => .inr state

private theorem observeResultKey_injective {p : Parameters}
    {s : Fin (n_boot p)} :
    Function.Injective (observeResultKey (p := p) (s := s)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [observeResultKey]

instance observeResultCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (BootstrapObservedFollower.ObserveResult p s) := by
  exact (observeResultKey_injective (p := p) (s := s)).countable

instance observeResultMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (BootstrapObservedFollower.ObserveResult p s) := ⊤

instance observeResultMeasurableSingletonClass (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSingletonClass (BootstrapObservedFollower.ObserveResult p s) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance startupBlockCaseMeasurableSpace (p : Parameters) :
    MeasurableSpace (BootstrapObservedFollower.StartupBlockCase p) := ⊤

instance startupBlockCaseMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (BootstrapObservedFollower.StartupBlockCase p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

/-- Reconstruction is identity because the accepted carrier already contains
all state fields and validity proofs. -/
def startupStateOfCode (code : StartupCode p s) : StartupState p s := code

theorem startupStateOfCode_eq (code : StartupCode p s) :
    startupStateOfCode code = code := rfl

/-- Candidate-register reconstruction is also identity on the accepted
all-candidate carrier. -/
def registersOfCode (code : RegistersCode p) : Registers p := code

theorem registersOfCode_eq (code : RegistersCode p) : registersOfCode code = code := rfl

/-! ## Measurable finite row reads and exact-grid observations -/

/-- The finite observable read of every candidate row at one private ID/time:
its DATA bit and its forward identification bit. -/
abbrev CandidateObservationCode (p : Parameters) :=
  Fin (M p) → (Bool × Bool)

noncomputable def candidateObservationCode (p : Parameters) (rows : CompleteRows p)
    (privateID : Fin (A_id p)) (time : Fin p.T) : CandidateObservationCode p := by
  classical
  exact fun candidate =>
    (decide (slotDraw ((rows candidate).2 time).1 = dataSlot),
      (rows candidate).1 privateID time)

theorem measurable_candidateObservationCode_fixed (p : Parameters)
    (privateID : Fin (A_id p)) (time : Fin p.T) :
    Measurable (fun rows : CompleteRows p =>
      candidateObservationCode p rows privateID time) := by
  classical
  apply measurable_pi_iff.mpr
  intro candidate
  have hrow : Measurable (fun rows : CompleteRows p => rows candidate) :=
    measurable_pi_apply candidate
  have hslice : Measurable (fun rows : CompleteRows p =>
      (((rows candidate).2 time).1)) := by
    exact measurable_fst.comp
      ((measurable_pi_apply time).comp (measurable_snd.comp hrow))
  have hslot : Measurable (fun rows : CompleteRows p =>
      slotDraw (((rows candidate).2 time).1)) :=
    measurable_slotDraw.comp hslice
  have hdata : Measurable (fun rows : CompleteRows p =>
      decide (slotDraw (((rows candidate).2 time).1) = dataSlot)) :=
    (measurable_of_finite
      (fun slot : Slot => decide (slot = dataSlot))).comp hslot
  have hforward : Measurable (fun rows : CompleteRows p =>
      (rows candidate).1 privateID time) := by
    exact (measurable_pi_apply time).comp
      ((measurable_pi_apply privateID).comp (measurable_fst.comp hrow))
  exact hdata.prodMk hforward

theorem measurable_candidateObservationCode_joint (p : Parameters) :
    Measurable (fun x : (Fin (A_id p) × Fin p.T) × CompleteRows p =>
      candidateObservationCode p x.2 x.1.1 x.1.2) := by
  apply measurable_from_prod_countable_right
  intro index
  exact measurable_candidateObservationCode_fixed p index.1 index.2

private noncomputable def observationGridIndex (p : Parameters) (y : Observation p) :
    Fin (D p + 1) := Classical.choose y.property

private theorem observationGridIndex_injective (p : Parameters) :
    Function.Injective (observationGridIndex p) := by
  intro y z h
  apply Subtype.ext
  have hy := Classical.choose_spec y.property
  have hz := Classical.choose_spec z.property
  apply Subtype.ext
  calc
    y.val.val = ((observationGridIndex p y).val : ℝ) / (D p : ℝ) := hy
    _ = ((observationGridIndex p z).val : ℝ) / (D p : ℝ) := congrArg
      (fun i : Fin (D p + 1) => (i.val : ℝ) / (D p : ℝ)) h
    _ = z.val.val := hz.symm

instance observationCountable (p : Parameters) : Countable (Observation p) :=
  (observationGridIndex_injective p).countable

/-- Positivity is tested on the original denominator-`D` observation. -/
noncomputable def observationPositiveFlag (p : Parameters) (observation : Observation p) : Bool :=
  decide (0 < observation.val.val)

theorem measurable_observationPositiveFlag (p : Parameters) :
    Measurable (observationPositiveFlag p) := measurable_of_countable _

/-- Separate joint-input carrier for the accepted positive-stay predicate. -/
abbrev PositiveStayInput (p : Parameters) :=
  IDArray p × (Fin (A_id p) × (Fin p.T × Observation p))

def assemblePositiveStayInput (ids : IDArray p) (privateID : Fin (A_id p))
    (time : Fin p.T) (observation : Observation p) : PositiveStayInput p :=
  (ids, (privateID, (time, observation)))

theorem measurable_assemblePositiveStayInput {Ω : Type*} [MeasurableSpace Ω]
    (ids : Ω → IDArray p) (privateID : Ω → Fin (A_id p))
    (time : Ω → Fin p.T) (observation : Ω → Observation p)
    (hids : Measurable ids) (hprivateID : Measurable privateID)
    (htime : Measurable time) (hobservation : Measurable observation) :
    Measurable (fun ω => assemblePositiveStayInput
      (ids ω) (privateID ω) (time ω) (observation ω)) := by
  exact hids.prodMk (hprivateID.prodMk (htime.prodMk hobservation))

noncomputable def positiveStayFlagOfInput (p : Parameters) (x : PositiveStayInput p) : Bool :=
  by
    classical
    exact decide (BootstrapObservedFollower.positiveStay x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem measurable_positiveStayFlagOfInput (p : Parameters) :
    Measurable (positiveStayFlagOfInput p) := by
  classical
  have hindex : Measurable (fun x : PositiveStayInput p => (x.2.1, x.2.2.1)) := by
    measurability
  have hids : Measurable (fun x : PositiveStayInput p => x.1) := measurable_fst
  let idBit : PositiveStayInput p → Bool := fun x => x.1 x.2.1 x.2.2.1
  let positiveBit : PositiveStayInput p → Bool := fun x => observationPositiveFlag p x.2.2.2
  have hidbit : Measurable idBit := by
    have hread : Measurable
        (fun z : (Fin (A_id p) × Fin p.T) × IDArray p => z.2 z.1.1 z.1.2) := by
      apply measurable_from_prod_countable_right
      intro index
      exact (measurable_pi_apply index.2).comp (measurable_pi_apply index.1)
    exact hread.comp (hindex.prodMk hids)
  have hpositive : Measurable positiveBit :=
    (measurable_observationPositiveFlag p).comp (by measurability)
  have hcombine : Measurable (fun x : PositiveStayInput p =>
      (idBit x, positiveBit x)) := hidbit.prodMk hpositive
  have hflag : Measurable (fun z : Bool × Bool => decide (z.1 = false ∧ z.2 = true)) :=
    measurable_of_finite _
  have hfactor : positiveStayFlagOfInput p =
      (fun z : Bool × Bool => decide (z.1 = false ∧ z.2 = true)) ∘
        (fun x : PositiveStayInput p => (idBit x, positiveBit x)) := by
    funext x
    simp [positiveStayFlagOfInput, BootstrapObservedFollower.positiveStay,
      observationPositiveFlag, idBit, positiveBit]
  rw [hfactor]
  exact hflag.comp hcombine

theorem measurable_positiveStayFlag_of_components {Ω : Type*}
    [MeasurableSpace Ω] (ids : Ω → IDArray p)
    (privateID : Ω → Fin (A_id p)) (time : Ω → Fin p.T)
    (observation : Ω → Observation p)
    (hids : Measurable ids) (hprivateID : Measurable privateID)
    (htime : Measurable time) (hobservation : Measurable observation) :
    Measurable (fun ω => positiveStayFlagOfInput p
      (assemblePositiveStayInput (ids ω) (privateID ω) (time ω) (observation ω))) := by
  exact (measurable_positiveStayFlagOfInput p).comp
    (measurable_assemblePositiveStayInput ids privateID time observation
      hids hprivateID htime hobservation)

theorem measurableSet_positiveStay (p : Parameters) :
    MeasurableSet {x : PositiveStayInput p |
      BootstrapObservedFollower.positiveStay x.1 x.2.1 x.2.2.1 x.2.2.2} := by
  classical
  have hflag := measurable_positiveStayFlagOfInput p
  have hset : {x : PositiveStayInput p |
      BootstrapObservedFollower.positiveStay x.1 x.2.1 x.2.2.1 x.2.2.2} =
      (positiveStayFlagOfInput p) ⁻¹' {true} := by
    ext x
    simp [positiveStayFlagOfInput, BootstrapObservedFollower.positiveStay]
  rw [hset]
  exact hflag (measurableSet_singleton true)

/-- The complete joint input to the existing observation advance. The source
factor is the unmodified source product; activity, ID, registers, time and the
exact typed own observation are separately varying inputs. -/
abbrev ObservationAdvanceInput (p : Parameters) :=
  ActualSource p ×
    (Bool × (Fin (A_id p) ×
      (RegistersCode p × (Fin p.T × Observation p))) )

def advanceSource (x : ObservationAdvanceInput p) : ActualSource p := x.1
def advanceActive (x : ObservationAdvanceInput p) : Bool := x.2.1
def advancePrivateID (x : ObservationAdvanceInput p) : Fin (A_id p) := x.2.2.1
def advanceRegisters (x : ObservationAdvanceInput p) : RegistersCode p := x.2.2.2.1
def advanceTime (x : ObservationAdvanceInput p) : Fin p.T := x.2.2.2.2.1
def advanceObservation (x : ObservationAdvanceInput p) : Observation p := x.2.2.2.2.2

def assembleObservationAdvanceInput (source : ActualSource p) (active : Bool)
    (privateID : Fin (A_id p)) (registers : RegistersCode p)
    (time : Fin p.T) (observation : Observation p) : ObservationAdvanceInput p :=
  (source, (active, (privateID, (registers, (time, observation)))))

theorem measurable_assembleObservationAdvanceInput {Ω : Type*} [MeasurableSpace Ω]
    (source : Ω → ActualSource p) (active : Ω → Bool)
    (privateID : Ω → Fin (A_id p)) (registers : Ω → RegistersCode p)
    (time : Ω → Fin p.T) (observation : Ω → Observation p)
    (hsource : Measurable source) (hactive : Measurable active)
    (hprivateID : Measurable privateID) (hregisters : Measurable registers)
    (htime : Measurable time) (hobservation : Measurable observation) :
    Measurable (fun ω => assembleObservationAdvanceInput (source ω) (active ω)
      (privateID ω) (registers ω) (time ω) (observation ω)) := by
  exact hsource.prodMk (hactive.prodMk (hprivateID.prodMk
    (hregisters.prodMk (htime.prodMk hobservation))))

/-- The exact finite key consumed by the all-candidate update. No continuous
row, private scalar, or complete source point is encoded. -/
abbrev ObservationAdvanceCode (p : Parameters) :=
  Bool × (Bool × (CandidateObservationCode p ×
    (Bool × (Fin (A_id p) × (RegistersCode p × Fin p.T)))) )

noncomputable def advanceCodeOfInput (p : Parameters) (x : ObservationAdvanceInput p) :
    ObservationAdvanceCode p :=
  (sourceIDs p x.1 (advancePrivateID x) (advanceTime x),
    (observationPositiveFlag p (advanceObservation x),
      (candidateObservationCode p (sourceRows p x.1) (advancePrivateID x) (advanceTime x),
        (advanceActive x,
          (advancePrivateID x, (advanceRegisters x, advanceTime x))))))

theorem advanceCodeOfInput_components (p : Parameters) (source : ActualSource p)
    (active : Bool) (privateID : Fin (A_id p)) (registers : RegistersCode p)
    (time : Fin p.T) (observation : Observation p) :
    advanceCodeOfInput p (assembleObservationAdvanceInput source active privateID
      registers time observation) =
      (sourceIDs p source privateID time,
        (observationPositiveFlag p observation,
          (candidateObservationCode p (sourceRows p source) privateID time,
            (active, (privateID, (registers, time)))))) := rfl

def advanceCodeIdBit (c : ObservationAdvanceCode p) : Bool := c.1
def advanceCodeObservationPositive (c : ObservationAdvanceCode p) : Bool := c.2.1
def advanceCodeRows (c : ObservationAdvanceCode p) : CandidateObservationCode p := c.2.2.1
def advanceCodeActive (c : ObservationAdvanceCode p) : Bool := c.2.2.2.1
def advanceCodePrivateID (c : ObservationAdvanceCode p) : Fin (A_id p) := c.2.2.2.2.1
def advanceCodeRegisters (c : ObservationAdvanceCode p) : RegistersCode p := c.2.2.2.2.2.1
def advanceCodeTime (c : ObservationAdvanceCode p) : Fin p.T := c.2.2.2.2.2.2

theorem measurable_advanceCodeOfInput (p : Parameters) :
    Measurable (advanceCodeOfInput p) := by
  have hindex : Measurable (fun x : ObservationAdvanceInput p =>
      (advancePrivateID x, advanceTime x)) := by
    unfold advancePrivateID advanceTime
    measurability
  have hids : Measurable (fun x : ObservationAdvanceInput p => sourceIDs p x.1) :=
    (measurable_sourceIDs p).comp measurable_fst
  have hrows : Measurable (fun x : ObservationAdvanceInput p => sourceRows p x.1) :=
    (measurable_sourceRows p).comp measurable_fst
  have hidbit : Measurable (fun x : ObservationAdvanceInput p =>
      sourceIDs p x.1 (advancePrivateID x) (advanceTime x)) := by
    have hread : Measurable
        (fun z : (Fin (A_id p) × Fin p.T) × IDArray p => z.2 z.1.1 z.1.2) := by
      apply measurable_from_prod_countable_right
      intro index
      exact (measurable_pi_apply index.2).comp (measurable_pi_apply index.1)
    exact hread.comp (hindex.prodMk hids)
  have hpositive : Measurable (fun x : ObservationAdvanceInput p =>
      observationPositiveFlag p (advanceObservation x)) := by
    exact (measurable_observationPositiveFlag p).comp
      (by change Measurable (fun x : ObservationAdvanceInput p => x.2.2.2.2.2); measurability)
  have hrowCode : Measurable (fun x : ObservationAdvanceInput p =>
      candidateObservationCode p (sourceRows p x.1)
        (advancePrivateID x) (advanceTime x)) := by
    exact measurable_candidateObservationCode_joint p |>.comp
      (hindex.prodMk hrows)
  have hactive : Measurable (advanceActive : ObservationAdvanceInput p → Bool) := by
    unfold advanceActive
    measurability
  have hprivate : Measurable (advancePrivateID : ObservationAdvanceInput p → Fin (A_id p)) := by
    unfold advancePrivateID
    measurability
  have hregisters : Measurable (advanceRegisters : ObservationAdvanceInput p → RegistersCode p) := by
    unfold advanceRegisters
    measurability
  have htime : Measurable (advanceTime : ObservationAdvanceInput p → Fin p.T) := by
    unfold advanceTime
    measurability
  exact hidbit.prodMk (hpositive.prodMk (hrowCode.prodMk
    (hactive.prodMk (hprivate.prodMk (hregisters.prodMk htime)))) )

/-- Candidate-local eligibility as a direct Boolean observable. -/
noncomputable def candidateEligibleFromCode (p : Parameters) (s : Fin (n_boot p))
    (c : ObservationAdvanceCode p) (candidate : Fin (M p)) : Bool :=
  by
    classical
    exact decide (c.2.2.2.2.2.2 ∈ calendarBlock p s ∧ c.2.2.2.1 = true ∧
      c.1 = false ∧ c.2.1 = true ∧ (c.2.2.1 candidate).1 = true)

/-- The accepted update applied to the direct observable code. -/
noncomputable def updateObservedEvidenceFromCode (p : Parameters) (s : Fin (n_boot p))
    (c : ObservationAdvanceCode p) : RegistersCode p := by
  classical
  exact
    { count := fun candidate =>
        if candidateEligibleFromCode p s c candidate then
          (c.2.2.2.2.2.1).count candidate + 1
        else (c.2.2.2.2.2.1).count candidate
      dead := fun candidate =>
        if candidateEligibleFromCode p s c candidate then
          (c.2.2.2.2.2.1).dead candidate ||
            decide ((c.2.2.1 candidate).2 = false)
        else (c.2.2.2.2.2.1).dead candidate
      pending := none }

/-- The full accepted pending/freeze rule applied to the direct code. -/
noncomputable def observationAdvanceFromCode (p : Parameters)
    (s : Fin (n_boot p)) (c : ObservationAdvanceCode p) : RegistersCode p := by
  classical
  exact if hpending : (c.2.2.2.2.2.1).pending.isSome then c.2.2.2.2.2.1 else
    if hpositive : c.2.2.2.2.2.2 ∈ calendarBlock p s ∧ c.2.2.2.1 = true ∧
        c.1 = false ∧ c.2.1 = true then
      let updated := updateObservedEvidenceFromCode p s c
      { count := updated.count
        dead := updated.dead
        pending := BootstrapAllCandidateController.uniqueMember
          (BootstrapAllCandidateController.passingSet updated) }
    else c.2.2.2.2.2.1

private theorem decideBool_eq_of_iff {a b : Prop} [Decidable a] [Decidable b]
    (h : a ↔ b) : decide a = decide b := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using h

theorem candidateEligibleFromCode_eq_observed (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : RegistersCode p) (time : Fin p.T) (observation : Observation p)
    (candidate : Fin (M p)) :
    candidateEligibleFromCode p s
      (advanceCodeOfInput p (assembleObservationAdvanceInput
        (assembleActualSource p ids rows privateCoords)
        active privateID registers time observation)) candidate =
      @decide (BootstrapObservedFollower.observedCandidateEligible p s ids rows active
        privateID time observation candidate) (Classical.propDecidable _) := by
  classical
  rw [advanceCodeOfInput_components p
    (assembleActualSource p ids rows privateCoords) active privateID registers time observation]
  unfold candidateEligibleFromCode
  apply decideBool_eq_of_iff
  dsimp [assembleActualSource, sourceIDs, sourceRows]
  simp [
    BootstrapObservedFollower.observedCandidateEligible,
    BootstrapObservedFollower.positiveStay, observationPositiveFlag,
    candidateObservationCode, BootstrapAllCandidateController.rowIsData,
    decide_eq_true_eq]
  tauto

theorem updateObservedEvidence_reconstruction (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : RegistersCode p) (time : Fin p.T) (observation : Observation p) :
    BootstrapObservedFollower.updateObservedEvidence p s ids rows active privateID
        registers time observation =
      updateObservedEvidenceFromCode p s
        (advanceCodeOfInput p (assembleObservationAdvanceInput
          (assembleActualSource p ids rows privateCoords) active privateID registers time observation)) := by
  classical
  apply BootstrapAllCandidateController.registers_ext
  · intro candidate
    simp only [BootstrapObservedFollower.updateObservedEvidence,
      updateObservedEvidenceFromCode]
    rw [candidateEligibleFromCode_eq_observed p s ids rows privateCoords active privateID
      registers time observation candidate]
    simp [decide_eq_true_eq, advanceCodeOfInput, assembleObservationAdvanceInput,
      assembleActualSource, advanceRegisters, advancePrivateID, advanceTime,
      sourceRows]
  · intro candidate
    simp only [BootstrapObservedFollower.updateObservedEvidence,
      updateObservedEvidenceFromCode]
    rw [candidateEligibleFromCode_eq_observed p s ids rows privateCoords active privateID
      registers time observation candidate]
    by_cases hforward : (rows candidate).1 privateID time
    · simp [hforward, advanceCodeOfInput, assembleObservationAdvanceInput,
        assembleActualSource, advanceRegisters, advancePrivateID, advanceTime,
        sourceRows, candidateObservationCode]
    · simp [hforward, advanceCodeOfInput, assembleObservationAdvanceInput,
        assembleActualSource, advanceRegisters, advancePrivateID, advanceTime,
        sourceRows, candidateObservationCode]
  · rfl

theorem observationAdvance_reconstruction (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p) (rows : CompleteRows p)
    (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : RegistersCode p) (time : Fin p.T) (observation : Observation p) :
    BootstrapObservedFollower.observationAdvance p s ids rows active privateID
        registers time observation =
      observationAdvanceFromCode p s
        (advanceCodeOfInput p (assembleObservationAdvanceInput
          (assembleActualSource p ids rows privateCoords) active privateID registers time observation)) := by
  classical
  let code := advanceCodeOfInput p (assembleObservationAdvanceInput
    (assembleActualSource p ids rows privateCoords) active privateID registers time observation)
  change BootstrapObservedFollower.observationAdvance p s ids rows active privateID
      registers time observation = observationAdvanceFromCode p s code
  have hcodeRegisters : code.2.2.2.2.2.1 = registers := by
    simp [code, advanceCodeOfInput, assembleObservationAdvanceInput,
      assembleActualSource, advanceRegisters]
  by_cases hpending : registers.pending.isSome
  · simp [BootstrapObservedFollower.observationAdvance, observationAdvanceFromCode,
      hpending, hcodeRegisters]
  · by_cases hpositive : time ∈ calendarBlock p s ∧ active = true ∧
        BootstrapObservedFollower.positiveStay ids privateID time observation
    · rcases hpositive with ⟨htime, hactive, hstay⟩
      subst active
      have hpositiveTrue : time ∈ calendarBlock p s ∧ (true : Bool) = true ∧
          BootstrapObservedFollower.positiveStay ids privateID time observation :=
        ⟨htime, rfl, hstay⟩
      have hcode : code.2.2.2.2.2.2 ∈ calendarBlock p s ∧
          code.2.2.2.1 = true ∧ code.1 = false ∧ code.2.1 = true := by
        rcases hstay with ⟨hid, hobs⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [code, advanceCodeOfInput, advanceTime, assembleObservationAdvanceInput,
            assembleActualSource] using htime
        · simp [code, advanceCodeOfInput, advanceActive, assembleObservationAdvanceInput,
            assembleActualSource]
        · simpa [code, advanceCodeOfInput, advancePrivateID, advanceTime,
            assembleObservationAdvanceInput, assembleActualSource, sourceIDs] using hid
        · simpa [code, advanceCodeOfInput, advanceObservation, observationPositiveFlag,
            assembleObservationAdvanceInput, assembleActualSource] using hobs
      have hcodeRegisters' : code.2.2.2.2.2.1 = registers := hcodeRegisters
      have hupdate : BootstrapObservedFollower.updateObservedEvidence p s ids rows true
          privateID registers time observation = updateObservedEvidenceFromCode p s code := by
        simpa [code] using updateObservedEvidence_reconstruction p s ids rows privateCoords
          true privateID registers time observation
      rw [BootstrapObservedFollower.observationAdvance, observationAdvanceFromCode]
      simp [hpending, hcodeRegisters', hpositiveTrue, hcode]
      rw [hupdate]
      simp
    · have hcode : ¬ (time ∈ calendarBlock p s ∧ active = true ∧
          sourceIDs p (assembleActualSource p ids rows privateCoords) privateID time = false ∧
            observationPositiveFlag p observation = true) := by
        intro hc
        rcases hc with ⟨htime, hactive, hid, hobs⟩
        apply hpositive
        refine ⟨htime, hactive, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [assembleActualSource, sourceIDs] using hid
        · simpa [observationPositiveFlag] using hobs
      have hcode' : ¬ (code.2.2.2.2.2.2 ∈ calendarBlock p s ∧
          code.2.2.2.1 = true ∧ code.1 = false ∧ code.2.1 = true) := by
        simpa [code, advanceCodeOfInput, advanceActive, advancePrivateID, advanceRegisters,
          advanceTime, advanceObservation, observationPositiveFlag,
          assembleObservationAdvanceInput, assembleActualSource, sourceIDs] using hcode
      rw [BootstrapObservedFollower.observationAdvance, observationAdvanceFromCode]
      simp [hpending, hcodeRegisters, hpositive, hcode']

theorem observationAdvanceInput_reconstruction (p : Parameters)
    (s : Fin (n_boot p)) (x : ObservationAdvanceInput p) :
    BootstrapObservedFollower.observationAdvance p s
        (sourceIDs p x.1) (sourceRows p x.1) (advanceActive x)
        (advancePrivateID x) (advanceRegisters x) (advanceTime x)
        (advanceObservation x) =
      observationAdvanceFromCode p s (advanceCodeOfInput p x) := by
  rcases x with ⟨source, active, privateID, registers, time, observation⟩
  simpa [advanceActive, advancePrivateID, advanceRegisters, advanceTime,
    advanceObservation, advanceSource, assembleObservationAdvanceInput,
    assembleActualSource_components] using
      observationAdvance_reconstruction p s (sourceIDs p source) (sourceRows p source)
        (sourcePrivate p source) active privateID registers time observation

theorem measurable_updateObservedEvidenceFromCode (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (updateObservedEvidenceFromCode p s) := measurable_of_countable _

theorem measurable_observationAdvanceFromCode (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (observationAdvanceFromCode p s) := measurable_of_countable _

theorem measurable_updateObservedEvidenceInput (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (fun x : ObservationAdvanceInput p =>
      BootstrapObservedFollower.updateObservedEvidence p s
        (sourceIDs p x.1) (sourceRows p x.1) (advanceActive x)
        (advancePrivateID x) (advanceRegisters x) (advanceTime x)
        (advanceObservation x)) := by
  have h : (fun x : ObservationAdvanceInput p =>
      BootstrapObservedFollower.updateObservedEvidence p s
        (sourceIDs p x.1) (sourceRows p x.1) (advanceActive x)
        (advancePrivateID x) (advanceRegisters x) (advanceTime x)
        (advanceObservation x)) =
      fun x => updateObservedEvidenceFromCode p s (advanceCodeOfInput p x) := by
    funext x
    exact updateObservedEvidence_reconstruction p s (sourceIDs p x.1)
      (sourceRows p x.1) (sourcePrivate p x.1) (advanceActive x)
      (advancePrivateID x) (advanceRegisters x) (advanceTime x) (advanceObservation x)
  rw [h]
  exact (measurable_updateObservedEvidenceFromCode p s).comp
    (measurable_advanceCodeOfInput p)

theorem measurable_observationAdvanceInput (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (fun x : ObservationAdvanceInput p =>
      BootstrapObservedFollower.observationAdvance p s
        (sourceIDs p x.1) (sourceRows p x.1) (advanceActive x)
        (advancePrivateID x) (advanceRegisters x) (advanceTime x)
        (advanceObservation x)) := by
  have h : (fun x : ObservationAdvanceInput p =>
      BootstrapObservedFollower.observationAdvance p s
        (sourceIDs p x.1) (sourceRows p x.1) (advanceActive x)
        (advancePrivateID x) (advanceRegisters x) (advanceTime x)
        (advanceObservation x)) =
      fun x => observationAdvanceFromCode p s (advanceCodeOfInput p x) := by
    funext x
    exact observationAdvance_reconstruction p s (sourceIDs p x.1)
      (sourceRows p x.1) (sourcePrivate p x.1) (advanceActive x)
      (advancePrivateID x) (advanceRegisters x) (advanceTime x) (advanceObservation x)
  rw [h]
  exact (measurable_observationAdvanceFromCode p s).comp
    (measurable_advanceCodeOfInput p)

/-- The actual eligible predicate is measurable jointly in the untouched
source, activity, private ID, registers, time, own observation, and candidate. -/
theorem measurable_observedCandidateEligibleInput (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (fun x : ObservationAdvanceInput p × Fin (M p) =>
      @decide (BootstrapObservedFollower.observedCandidateEligible p s
        (sourceIDs p x.1.1) (sourceRows p x.1.1) (advanceActive x.1)
        (advancePrivateID x.1) (advanceTime x.1) (advanceObservation x.1) x.2)
        (Classical.propDecidable _)) := by
  let f : ObservationAdvanceCode p × Fin (M p) → Bool := fun z =>
    candidateEligibleFromCode p s z.1 z.2
  have hf : Measurable f := measurable_of_countable f
  have hkey : Measurable (fun x : ObservationAdvanceInput p × Fin (M p) =>
      (advanceCodeOfInput p x.1, x.2)) :=
    (measurable_advanceCodeOfInput p).comp measurable_fst |>.prodMk measurable_snd
  have hfactor : (fun x : ObservationAdvanceInput p × Fin (M p) =>
      @decide (BootstrapObservedFollower.observedCandidateEligible p s
        (sourceIDs p x.1.1) (sourceRows p x.1.1) (advanceActive x.1)
        (advancePrivateID x.1) (advanceTime x.1) (advanceObservation x.1) x.2)
        (Classical.propDecidable _)) =
      f ∘ (fun x => (advanceCodeOfInput p x.1, x.2)) := by
    funext x
    exact (candidateEligibleFromCode_eq_observed p s
      (sourceIDs p x.1.1) (sourceRows p x.1.1) (sourcePrivate p x.1.1)
      (advanceActive x.1) (advancePrivateID x.1) (advanceRegisters x.1)
      (advanceTime x.1) (advanceObservation x.1) x.2).symm
  rw [hfactor]
  exact hf.comp hkey

theorem measurable_observedCandidateEligible_of_components {Ω : Type*}
    [MeasurableSpace Ω] (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Ω → Bool) (privateID : Ω → Fin (A_id p))
    (registers : Ω → RegistersCode p) (time : Ω → Fin p.T)
    (observation : Ω → Observation p) (candidate : Ω → Fin (M p))
    (hids : Measurable ids) (hrows : Measurable rows)
    (hprivate : Measurable privateCoords) (hactive : Measurable active)
    (hprivateID : Measurable privateID) (hregisters : Measurable registers)
    (htime : Measurable time) (hobservation : Measurable observation)
    (hcandidate : Measurable candidate) :
    Measurable (fun ω =>
      @decide (BootstrapObservedFollower.observedCandidateEligible p s
        (ids ω) (rows ω) (active ω) (privateID ω) (time ω) (observation ω)
        (candidate ω)) (Classical.propDecidable _)) := by
  let source : Ω → ActualSource p := fun ω =>
    assembleActualSource p (ids ω) (rows ω) (privateCoords ω)
  have hsource : Measurable source := by
    simpa [source] using
      measurable_assembleActualSource ids rows privateCoords hids hrows hprivate
  let input : Ω → ObservationAdvanceInput p := fun ω =>
    assembleObservationAdvanceInput (source ω) (active ω) (privateID ω)
      (registers ω) (time ω) (observation ω)
  have hinput : Measurable input := by
    exact measurable_assembleObservationAdvanceInput source active privateID
      registers time observation hsource hactive hprivateID hregisters htime hobservation
  have hpair : Measurable (fun ω => (input ω, candidate ω)) :=
    hinput.prodMk hcandidate
  have hresult := (measurable_observedCandidateEligibleInput p s).comp hpair
  change Measurable (fun ω =>
    @decide (BootstrapObservedFollower.observedCandidateEligible p s
      (sourceIDs p (input ω).1) (sourceRows p (input ω).1) (advanceActive (input ω))
      (advancePrivateID (input ω)) (advanceTime (input ω))
      (advanceObservation (input ω)) (candidate ω)) (Classical.propDecidable _)) at hresult
  change Measurable (fun ω =>
    @decide (BootstrapObservedFollower.observedCandidateEligible p s
      (sourceIDs p (input ω).1) (sourceRows p (input ω).1) (advanceActive (input ω))
      (advancePrivateID (input ω)) (advanceTime (input ω))
      (advanceObservation (input ω)) (candidate ω)) (Classical.propDecidable _))
  exact hresult

/-- Arbitrary-base composition for the joint actual observer advance. Each
component map is supplied separately; no candidate update is a premise. -/
theorem measurable_observationAdvance_of_components {Ω : Type*} [MeasurableSpace Ω]
    (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Ω → Bool) (privateID : Ω → Fin (A_id p))
    (registers : Ω → RegistersCode p) (time : Ω → Fin p.T)
    (observation : Ω → Observation p)
    (hids : Measurable ids) (hrows : Measurable rows) (hprivate : Measurable privateCoords)
    (hactive : Measurable active) (hprivateID : Measurable privateID)
    (hregisters : Measurable registers) (htime : Measurable time)
    (hobservation : Measurable observation) :
    Measurable (fun ω => BootstrapObservedFollower.observationAdvance p s
      (ids ω) (rows ω) (active ω) (privateID ω) (registers ω) (time ω)
      (observation ω)) := by
  have hsource : Measurable (fun ω => assembleActualSource p
      (ids ω) (rows ω) (privateCoords ω)) :=
    measurable_assembleActualSource (fun ω => ids ω) (fun ω => rows ω)
      (fun ω => privateCoords ω) hids hrows hprivate
  exact (measurable_observationAdvanceInput p s).comp
    (measurable_assembleObservationAdvanceInput
      (fun ω => assembleActualSource p (ids ω) (rows ω) (privateCoords ω))
      active privateID registers time observation hsource hactive hprivateID
      hregisters htime hobservation)

theorem measurable_updateObservedEvidence_of_components {Ω : Type*}
    [MeasurableSpace Ω] (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (active : Ω → Bool) (privateID : Ω → Fin (A_id p))
    (registers : Ω → RegistersCode p) (time : Ω → Fin p.T)
    (observation : Ω → Observation p)
    (hids : Measurable ids) (hrows : Measurable rows) (hprivate : Measurable privateCoords)
    (hactive : Measurable active) (hprivateID : Measurable privateID)
    (hregisters : Measurable registers) (htime : Measurable time)
    (hobservation : Measurable observation) :
    Measurable (fun ω => BootstrapObservedFollower.updateObservedEvidence p s
      (ids ω) (rows ω) (active ω) (privateID ω) (registers ω) (time ω)
      (observation ω)) := by
  have hsource : Measurable (fun ω => assembleActualSource p
      (ids ω) (rows ω) (privateCoords ω)) :=
    measurable_assembleActualSource (fun ω => ids ω) (fun ω => rows ω)
      (fun ω => privateCoords ω) hids hrows hprivate
  exact (measurable_updateObservedEvidenceInput p s).comp
    (measurable_assembleObservationAdvanceInput
      (fun ω => assembleActualSource p (ids ω) (rows ω) (privateCoords ω))
      active privateID registers time observation hsource hactive hprivateID
      hregisters htime hobservation)

/-! ## Actual observation result, numerators, and block finish -/

/-- The exact input to the existing `observe` operation. The first component
is discrete state/time; the second retains the full source and exact own
observation. -/
abbrev ObserveInput (p : Parameters) (s : Fin (n_boot p)) :=
  (StartupCode p s × Fin p.T) × (ActualSource p × Observation p)

def assembleObserveInput (source : ActualSource p) (state : StartupCode p s)
    (time : Fin p.T) (observation : Observation p) : ObserveInput p s :=
  ((state, time), (source, observation))

theorem measurable_assembleObserveInput {Ω : Type*} [MeasurableSpace Ω]
    (source : Ω → ActualSource p) (state : Ω → StartupCode p s)
    (time : Ω → Fin p.T) (observation : Ω → Observation p)
    (hsource : Measurable source) (hstate : Measurable state)
    (htime : Measurable time) (hobservation : Measurable observation) :
    Measurable (fun ω => assembleObserveInput (source ω) (state ω) (time ω)
      (observation ω)) := by
  exact (hstate.prodMk htime).prodMk (hsource.prodMk hobservation)

/-- The finite read record used by `observe`: a valid active observation keeps
its positive bit and ID bit; candidate row bits are included only before the
pending freeze. -/
abbrev ObserverReadCode (p : Parameters) :=
  Option (Bool × (Bool × Option (CandidateObservationCode p)))

abbrev ObserverReadInput (p : Parameters) (s : Fin (n_boot p)) :=
  (StartupCode p s × Fin p.T) × (ActualSource p × Observation p)

noncomputable def observerReadCode (p : Parameters) (s : Fin (n_boot p))
    (x : ObserverReadInput p s) : ObserverReadCode p := by
  classical
  match BootstrapObservedFollower.validateRound p s x.1.1 x.1.2 with
  | .failure _ => exact none
  | .next _ _ _ =>
      match x.1.1.blockCase with
      | .inactive => exact none
      | .active _ privateID _ registers =>
          exact some (observationPositiveFlag p x.2.2,
            (sourceIDs p x.2.1 privateID x.1.2,
              if registers.pending.isSome then none else
                some (candidateObservationCode p (sourceRows p x.2.1) privateID x.1.2)))

instance observerReadCodeCountable (p : Parameters) : Countable (ObserverReadCode p) := by
  exact inferInstance

instance observerReadCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (ObserverReadCode p) := ⊤

instance observerReadCodeMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (ObserverReadCode p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

instance candidateObservationOptionMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (CandidateObservationCode p)) := ⊤

instance candidateObservationOptionMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (Option (CandidateObservationCode p)) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

private theorem measurable_observerReadCode (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (observerReadCode p s) := by
  apply measurable_from_prod_countable_right
  intro key
  rcases key with ⟨state, time⟩
  classical
  cases hvalidation : BootstrapObservedFollower.validateRound p s state time with
  | failure error =>
      simp [observerReadCode, hvalidation]
  | next hin hopen hnext =>
      cases hcase : state.blockCase with
      | inactive =>
          simp [observerReadCode, hvalidation, hcase]
      | active held privateID gain registers =>
          have hpositive : Measurable (fun z : ActualSource p × Observation p =>
              observationPositiveFlag p z.2) :=
            (measurable_observationPositiveFlag p).comp measurable_snd
          have hid : Measurable (fun z : ActualSource p × Observation p =>
              sourceIDs p z.1 privateID time) := by
            exact (measurable_pi_apply time).comp
              ((measurable_pi_apply privateID).comp
                ((measurable_sourceIDs p).comp measurable_fst))
          by_cases hpending : registers.pending.isSome
          · have hpair := hpositive.prodMk hid
            let pack : Bool × (Bool × Option (CandidateObservationCode p)) →
                ObserverReadCode p := fun z => some (z.1, (z.2.1, none))
            have hpack : Measurable pack := measurable_of_countable pack
            have hdata : Measurable (fun z : ActualSource p × Observation p =>
                (observationPositiveFlag p z.2,
                  (sourceIDs p z.1 privateID time,
                    (none : Option (CandidateObservationCode p))))) := by
              exact hpositive.prodMk (hid.prodMk measurable_const)
            have hresult : (fun z : ActualSource p × Observation p =>
                observerReadCode p s ((state, time), z)) = pack ∘ (fun z =>
                  (observationPositiveFlag p z.2, (sourceIDs p z.1 privateID time, none))) := by
              funext z
              simp [observerReadCode, hvalidation, hcase, hpending, pack]
            rw [hresult]
            exact hpack.comp hdata
          · have hrows : Measurable (fun z : ActualSource p × Observation p =>
                candidateObservationCode p (sourceRows p z.1) privateID time) := by
              exact (measurable_candidateObservationCode_fixed p privateID time).comp
                ((measurable_sourceRows p).comp measurable_fst)
            let pack : Bool × (Bool × Option (CandidateObservationCode p)) →
                ObserverReadCode p := fun z => some (z.1, (z.2.1, z.2.2))
            have hpack : Measurable pack := measurable_of_countable pack
            have hdata : Measurable (fun z : ActualSource p × Observation p =>
                (observationPositiveFlag p z.2,
                  (sourceIDs p z.1 privateID time,
                    some (candidateObservationCode p (sourceRows p z.1) privateID time)))) := by
              have hsome : Measurable (fun z : CandidateObservationCode p =>
                  (some z : Option (CandidateObservationCode p))) :=
                measurable_of_countable _
              exact hpositive.prodMk (hid.prodMk (hsome.comp hrows))
            have hresult : (fun z : ActualSource p × Observation p =>
                observerReadCode p s ((state, time), z)) = pack ∘ (fun z =>
                  (observationPositiveFlag p z.2,
                    (sourceIDs p z.1 privateID time,
                      some (candidateObservationCode p (sourceRows p z.1) privateID time)))) := by
              funext z
              simp [observerReadCode, hvalidation, hcase, hpending, pack]
            rw [hresult]
            exact hpack.comp hdata

/-- A fully discrete observable key for one real observation step. -/
abbrev ObserverInputKey (p : Parameters) (s : Fin (n_boot p)) :=
  StartupCode p s × (Fin p.T × ObserverReadCode p)

noncomputable def observerInputKey (p : Parameters) (s : Fin (n_boot p))
    (x : ObserveInput p s) : ObserverInputKey p s :=
  (x.1.1, (x.1.2, observerReadCode p s x))

theorem measurable_observerInputKey (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (observerInputKey p s) := by
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_observerReadCode p s).comp measurable_id))

private theorem observerInputKey_fiber_constant (p : Parameters)
    (s : Fin (n_boot p)) (x y : ObserveInput p s)
    (hkey : observerInputKey p s x = observerInputKey p s y) :
    BootstrapObservedFollower.observe p s x.1.1
      (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2 =
    BootstrapObservedFollower.observe p s y.1.1
      (sourceIDs p y.2.1) (sourceRows p y.2.1) y.1.2 y.2.2 := by
  have hkey' := hkey
  change (x.1.1, (x.1.2, observerReadCode p s x)) =
    (y.1.1, (y.1.2, observerReadCode p s y)) at hkey'
  injection hkey' with hstate hrest
  injection hrest with htime hread
  rcases x with ⟨⟨stateX, timeX⟩, ⟨sourceX, observationX⟩⟩
  rcases y with ⟨⟨stateY, timeY⟩, ⟨sourceY, observationY⟩⟩
  dsimp at hstate htime
  subst stateY
  subst timeY
  change BootstrapObservedFollower.observe p s stateX (sourceIDs p sourceX)
      (sourceRows p sourceX) timeX observationX =
    BootstrapObservedFollower.observe p s stateX (sourceIDs p sourceY)
      (sourceRows p sourceY) timeX observationY
  cases hvalidation : BootstrapObservedFollower.validateRound p s stateX timeX with
  | failure error =>
      simp [BootstrapObservedFollower.observe, hvalidation]
  | next hin hopen hnext =>
      cases hcase : stateX.blockCase with
      | inactive =>
          simp [BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
            BootstrapObservedFollower.observeBlockCase, hvalidation, hcase]
      | active held privateID gain registers =>
          have hread' := hread
          by_cases hpending : registers.pending.isSome
          · simp [observerReadCode, hvalidation, hcase, hpending] at hread'
            rcases hread' with ⟨hpositive, hid⟩
            have hpositiveProp : 0 < observationX.val.val ↔
                0 < observationY.val.val := by
              have hp := congrArg (fun b : Bool => b = true) hpositive
              simpa [observationPositiveFlag] using hp
            have hstay :
                BootstrapObservedFollower.positiveStay (sourceIDs p sourceX)
                  privateID timeX observationX =
                BootstrapObservedFollower.positiveStay (sourceIDs p sourceY)
                  privateID timeX observationY := by
              simp [BootstrapObservedFollower.positiveStay, hid, hpositiveProp]
            have hadvance :
                BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceX) (sourceRows p sourceX) true privateID registers
                  timeX observationX =
                BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceY) (sourceRows p sourceY) true privateID registers
                  timeX observationY := by
              simp [BootstrapObservedFollower.observationAdvance, hpending]
            cases stateX with
            | mk numerators lower processed blockCase gainBound =>
              have hcase' : blockCase = .active held privateID gain registers := by
                simpa using hcase
              subst blockCase
              simp [BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
                BootstrapObservedFollower.observeBlockCase, hvalidation, hadvance]
              rw [hstay]
          · simp [observerReadCode, hvalidation, hcase, hpending] at hread'
            rcases hread' with ⟨hpositive, hidAndRows⟩
            rcases hidAndRows with ⟨hid, hrowsSome⟩
            have hrows := hrowsSome
            have hpositiveProp : 0 < observationX.val.val ↔
                0 < observationY.val.val := by
              have hp := congrArg (fun b : Bool => b = true) hpositive
              simpa [observationPositiveFlag] using hp
            have hstay :
                BootstrapObservedFollower.positiveStay (sourceIDs p sourceX)
                  privateID timeX observationX =
                BootstrapObservedFollower.positiveStay (sourceIDs p sourceY)
                  privateID timeX observationY := by
              simp [BootstrapObservedFollower.positiveStay, hid, hpositiveProp]
            have hcode :
                advanceCodeOfInput p
                    (assembleObservationAdvanceInput sourceX true privateID registers
                      timeX observationX) =
                  advanceCodeOfInput p
                    (assembleObservationAdvanceInput sourceY true privateID registers
                      timeX observationY) := by
              rw [advanceCodeOfInput_components p sourceX true privateID registers
                    timeX observationX,
                  advanceCodeOfInput_components p sourceY true privateID registers
                    timeX observationY]
              apply Prod.ext
              · exact hid
              · apply Prod.ext
                · exact hpositive
                · apply Prod.ext
                  · exact hrows
                  · apply Prod.ext
                    · rfl
                    · apply Prod.ext
                      · rfl
                      · apply Prod.ext <;> rfl
            have hadvance :
                BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceX) (sourceRows p sourceX) true privateID registers
                  timeX observationX =
                BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceY) (sourceRows p sourceY) true privateID registers
                  timeX observationY := by
              have hleft := observationAdvanceInput_reconstruction p s
                (assembleObservationAdvanceInput sourceX true privateID registers
                  timeX observationX)
              have hright := observationAdvanceInput_reconstruction p s
                (assembleObservationAdvanceInput sourceY true privateID registers
                  timeX observationY)
              have hleft' : BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceX) (sourceRows p sourceX) true privateID registers
                  timeX observationX = observationAdvanceFromCode p s
                    (advanceCodeOfInput p (assembleObservationAdvanceInput sourceX true
                      privateID registers timeX observationX)) := by
                change BootstrapObservedFollower.observationAdvance p s
                    (sourceIDs p sourceX) (sourceRows p sourceX) true privateID registers
                    timeX observationX = observationAdvanceFromCode p s
                      (advanceCodeOfInput p (assembleObservationAdvanceInput sourceX true
                        privateID registers timeX observationX)) at hleft
                exact hleft
              have hright' : BootstrapObservedFollower.observationAdvance p s
                  (sourceIDs p sourceY) (sourceRows p sourceY) true privateID registers
                  timeX observationY = observationAdvanceFromCode p s
                    (advanceCodeOfInput p (assembleObservationAdvanceInput sourceY true
                      privateID registers timeX observationY)) := by
                change BootstrapObservedFollower.observationAdvance p s
                    (sourceIDs p sourceY) (sourceRows p sourceY) true privateID registers
                    timeX observationY = observationAdvanceFromCode p s
                      (advanceCodeOfInput p (assembleObservationAdvanceInput sourceY true
                        privateID registers timeX observationY)) at hright
                exact hright
              rw [hleft', hright']
              exact congrArg (observationAdvanceFromCode p s) hcode
            cases stateX with
            | mk numerators lower processed blockCase gainBound =>
              have hcase' : blockCase = .active held privateID gain registers := by
                simpa using hcase
              subst blockCase
              simp [BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
                BootstrapObservedFollower.observeBlockCase, hvalidation, hadvance]
              rw [hstay]

theorem measurable_observeInput (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (fun x : ObserveInput p s =>
      BootstrapObservedFollower.observe p s x.1.1
        (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2) := by
  exact measurable_of_countable_key (observerInputKey p s)
    (measurable_observerInputKey p s) _
    (observerInputKey_fiber_constant p s)

theorem measurable_observe_of_components {Ω : Type*} [MeasurableSpace Ω]
    (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (state : Ω → StartupCode p s) (time : Ω → Fin p.T)
    (observation : Ω → Observation p)
    (hids : Measurable ids) (hrows : Measurable rows) (hprivate : Measurable privateCoords)
    (hstate : Measurable state) (htime : Measurable time)
    (hobservation : Measurable observation) :
    Measurable (fun ω => BootstrapObservedFollower.observe p s (state ω)
      (ids ω) (rows ω) (time ω) (observation ω)) := by
  let source : Ω → ActualSource p := fun ω =>
    assembleActualSource p (ids ω) (rows ω) (privateCoords ω)
  have hsource : Measurable source := by
    simpa [source] using
      measurable_assembleActualSource ids rows privateCoords hids hrows hprivate
  exact (measurable_observeInput p s).comp
    (measurable_assembleObserveInput source state time observation
      hsource hstate htime hobservation)

/-- The state projection of the existing `observeBlockCase`, using the
operation's actual checked validation and retaining every invalid-round case. -/
noncomputable def observeBlockCaseFromInput (p : Parameters) (s : Fin (n_boot p))
    (x : ObserveInput p s) : BootstrapObservedFollower.StartupBlockCase p :=
  BootstrapObservedFollower.observeBlockCase p s x.1.1
    (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2
    (BootstrapObservedFollower.validateRound p s x.1.1 x.1.2)

def observeResultBlockCase (p : Parameters) (s : Fin (n_boot p))
    (state : StartupCode p s) (result : BootstrapObservedFollower.ObserveResult p s) :
    BootstrapObservedFollower.StartupBlockCase p :=
  match result with
  | .rejected _ => state.blockCase
  | .accepted output => output.blockCase

theorem observeBlockCaseFromInput_eq_resultProjection (p : Parameters)
    (s : Fin (n_boot p)) (x : ObserveInput p s) :
    observeBlockCaseFromInput p s x =
      observeResultBlockCase p s x.1.1
        (BootstrapObservedFollower.observe p s x.1.1
          (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2) := by
  cases hvalidation : BootstrapObservedFollower.validateRound p s x.1.1 x.1.2 with
  | failure error =>
      simp [observeBlockCaseFromInput, observeResultBlockCase,
        BootstrapObservedFollower.observe, BootstrapObservedFollower.observeBlockCase,
        hvalidation]
  | next hin hopen hnext =>
      simp [observeBlockCaseFromInput, observeResultBlockCase,
        BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hvalidation]

theorem measurable_observeBlockCaseInput (p : Parameters)
    (s : Fin (n_boot p)) :
    Measurable (observeBlockCaseFromInput p s) := by
  let project : StartupCode p s × BootstrapObservedFollower.ObserveResult p s →
      BootstrapObservedFollower.StartupBlockCase p :=
    fun z => observeResultBlockCase p s z.1 z.2
  have hproject : Measurable project := measurable_of_countable project
  have hpair : Measurable (fun x : ObserveInput p s =>
      (x.1.1, BootstrapObservedFollower.observe p s x.1.1
        (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_observeInput p s)
  have heq : observeBlockCaseFromInput p s =
      project ∘ (fun x : ObserveInput p s =>
        (x.1.1, BootstrapObservedFollower.observe p s x.1.1
          (sourceIDs p x.2.1) (sourceRows p x.2.1) x.1.2 x.2.2)) := by
    funext x
    exact observeBlockCaseFromInput_eq_resultProjection p s x
  rw [heq]
  exact hproject.comp hpair

theorem measurable_observeBlockCase_of_components {Ω : Type*}
    [MeasurableSpace Ω] (ids : Ω → IDArray p) (rows : Ω → CompleteRows p)
    (privateCoords : Ω → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (state : Ω → StartupCode p s) (time : Ω → Fin p.T)
    (observation : Ω → Observation p)
    (hids : Measurable ids) (hrows : Measurable rows)
    (hprivate : Measurable privateCoords) (hstate : Measurable state)
    (htime : Measurable time) (hobservation : Measurable observation) :
    Measurable (fun ω => observeBlockCaseFromInput p s
      (assembleObserveInput
        (assembleActualSource p (ids ω) (rows ω) (privateCoords ω))
        (state ω) (time ω) (observation ω))) := by
  have hsource : Measurable (fun ω =>
      assembleActualSource p (ids ω) (rows ω) (privateCoords ω)) :=
    measurable_assembleActualSource ids rows privateCoords hids hrows hprivate
  exact (measurable_observeBlockCaseInput p s).comp
    (measurable_assembleObserveInput
      (fun ω => assembleActualSource p (ids ω) (rows ω) (privateCoords ω))
      state time observation hsource hstate htime hobservation)

private def finishFailureKey {p : Parameters} {s : Fin (n_boot p)}
    (error : BootstrapObservedFollower.FinishFailure p s) : ℕ × ℕ :=
  match error with
  | .incomplete processed expected => (processed, expected)

private theorem finishFailureKey_injective {p : Parameters}
    {s : Fin (n_boot p)} :
    Function.Injective (finishFailureKey (p := p) (s := s)) := by
  intro a b h
  cases a
  cases b
  simp_all [finishFailureKey]

instance finishFailureCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (BootstrapObservedFollower.FinishFailure p s) :=
  (finishFailureKey_injective (p := p) (s := s)).countable

private def boundaryOutputKey {p : Parameters} {s : Fin (n_boot p)}
    (output : BootstrapObservedFollower.BoundaryOutput p s) :
    Sum ((Fin p.K → ℕ) × ReferencePrelaunchFollower.Activation p)
      (Fin (M p) × ReferencePrelaunchFollower.Activation p) :=
  match output with
  | .continueWithWeights numerators _ activation => .inl (numerators, activation)
  | .declareRow row activation => .inr (row, activation)

private theorem boundaryOutputKey_injective {p : Parameters}
    {s : Fin (n_boot p)} :
    Function.Injective (boundaryOutputKey (p := p) (s := s)) := by
  intro a b h
  cases a with
  | continueWithWeights na ha aa =>
      cases b with
      | continueWithWeights nb hb ab =>
          simp only [boundaryOutputKey, Sum.inl.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | declareRow row activation => cases h
  | declareRow ra aa =>
      cases b with
      | continueWithWeights numerators lowerBound activation => cases h
      | declareRow rb ab =>
          simp only [boundaryOutputKey, Sum.inr.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl

instance boundaryOutputCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (BootstrapObservedFollower.BoundaryOutput p s) := by
  exact (boundaryOutputKey_injective (p := p) (s := s)).countable

private def finishResultKey {p : Parameters} {s : Fin (n_boot p)}
    (result : Except (BootstrapObservedFollower.FinishFailure p s)
      (BootstrapObservedFollower.BoundaryOutput p s)) :
    Sum (BootstrapObservedFollower.FinishFailure p s)
      (BootstrapObservedFollower.BoundaryOutput p s) :=
  match result with
  | .error error => .inl error
  | .ok output => .inr output

private theorem finishResultKey_injective {p : Parameters}
    {s : Fin (n_boot p)} :
    Function.Injective (finishResultKey (p := p) (s := s)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [finishResultKey]

instance finishResultCountable (p : Parameters) (s : Fin (n_boot p)) :
    Countable (Except (BootstrapObservedFollower.FinishFailure p s)
      (BootstrapObservedFollower.BoundaryOutput p s)) := by
  exact (finishResultKey_injective (p := p) (s := s)).countable

instance finishResultMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (Except (BootstrapObservedFollower.FinishFailure p s)
      (BootstrapObservedFollower.BoundaryOutput p s)) := ⊤

instance finishResultMeasurableSingletonClass (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSingletonClass (Except (BootstrapObservedFollower.FinishFailure p s)
      (BootstrapObservedFollower.BoundaryOutput p s)) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

/-- Direct output code for the existing finish operation. It retains both
continuation-with-updated-weights and pending-row activation cases, along with
incomplete-block errors. -/
noncomputable def finishBlockCode (p : Parameters) (s : Fin (n_boot p))
    (state : StartupCode p s) := BootstrapObservedFollower.finishBlock p s state

theorem finishBlockCode_reconstruction (p : Parameters) (s : Fin (n_boot p))
    (state : StartupCode p s) :
    finishBlockCode p s state = BootstrapObservedFollower.finishBlock p s state := rfl

/-- Numerator output uses the direct existing countable Pi carrier. -/
noncomputable def updatedNumeratorsCode (p : Parameters) (s : Fin (n_boot p))
    (state : StartupCode p s) : Fin p.K → ℕ :=
  BootstrapObservedFollower.updatedNumerators p s state

theorem updatedNumeratorsCode_reconstruction (p : Parameters)
    (s : Fin (n_boot p)) (state : StartupCode p s) :
    updatedNumeratorsCode p s state =
      BootstrapObservedFollower.updatedNumerators p s state := rfl

theorem measurable_updatedNumeratorsCode (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (updatedNumeratorsCode p s) := by
  apply measurable_pi_iff.mpr
  intro arm
  exact measurable_of_countable (fun state : StartupCode p s =>
    BootstrapObservedFollower.updatedNumerators p s state arm)

theorem measurable_finishBlockCode (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (finishBlockCode p s) := measurable_of_countable _

theorem measurable_updatedNumeratorsCode_of_components {Ω : Type*}
    [MeasurableSpace Ω] (state : Ω → StartupCode p s) (hstate : Measurable state) :
    Measurable (fun ω => updatedNumeratorsCode p s (state ω)) :=
  (measurable_updatedNumeratorsCode p s).comp hstate

theorem measurable_finishBlockCode_of_components {Ω : Type*}
    [MeasurableSpace Ω] (state : Ω → StartupCode p s) (hstate : Measurable state) :
    Measurable (fun ω => finishBlockCode p s (state ω)) :=
  (measurable_finishBlockCode p s).comp hstate

end Bandits.Support.ActualBootstrapObservationCode

end
