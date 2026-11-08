/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.SparseCalendarReplay
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.FollowerCutoffScan
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.CompletePublicTable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.DeriveCountable

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Lean.Elab.Tactic.Omega

/-!
# Measurability of one actual follower DOWN operation

This module studies the existing `ActiveFollowerDownAcceptance.downTransition`.
The input buffer's timestamp/pilot skeleton is fixed while each stored
observation and thinning scalar ranges independently over its source carrier.
The only continuous row reads are the current DOWN selector/affine sample and
the proposal scalars inspected by the actual accepted cutoff scan.

The mathematical inputs are `sources/zip4/manuscript/06_interruptions.tex:192-209,270-276`,
`sources/zip4/manuscript/05_binary_transport.tex:36-43`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
This module makes no claim that its supplied local feedback or carried buffer
has physical provenance, and does not close a manuscript recovery or regret
statement.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerDownMeasurability

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.AffineChannelLaw
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveRoundActions

abbrev Parameters := ConstructorDimensions.Parameters

/-- One varying saved observation and its independently varying thin scalar. -/
abbrev SavedScalar := SparseCalendarReward × SparseCalendarThinScalar

/-- A finite set of saved scalar positions has the original product carrier:
each observation is in `[0,1]` and each thinning value is in `[0,1)`. -/
abbrev SavedScalarFamily (n : ℕ) := Fin n → SavedScalar

/-- Replace only the two continuous fields in each existing buffer position.
The timestamps, pilots, order, duplicates, and length are copied literally. -/
def replaceBufferScalars {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) : List (SparseCalendarRecord p.K) :=
  List.ofFn fun j : Fin buffer.length =>
    let old := buffer[j]
    ⟨old.calendarRound, old.pilot, (values j).1, (values j).2⟩

/-- The buffer adapter leaves every discrete record field exactly as carried. -/
theorem replaceBufferScalars_get {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) (j : Fin buffer.length) :
    (replaceBufferScalars buffer values).get
        ⟨j.val, by simp [replaceBufferScalars]⟩ =
      ⟨buffer[j].calendarRound, buffer[j].pilot, (values j).1, (values j).2⟩ := by
  simp [replaceBufferScalars]

/-- The adapter preserves the finite buffer skeleton length. -/
theorem replaceBufferScalars_length {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) :
    (replaceBufferScalars buffer values).length = buffer.length := by
  simp [replaceBufferScalars]

/-- Adapt the two allowed buffer fields while leaving every incoming follower
register, status, decoder bank, and initialization flag untouched. -/
def adaptedInputState {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    ReferencePrelaunchFollower.State p rate.eta :=
  { state with buffer := replaceBufferScalars state.buffer values }

theorem adaptedInputState_buffer {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    (adaptedInputState rate state values).buffer = replaceBufferScalars state.buffer values := rfl

theorem adaptedInputState_registers {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    (adaptedInputState rate state values).lastDown = state.lastDown ∧
      (adaptedInputState rate state values).S = state.S ∧
      (adaptedInputState rate state values).delta = state.delta ∧
      (adaptedInputState rate state values).backlog = state.backlog ∧
      (adaptedInputState rate state values).status = state.status ∧
      (adaptedInputState rate state values).downBatch = state.downBatch ∧
      (adaptedInputState rate state values).initializationFailure = state.initializationFailure := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original finite grid of quantized buffer observations in the checked
input-domain predicate. -/
def quantizedObservationGrid (p : Parameters) : Set SparseCalendarReward :=
  {y | ∃ q : Fin (D p + 1), y.1 = (q.val : ℝ) / (D p : ℝ)}

/-- The finite-grid check is the explicit finite union of its equality tests. -/
theorem quantizedObservationGrid_eq_iUnion (p : Parameters) :
    quantizedObservationGrid p =
      ⋃ q : Fin (D p + 1), {y : SparseCalendarReward |
        y.1 = (q.val : ℝ) / (D p : ℝ)} := by
  ext y
  simp only [quantizedObservationGrid, Set.mem_ofPred_eq, Set.mem_iUnion]

/-- The actual finite-grid test is measurable because it is a finite union
of measurable scalar equalities, not because off-grid inputs are removed. -/
theorem measurableSet_quantizedObservationGrid (p : Parameters) :
    MeasurableSet (quantizedObservationGrid p) := by
  rw [quantizedObservationGrid_eq_iUnion]
  exact MeasurableSet.iUnion fun q =>
    measurableSet_eq_fun measurable_subtype_coe measurable_const

/-- The honest locally supplied current feedback associated with one finite
quantization index. This carries no physical-provenance assertion. -/
def feedbackAtGrid (p : Parameters) (q : Fin (D p + 1)) : Observation p := by
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hq : (q.val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ q.isLt)
  refine ⟨⟨(q.val : ℝ) / (D p : ℝ), ?_⟩, ?_⟩
  · exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hD), (div_le_one hD).2 hq⟩
  · exact ⟨q, rfl⟩

theorem feedbackAtGrid_val (p : Parameters) (q : Fin (D p + 1)) :
    (feedbackAtGrid p q).val.val = (q.val : ℝ) / (D p : ℝ) := rfl

theorem feedbackAtGrid_is_quantized (p : Parameters) (q : Fin (D p + 1)) :
    ∃ q' : Fin (D p + 1), (feedbackAtGrid p q).val.val =
      (q'.val : ℝ) / (D p : ℝ) := ⟨q, rfl⟩

theorem measurable_feedbackAtGrid (p : Parameters) :
    Measurable (feedbackAtGrid p) := measurable_of_finite _

/-- The existing decoder step reads only the actual current typed round input.
Equality of this input includes the supplied local feedback; it asserts no
physical provenance for that feedback. -/
theorem currentDecodeStep_eq_of_currentRoundInput_eq {p : Parameters}
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (t : Fin p.T)
    (feedback feedback' : Observation p) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hinput : currentRoundInput p i row t feedback rate state =
      currentRoundInput p i row' t feedback' rate state) :
    currentDecodeStep p i row t feedback rate state =
      currentDecodeStep p i row' t feedback' rate state := by
  unfold currentDecodeStep
  exact decodeStep_depends_on_current_input p
    (currentInputExtension p (currentRoundInput p i row t feedback rate state))
    (currentInputExtension p (currentRoundInput p i row' t feedback' rate state))
    state.downBatch t hinput

/-- Parsed output is still computed by the actual batch decoder and parser;
the equality only records that their row dependence enters through the
current local round input. -/
theorem parsedCurrentOutput_eq_of_currentRoundInput_eq {p : Parameters}
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (t : Fin p.T)
    (feedback feedback' : Observation p) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hinput : currentRoundInput p i row t feedback rate state =
      currentRoundInput p i row' t feedback' rate state) :
    parsedCurrentOutput p i row t feedback rate state =
      parsedCurrentOutput p i row' t feedback' rate state := by
  simp only [parsedCurrentOutput]
  rw [currentDecodeStep_eq_of_currentRoundInput_eq i row row' t feedback feedback'
    rate state hinput]

instance downFieldsCountable : Countable OrdinaryMessageCodec.DownFields := by
  let encode : OrdinaryMessageCodec.DownFields → ℕ × ℕ × ℕ × ℕ × ℕ :=
    fun fields => (fields.sigma, fields.a, fields.e, fields.h, fields.q)
  have hinj : Function.Injective encode := by
    intro left right h
    cases left
    cases right
    simp_all [encode]
  exact hinj.countable

instance decoderEntryCountable (T B : ℕ) :
    Countable (AffineBatchDecoder.Entry T B) := by
  let encode : AffineBatchDecoder.Entry T B → Fin T × AffineChannelLaw.Sample B :=
    fun entry => (entry.time, entry.sample)
  have hinj : Function.Injective encode := by
    intro left right h
    cases left
    cases right
    simp_all [encode]
  exact hinj.countable

instance downRecordCountable (params : CodecParams) : Countable (DownRecord params) :=
  Subtype.val_injective.countable

instance decoderStateCountable (T B : ℕ) :
    Countable (AffineBatchDecoder.State T B) := by
  let encode : AffineBatchDecoder.State T B →
      List (AffineBatchDecoder.Entry T B) × List (List (AffineBatchDecoder.Entry T B)) :=
    fun state => (state.pending, state.completed)
  have hinj : Function.Injective encode := by
    intro left right h
    cases left
    cases right
    cases h
    rfl
  exact hinj.countable

/-- Exact code for one decoder entry. Its two fields retain the original
calendar index and complete affine sample. -/
abbrev DecoderEntryCode (p : Parameters) :=
  Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p)

/-- Exact countable code for both pending and completed decoder batches. -/
abbrev DecoderBatchCode (p : Parameters) :=
  List (DecoderEntryCode p) × List (List (DecoderEntryCode p))

def decoderEntryCode {p : Parameters}
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :
    DecoderEntryCode p := (entry.time, entry.sample)

def decoderEntryOfCode {p : Parameters} (entry : DecoderEntryCode p) :
    AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) := ⟨entry.1, entry.2⟩

def decoderBatchCode {p : Parameters}
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    DecoderBatchCode p :=
  (batch.pending.map decoderEntryCode,
    batch.completed.map fun completed => completed.map decoderEntryCode)

def decoderBatchOfCode {p : Parameters} (batch : DecoderBatchCode p) :
    AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) :=
  ⟨batch.1.map decoderEntryOfCode,
    batch.2.map fun completed => completed.map decoderEntryOfCode⟩

theorem decoderBatchOfCode_code {p : Parameters}
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    decoderBatchOfCode (decoderBatchCode batch) = batch := by
  cases batch
  simp [decoderBatchOfCode, decoderBatchCode, decoderEntryCode, decoderEntryOfCode,
    List.map_map, Function.comp_def]

/-- The status field in a discrete follower code. -/
def followerStatusCode (status : FollowerStatus) : Fin 3 :=
  match status with
  | .unoccupied => 0
  | .pending => 1
  | .released => 2

def followerStatusOfCode (status : Fin 3) : FollowerStatus :=
  if status.val = 0 then .unoccupied else
    if status.val = 1 then .pending else .released

theorem followerStatusOfCode_code (status : FollowerStatus) :
    followerStatusOfCode (followerStatusCode status) = status := by
  cases status <;> rfl

/-- The code for the discrete part of a follower state. It excludes the
continuous buffer; the decoder bank is represented by its exact finite-list
code above. -/
structure FollowerStateCode (p : Parameters) (rate : RateInput p) where
  lastDown : Option (DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
  S : ℕ
  delta : ℕ
  backlog : ℕ
  status : Fin 3
  downBatch : DecoderBatchCode p
  initializationFailure : Bool
  deriving Countable

instance followerStateCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (FollowerStateCode p rate) := ⊤

def followerStateCode {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) : FollowerStateCode p rate :=
  ⟨state.lastDown, state.S, state.delta, state.backlog,
    followerStatusCode state.status, decoderBatchCode state.downBatch,
    state.initializationFailure⟩

def followerStateOfCode {p : Parameters} (rate : RateInput p)
    (code : FollowerStateCode p rate)
    (buffer : List (SparseCalendarRecord p.K)) :
    ReferencePrelaunchFollower.State p rate.eta :=
  ⟨code.lastDown, code.S, code.delta, code.backlog,
    followerStatusOfCode code.status, decoderBatchOfCode code.downBatch,
    buffer, code.initializationFailure⟩

theorem followerStateOfCode_code_eq {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (buffer : List (SparseCalendarRecord p.K)) (hbuffer : state.buffer = buffer) :
    followerStateOfCode rate (followerStateCode rate state) buffer = state := by
  cases state
  simp_all [followerStateOfCode, followerStateCode, followerStatusOfCode_code,
    decoderBatchOfCode_code]

theorem followerStateOfCode_code {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (buffer : List (SparseCalendarRecord p.K)) :
    followerStateOfCode rate (followerStateCode rate state) buffer =
      { state with buffer := buffer } := by
  cases state
  simp [followerStateOfCode, followerStateCode, followerStatusOfCode_code,
    decoderBatchOfCode_code]

/-- The code form of a cutoff scan retains its exact endpoint and actual read
list. -/
abbrev CutoffScanCode (p : Parameters) := ℕ × List (Fin p.T)

def cutoffScanCode {p : Parameters} (scan : FollowerCutoffScan.ScanResult p.T) :
    CutoffScanCode p := (scan.endpoint, scan.inspected)

def cutoffScanOfCode {p : Parameters} (scan : CutoffScanCode p) :
    FollowerCutoffScan.ScanResult p.T := ⟨scan.1, scan.2⟩

theorem cutoffScanOfCode_code {p : Parameters}
    (scan : FollowerCutoffScan.ScanResult p.T) :
    cutoffScanOfCode (cutoffScanCode scan) = scan := by
  cases scan
  rfl

instance cutoffScanCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (CutoffScanCode p) := ⊤

theorem measurable_of_countable_fibers {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] (f : α → β)
    (hf : ∀ b, MeasurableSet {x | f x = b}) : Measurable f := by
  classical
  intro s hs
  have hpre : f ⁻¹' s = ⋃ b : s, {x | f x = b.1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨⟨f x, hx⟩, rfl⟩
    · rintro ⟨b, hxb⟩
      exact hxb.symm ▸ b.property
  rw [hpre]
  exact MeasurableSet.iUnion fun b => by
    simpa using hf b.1

/-- The actual selected row proposal at one calendar coordinate is measurable
through the complete-row learning projection and its literal `prop` scalar. -/
theorem measurable_completeRowProposalBit (p : Parameters) (eta : ℝ)
    (j : Fin p.T) :
    Measurable (fun row : CompleteRow p =>
      FollowerCutoffScan.completeRowProposalBit p eta row j) := by
  let scalar : CompleteRow p → ℝ := fun row =>
    ((ContinuousLearningRows.scalarAt j ContinuousControlSlice.Label.prop
      (CompletePublicTable.completeRowLearning p row)).val)
  have hscalar : Measurable scalar := by
    exact measurable_subtype_coe.comp
      ((ContinuousLearningRows.measurable_scalarAt j ContinuousControlSlice.Label.prop).comp
        (CompletePublicTable.measurable_completeRowLearning p))
  have hthreshold : MeasurableSet {row : CompleteRow p | scalar row <
      FollowerCutoffScan.proposalHazard p eta} :=
    measurableSet_lt hscalar measurable_const
  have htrue : {row : CompleteRow p |
      FollowerCutoffScan.completeRowProposalBit p eta row j = true} =
      {row | scalar row < FollowerCutoffScan.proposalHazard p eta} := by
    ext row
    simp [scalar, FollowerCutoffScan.completeRowProposalBit,
      FollowerCutoffScan.thresholdProposalBit, ContinuousLearningRows.scalarAt,
      decide_eq_true_eq]
  have hfalse : {row : CompleteRow p |
      FollowerCutoffScan.completeRowProposalBit p eta row j = false} =
      {row | scalar row < FollowerCutoffScan.proposalHazard p eta}ᶜ := by
    ext row
    simp [scalar, FollowerCutoffScan.completeRowProposalBit,
      FollowerCutoffScan.thresholdProposalBit, ContinuousLearningRows.scalarAt]
  apply measurable_of_countable_fibers
  intro b
  cases b
  · rw [hfalse]
    exact hthreshold.compl
  · rw [htrue]
    exact hthreshold

def completeRowProposalBits (p : Parameters) (eta : ℝ)
    (row : CompleteRow p) : Fin p.T → Bool :=
  FollowerCutoffScan.completeRowProposalBit p eta row

theorem measurable_completeRowProposalBits (p : Parameters) (eta : ℝ) :
    Measurable (completeRowProposalBits p eta) := by
  rw [measurable_pi_iff]
  intro j
  exact measurable_completeRowProposalBit p eta j

/-- The code form of the actual accepted-interval scan on a supplied vector
of proposal bits. The code retains both the endpoint and the loop's exact
chronological read list. -/
def acceptedCutoffScanCodeFromBits {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (hstart : (downStart p rate M).val ≤ t.val)
    (bits : Fin p.T → Bool) : CutoffScanCode p :=
  cutoffScanCode (FollowerCutoffScan.followerCutoffScan p rate.eta.val
    (downStart p rate M) t hstart bits)

theorem measurable_acceptedCutoffScanCodeFromBits {p : Parameters}
    (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (hstart : (downStart p rate M).val ≤ t.val) :
    Measurable (acceptedCutoffScanCodeFromBits rate M t hstart) := by
  exact measurable_of_finite _

theorem measurable_acceptedCutoffScanCode {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (hstart : (downStart p rate M).val ≤ t.val) :
    Measurable (fun row : CompleteRow p =>
      cutoffScanCode (acceptedCutoffScan p rate M t hstart row)) := by
  have hbits : Measurable (completeRowProposalBits p rate.eta.val) :=
    measurable_completeRowProposalBits p rate.eta.val
  have hscan := measurable_acceptedCutoffScanCodeFromBits rate M t hstart
  convert hscan.comp hbits using 1
  funext row
  simp [acceptedCutoffScanCodeFromBits, completeRowProposalBits,
    ActiveFollowerDownAcceptance.acceptedCutoffScan,
    FollowerCutoffScan.completeRowCutoffScan]

/-- The accepted scan endpoint and exact read list are unchanged when the
selected complete rows agree on the actual `prop` scalars that this scan read.
No condition is imposed on forward bits, future controls, or other labels. -/
theorem acceptedCutoffScan_eq_of_inspected_prop_eq {p : Parameters}
    (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (t : Fin p.T) (hstart : (downStart p rate M).val ≤ t.val)
    (row row' : CompleteRow p)
    (hprop : ∀ j ∈ (acceptedCutoffScan p rate M t hstart row).inspected,
      (CompletePublicTable.completeRowLearning p row j).1
          ContinuousControlSlice.Label.prop =
        (CompletePublicTable.completeRowLearning p row' j).1
          ContinuousControlSlice.Label.prop) :
    acceptedCutoffScan p rate M t hstart row =
      acceptedCutoffScan p rate M t hstart row' := by
  simpa [ActiveFollowerDownAcceptance.acceptedCutoffScan] using
    FollowerCutoffScan.completeRowCutoffScan_noninterference p rate.eta.val
      (downStart p rate M) t hstart row row' hprop

/-- The exact contribution of one unchanged skeleton position when only its
observation and thinning coordinates vary. -/
def sparsePositionContribution {K : ℕ} (buffer : List (SparseCalendarRecord K))
    (values : SavedScalarFamily buffer.length) (d : ℕ) (D eta : ℝ)
    (h : ℕ) (arm : Fin K) (r : ℕ) (j : Fin buffer.length) : ℕ :=
  if buffer[j].calendarRound = r ∧ buffer[j].pilot = arm then
    SparseCalendarReplay.savedContribution K d D eta h (values j).1 (values j).2
  else 0

/-- Measurability follows from the actual non-strict thinning comparison and
the literal natural floor of the scaled stored observation. -/
theorem measurable_savedContribution (K d : ℕ) (D eta : ℝ) (h : ℕ) :
    Measurable (fun value : SavedScalar =>
      SparseCalendarReplay.savedContribution K d D eta h value.1 value.2) := by
  classical
  have hy : Measurable (fun value : SavedScalar => value.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have hv : Measurable (fun value : SavedScalar => value.2.1) :=
    measurable_subtype_coe.comp measurable_snd
  have hscale : Measurable (fun value : SavedScalar =>
      (D : ℝ) * eta * (2 : ℝ) ^ h * value.1.1) := by
    exact measurable_const.mul hy
  have hfloor : Measurable (fun value : SavedScalar =>
      Nat.floor ((D : ℝ) * eta * (2 : ℝ) ^ h * value.1.1)) :=
    Nat.measurable_floor.comp hscale
  have hthin : MeasurableSet {value : SavedScalar |
      value.2.1 ≤ (4 * (d : ℝ) * (K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability K d} :=
    measurableSet_le hv measurable_const
  change Measurable (fun value : SavedScalar =>
    if value.2.1 ≤ (4 * (d : ℝ) * (K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability K d then
      Nat.floor ((D : ℝ) * eta * (2 : ℝ) ^ h * value.1.1) else 0)
  exact Measurable.ite hthin hfloor measurable_const

theorem measurable_sparsePositionContribution {K : ℕ}
    (buffer : List (SparseCalendarRecord K))
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ)
    (j : Fin buffer.length) :
    Measurable (fun values : SavedScalarFamily buffer.length =>
      sparsePositionContribution buffer values d D eta h arm r j) := by
  classical
  have hvalue : Measurable (fun values : SavedScalarFamily buffer.length => values j) :=
    measurable_pi_apply j
  have hsaved := (measurable_savedContribution K d D eta h).comp hvalue
  have hposition : MeasurableSet {values : SavedScalarFamily buffer.length |
      buffer[j].calendarRound = r ∧ buffer[j].pilot = arm} := by
    by_cases h : buffer[j].calendarRound = r ∧ buffer[j].pilot = arm
    · simp
    · simp
  change Measurable (fun values : SavedScalarFamily buffer.length =>
    if buffer[j].calendarRound = r ∧ buffer[j].pilot = arm then
      SparseCalendarReplay.savedContribution K d D eta h (values j).1 (values j).2 else 0)
  exact Measurable.ite hposition hsaved measurable_const

/-- Finite position-wise version of the existing sparse contribution, ready
to expose each varying stored observation and thinning scalar to measurability. -/
def sparseContributionFromFamily {K : ℕ} (buffer : List (SparseCalendarRecord K))
    (values : SavedScalarFamily buffer.length) (d : ℕ) (D eta : ℝ)
    (h : ℕ) (arm : Fin K) (r : ℕ) : ℕ :=
  ∑ j : Fin buffer.length, sparsePositionContribution buffer values d D eta h arm r j

theorem measurable_sparseContributionFromFamily {K : ℕ}
    (buffer : List (SparseCalendarRecord K)) (d : ℕ) (D eta : ℝ)
    (h : ℕ) (arm : Fin K) (r : ℕ) :
    Measurable (fun values : SavedScalarFamily buffer.length =>
      sparseContributionFromFamily buffer values d D eta h arm r) := by
  classical
  apply Finset.measurable_fun_sum Finset.univ
  intro j hj
  exact measurable_sparsePositionContribution buffer d D eta h arm r j

theorem sparseContributionFromFamily_eq_existing {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) (d : ℕ) (D eta : ℝ)
    (h : ℕ) (arm : Fin p.K) (r : ℕ) :
    sparseContributionFromFamily buffer values d D eta h arm r =
      SparseCalendarReplay.sparseBufferContribution d D eta h arm r
        (replaceBufferScalars (p := p) buffer values) := by
  classical
  let contribution : SparseCalendarRecord p.K → ℕ := fun record =>
    if record.calendarRound = r ∧ record.pilot = arm then
      SparseCalendarReplay.savedContribution p.K d D eta h record.observation record.thinScalar
    else 0
  have hfold : ∀ records : List (SparseCalendarRecord p.K),
      List.foldr (fun record total => contribution record + total) 0 records =
        (records.map contribution).sum := by
    intro records
    induction records with
    | nil => simp
    | cons record records ih => simp [ih]
  have hmap : (List.ofFn fun j : Fin buffer.length =>
      contribution ⟨buffer[j].calendarRound, buffer[j].pilot, (values j).1, (values j).2⟩) =
      (replaceBufferScalars (p := p) buffer values).map contribution := by
    simp [replaceBufferScalars, contribution, List.map_ofFn, Function.comp_def]
  calc
    sparseContributionFromFamily buffer values d D eta h arm r =
        (List.ofFn fun j : Fin buffer.length =>
          contribution ⟨buffer[j].calendarRound, buffer[j].pilot,
            (values j).1, (values j).2⟩).sum := by
      simp [sparseContributionFromFamily, sparsePositionContribution,
        contribution, List.sum_ofFn]
    _ = ((replaceBufferScalars (p := p) buffer values).map contribution).sum := by
      rw [hmap]
    _ = SparseCalendarReplay.sparseBufferContribution d D eta h arm r
        (replaceBufferScalars (p := p) buffer values) := by
      symm
      change List.foldr (fun record total => contribution record + total) 0 _ = _
      exact hfold _

/-- The part of the carried-buffer input check determined only by timestamps,
pilots, and their pairwise duplicate condition. -/
def bufferSkeletonDomain (p : Parameters) (buffer : List (SparseCalendarRecord p.K)) : Prop :=
  (∀ j : Fin buffer.length, 1 ≤ buffer[j].calendarRound ∧
      buffer[j].calendarRound ≤ p.T) ∧
    (List.ofFn fun j : Fin buffer.length =>
      (buffer[j].calendarRound, buffer[j].pilot)).Nodup

/-- The actual finite-grid predicate on every stored observation. It is kept
separate from the skeleton so off-grid values remain present and can fail the
existing checked operation. -/
def carriedBufferGridTest (p : Parameters) (buffer : List (SparseCalendarRecord p.K)) : Prop :=
  ∀ record ∈ buffer, record.observation ∈ quantizedObservationGrid p

theorem carriedBufferGridTest_replace_iff {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) :
    carriedBufferGridTest p (replaceBufferScalars buffer values) ↔
      ∀ j : Fin buffer.length, (values j).1 ∈ quantizedObservationGrid p := by
  simp [carriedBufferGridTest, replaceBufferScalars, quantizedObservationGrid]

theorem bufferInputDomain_replace_iff {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) :
    ActiveFollowerDownAcceptance.bufferInputDomain p
      (replaceBufferScalars buffer values) ↔
        bufferSkeletonDomain p buffer ∧
          carriedBufferGridTest p (replaceBufferScalars buffer values) := by
  simp [ActiveFollowerDownAcceptance.bufferInputDomain,
    ActiveFollowerDownAcceptance.bufferRecordDomain, bufferSkeletonDomain,
    carriedBufferGridTest, replaceBufferScalars, quantizedObservationGrid,
    List.map_ofFn, Function.comp_def,
    and_assoc, forall_and]
  intro _ _
  exact and_comm

theorem measurableSet_bufferInputDomain {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) :
    MeasurableSet {values : SavedScalarFamily buffer.length |
      ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars buffer values)} := by
  classical
  have hgrid : MeasurableSet {values : SavedScalarFamily buffer.length |
      ∀ j : Fin buffer.length, (values j).1 ∈ quantizedObservationGrid p} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_quantizedObservationGrid p).preimage
      (measurable_fst.comp (measurable_pi_apply j))
  have hcarried : MeasurableSet {values : SavedScalarFamily buffer.length |
      carriedBufferGridTest p (replaceBufferScalars buffer values)} := by
    have hset : {values : SavedScalarFamily buffer.length |
        carriedBufferGridTest p (replaceBufferScalars buffer values)} =
        {values | ∀ j : Fin buffer.length,
          (values j).1 ∈ quantizedObservationGrid p} := by
      ext values
      exact (carriedBufferGridTest_replace_iff buffer values)
    rw [hset]
    exact hgrid
  have hset : {values : SavedScalarFamily buffer.length |
      ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars buffer values)} =
      {values | bufferSkeletonDomain p buffer ∧
        carriedBufferGridTest p (replaceBufferScalars buffer values)} := by
    ext values
    exact bufferInputDomain_replace_iff buffer values
  rw [hset]
  have hskeleton : MeasurableSet
      {values : SavedScalarFamily buffer.length | bufferSkeletonDomain p buffer} := by
    by_cases h : bufferSkeletonDomain p buffer <;> simp [h]
  exact hskeleton.inter hcarried

/-- The variable sparse arrival assembled position by position from the
original buffer skeleton and its independent observation/thinning inputs. -/
def bufferArrivalFromFamily {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) (r : ℕ) : ℕ :=
  sparseContributionFromFamily buffer values (p.m - 1) (D p : ℝ) rate.eta.val
    M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r

theorem measurable_bufferArrivalFromFamily {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (buffer : List (SparseCalendarRecord p.K)) (r : ℕ) :
    Measurable (fun values : SavedScalarFamily buffer.length =>
      bufferArrivalFromFamily rate M buffer values r) :=
  measurable_sparseContributionFromFamily buffer (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r

theorem bufferArrivalFromFamily_eq_actual {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) (r : ℕ) :
    bufferArrivalFromFamily rate M state.buffer values r =
      ActiveFollowerDownAcceptance.bufferArrivalAt p rate M
        (adaptedInputState rate state values) r := by
  simp [bufferArrivalFromFamily, ActiveFollowerDownAcceptance.bufferArrivalAt,
    adaptedInputState, sparseContributionFromFamily_eq_existing]

/-- Countable code for all natural sparse arrivals through the source calendar
and the one-based terminal endpoint `T+1`. -/
abbrev BufferArrivalVectorCode (p : Parameters) := Fin (p.T + 2) → ℕ

instance bufferArrivalVectorCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (BufferArrivalVectorCode p) := ⊤

def bufferArrivalVectorFromFamily {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) : BufferArrivalVectorCode p :=
  fun j => bufferArrivalFromFamily rate M buffer values j.val

theorem measurable_bufferArrivalVectorFromFamily {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (buffer : List (SparseCalendarRecord p.K)) :
    Measurable (bufferArrivalVectorFromFamily rate M buffer) := by
  apply measurable_of_countable_fibers
  intro arrivals
  have hfiber : {values : SavedScalarFamily buffer.length |
      bufferArrivalVectorFromFamily rate M buffer values = arrivals} =
      {values | ∀ j : Fin (p.T + 2),
        bufferArrivalFromFamily rate M buffer values j.val = arrivals j} := by
    ext values
    change (bufferArrivalVectorFromFamily rate M buffer values = arrivals) ↔ _
    constructor
    · intro h j
      exact congrFun h j
    · intro h
      funext j
      exact h j
  rw [hfiber]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  have hcomponent := measurable_bufferArrivalFromFamily rate M buffer j.val
  have hset : {values : SavedScalarFamily buffer.length |
      bufferArrivalFromFamily rate M buffer values j.val = arrivals j} =
      (fun values : SavedScalarFamily buffer.length =>
        bufferArrivalFromFamily rate M buffer values j.val) ⁻¹' {arrivals j} := by
    ext values
    simp
  rw [hset]
  exact hcomponent (MeasurableSet.singleton (arrivals j))

/-- The replay records are built from the actual variable sparse contribution
at each round. `checkedRecovery` below is proved equal to the existing
chronological `checkedReplay` on these records. -/
def familyRecoveryQueueRecords {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) (ell : ℕ) : List (Bool × ℕ) :=
  (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).map fun r =>
    (true, bufferArrivalFromFamily rate M buffer values r)

theorem checkedRecovery_adapted_eq_familyReplay {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) (ell : ℕ) :
    ActiveFollowerDownAcceptance.checkedRecovery p rate M
        (adaptedInputState rate state values) ell =
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
        ⟨(0, M.val.q), 0⟩
        (familyRecoveryQueueRecords rate M state.buffer values ell) := by
  rw [ActiveFollowerDownAcceptance.checkedRecovery_eq_checkedReplay]
  simp [familyRecoveryQueueRecords, ActiveFollowerDownAcceptance.recoveryQueueRecords,
    ActiveFollowerDownAcceptance.recoveryArrivals,
    ActiveFollowerDownAcceptance.recoveryRounds,
    bufferArrivalFromFamily_eq_actual, List.map_map, Function.comp_def]

def skipReasonCode (reason : SkipReason) : Fin 2 :=
  match reason with
  | .notSelectedDown => 0
  | .occupiedAtChoice => 1

def skipReasonOfCode (reason : Fin 2) : SkipReason :=
  if reason.val = 0 then .notSelectedDown else .occupiedAtChoice

theorem skipReasonOfCode_code (reason : SkipReason) :
    skipReasonOfCode (skipReasonCode reason) = reason := by
  cases reason <;> rfl

def inputFailureCode (reason : InputFailure) : Fin 3 :=
  match reason with
  | .registers => 0
  | .decoderBatch => 1
  | .sparseBuffer => 2

def inputFailureOfCode (reason : Fin 3) : InputFailure :=
  if reason.val = 0 then .registers else
    if reason.val = 1 then .decoderBatch else .sparseBuffer

theorem inputFailureOfCode_code (reason : InputFailure) :
    inputFailureOfCode (inputFailureCode reason) = reason := by
  cases reason <;> rfl

def replayFailureKindCode (reason : ReplayFailureKind) : Fin 5 :=
  match reason with
  | .inputRegisters => 0
  | .arrival => 1
  | .service => 2
  | .servedSum => 3
  | .backlog => 4

def replayFailureKindOfCode (reason : Fin 5) : ReplayFailureKind :=
  if reason.val = 0 then .inputRegisters else
    if reason.val = 1 then .arrival else
      if reason.val = 2 then .service else
        if reason.val = 3 then .servedSum else .backlog

theorem replayFailureKindOfCode_code (reason : ReplayFailureKind) :
    replayFailureKindOfCode (replayFailureKindCode reason) = reason := by
  cases reason <;> rfl

/-- The exact discrete spelling of a replay failure, including its first
failed offset and reason. -/
abbrev ReplayFailureCode := ℕ × Fin 5

def replayFailureCode (failure : ReplayFailure) : ReplayFailureCode :=
  (failure.completed, replayFailureKindCode failure.kind)

def replayFailureOfCode (failure : ReplayFailureCode) : ReplayFailure :=
  ⟨failure.1, replayFailureKindOfCode failure.2⟩

theorem replayFailureOfCode_code (failure : ReplayFailure) :
    replayFailureOfCode (replayFailureCode failure) = failure := by
  cases failure
  simp [replayFailureCode, replayFailureOfCode, replayFailureKindOfCode_code]

/-- The exact discrete spelling of each direct output-domain failure or a
replay failure. -/
structure OutputFailureCode where
  tag : Fin 5
  offset : ℕ
  replayKind : Fin 5
  deriving Countable

def outputFailureCode (reason : OutputFailure) : OutputFailureCode :=
  match reason with
  | .arrival => ⟨0, 0, 0⟩
  | .servedSum => ⟨1, 0, 0⟩
  | .lastService => ⟨2, 0, 0⟩
  | .backlog => ⟨3, 0, 0⟩
  | .replay failure => ⟨4, failure.completed, replayFailureKindCode failure.kind⟩

def outputFailureOfCode (reason : OutputFailureCode) : OutputFailure :=
  if reason.tag.val = 0 then .arrival else
    if reason.tag.val = 1 then .servedSum else
      if reason.tag.val = 2 then .lastService else
        if reason.tag.val = 3 then .backlog else
          .replay ⟨reason.offset, replayFailureKindOfCode reason.replayKind⟩

theorem outputFailureOfCode_code (reason : OutputFailure) :
    outputFailureOfCode (outputFailureCode reason) = reason := by
  cases reason with
  | arrival => rfl
  | servedSum => rfl
  | lastService => rfl
  | backlog => rfl
  | replay failure =>
      cases failure
      simp [outputFailureOfCode, outputFailureCode, replayFailureKindOfCode_code]

/-- A countable code for every changing branch and discrete output of the
existing operation. The constructor records whether the buffer is retained
(all constructors except `accepted`) or cleared (`accepted`). -/
inductive LocalDownResultCode (p : Parameters) (rate : RateInput p) where
  | skipped (before : FollowerStateCode p rate) (reason : Fin 2)
  | inputFailure (before : FollowerStateCode p rate) (reason : Fin 3)
  | decodeOrParseRejected (before after : FollowerStateCode p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
  | parsedButUnaccepted (before after : FollowerStateCode p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
  | outputFailure (before : FollowerStateCode p rate) (reason : OutputFailureCode)
  | accepted (before after : FollowerStateCode p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (scan : CutoffScanCode p) (registers : ℕ × ℕ) (lastService : ℕ)
  deriving Countable

instance localDownResultCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (LocalDownResultCode p rate) := ⊤

/-- Explicit continuous-buffer behavior recorded by the discrete result tag. -/
inductive BufferEffect where
  | same
  | cleared
  deriving DecidableEq, Countable

def localDownCodeBufferEffect {p : Parameters} {rate : RateInput p}
    (code : LocalDownResultCode p rate) : BufferEffect :=
  match code with
  | .accepted .. => .cleared
  | _ => .same

/-- Forget only the continuous buffer fields of a result state, preserving its
actual discrete registers and decoder batch. -/
def encodeFollowerState {p : Parameters} {rate : RateInput p}
    (state : ReferencePrelaunchFollower.State p rate.eta) : FollowerStateCode p rate :=
  followerStateCode rate state

/-- Encode the full discrete result of the real local operation. -/
def encodeLocalDownResult {p : Parameters} {rate : RateInput p}
    (result : LocalDownResult p rate) : LocalDownResultCode p rate :=
  match result with
  | .skipped before reason =>
      .skipped (encodeFollowerState before) (skipReasonCode reason)
  | .inputFailure before reason =>
      .inputFailure (encodeFollowerState before) (inputFailureCode reason)
  | .decodeOrParseRejected before after raw =>
      .decodeOrParseRejected (encodeFollowerState before) (encodeFollowerState after) raw
  | .parsedButUnaccepted before after raw reply =>
      .parsedButUnaccepted (encodeFollowerState before) (encodeFollowerState after) raw reply
  | .outputFailure before reason =>
      .outputFailure (encodeFollowerState before) (outputFailureCode reason)
  | .accepted before after raw reply scan registers lastService =>
      .accepted (encodeFollowerState before) (encodeFollowerState after) raw reply
        (cutoffScanCode scan) registers lastService

/-- Reconstruct a complete result from its countable code and the original
varying input buffer. Same-buffer and cleared-buffer behavior is determined by
the recorded result constructor. -/
def reconstructLocalDownResult {p : Parameters} {rate : RateInput p}
    (code : LocalDownResultCode p rate)
    (originalBuffer : List (SparseCalendarRecord p.K)) : LocalDownResult p rate :=
  match code with
  | .skipped before reason =>
      .skipped (followerStateOfCode rate before originalBuffer) (skipReasonOfCode reason)
  | .inputFailure before reason =>
      .inputFailure (followerStateOfCode rate before originalBuffer)
        (inputFailureOfCode reason)
  | .decodeOrParseRejected before after raw =>
      .decodeOrParseRejected (followerStateOfCode rate before originalBuffer)
        (followerStateOfCode rate after originalBuffer) raw
  | .parsedButUnaccepted before after raw reply =>
      .parsedButUnaccepted (followerStateOfCode rate before originalBuffer)
        (followerStateOfCode rate after originalBuffer) raw reply
  | .outputFailure before reason =>
      .outputFailure (followerStateOfCode rate before originalBuffer)
        (outputFailureOfCode reason)
  | .accepted before after raw reply scan registers lastService =>
      .accepted (followerStateOfCode rate before originalBuffer)
        (followerStateOfCode rate after []) raw reply (cutoffScanOfCode scan)
        registers lastService

/-- Every constructor before acceptance retains the input buffer; acceptance
clears it after installing the exact recovered state. -/
def localDownBufferBehavior {p : Parameters} {rate : RateInput p}
    (originalBuffer : List (SparseCalendarRecord p.K)) (result : LocalDownResult p rate) : Prop :=
  match result with
  | .skipped before _ => before.buffer = originalBuffer
  | .inputFailure before _ => before.buffer = originalBuffer
  | .decodeOrParseRejected before after _ =>
      before.buffer = originalBuffer ∧ after.buffer = originalBuffer
  | .parsedButUnaccepted before after _ _ =>
      before.buffer = originalBuffer ∧ after.buffer = originalBuffer
  | .outputFailure before _ => before.buffer = originalBuffer
  | .accepted before after _ _ _ _ _ =>
      before.buffer = originalBuffer ∧ after.buffer = []

theorem reconstruct_encodeLocalDownResult {p : Parameters} {rate : RateInput p}
    (originalBuffer : List (SparseCalendarRecord p.K)) (result : LocalDownResult p rate)
    (hbuffer : localDownBufferBehavior originalBuffer result) :
    reconstructLocalDownResult (encodeLocalDownResult result) originalBuffer = result := by
  cases result with
  | skipped before reason =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState, skipReasonOfCode_code]
      rw [hs]
  | inputFailure before reason =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState, inputFailureOfCode_code]
      rw [hs]
  | decodeOrParseRejected before after raw =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      rcases hb with ⟨hb, ha⟩
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      have ht := followerStateOfCode_code_eq rate after originalBuffer ha
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState]
      rw [hs, ht]
  | parsedButUnaccepted before after raw reply =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      rcases hb with ⟨hb, ha⟩
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      have ht := followerStateOfCode_code_eq rate after originalBuffer ha
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState]
      rw [hs, ht]
  | outputFailure before reason =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState, outputFailureOfCode_code]
      rw [hs]
  | accepted before after raw reply scan registers lastService =>
      have hb := hbuffer
      unfold localDownBufferBehavior at hb
      rcases hb with ⟨hb, ha⟩
      have hs := followerStateOfCode_code_eq rate before originalBuffer hb
      have ht := followerStateOfCode_code_eq rate after [] ha
      simp only [encodeLocalDownResult, reconstructLocalDownResult,
        encodeFollowerState, cutoffScanOfCode_code]
      rw [hs, ht]

/-- The real operation's result code, with exactly the input variables stated
by the local protocol. -/
def downTransitionCode {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedbackIndex : Fin (D p + 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) : LocalDownResultCode p rate :=
  encodeLocalDownResult
    (ActiveFollowerDownAcceptance.downTransition p i row t (feedbackAtGrid p feedbackIndex)
      rate (adaptedInputState rate state values))

theorem downTransition_bufferBehavior {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    localDownBufferBehavior state.buffer
      (ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state) := by
  classical
  unfold ActiveFollowerDownAcceptance.downTransition
  split_ifs with hselected hstatus hregisters hbatch hbuffer
  · dsimp only
    split
    · simp [localDownBufferBehavior]
    · split_ifs with haccepted
      all_goals try split
      all_goals simp [localDownBufferBehavior]
  all_goals simp [localDownBufferBehavior]

theorem downTransitionCode_reconstruct {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedbackIndex : Fin (D p + 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length) :
    reconstructLocalDownResult (downTransitionCode i row t feedbackIndex rate state values)
        (replaceBufferScalars state.buffer values) =
      ActiveFollowerDownAcceptance.downTransition p i row t (feedbackAtGrid p feedbackIndex)
        rate (adaptedInputState rate state values) := by
  apply reconstruct_encodeLocalDownResult
  simpa [adaptedInputState, adaptedInputState_buffer] using
    downTransition_bufferBehavior i row t (feedbackAtGrid p feedbackIndex) rate
      (adaptedInputState rate state values)

end Bandits.Support.FollowerDownMeasurability
