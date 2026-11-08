/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FollowerDownMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Joint measurability of the existing follower DOWN operation

The exports here prove joint measurability of the complete countable code of
the existing local DOWN operation while its complete row, calendar time,
finite-grid feedback index, and saved buffer scalars vary. The saved scalar
family retains the original `[0,1] × [0,1)` product at every fixed skeleton
position. The result remains the actual checked decoder, parser, acceptance,
scan, sparse replay, and install operation.

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-209,270-276`,
`sources/zip4/manuscript/05_binary_transport.tex:36-43`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.FollowerDownJointMeasurability

open MeasureTheory
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
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.FollowerDownMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

/-- The literal joint input carrier; `state` and its finite buffer skeleton
are fixed parameters of each theorem instance. -/
abbrev DownJointInput (p : Parameters) (n : ℕ) :=
  (((CompleteRow p × Fin p.T) × Fin (D p + 1)) × SavedScalarFamily n)

/-- A finite read of the current channel, retaining the actual feedback index. -/
@[ext] structure DownRoundRead (p : Parameters) where
  time : Fin p.T
  feedbackIndex : Fin (D p + 1)
  selected : Bool
  sample : Sample (ContinuousLearningRows.B p)
  deriving DecidableEq, Countable

instance downRoundReadMeasurableSpace (p : Parameters) :
    MeasurableSpace (DownRoundRead p) := ⊤

/-- For every stored position and possible source exponent, retain the actual
saved-contribution result. This is a countable code of the original continuous
observation and thinning fields, with no grid restriction. -/
abbrev BufferContributionCode (p : Parameters) (n : ℕ) :=
  Fin n → Fin (D p + 1) → ℕ

instance bufferContributionCodeMeasurableSpace (p : Parameters) (n : ℕ) :
    MeasurableSpace (BufferContributionCode p n) := ⊤

/-- The complete countable sufficient read signature used to factor the real
operation. -/
abbrev DownReadSignature (p : Parameters) (n : ℕ) :=
  ((DownRoundRead p × (Fin p.T → Bool)) ×
    (Bool × BufferContributionCode p n))

/-- The existing selected slot as a function of one complete row. -/
def downSelectedSlotAt {p : Parameters} (row : CompleteRow p) (t : Fin p.T) :
    PublicDiscreteDraws.Slot :=
  PublicDiscreteDraws.slotDraw
    (ContinuousLearningRows.sliceAt t (CompletePublicTable.completeRowLearning p row))

/-- The existing selected follower as a function of one complete row. -/
def downSelectedFollowerAt {p : Parameters} (row : CompleteRow p) (t : Fin p.T) :
    Fin (p.m - 1) :=
  PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
    (ContinuousLearningRows.sliceAt t (CompletePublicTable.completeRowLearning p row))

/-- Boolean form of the existing DOWN selection predicate. -/
noncomputable def downSelectionBit {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) : Bool := by
  classical
  exact decide (ActiveFollowerDownAcceptance.downSelected p i row t)

private theorem decide_eq_of_prop_eq {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P = Q) : decide P = decide Q := by
  cases hp : decide P <;> cases hq : decide Q <;>
    simp_all only [decide_eq_true_eq, Bool.true_eq_false, Bool.false_eq_true]

theorem downSelectionBit_eq_true {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) :
    downSelectionBit i row t = true ↔
      ActiveFollowerDownAcceptance.downSelected p i row t := by
  classical
  unfold downSelectionBit
  exact Bool.decide_iff (ActiveFollowerDownAcceptance.downSelected p i row t)

/-- The row/time projection of the joint input. -/
def jointRowTime {p : Parameters} {n : ℕ} (x : DownJointInput p n) :
    CompleteRow p × Fin p.T := x.1.1

def jointFeedbackIndex {p : Parameters} {n : ℕ} (x : DownJointInput p n) :
    Fin (D p + 1) := x.1.2

def jointValues {p : Parameters} {n : ℕ} (x : DownJointInput p n) : SavedScalarFamily n :=
  x.2

def jointRow {p : Parameters} {n : ℕ} (x : DownJointInput p n) : CompleteRow p :=
  (jointRowTime x).1

def jointTime {p : Parameters} {n : ℕ} (x : DownJointInput p n) : Fin p.T :=
  (jointRowTime x).2

private theorem measurable_finIndex_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (n : ℕ) (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun z : α × Fin n => f z.2 z.1) := by
  intro s hs
  have hpre : (fun z : α × Fin n => f z.2 z.1) ⁻¹' s =
      ⋃ j : Fin n, {z | z.2 = j} ∩ {z | f j z.1 ∈ s} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨z.2, rfl, hz⟩
    · rintro ⟨j, hj, hz⟩
      rw [hj]
      exact hz
  rw [hpre]
  apply MeasurableSet.iUnion
  intro j
  have hindex : MeasurableSet {z : α × Fin n | z.2 = j} :=
    (measurableSet_singleton j).preimage measurable_snd
  have hvalue : MeasurableSet {z : α × Fin n | f j z.1 ∈ s} :=
    ((hf j).comp measurable_fst) hs
  exact hindex.inter hvalue

/-- Measurability of the actual current selected-follower/DOWN selector. -/
theorem measurable_downSelectedAt (p : Parameters) (i : Fin (p.m - 1))
    (t : Fin p.T) : Measurable (fun row : CompleteRow p =>
      downSelectionBit i row t) := by
  classical
  let learning : CompleteRow p → LearningRow p := CompletePublicTable.completeRowLearning p
  let slot : CompleteRow p → PublicDiscreteDraws.Slot := fun row =>
    PublicDiscreteDraws.slotDraw (ContinuousLearningRows.sliceAt t (learning row))
  let follower : CompleteRow p → Fin (p.m - 1) := fun row =>
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (ContinuousLearningRows.sliceAt t (learning row))
  have hslot : Measurable slot := by
    exact (PublicDiscreteDraws.measurable_slotDraw.comp
      ((ContinuousLearningRows.measurable_sliceAt t).comp
        (CompletePublicTable.measurable_completeRowLearning p)))
  have hfollower : Measurable follower := by
    exact (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      ((ContinuousLearningRows.measurable_sliceAt t).comp
        (CompletePublicTable.measurable_completeRowLearning p))
  have hslotBool : Measurable (fun row : CompleteRow p =>
      decide (slot row = PublicDiscreteDraws.downSlot)) :=
    (measurable_of_finite fun s : PublicDiscreteDraws.Slot =>
      decide (s = PublicDiscreteDraws.downSlot)).comp hslot
  have hfollowerBool : Measurable (fun row : CompleteRow p => decide (follower row = i)) :=
    (measurable_of_finite fun f : Fin (p.m - 1) => decide (f = i)).comp hfollower
  have hcombine : Measurable (fun bits : Bool × Bool => bits.1 && bits.2) :=
    measurable_of_finite fun bits : Bool × Bool => bits.1 && bits.2
  have hEq : (fun row : CompleteRow p => downSelectionBit i row t) =
      fun row => decide (slot row = PublicDiscreteDraws.downSlot) && decide (follower row = i) := by
    funext row
    unfold downSelectionBit
    have hselected : ActiveFollowerDownAcceptance.downSelected p i row t =
        (slot row = PublicDiscreteDraws.downSlot ∧ follower row = i) := by
      apply propext
      simp only [ActiveFollowerDownAcceptance.downSelected, slot, follower, learning,
        ContinuousLearningRows.sliceAt, CompletePublicTable.completeRowLearning]
      rfl
    rw [hselected]
    by_cases hslot' : slot row = PublicDiscreteDraws.downSlot <;>
      by_cases hfollower' : follower row = i
    all_goals simp [hslot', hfollower']
  rw [hEq]
  simpa only [Function.comp_def] using
    hcombine.comp (hslotBool.prodMk hfollowerBool)

/-- The actual affine sample at the selected channel for one fixed time. -/
theorem measurable_downSampleAt (p : Parameters) (i : Fin (p.m - 1))
    (t : Fin p.T) : Measurable (fun row : CompleteRow p =>
      (row.2 t).2 (0, i)) := by
  change Measurable
    (ContinuousLearningRows.affineAt t (0, i) ∘ CompletePublicTable.completeRowLearning p)
  exact (ContinuousLearningRows.measurable_affineAt t (0, i)).comp
    (CompletePublicTable.measurable_completeRowLearning p)

/-- The current input data on the whole joint carrier. -/
noncomputable def downRoundRead {p : Parameters} {n : ℕ} (i : Fin (p.m - 1))
    (x : DownJointInput p n) : DownRoundRead p := by
  classical
  exact ⟨jointTime x, jointFeedbackIndex x,
    downSelectionBit i (jointRow x) (jointTime x),
    ((jointRow x).2 (jointTime x)).2 (0, i)⟩

theorem measurable_downRoundRead {p : Parameters} (i : Fin (p.m - 1)) (n : ℕ) :
    Measurable (downRoundRead (p := p) (n := n) i) := by
  have hrowtime : Measurable (jointRowTime (p := p) (n := n)) :=
    measurable_fst.comp measurable_fst
  have htime : Measurable (jointTime (p := p) (n := n)) :=
    measurable_snd.comp hrowtime
  have hfeedback : Measurable (jointFeedbackIndex (p := p) (n := n)) :=
    measurable_snd.comp measurable_fst
  have hselectedAt : ∀ t : Fin p.T,
      Measurable (fun row : CompleteRow p => downSelectionBit i row t) := by
    intro t
    exact measurable_downSelectedAt p i t
  have hsampleAt : ∀ t : Fin p.T,
      Measurable (fun row : CompleteRow p => (row.2 t).2 (0, i)) :=
    measurable_downSampleAt p i
  have hselected : Measurable (fun x : DownJointInput p n =>
      downSelectionBit i (jointRow x) (jointTime x)) := by
    exact (measurable_finIndex_eval p.T
      (fun t row => downSelectionBit i row t)
      hselectedAt).comp hrowtime
  have hsample : Measurable (fun x : DownJointInput p n =>
      ((jointRow x).2 (jointTime x)).2 (0, i)) := by
    exact (measurable_finIndex_eval p.T
      (fun t row => (row.2 t).2 (0, i)) hsampleAt).comp hrowtime
  apply measurable_of_countable_fibers
  intro read
  have hset : {x : DownJointInput p n | downRoundRead i x = read} =
      {x | jointTime x = read.time} ∩
        ({x | jointFeedbackIndex x = read.feedbackIndex} ∩
          ({x | downSelectionBit i (jointRow x) (jointTime x) = read.selected} ∩
            {x | ((jointRow x).2 (jointTime x)).2 (0, i) = read.sample})) := by
    ext x
    rcases read with ⟨rt, rf, rs, rSample⟩
    simp only [downRoundRead, DownRoundRead.mk.injEq,
      Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hset]
  exact (htime (measurableSet_singleton read.time)).inter
    ((hfeedback (measurableSet_singleton read.feedbackIndex)).inter
      ((hselected (measurableSet_singleton read.selected)).inter
        (hsample (measurableSet_singleton read.sample))))

/-- Proposal coordinates strictly before the current time; later coordinates
are erased from this literal scan read. -/
def pastProposalBitsAt {p : Parameters} (rate : RateInput p) (row : CompleteRow p)
    (t : Fin p.T) : Fin p.T → Bool := fun j =>
  if j.val < t.val then
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j
  else false

theorem measurable_pastProposalBitsAt {p : Parameters} {n : ℕ} (rate : RateInput p) :
    Measurable (fun x : DownJointInput p n =>
      pastProposalBitsAt rate (jointRow x) (jointTime x)) := by
  rw [measurable_pi_iff]
  intro j
  have htime : Measurable (jointTime (p := p) (n := n)) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hrow : Measurable (jointRow (p := p) (n := n)) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hconditionBool : Measurable (fun x : DownJointInput p n =>
      decide (j.val < (jointTime x).val)) := by
    exact (measurable_of_finite (fun t : Fin p.T => decide (j.val < t.val))).comp htime
  have hcondition : MeasurableSet {x : DownJointInput p n | j.val < (jointTime x).val} := by
    have hset : {x : DownJointInput p n | j.val < (jointTime x).val} =
        (fun x => decide (j.val < (jointTime x).val)) ⁻¹' {true} := by
      ext x
      simp
    rw [hset]
    exact hconditionBool (measurableSet_singleton true)
  have hbit : Measurable (fun x : DownJointInput p n =>
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val (jointRow x) j) :=
    (measurable_completeRowProposalBit p rate.eta.val j).comp hrow
  change Measurable (fun x : DownJointInput p n =>
    if j.val < (jointTime x).val then
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val (jointRow x) j else false)
  exact Measurable.ite hcondition hbit measurable_const

/-- The actual finite-grid and timestamp/pilot buffer input check, encoded by
its Boolean result. -/
noncomputable def bufferInputValidAt {p : Parameters} (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) : Bool := by
  classical
  exact decide (ActiveFollowerDownAcceptance.bufferInputDomain p
    (replaceBufferScalars buffer values))

theorem bufferInputValidAt_true_iff {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) (values : SavedScalarFamily buffer.length) :
    bufferInputValidAt buffer values = true ↔
      ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars buffer values) := by
  classical
  simp [bufferInputValidAt]

theorem measurable_bufferInputValidAt {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) :
    Measurable (bufferInputValidAt (p := p) buffer) := by
  apply measurable_of_countable_fibers
  intro b
  cases b
  · have hset : {values : SavedScalarFamily buffer.length |
        bufferInputValidAt buffer values = false} =
      {values | ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars buffer values)}ᶜ := by
      ext values
      simp [bufferInputValidAt]
    rw [hset]
    exact (measurableSet_bufferInputDomain buffer).compl
  · have hset : {values : SavedScalarFamily buffer.length |
        bufferInputValidAt buffer values = true} =
      {values | ActiveFollowerDownAcceptance.bufferInputDomain p
        (replaceBufferScalars buffer values)} := by
      ext values
      simp [bufferInputValidAt]
    rw [hset]
    exact measurableSet_bufferInputDomain buffer

/-- The contribution code for every buffer position and every possible
admissible DOWN exponent. -/
def bufferContributionCodeAt {p : Parameters}
    (rate : RateInput p) (buffer : List (SparseCalendarRecord p.K))
    (values : SavedScalarFamily buffer.length) : BufferContributionCode p buffer.length :=
  fun j h => SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
    rate.eta.val h.val (values j).1 (values j).2

theorem measurable_bufferContributionCodeAt {p : Parameters} (rate : RateInput p)
    (buffer : List (SparseCalendarRecord p.K)) :
    Measurable (bufferContributionCodeAt (p := p) rate buffer) := by
  apply measurable_of_countable_fibers
  intro code
  have hset : {values : SavedScalarFamily buffer.length |
      bufferContributionCodeAt rate buffer values = code} =
      ⋂ j : Fin buffer.length, ⋂ h : Fin (D p + 1),
        {values | SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
          rate.eta.val h.val (values j).1 (values j).2 = code j h} := by
    ext values
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, funext_iff,
      bufferContributionCodeAt]
  rw [hset]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro h
  have hvalue : Measurable (fun values : SavedScalarFamily buffer.length =>
      SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
        rate.eta.val h.val (values j).1 (values j).2) := by
    exact (FollowerDownMeasurability.measurable_savedContribution p.K (p.m - 1)
      (D p : ℝ) rate.eta.val h.val).comp (measurable_pi_apply j)
  have hfiber := hvalue (measurableSet_singleton (code j h))
  have hset : (fun values : SavedScalarFamily buffer.length =>
        SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
          rate.eta.val h.val (values j).1 (values j).2) ⁻¹' {code j h} =
      {values | SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
          rate.eta.val h.val (values j).1 (values j).2 = code j h} := by
    ext values
    simp
  rw [← hset]
  exact hfiber

/-- The sufficient countable reads of the true operation. -/
def downReadSignatureAt {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : DownJointInput p state.buffer.length) : DownReadSignature p state.buffer.length :=
  ((downRoundRead i x, pastProposalBitsAt rate (jointRow x) (jointTime x)),
    (bufferInputValidAt state.buffer (jointValues x),
      bufferContributionCodeAt rate state.buffer (jointValues x)))

theorem measurable_downReadSignatureAt {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (downReadSignatureAt i rate state) := by
  have hround := measurable_downRoundRead i state.buffer.length
  have hbits := measurable_pastProposalBitsAt (n := state.buffer.length) rate
  have hvalid := (measurable_bufferInputValidAt (p := p) state.buffer).comp
    (measurable_snd : Measurable
      (jointValues (p := p) (n := state.buffer.length)))
  have hcontribution := (measurable_bufferContributionCodeAt rate state.buffer).comp
    (measurable_snd : Measurable
      (jointValues (p := p) (n := state.buffer.length)))
  exact (hround.prodMk hbits).prodMk (hvalid.prodMk hcontribution)

/-- The operation's countable code evaluated on the joint input carrier. -/
def downTransitionCodeAt {p : Parameters} (i : Fin (p.m - 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : DownJointInput p state.buffer.length) : LocalDownResultCode p rate :=
  FollowerDownMeasurability.downTransitionCode i (jointRow x) (jointTime x)
    (jointFeedbackIndex x) rate state (jointValues x)

/-- Every source-admissible exponent is among the finite exponents recorded by
`BufferContributionCode`. -/
theorem downExponent_le_D {p : Parameters} (rate : RateInput p)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    M.val.h ≤ D p := by
  have hdom := M.property
  simp only [OrdinaryMessageCodec.downAdmissible,
    ReferencePrelaunchFollower.codecParams] at hdom
  rcases hdom with ⟨_, _, _, _, _, _, _, hh, _, _, _⟩
  exact hh.trans (ConstructorDimensions.b_N_le_D p)

/-- Equal contribution codes give equal actual sparse arrivals for every
calendar round, including duplicate or otherwise invalid carried skeletons. -/
theorem bufferArrivalFromFamily_eq_of_contributionCode_eq {p : Parameters}
    (rate : RateInput p) (buffer : List (SparseCalendarRecord p.K))
    (values values' : SavedScalarFamily buffer.length)
    (hcode : bufferContributionCodeAt rate buffer values =
      bufferContributionCodeAt rate buffer values')
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (r : ℕ) :
    bufferArrivalFromFamily rate M buffer values r =
      bufferArrivalFromFamily rate M buffer values' r := by
  classical
  let exponent : Fin (D p + 1) :=
    ⟨M.val.h, Nat.lt_succ_of_le (downExponent_le_D rate M)⟩
  unfold bufferArrivalFromFamily sparseContributionFromFamily
  apply Finset.sum_congr rfl
  intro j hj
  have hentry := congrFun (congrFun hcode j) exponent
  by_cases hposition : buffer[j].calendarRound = r ∧
      buffer[j].pilot = PrelaunchBufferRecovery.downArm rate.eta M
  · have hleft := hposition
    simp only [sparsePositionContribution, ite_eq_left hleft]
    simpa [bufferContributionCodeAt, exponent] using hentry
  · simp only [sparsePositionContribution]
    simp only [ite_eq_right hposition]

/-- A factorization criterion for a countable-valued result through a discrete
read signature. It uses only measurable fibers and a proved equality on every
signature fiber. -/
theorem measurable_of_countable_read_factorization {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    [MeasurableSpace γ] [Countable γ]
    (read : α → β) (hread : Measurable read) (f : α → γ)
    (hinvariant : ∀ x y, read x = read y → f x = f y) : Measurable f := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers f
  intro target
  let readFiber : Set β := {b | ∃ x, read x = b ∧ f x = target}
  have hpre : {x | f x = target} = read ⁻¹' readFiber := by
    ext x
    constructor
    · intro hx
      exact ⟨x, rfl, hx⟩
    · rintro ⟨y, hy, hfy⟩
      have hxy : read x = read y := hy.symm
      exact (hinvariant x y hxy).trans hfy
  rw [hpre]
  exact hread (MeasurableSet.of_discrete)

/-- The actual DOWN code is constant on equal complete sufficient read
signatures. The replay code contains the position-wise saved contributions at
every admissible decoded exponent; no replay result or parser output is
supplied as an assumption. -/
theorem downTransitionCodeAt_eq_of_readSignature_eq {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x y : DownJointInput p state.buffer.length)
    (hread : downReadSignatureAt i rate state x =
      downReadSignatureAt i rate state y) :
    downTransitionCodeAt i rate state x = downTransitionCodeAt i rate state y := by
  classical
  rcases Prod.mk.inj hread with ⟨hleft, hright⟩
  rcases Prod.mk.inj hleft with ⟨hround, hbits⟩
  rcases Prod.mk.inj hright with ⟨hvalid, hcontribution⟩
  let row := jointRow x
  let row' := jointRow y
  let t := jointTime x
  let t' := jointTime y
  let feedbackIndex := jointFeedbackIndex x
  let feedbackIndex' := jointFeedbackIndex y
  let values := jointValues x
  let values' := jointValues y
  let localState := adaptedInputState rate state values
  let localState' := adaptedInputState rate state values'
  have htime : t = t' := by
    exact congrArg DownRoundRead.time hround
  have hfeedback : feedbackIndex = feedbackIndex' := by
    exact congrArg DownRoundRead.feedbackIndex hround
  have hselectedBool :
      downSelectionBit i row t = downSelectionBit i row' t' := by
    simpa [downRoundRead, row, row', t, t'] using
      congrArg DownRoundRead.selected hround
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row t =
      ActiveFollowerDownAcceptance.downSelected p i row' t' := by
    apply propext
    exact (downSelectionBit_eq_true i row t).symm.trans
      (hselectedBool ▸ downSelectionBit_eq_true i row' t')
  have hsample : (row.2 t).2 (0, i) = (row'.2 t').2 (0, i) := by
    simpa [downRoundRead, row, row', t, t'] using
      congrArg DownRoundRead.sample hround
  have hproposalBits : pastProposalBitsAt rate row t =
      pastProposalBitsAt rate row' t' := by
    simpa [row, row', t, t'] using hbits
  have hvalid' : bufferInputValidAt state.buffer values =
      bufferInputValidAt state.buffer values' := by
    simpa [values, values'] using hvalid
  have hcontribution' : bufferContributionCodeAt rate state.buffer values =
      bufferContributionCodeAt rate state.buffer values' := by
    simpa [values, values'] using hcontribution
  have hinputDomain : ActiveFollowerDownAcceptance.bufferInputDomain p
      (replaceBufferScalars state.buffer values) =
        ActiveFollowerDownAcceptance.bufferInputDomain p
          (replaceBufferScalars state.buffer values') := by
    apply propext
    constructor
    · intro h
      have hb := (bufferInputValidAt_true_iff state.buffer values).2 h
      rw [hvalid'] at hb
      exact (bufferInputValidAt_true_iff state.buffer values').1 hb
    · intro h
      have hb := (bufferInputValidAt_true_iff state.buffer values').2 h
      rw [← hvalid'] at hb
      exact (bufferInputValidAt_true_iff state.buffer values).1 hb
  have hstatus : (localState.status = FollowerStatus.unoccupied) =
      (localState'.status = FollowerStatus.unoccupied) := by
    simp [localState, localState', adaptedInputState]
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate localState =
      ActiveFollowerDownAcceptance.registerInputDomain p rate localState' := by
    simp [ActiveFollowerDownAcceptance.registerInputDomain,
      localState, localState', adaptedInputState]
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p localState.downBatch =
      ActiveFollowerDownAcceptance.decoderInputDomain p localState'.downBatch := by
    simp [ActiveFollowerDownAcceptance.decoderInputDomain,
      localState, localState', adaptedInputState]
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p localState.buffer =
      ActiveFollowerDownAcceptance.bufferInputDomain p localState'.buffer := by
    simpa [localState, localState', adaptedInputState] using hinputDomain
  have hcurrent : ActiveFollowerDownAcceptance.currentRoundInput p i row t
      (feedbackAtGrid p feedbackIndex) rate localState =
      ActiveFollowerDownAcceptance.currentRoundInput p i row' t'
        (feedbackAtGrid p feedbackIndex') rate localState' := by
    change AffineBatchDecoder.RoundInput.mk
        (decide (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (row.2 t).1 = i))
        (decide (localState.status = FollowerStatus.unoccupied))
        ((row.2 t).2 (0, i)) (feedbackAtGrid p feedbackIndex).val.val =
      AffineBatchDecoder.RoundInput.mk
        (decide (PublicDiscreteDraws.slotDraw (row'.2 t').1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (row'.2 t').1 = i))
        (decide (localState'.status = FollowerStatus.unoccupied))
        ((row'.2 t').2 (0, i)) (feedbackAtGrid p feedbackIndex').val.val
    simp only [AffineBatchDecoder.RoundInput.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact decide_eq_of_prop_eq hselected
    · exact decide_eq_of_prop_eq hstatus
    · simpa only [AffineBatchDecoder.width, ContinuousLearningRows.B] using hsample
    · exact congrArg (fun o : Observation p => o.val.val)
        (congrArg (feedbackAtGrid p) hfeedback)
  have hdecoded : currentDecodeStep p i row t (feedbackAtGrid p feedbackIndex)
      rate localState = currentDecodeStep p i row' t' (feedbackAtGrid p feedbackIndex')
        rate localState' := by
    have htrace : currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row t
            (feedbackAtGrid p feedbackIndex) rate localState) =
        currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row' t'
            (feedbackAtGrid p feedbackIndex') rate localState') :=
      congrArg (currentInputExtension p) hcurrent
    rw [← htime, ← hfeedback] at htrace
    unfold currentDecodeStep
    rw [← htime, ← hfeedback]
    simpa [currentInputExtension, localState, localState', adaptedInputState] using
      ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p
        (currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row t
            (feedbackAtGrid p feedbackIndex) rate localState))
        (currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row' t
            (feedbackAtGrid p feedbackIndex) rate localState'))
        localState.downBatch t (by exact congrFun htrace t)
  have hscan : ∀ (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (hstart : (downStart p rate M).val ≤ t.val),
      acceptedCutoffScan p rate M t hstart row =
        acceptedCutoffScan p rate M t hstart row' := by
    intro M hstart
    change FollowerCutoffScan.followerCutoffScan p rate.eta.val
        (downStart p rate M) t hstart
          (fun j => FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j) =
      FollowerCutoffScan.followerCutoffScan p rate.eta.val
        (downStart p rate M) t hstart
          (fun j => FollowerCutoffScan.completeRowProposalBit p rate.eta.val row' j)
    apply FollowerCutoffScan.followerCutoffScan_noninterference
    intro j hj
    have hsource := FollowerCutoffScan.followerCutoffScan_inspected_source_bounds
      p rate.eta.val (downStart p rate M) t hstart
      (fun k => FollowerCutoffScan.completeRowProposalBit p rate.eta.val row k) j hj
    have hjpast : j.val < t.val := by omega
    have hproposalBits' := hproposalBits
    rw [← htime] at hproposalBits'
    have hbit := congrFun hproposalBits' j
    simpa only [pastProposalBitsAt, ite_eq_left hjpast] using hbit
  have harrival : ∀ (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (r : ℕ),
      ActiveFollowerDownAcceptance.bufferArrivalAt p rate M localState r =
        ActiveFollowerDownAcceptance.bufferArrivalAt p rate M localState' r := by
    intro M r
    calc
      ActiveFollowerDownAcceptance.bufferArrivalAt p rate M localState r =
          bufferArrivalFromFamily rate M state.buffer values r := by
        symm
        exact bufferArrivalFromFamily_eq_actual rate M state values r
      _ = bufferArrivalFromFamily rate M state.buffer values' r :=
        bufferArrivalFromFamily_eq_of_contributionCode_eq rate state.buffer values values'
          hcontribution' M r
      _ = ActiveFollowerDownAcceptance.bufferArrivalAt p rate M localState' r :=
        bufferArrivalFromFamily_eq_actual rate M state values' r
  have hchecked : ∀ (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (ell : ℕ),
      ActiveFollowerDownAcceptance.checkedRecovery p rate M localState ell =
        ActiveFollowerDownAcceptance.checkedRecovery p rate M localState' ell := by
    intro M ell
    unfold ActiveFollowerDownAcceptance.checkedRecovery
    congr 1
    funext r
    exact harrival M r
  have hselectedAtLeft : ActiveFollowerDownAcceptance.downSelected p i row t =
      ActiveFollowerDownAcceptance.downSelected p i row' t := by
    simpa [← htime] using hselected
  have hdecodedAtLeft : currentDecodeStep p i row t (feedbackAtGrid p feedbackIndex)
        rate localState = currentDecodeStep p i row' t
        (feedbackAtGrid p feedbackIndex) rate localState' := by
    simpa [← htime, ← hfeedback] using hdecoded
  have hbeforeCode : FollowerDownMeasurability.encodeFollowerState localState =
      FollowerDownMeasurability.encodeFollowerState localState' := by
    simp [FollowerDownMeasurability.encodeFollowerState,
      FollowerDownMeasurability.followerStateCode,
      localState, localState', adaptedInputState]
  have hafterCodeCommon : FollowerDownMeasurability.encodeFollowerState
        {localState with downBatch :=
          (currentDecodeStep p i row' t (feedbackAtGrid p feedbackIndex) rate localState').1} =
      FollowerDownMeasurability.encodeFollowerState
        {localState' with downBatch :=
          (currentDecodeStep p i row' t (feedbackAtGrid p feedbackIndex) rate localState').1} := by
    simp [FollowerDownMeasurability.encodeFollowerState,
      FollowerDownMeasurability.followerStateCode,
      localState, localState', adaptedInputState]
  have hacceptedStart : ReferencePrelaunchFollower.acceptedStart localState =
      ReferencePrelaunchFollower.acceptedStart localState' := by
    simp [localState, localState', adaptedInputState,
      ReferencePrelaunchFollower.acceptedStart]
  have htransitionCode :
      FollowerDownMeasurability.encodeLocalDownResult
          (ActiveFollowerDownAcceptance.downTransition p i row t
            (feedbackAtGrid p feedbackIndex) rate localState) =
        FollowerDownMeasurability.encodeLocalDownResult
          (ActiveFollowerDownAcceptance.downTransition p i row' t'
            (feedbackAtGrid p feedbackIndex') rate localState') := by
    unfold ActiveFollowerDownAcceptance.downTransition
    rw [← htime, ← hfeedback]
    simp_rw [hdecodedAtLeft, hscan, hchecked]
    simp only [hselectedAtLeft, hstatus, hregisters, hbatch, hbuffer, hacceptedStart]
    split_ifs <;> (try split) <;> (try split_ifs) <;> (try split) <;>
      simp_all [FollowerDownMeasurability.encodeLocalDownResult,
        FollowerDownMeasurability.encodeFollowerState,
        FollowerDownMeasurability.followerStateCode]
  unfold downTransitionCodeAt FollowerDownMeasurability.downTransitionCode
  change FollowerDownMeasurability.encodeLocalDownResult
      (ActiveFollowerDownAcceptance.downTransition p i row t
        (feedbackAtGrid p feedbackIndex) rate localState) =
    FollowerDownMeasurability.encodeLocalDownResult
      (ActiveFollowerDownAcceptance.downTransition p i row' t'
        (feedbackAtGrid p feedbackIndex') rate localState')
  exact htransitionCode

/-- Joint measurability of the complete existing DOWN code in the complete
row, calendar time, finite feedback index, and original finite product of
saved observation/thinning coordinates. -/
theorem measurable_downTransitionCode_joint {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (downTransitionCodeAt i rate state) := by
  apply measurable_of_countable_read_factorization
    (downReadSignatureAt i rate state)
    (measurable_downReadSignatureAt i rate state)
  intro x y hxy
  exact downTransitionCodeAt_eq_of_readSignature_eq i rate state x y hxy

/-- Expanded form of the joint theorem with the four original input variables
visible in the function domain. -/
theorem measurable_downTransitionCode_joint_apply {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (fun x : DownJointInput p state.buffer.length =>
      FollowerDownMeasurability.downTransitionCode i
        x.1.1.1 x.1.1.2 x.1.2 rate state x.2) := by
  convert measurable_downTransitionCode_joint i rate state using 1
  rfl

/-- Consume the existing exact reconstruction theorem for every joint input;
the measurable countable code therefore recovers the complete actual
`LocalDownResult`, with its true continuous buffers and buffer-clearing tag. -/
theorem downTransitionCode_joint_reconstruct {p : Parameters}
    (i : Fin (p.m - 1)) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (x : DownJointInput p state.buffer.length) :
    reconstructLocalDownResult (downTransitionCodeAt i rate state x)
        (replaceBufferScalars state.buffer (jointValues x)) =
      ActiveFollowerDownAcceptance.downTransition p i (jointRow x) (jointTime x)
        (feedbackAtGrid p (jointFeedbackIndex x)) rate
        (adaptedInputState rate state (jointValues x)) := by
  exact FollowerDownMeasurability.downTransitionCode_reconstruct i
    (jointRow x) (jointTime x) (jointFeedbackIndex x) rate state (jointValues x)

/-- Literal row-read equality: once the actual current selected DOWN input and
all proposal bits strictly before `t` agree, changing forward bits, future
controls, or other row coordinates leaves the complete operation code fixed.
The original carried buffer and its independently varying saved scalars are
the same on both sides. -/
theorem downTransitionCode_eq_of_currentInput_and_pastProposalBits {p : Parameters}
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (t : Fin p.T)
    (feedbackIndex : Fin (D p + 1)) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : SavedScalarFamily state.buffer.length)
    (hcurrent : ActiveFollowerDownAcceptance.currentRoundInput p i row t
        (feedbackAtGrid p feedbackIndex) rate (adaptedInputState rate state values) =
      ActiveFollowerDownAcceptance.currentRoundInput p i row' t
        (feedbackAtGrid p feedbackIndex) rate (adaptedInputState rate state values))
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j =
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row' j) :
    FollowerDownMeasurability.downTransitionCode i row t feedbackIndex rate state values =
      FollowerDownMeasurability.downTransitionCode i row' t feedbackIndex rate state values := by
  classical
  let x : DownJointInput p state.buffer.length := ⟨((row, t), feedbackIndex), values⟩
  let y : DownJointInput p state.buffer.length := ⟨((row', t), feedbackIndex), values⟩
  have hselBool : downSelectionBit i row t = downSelectionBit i row' t := by
    have hsel := congrArg AffineBatchDecoder.RoundInput.selected hcurrent
    unfold ActiveFollowerDownAcceptance.currentRoundInput at hsel
    change decide (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) =
      decide (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) at hsel
    have hpropRaw : (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) ↔
      (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) := by
      constructor
      · intro hp
        exact (Bool.decide_iff _).mp (hsel.symm.trans ((Bool.decide_iff _).mpr hp))
      · intro hp
        exact (Bool.decide_iff _).mp (hsel.trans ((Bool.decide_iff _).mpr hp))
    have hprop : ActiveFollowerDownAcceptance.downSelected p i row t =
        ActiveFollowerDownAcceptance.downSelected p i row' t := by
      apply propext
      simpa only [ActiveFollowerDownAcceptance.downSelected] using hpropRaw
    exact decide_eq_of_prop_eq hprop
  have hsample' : (row.2 t).2 (0, i) = (row'.2 t).2 (0, i) := by
    have hsample := congrArg AffineBatchDecoder.RoundInput.sample hcurrent
    simpa only [ActiveFollowerDownAcceptance.currentRoundInput,
      AffineBatchDecoder.width, ContinuousLearningRows.B] using hsample
  have hround : downRoundRead i x = downRoundRead i y := by
    apply DownRoundRead.ext
    · rfl
    · rfl
    · change downSelectionBit i row t = downSelectionBit i row' t
      exact hselBool
    · change (row.2 t).2 (0, i) = (row'.2 t).2 (0, i)
      exact hsample'
  have hbits : pastProposalBitsAt rate row t = pastProposalBitsAt rate row' t := by
    funext j
    by_cases hj : j.val < t.val
    · simp [pastProposalBitsAt, hj, hpast j hj]
    · simp [pastProposalBitsAt, hj]
  have hsignature : downReadSignatureAt i rate state x =
      downReadSignatureAt i rate state y := by
    unfold downReadSignatureAt
    exact Prod.ext (Prod.ext hround hbits) (Prod.ext rfl rfl)
  change downTransitionCodeAt i rate state x = downTransitionCodeAt i rate state y
  exact downTransitionCodeAt_eq_of_readSignature_eq i rate state x y hsignature

/-- Countable code for the discrete timestamp/pilot skeleton of a fixed-size
carried buffer. -/
abbrev BufferSkeletonCode (p : Parameters) (n : ℕ) := Fin n → ℕ × Fin p.K

instance bufferSkeletonCodeCountable (p : Parameters) (n : ℕ) :
    Countable (BufferSkeletonCode p n) := inferInstance

instance bufferSkeletonCodeMeasurableSpace (p : Parameters) (n : ℕ) :
    MeasurableSpace (BufferSkeletonCode p n) := ⊤

/-- Extract only timestamps and pilots, preserving the literal list order. -/
def bufferSkeletonCode {p : Parameters} (buffer : List (SparseCalendarRecord p.K)) :
    BufferSkeletonCode p buffer.length :=
  fun j => (buffer[j].calendarRound, buffer[j].pilot)

/-- Extract the original continuous observation/thinning coordinates in their
literal finite product order. -/
def bufferScalarsCode {p : Parameters} (buffer : List (SparseCalendarRecord p.K)) :
    SavedScalarFamily buffer.length :=
  fun j => (buffer[j].observation, buffer[j].thinScalar)

/-- Rebuild a carried buffer from its exact discrete skeleton and original
saved scalar family. This is a data decomposition, not an execution trace. -/
def bufferFromSkeletonAndScalars {p : Parameters} {n : ℕ}
    (skeleton : BufferSkeletonCode p n) (values : SavedScalarFamily n) :
    List (SparseCalendarRecord p.K) :=
  List.ofFn fun j : Fin n => ⟨(skeleton j).1, (skeleton j).2,
    (values j).1, (values j).2⟩

/-- Every existing buffer is exactly recovered from its countable skeleton and
its unmodified continuous coordinates. -/
theorem bufferFromSkeletonAndScalars_code {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) :
    bufferFromSkeletonAndScalars (bufferSkeletonCode buffer) (bufferScalarsCode buffer) =
      buffer := by
  classical
  simp [bufferFromSkeletonAndScalars, bufferSkeletonCode, bufferScalarsCode]

/-- Usable decomposition of an arbitrary carried follower state into its
countable discrete register/batch code and exact timestamp/pilot skeleton,
with every stored observation and thinning value retained. -/
theorem carriedState_countable_decomposition {p : Parameters} (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    followerStateOfCode rate (followerStateCode rate state)
        (bufferFromSkeletonAndScalars (bufferSkeletonCode state.buffer)
          (bufferScalarsCode state.buffer)) = state := by
  rw [bufferFromSkeletonAndScalars_code]
  exact FollowerDownMeasurability.followerStateOfCode_code_eq rate state
    state.buffer rfl

end Bandits.Support.FollowerDownJointMeasurability

end
