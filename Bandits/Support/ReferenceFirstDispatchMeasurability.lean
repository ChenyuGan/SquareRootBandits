/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceDownCutJointMeasurability
public import Bandits.Support.CheckedAssignmentJointMeasurability

/-!
# Borel observation of the actual first coordinator dispatch

This module follows the first-assignment construction and the local clock and
transport protocol. The input is the original calendar coordinate and complete
public row, and the first launch receives its complete `K + 1` assignment
vector. The output records the actual first outcome data and the actual
choice-time view. No law, freshness statement, later dispatcher branch,
initialization splice, or manuscript closure is asserted.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-113`,
`sources/zip4/manuscript/05_binary_transport.tex:62-78`,
`sources/zip4/manuscript/06_interruptions.tex:41-69,246-256`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceFirstDispatchMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev LearningRate := ReferencePrelaunchFollower.LearningRate

variable {p : Parameters} {rate : RateInput p}

local instance firstSlowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤

/-- The original product Borel domain for one first-dispatch call. -/
abbrev FirstDomain (p : Parameters) :=
  Fin p.T × CompletePublicTable.CompleteRow p

/-- Build the exact first-dispatch input from the same rate and original row.
In particular, the complete vector is not replaced by one selected arm. -/
def firstInputAt (rate : RateInput p) (z : FirstDomain p) :
    CoordinatorRoundDispatch.FirstInput p :=
  { eta := rate.eta
    eta_le_source_cap := rate.sourceCap
    n := rate.n
    n_eq_eta_mul_D := rate.n_scale
    time := z.1
    row := z.2 }

/-- The exact launch input used by `dispatchFirst`; its coordinates are the
whole assignment vector read from this same `(time,row)`. -/
def firstLaunchInputAt (rate : RateInput p) (z : FirstDomain p) :
    FirstAssignmentLaunch.Input p rate.eta :=
  CoordinatorRoundDispatch.firstLaunchInput (firstInputAt rate z)

theorem firstLaunchInputAt_coordinates (z : FirstDomain p) :
    (firstLaunchInputAt rate z).coordinates =
      LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1 := rfl

private theorem measurable_eval_fin {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {α : Type*} [MeasurableSpace α]
    (f : Ω → Fin n → α) (i : Ω → Fin n) (hf : Measurable f)
    (hi : Measurable i) : Measurable (fun x => f x (i x)) := by
  classical
  intro s hs
  have hset : (fun x => f x (i x)) ⁻¹' s =
      ⋃ j : Fin n, {x | i x = j} ∩ (fun x => f x j) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨i x, rfl, hx⟩
    · rintro ⟨j, hidx, hval⟩
      rw [hidx]
      exact hval
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (hi (measurableSet_singleton j)).inter
      (((measurable_pi_apply j).comp hf) hs)

/-- Borel measurability of the whole original assignment vector on the
time-row product. -/
theorem measurable_firstAssignmentVector :
    Measurable (fun z : FirstDomain p =>
      LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1) := by
  have hfamily : Measurable (fun z : FirstDomain p =>
      fun t : Fin p.T =>
        LaterAssignmentStartOperation.ownAssignmentVector z.2 t) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (LaterAssignmentStartMeasurability.measurable_ownAssignmentVector
      (p := p) t).comp measurable_snd
  exact measurable_eval_fin (α := Fin (p.K + 1) → ContinuousControlSlice.Scalar)
    (f := fun z : FirstDomain p => fun t : Fin p.T =>
      LaterAssignmentStartOperation.ownAssignmentVector z.2 t)
    (i := fun z => z.1) hfamily measurable_fst

/-- The actual first slow set is the accepted canonical sampler on all
`K + 1` coordinates with the source's unit current and anchor weights. -/
def firstSlowSetAt (z : FirstDomain p) : SlowSet p.K p.m :=
  (firstLaunchInputAt rate z).slowSet

theorem measurable_firstSlowSetAt : Measurable (firstSlowSetAt (rate := rate)) := by
  change Measurable (fun z : FirstDomain p =>
    CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
      (LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1))
  exact (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m
    p.m_lt_K (fun _ => 1) (fun _ => 1) (by intro _; norm_num)
    (by intro _; norm_num)).comp measurable_firstAssignmentVector

local instance firstAssignmentMeasurableSpace :
    MeasurableSpace (ActiveRoundActions.Assignment p.m p.K) := ⊤
local instance firstSnapshotMissingMeasurableSpace :
    MeasurableSpace (Finset (ActiveRoundActions.Follower p.m)) := ⊤
local instance firstFollowerStatusMeasurableSpace :
    MeasurableSpace ActiveRoundActions.FollowerStatus := ⊤
local instance firstDownRecordMeasurableSpace {eta : LearningRate} :
    MeasurableSpace (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p eta)) := ⊤
local instance firstDownWordMeasurableSpace {eta : LearningRate} :
    MeasurableSpace (OrdinaryMessageCodec.Word
      (ReferencePrelaunchFollower.codecParams p eta)) := ⊤
local instance firstClockMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.ClockRegisters p) := ⊤
/-- Lossless data fields of the original first `Start` value. The snapshot's
two data fields are recorded explicitly; assignment and snapshot proofs carry
no data and are reconstructed by their original structures. -/
structure FirstStartObservation (p : Parameters) (eta : LearningRate) where
  sigma : Fin p.T
  coordinates : Fin (p.K + 1) → ContinuousControlSlice.Scalar
  slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m
  auxiliaryArm : Fin p.K
  assignment : ActiveRoundActions.Assignment p.m p.K
  snapshotMissing : Finset (ActiveRoundActions.Follower p.m)
  snapshotStatus : ActiveRoundActions.Follower p.m →
    ActiveRoundActions.FollowerStatus
  baseScores : Fin p.K → ℕ
  queues : Fin p.K → ℕ
  weights : Fin p.K → ℝ
  anchor : Fin p.K → ℝ
  recordingRates : Fin p.K → ℝ
  outgoing : ActiveRoundActions.Follower p.m →
    OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta)
  outgoingWords : ActiveRoundActions.Follower p.m →
    OrdinaryMessageCodec.Word (ReferencePrelaunchFollower.codecParams p eta)

/-- The complete ordinary-Borel observation of a first launch start. -/
def firstStartRemainderCode {p : Parameters} {eta : LearningRate}
    (s : FirstAssignmentLaunch.Start p eta) :=
  Prod.mk s.slowSet
    (Prod.mk s.auxiliaryArm
      (Prod.mk s.assignment
        (Prod.mk s.snapshot.missing
          (Prod.mk s.snapshot.status
            (Prod.mk s.baseScores
              (Prod.mk s.queues
                (Prod.mk s.weights
                  (Prod.mk s.anchor
                    (Prod.mk s.recordingRates
                      (Prod.mk s.outgoing s.outgoingWords))))))))))

def firstStartObservationCode {p : Parameters} {eta : LearningRate}
    (s : FirstAssignmentLaunch.Start p eta) :=
  (s.sigma, (s.coordinates, firstStartRemainderCode s))

private theorem firstStartRemainderCode_eq_of_key
    {s t : FirstAssignmentLaunch.Input p rate.eta}
    (htime : s.sigma = t.sigma) (hslow : s.slowSet = t.slowSet) :
    firstStartRemainderCode s.start = firstStartRemainderCode t.start := by
  have haux : s.auxiliaryArm = t.auxiliaryArm := by
    unfold FirstAssignmentLaunch.Input.auxiliaryArm
    simp only [hslow]
  have harm : s.followerArm = t.followerArm := by
    unfold FirstAssignmentLaunch.Input.followerArm
    rw [hslow]
  have hassign : s.assignment = t.assignment := by
    simp only [FirstAssignmentLaunch.Input.assignment, harm, haux]
  have hexponent (i : Fin (p.m - 1)) : s.exponent i = t.exponent i := by
    have hthreshold : s.recordingThreshold i = t.recordingThreshold i := by
      unfold FirstAssignmentLaunch.Input.recordingThreshold
      rw [congrFun harm i]
    have hcast : (s.exponent i : ℤ) = (t.exponent i : ℤ) := by
      rw [s.exponent_intCast, t.exponent_intCast, hthreshold]
    exact_mod_cast hcast
  have hrecord : s.downRecord = t.downRecord := by
    funext i
    apply Subtype.ext
    rw [s.downRecord_fields, t.downRecord_fields, htime, congrFun harm i, haux, hexponent i]
  have hword : s.downWord = t.downWord := by
    funext i
    unfold FirstAssignmentLaunch.Input.downWord
    rw [congrFun hrecord i]
  simp only [firstStartRemainderCode, FirstAssignmentLaunch.Input.start]
  simp only [hslow, haux, hassign, FirstAssignmentLaunch.Input.initialSnapshot,
    ActiveRoundActions.initialSnapshot, hrecord, hword]

local instance firstSlowSetDataMeasurableSpace (p : Parameters) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤

instance firstStartMeasurableSpace {p : Parameters} {eta : LearningRate} :
    MeasurableSpace (FirstAssignmentLaunch.Start p eta) :=
  MeasurableSpace.comap firstStartObservationCode inferInstance

/-- The observation retains every start data field. -/
def observeFirstStart {p : Parameters} {eta : LearningRate}
    (s : FirstAssignmentLaunch.Start p eta) : FirstStartObservation p eta :=
  { sigma := s.sigma
    coordinates := s.coordinates
    slowSet := s.slowSet
    auxiliaryArm := s.auxiliaryArm
    assignment := s.assignment
    snapshotMissing := s.snapshot.missing
    snapshotStatus := s.snapshot.status
    baseScores := s.baseScores
    queues := s.queues
    weights := s.weights
    anchor := s.anchor
    recordingRates := s.recordingRates
    outgoing := s.outgoing
    outgoingWords := s.outgoingWords }

/-- Decode the observed start fields back into the exact existing `Start`
carrier. -/
def FirstStartObservation.decode {p : Parameters} {eta : LearningRate}
    (o : FirstStartObservation p eta) : FirstAssignmentLaunch.Start p eta :=
  { sigma := o.sigma
    coordinates := o.coordinates
    slowSet := o.slowSet
    auxiliaryArm := o.auxiliaryArm
    assignment := o.assignment
    snapshot := ⟨o.snapshotMissing, o.snapshotStatus⟩
    baseScores := o.baseScores
    queues := o.queues
    weights := o.weights
    anchor := o.anchor
    recordingRates := o.recordingRates
    outgoing := o.outgoing
    outgoingWords := o.outgoingWords }

theorem FirstStartObservation.decode_observeFirstStart {p : Parameters}
    {eta : LearningRate} (s : FirstAssignmentLaunch.Start p eta) :
    (observeFirstStart s).decode = s := by
  cases s
  rfl

theorem firstStartObservationCode_injective {p : Parameters}
    {eta : LearningRate} :
    Function.Injective (@firstStartObservationCode p eta) := by
  intro left right h
  cases left with
  | mk ls lc lslow laux las lsnapshot lb lq lw lanchor lr lo low =>
    cases right with
    | mk rs rc rslow raux ras rsnapshot rb rq rw ranchor rr ro row =>
      simp only [firstStartObservationCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hrem⟩
      simp only [firstStartRemainderCode, Prod.mk.injEq] at hrem
      rcases hrem with ⟨rfl, rfl, rfl, hmissing, hstatus, rfl,
        rfl, rfl, rfl, rfl, htail⟩
      rcases htail with ⟨rfl, rfl⟩
      cases lsnapshot
      cases rsnapshot
      simp_all

local instance firstStartRoundResultMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

/-- The deterministic first payload at a fixed time and already sampled slow
set. It records the same exact source rate and zero queue/unit anchor fields as
`Input.ofFirstAssignment`. -/
def firstPayloadAt (rate : RateInput p) (time : Fin p.T)
    (slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    AssignmentStartPayload.Input p rate.eta := {
  eta_le_source_cap := rate.sourceCap
  n := rate.n
  n_eq_eta_mul_D := rate.n_scale
  sigma := time
  slowSet := slowSet
  anchor := fun _ => 1
  anchor_pos := by intro _; norm_num
  queues := fun _ => 0
  queues_le_TD := by intro _; exact Nat.zero_le _ }

/-- The data decoder's actual launch payload is exactly the first payload
computed from the same time and actual sampled slow set. -/
theorem firstPayloadAt_eq_ofFirstAssignment (z : FirstDomain p) :
    firstPayloadAt rate z.1 (firstSlowSetAt (rate := rate) z) =
      AssignmentStartPayload.Input.ofFirstAssignment (firstLaunchInputAt rate z) := by
  cases z
  rfl

abbrev FirstChoiceKey (p : Parameters) :=
  Fin p.T × CanonicalOrientedSetLaw.SlowSet p.K p.m

local instance firstChoiceKeyMeasurableSpace (p : Parameters) :
    MeasurableSpace (FirstChoiceKey p) := ⊤

def firstChoiceKeyAt (rate : RateInput p) (z : FirstDomain p) : FirstChoiceKey p :=
  (z.1, firstSlowSetAt (rate := rate) z)

theorem measurable_firstChoiceKeyAt :
    Measurable (firstChoiceKeyAt (rate := rate)) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro q
  have hset : {z : FirstDomain p | firstChoiceKeyAt rate z = q} =
      {z | z.1 = q.1} ∩ {z | firstSlowSetAt (rate := rate) z = q.2} := by
    ext z
    change (z.1, firstSlowSetAt (rate := rate) z) = q ↔ _
    constructor
    · intro h
      exact ⟨by simpa using congrArg Prod.fst h,
        by simpa using congrArg Prod.snd h⟩
    · rintro ⟨ht, hs⟩
      exact Prod.ext ht hs
  rw [hset]
  exact (measurable_fst (measurableSet_singleton q.1)).inter
    (measurable_firstSlowSetAt (measurableSet_singleton q.2))

private theorem measurable_of_constant_on_countable_fibers
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (f : α → γ)
    (hconstant : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro s _
  have hpre : f ⁻¹' s =
      ⋃ b, ⋃ (_ : ∃ y, key y = b ∧ f y ∈ s), {x | key x = b} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨key x, ⟨x, rfl, hx⟩, rfl⟩
    · rintro ⟨b, ⟨y, hy, hys⟩, hx⟩
      exact (hconstant x y (hx.trans hy.symm)).symm ▸ hys
  rw [hpre]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ =>
    hkey (measurableSet_singleton b)

private theorem measurable_over_countable_fiber
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [Countable γ]
    [MeasurableSingletonClass β] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (key : α → β) (hkey : Measurable key) (fiber : β → α → γ)
    (hfiber : ∀ b, Measurable (fiber b)) :
    Measurable (fun x => fiber (key x) x) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro c
  have hset : {x | fiber (key x) x = c} =
      ⋃ b, {x | key x = b} ∩ {x | fiber b x = c} := by
    ext x
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun b =>
    (hkey (measurableSet_singleton b)).inter
      (hfiber b (measurableSet_singleton c))

def firstChoiceSection (rate : RateInput p) (q : FirstChoiceKey p)
    (row : CompletePublicTable.CompleteRow p) : Option (Fin p.K) :=
  CoordinatorLocalArmChoice.coordinatorArmChoice
    (firstPayloadAt rate q.1 q.2) Finset.univ none q.1 (fun _ => 1) row

theorem measurable_firstChoiceSection (q : FirstChoiceKey p) :
    Measurable (firstChoiceSection (p := p) rate q) := by
  exact CoordinatorLocalArmChoice.measurable_coordinatorArmChoice
    (firstPayloadAt rate q.1 q.2) Finset.univ none q.1 (fun _ => 1)

def firstChoiceAt (rate : RateInput p) (z : FirstDomain p) : Option (Fin p.K) :=
  firstChoiceSection rate (firstChoiceKeyAt rate z) z.2

theorem measurable_firstChoiceAt : Measurable (firstChoiceAt (rate := rate)) := by
  exact measurable_over_countable_fiber (firstChoiceKeyAt rate)
    measurable_firstChoiceKeyAt
    (fun q z => firstChoiceSection rate q z.2)
    (fun q => (measurable_firstChoiceSection (p := p) (rate := rate) q).comp
      measurable_snd)

def firstChoiceViewForKey (rate : RateInput p) (q : FirstChoiceKey p) :
    ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := firstPayloadAt rate q.1 q.2
  pendingAtChoice := Finset.univ
  cutoff := none
  complementWeights := fun _ => 1 }

def firstChoiceViewAt (rate : RateInput p) (z : FirstDomain p) :
    ReferenceDownReception.ChoiceTimeView p rate.eta :=
  firstChoiceViewForKey rate (firstChoiceKeyAt rate z)

theorem measurable_firstChoiceViewObservationAt :
    Measurable (fun z : FirstDomain p =>
      ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (firstChoiceViewAt rate z)) := by
  have hkey : Measurable (fun q : FirstChoiceKey p =>
      ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (firstChoiceViewForKey rate q)) := measurable_of_countable _
  exact hkey.comp measurable_firstChoiceKeyAt

theorem measurable_firstChoiceViewAt :
    Measurable (firstChoiceViewAt (rate := rate)) := by
  have hkey : Measurable (firstChoiceViewForKey rate) := measurable_of_countable _
  exact hkey.comp measurable_firstChoiceKeyAt

def firstStartResultAt (rate : RateInput p) (z : FirstDomain p) :
    CoordinatorPhaseClock.StartRoundResult p :=
  CoordinatorAssignmentRegisterInstall.firstStartRoundResult
    (firstLaunchInputAt rate z)

theorem firstInstalledStartResultAt (z : FirstDomain p) :
    (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)).startRoundResult =
      firstStartResultAt rate z := rfl

def firstStartedClockAt (rate : RateInput p) (z : FirstDomain p) :
    CoordinatorPhaseClock.ClockRegisters p := {
  sigma := some z.1
  u := none
  g := FollowerCutoffScan.gridBoundary p rate.eta.val z.1
  lastProposal := none }

theorem measurable_firstStartedClockAt :
    Measurable (firstStartedClockAt (rate := rate)) := by
  let f : Fin p.T → CoordinatorPhaseClock.ClockRegisters p := fun t => {
    sigma := some t
    u := none
    g := FollowerCutoffScan.gridBoundary p rate.eta.val t
    lastProposal := none }
  have hf : Measurable f := measurable_of_countable _
  exact hf.comp measurable_fst

theorem firstStartedClockAt_eq_actual (z : FirstDomain p) :
    firstStartedClockAt rate z = (firstStartResultAt rate z).clock := rfl

/-- The coordinator-register observation extends complement scores by zero
outside their actual complement. Restriction to the recorded slow set recovers
every register entry. -/
def firstRegisterObservationCode {p : Parameters} {eta : LearningRate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta) :=
  (r.payload, (r.priorClock, (r.pendingAtChoice, (r.time,
    (r.gridBoundary, fun a : Fin p.K =>
      if ha : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet then
        r.complementScores ⟨a, ha⟩ else 0)))))

instance firstRegistersMeasurableSpace {p : Parameters} {eta : LearningRate} :
    MeasurableSpace (CoordinatorLiveChoiceRecorderStep.Registers p eta) :=
  MeasurableSpace.comap firstRegisterObservationCode inferInstance

theorem firstRegisterObservationCode_injective {p : Parameters}
    {eta : LearningRate} :
    Function.Injective (@firstRegisterObservationCode p eta) := by
  intro left right h
  cases left with
  | mk lp lc lpending lt lg lscores =>
    cases right with
    | mk rp rc rpending rt rg rscores =>
      simp only [firstRegisterObservationCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hscores⟩
      have hscore : lscores = rscores := by
        funext j
        have hv := congrFun hscores j.1
        have hj : j.1 ∈ fastArmFinset lp.slowSet := j.2
        simpa only [dite_eq_left hj] using hv
      cases hscore
      rfl

/-- All constructors of the raw first-outcome carrier are retained in the
lossless observation, with the chosen arm absent only on its three explicitly
tagged failure constructors. -/
inductive FirstOutcomeTag where
  | choiceDomainFailure
  | recorderBoundaryFailure
  | choiceRejected
  | chosen
  deriving DecidableEq

local instance firstOutcomeTagMeasurableSpace :
    MeasurableSpace FirstOutcomeTag := ⊤
local instance firstOptionalArmMeasurableSpace :
    MeasurableSpace (Option (Fin p.K)) := ⊤

/-- Lossless data from one actual first-dispatch outcome. The start retains its
complete original vector; register scores and owned queues/services retain all
actual complement coordinates. -/
structure FirstDispatchObservation (p : Parameters) (eta : LearningRate) where
  tag : FirstOutcomeTag
  start : FirstAssignmentLaunch.Start p eta
  startRoundResult : CoordinatorPhaseClock.StartRoundResult p
  registers : CoordinatorLiveChoiceRecorderStep.Registers p eta
  queue : Fin p.K → ℕ
  previousService : Fin p.K → ℕ
  followerBaseScore : Fin (p.m - 1) → ℕ
  arm : Option (Fin p.K)

def firstDispatchObservationCode {p : Parameters} {eta : LearningRate}
    (o : FirstDispatchObservation p eta) :=
  (o.tag, (o.start, (o.startRoundResult, (o.registers,
    (o.queue, (o.previousService, (o.followerBaseScore, o.arm)))))))

instance firstDispatchObservationMeasurableSpace {p : Parameters}
    {eta : LearningRate} : MeasurableSpace (FirstDispatchObservation p eta) :=
  MeasurableSpace.comap firstDispatchObservationCode inferInstance

/-- The data decoder; it reads the observed start, clock, registers and
extended queue/service vectors directly and never calls `dispatchFirst`. -/
structure FirstInstallationData (p : Parameters) (eta : LearningRate) where
  start : FirstAssignmentLaunch.Start p eta
  startRoundResult : CoordinatorPhaseClock.StartRoundResult p
  registers : CoordinatorLiveChoiceRecorderStep.Registers p eta
  queue : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ
  previousService : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ
  followerBaseScore : Fin (p.m - 1) → ℕ

def decodeFirstDispatchObservation {p : Parameters} {eta : LearningRate}
    (o : FirstDispatchObservation p eta) :
      FirstInstallationData p eta × Option (Fin p.K) :=
  (⟨o.start, o.startRoundResult, o.registers,
    fun j => o.queue j.1, fun j => o.previousService j.1,
    o.followerBaseScore⟩, o.arm)

/-- The first-dispatch outcome is encoded without dropping any constructor or
installation field. -/
def observeFirstOutcome {p : Parameters}
    {x : CoordinatorRoundDispatch.FirstInput p}
    (outcome : CoordinatorRoundDispatch.FirstOutcome x) :
      FirstDispatchObservation p x.eta := by
  cases outcome with
  | choiceDomainFailure installed =>
      exact {
        tag := .choiceDomainFailure
        start := installed.start
        startRoundResult := installed.startRoundResult
        registers := installed.registers
        queue := fun a => if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
          installed.ownedRegisters.queue ⟨a, ha⟩ else 0
        previousService := fun a =>
          if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
            installed.ownedRegisters.previousService ⟨a, ha⟩ else 0
        followerBaseScore := installed.followerBaseScore
        arm := none }
  | recorderBoundaryFailure installed =>
      exact {
        tag := .recorderBoundaryFailure
        start := installed.start
        startRoundResult := installed.startRoundResult
        registers := installed.registers
        queue := fun a => if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
          installed.ownedRegisters.queue ⟨a, ha⟩ else 0
        previousService := fun a =>
          if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
            installed.ownedRegisters.previousService ⟨a, ha⟩ else 0
        followerBaseScore := installed.followerBaseScore
        arm := none }
  | choiceRejected installed =>
      exact {
        tag := .choiceRejected
        start := installed.start
        startRoundResult := installed.startRoundResult
        registers := installed.registers
        queue := fun a => if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
          installed.ownedRegisters.queue ⟨a, ha⟩ else 0
        previousService := fun a =>
          if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
            installed.ownedRegisters.previousService ⟨a, ha⟩ else 0
        followerBaseScore := installed.followerBaseScore
        arm := none }
  | chosen installed selected =>
      exact {
        tag := .chosen
        start := installed.start
        startRoundResult := installed.startRoundResult
        registers := installed.registers
        queue := fun a => if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
          installed.ownedRegisters.queue ⟨a, ha⟩ else 0
        previousService := fun a =>
          if ha : a ∈ fastArmFinset installed.registers.payload.slowSet then
            installed.ownedRegisters.previousService ⟨a, ha⟩ else 0
        followerBaseScore := installed.followerBaseScore
        arm := some selected.arm }

def firstOutcomeAt (rate : RateInput p) (z : FirstDomain p) :=
  CoordinatorRoundDispatch.dispatchFirst (firstInputAt rate z)

def firstInstalledChoiceView {x : CoordinatorRoundDispatch.FirstInput p}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput x)) :
    ReferenceDownReception.ChoiceTimeView p x.eta := {
  payload := installed.registers.payload
  pendingAtChoice := by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using
      installed.startRoundResult.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
    installed.startRoundResult.clock.u
  complementWeights := installed.registers.complementWeights }

def firstInstalledArmChoice {x : CoordinatorRoundDispatch.FirstInput p}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput x)) : Option (Fin p.K) :=
  CoordinatorLocalArmChoice.coordinatorArmChoice installed.registers.payload
    installed.startRoundResult.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
    installed.registers.time installed.registers.complementWeights x.row

def firstOutcomeView {x : CoordinatorRoundDispatch.FirstInput p}
    (outcome : CoordinatorRoundDispatch.FirstOutcome x) :
    Option (ReferenceDownReception.ChoiceTimeView p x.eta) := by
  cases outcome with
  | choiceDomainFailure _ => exact none
  | recorderBoundaryFailure _ => exact none
  | choiceRejected _ => exact none
  | chosen installed _ => exact some (firstInstalledChoiceView installed)

def firstOutcomeArm {x : CoordinatorRoundDispatch.FirstInput p}
    (outcome : CoordinatorRoundDispatch.FirstOutcome x) : Fin p.K :=
  match outcome with
  | .choiceDomainFailure _ => ReferenceActivePhysicalStep.coordinatorFallback p
  | .recorderBoundaryFailure _ => ReferenceActivePhysicalStep.coordinatorFallback p
  | .choiceRejected _ => ReferenceActivePhysicalStep.coordinatorFallback p
  | .chosen _ selected => selected.arm

/-- The actual first operation's literal body reaches its chosen branch. The
proof discharges the local nonempty-choice obligation created by the actual
unit-anchor installation. -/
theorem firstOutcomeAt_chosen (z : FirstDomain p) :
    ∃ installed selected,
      firstOutcomeAt rate z = .chosen installed selected := by
  classical
  unfold firstOutcomeAt CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch actualInstall started payload weights cutoff hpayload hstarted
    hcutoff hweights hchoice hboundary hnonempty
  have hsome : ∃ arm, CoordinatorLocalArmChoice.coordinatorArmChoice payload
      started.pending cutoff actualInstall.registers.time weights
        (firstInputAt rate z).row = some arm := by
    cases hresult : CoordinatorLocalArmChoice.coordinatorArmChoice payload
        started.pending cutoff actualInstall.registers.time weights
          (firstInputAt rate z).row with
    | none => exact False.elim (hnonempty hresult)
    | some arm => exact ⟨arm, rfl⟩
  obtain ⟨arm, harm⟩ := hsome
  refine ⟨actualInstall,
    { arm := arm
      choiceInputsValid := hchoice
      recorderBoundaryValid := hboundary
      armChoice_eq := harm }, ?_⟩
  split
  · exact False.elim (hnonempty (by assumption))
  · case h_2 arm' heq =>
      have harmeq : arm' = arm := Option.some.inj (heq.symm.trans harm)
      subst arm'
      rfl

/-- On any chosen result of the actual operation, the retained installation
is the original literal `installFirst` call. -/
theorem firstOutcomeAt_chosen_installation (z : FirstDomain p)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (firstLaunchInputAt rate z))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights z.2)
    (hchosen : firstOutcomeAt rate z = .chosen installed selected) :
    installed = CoordinatorAssignmentRegisterInstall.installFirst
      (firstLaunchInputAt rate z) := by
  classical
  unfold firstOutcomeAt CoordinatorRoundDispatch.dispatchFirst at hchosen
  extract_lets launch actualInstall started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty at hchosen
  split at hchosen
  · contradiction
  · exact (CoordinatorRoundDispatch.FirstOutcome.chosen.inj hchosen).1.symm

/-- The accepted `ArmSelection.armChoice_eq` in the exact chosen result is
the fixed slow-set/time fiber operation whose Borel sections were established
above. -/
theorem firstChoiceAt_eq_chosen_arm (z : FirstDomain p)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (firstLaunchInputAt rate z))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights z.2)
    (hchosen : firstOutcomeAt rate z = .chosen installed selected) :
    firstChoiceAt rate z = some selected.arm := by
  have hinstall := firstOutcomeAt_chosen_installation z installed selected hchosen
  have hchoice : firstInstalledArmChoice (x := firstInputAt rate z) installed =
      some selected.arm := selected.armChoice_eq
  have htransport := congrArg (firstInstalledArmChoice (x := firstInputAt rate z)) hinstall
  rw [htransport] at hchoice
  have hweights :
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)).registers.complementWeights =
        fun _ => 1 := by
    funext j
    exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one
      (firstLaunchInputAt rate z) j
  have hpayload := firstPayloadAt_eq_ofFirstAssignment (rate := rate) z
  have hdirect : firstInstalledArmChoice (x := firstInputAt rate z)
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)) =
        firstChoiceAt rate z := by
    calc
      firstInstalledArmChoice (x := firstInputAt rate z)
          (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)) =
          CoordinatorLocalArmChoice.coordinatorArmChoice
            (AssignmentStartPayload.Input.ofFirstAssignment (firstLaunchInputAt rate z))
            Finset.univ none z.1 (fun _ => 1) z.2 := by
              change CoordinatorLocalArmChoice.coordinatorArmChoice
                  (AssignmentStartPayload.Input.ofFirstAssignment (firstLaunchInputAt rate z))
                  Finset.univ none (firstLaunchInputAt rate z).sigma
                  (CoordinatorAssignmentRegisterInstall.installFirst
                    (firstLaunchInputAt rate z)).registers.complementWeights z.2 =
                CoordinatorLocalArmChoice.coordinatorArmChoice
                  (AssignmentStartPayload.Input.ofFirstAssignment (firstLaunchInputAt rate z))
                  Finset.univ none z.1 (fun _ => 1) z.2
              rw [hweights]
              rfl
      _ = firstChoiceAt rate z := by
        unfold firstChoiceAt firstChoiceSection firstChoiceKeyAt
        change CoordinatorLocalArmChoice.coordinatorArmChoice
            (AssignmentStartPayload.Input.ofFirstAssignment (firstLaunchInputAt rate z))
            Finset.univ none z.1
            (CoordinatorAssignmentRegisterInstall.installFirst
              (firstLaunchInputAt rate z)).registers.complementWeights z.2 =
          CoordinatorLocalArmChoice.coordinatorArmChoice
            (firstPayloadAt rate z.1 (firstSlowSetAt z))
            Finset.univ none z.1 (fun _ => 1) z.2
        rw [hweights, hpayload]
        rfl
  exact hdirect.symm.trans hchoice

/-- The actual choice-time sender view projected from the raw first outcome.
All failed outcome tags retain `none`; the actual operation's success proof
below shows those tags do not occur at this input. -/
def firstOutcomeViewAt (rate : RateInput p) (z : FirstDomain p) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  firstOutcomeView (firstOutcomeAt rate z)

theorem firstOutcomeViewAt_eq_firstChoiceViewAt (z : FirstDomain p) :
    firstOutcomeViewAt rate z = some (firstChoiceViewAt rate z) := by
  obtain ⟨installed, selected, hchosen⟩ := firstOutcomeAt_chosen z
  have hinstall := firstOutcomeAt_chosen_installation z installed selected hchosen
  have htransport := congrArg (firstInstalledChoiceView (x := firstInputAt rate z)) hinstall
  have hdirect : firstInstalledChoiceView (x := firstInputAt rate z)
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)) =
        firstChoiceViewAt rate z := by
    have hpayload := firstPayloadAt_eq_ofFirstAssignment (rate := rate) z
    change firstInstalledChoiceView (x := firstInputAt rate z)
        (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)) =
      firstChoiceViewForKey rate (firstChoiceKeyAt rate z)
    dsimp only [firstInstalledChoiceView, firstChoiceViewForKey, firstChoiceKeyAt]
    rw [hpayload]
    congr 1
  change firstOutcomeView (firstOutcomeAt rate z) =
    some (firstChoiceViewAt rate z)
  unfold firstOutcomeAt
  rw [show CoordinatorRoundDispatch.dispatchFirst (firstInputAt rate z) =
    .chosen installed selected from hchosen]
  simp only [firstOutcomeView]
  rw [hinstall, hdirect]
  rfl

theorem measurable_firstOutcomeViewAt :
    Measurable (firstOutcomeViewAt (rate := rate)) := by
  rw [show firstOutcomeViewAt (rate := rate) = fun z => some (firstChoiceViewAt rate z) from
    funext (firstOutcomeViewAt_eq_firstChoiceViewAt (rate := rate))]
  have hkey : Measurable (fun q : FirstChoiceKey p =>
      some (firstChoiceViewForKey rate q)) := measurable_of_countable _
  exact hkey.comp measurable_firstChoiceKeyAt

def firstOutcomeArmAt (rate : RateInput p) (z : FirstDomain p) : Fin p.K :=
  firstOutcomeArm (firstOutcomeAt rate z)

theorem firstOutcomeArmAt_eq_firstChoiceAt (z : FirstDomain p) :
    firstOutcomeArmAt rate z = (firstChoiceAt rate z).getD
      (ReferenceActivePhysicalStep.coordinatorFallback p) := by
  obtain ⟨installed, selected, hchosen⟩ := firstOutcomeAt_chosen z
  have harm : firstOutcomeArmAt rate z = selected.arm := by
    simpa [firstOutcomeArmAt, firstOutcomeArm] using congrArg firstOutcomeArm hchosen
  rw [harm, firstChoiceAt_eq_chosen_arm z installed selected hchosen]
  rfl

theorem measurable_firstOutcomeArmAt :
    Measurable (firstOutcomeArmAt (rate := rate)) := by
  rw [show firstOutcomeArmAt (rate := rate) = fun z =>
      (firstChoiceAt rate z).getD (ReferenceActivePhysicalStep.coordinatorFallback p) from
    funext (firstOutcomeArmAt_eq_firstChoiceAt (rate := rate))]
  exact (measurable_of_countable
    (fun o : Option (Fin p.K) => o.getD (ReferenceActivePhysicalStep.coordinatorFallback p))).comp
      measurable_firstChoiceAt

/-- Literal registers at a fixed first-choice key, with zero complement
scores. This does not sample a set or read another row. -/
def firstRegistersForKey (rate : RateInput p) (q : FirstChoiceKey p) :
    CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
  payload := firstPayloadAt rate q.1 q.2
  priorClock := {
    sigma := some q.1
    u := none
    g := FollowerCutoffScan.gridBoundary p rate.eta.val q.1
    lastProposal := none }
  pendingAtChoice := Finset.univ
  time := q.1
  gridBoundary := FollowerCutoffScan.gridBoundary p rate.eta.val q.1
  complementScores := fun _ => 0 }

theorem firstRegistersForKey_eq_actual (z : FirstDomain p) :
    firstRegistersForKey rate (firstChoiceKeyAt rate z) =
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate z)).registers := rfl

theorem measurable_firstInstalledRegistersAt :
    Measurable (fun z : FirstDomain p =>
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate z)).registers) := by
  exact (measurable_of_countable (firstRegistersForKey rate)).comp
    measurable_firstChoiceKeyAt

theorem measurable_firstStartResultAt :
    Measurable (firstStartResultAt (rate := rate)) := by
  apply measurable_of_constant_on_countable_fibers
    (fun z : FirstDomain p => z.1) measurable_fst
  intro x y htime
  unfold firstStartResultAt CoordinatorAssignmentRegisterInstall.firstStartRoundResult
  dsimp only [firstLaunchInputAt, CoordinatorRoundDispatch.firstLaunchInput, firstInputAt]
  simp only [htime]

/-- The original continuous vector is kept separately from the deterministic
time/slow-set data; its sigma algebra remains the original product Borel one. -/
theorem measurable_firstInstalledStartAt :
    Measurable (fun z : FirstDomain p =>
      (CoordinatorAssignmentRegisterInstall.installFirst
        (firstLaunchInputAt rate z)).start) := by
  apply measurable_comap_iff.mpr
  have hrest : Measurable (fun z : FirstDomain p =>
      firstStartRemainderCode (firstLaunchInputAt rate z).start) := by
    apply measurable_of_constant_on_countable_fibers
      (firstChoiceKeyAt rate) measurable_firstChoiceKeyAt
    intro x y hkey
    exact firstStartRemainderCode_eq_of_key
      (s := firstLaunchInputAt rate x) (t := firstLaunchInputAt rate y)
      (congrArg (fun q : FirstChoiceKey p => q.1) hkey)
      (congrArg (fun q : FirstChoiceKey p => q.2) hkey)
  exact measurable_fst.prodMk (measurable_firstAssignmentVector.prodMk hrest)

/-- The observation is applied to the actual dispatcher outcome. -/
def firstDispatchObservationAt (rate : RateInput p) (z : FirstDomain p) :
    FirstDispatchObservation p rate.eta := observeFirstOutcome (firstOutcomeAt rate z)

/-- Literal data normal form for the actual first dispatch. The optional arm
is the accepted choice operation on the original row, not an external input. -/
def firstDispatchDataAt (rate : RateInput p) (z : FirstDomain p) :
    FirstDispatchObservation p rate.eta := {
  tag := .chosen
  start := (CoordinatorAssignmentRegisterInstall.installFirst
    (firstLaunchInputAt rate z)).start
  startRoundResult := firstStartResultAt rate z
  registers := (CoordinatorAssignmentRegisterInstall.installFirst
    (firstLaunchInputAt rate z)).registers
  queue := fun _ => 0
  previousService := fun _ => 0
  followerBaseScore := fun _ => 0
  arm := firstChoiceAt rate z }

theorem firstDispatchObservationAt_eq_data (z : FirstDomain p) :
    firstDispatchObservationAt rate z = firstDispatchDataAt rate z := by
  classical
  obtain ⟨installed, selected, hchosen⟩ := firstOutcomeAt_chosen (rate := rate) z
  have hchoice := firstChoiceAt_eq_chosen_arm z installed selected hchosen
  have hinstall := firstOutcomeAt_chosen_installation z installed selected hchosen
  unfold firstDispatchObservationAt
  rw [hchosen]
  simp only [observeFirstOutcome, firstDispatchDataAt, hchoice]
  cases hinstall
  congr 1
  · funext a
    split <;> rfl
  · funext a
    split <;> rfl

/-- Borel measurability of every retained field, including the full original
assignment vector, original start, payload, clock, registers and chosen arm. -/
theorem measurable_firstDispatchObservationAt :
    Measurable (firstDispatchObservationAt (rate := rate)) := by
  rw [show firstDispatchObservationAt rate = firstDispatchDataAt rate from
    funext (firstDispatchObservationAt_eq_data (rate := rate))]
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (measurable_firstInstalledStartAt.prodMk
    (measurable_firstStartResultAt.prodMk (measurable_firstInstalledRegistersAt.prodMk
      (measurable_const.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_firstChoiceAt))))))

theorem firstDispatchObservationAt_tag (z : FirstDomain p) :
    (firstDispatchObservationAt rate z).tag = .chosen := by
  rw [firstDispatchObservationAt_eq_data]
  rfl

theorem firstDispatchObservationAt_coordinates (z : FirstDomain p) :
    (firstDispatchObservationAt rate z).start.coordinates =
      LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1 := by
  rw [firstDispatchObservationAt_eq_data]
  rfl

theorem firstDispatchObservationAt_payload (z : FirstDomain p) :
    (firstDispatchObservationAt rate z).registers.payload =
      firstPayloadAt rate z.1 (firstSlowSetAt (rate := rate) z) := by
  rw [firstDispatchObservationAt_eq_data]
  rfl

theorem firstDispatchObservationAt_startedClock (z : FirstDomain p) :
    (firstDispatchObservationAt rate z).startRoundResult.clock =
      firstStartedClockAt rate z := by
  rw [firstDispatchObservationAt_eq_data]
  rfl

/-- All data fields of the original installation, separated only from its two
proof fields. -/
def FirstInstallationData.ofInstallation {p : Parameters} {eta : LearningRate}
    {s : FirstAssignmentLaunch.Input p eta}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation s) :
    FirstInstallationData p eta := {
  start := installed.start
  startRoundResult := installed.startRoundResult
  registers := installed.registers
  queue := installed.ownedRegisters.queue
  previousService := installed.ownedRegisters.previousService
  followerBaseScore := installed.followerBaseScore }

/-- Restore the existing installation carrier from decoded data. The only
inputs omitted by the observation are the original start and clock proofs. -/
def FirstInstallationData.restore {p : Parameters} {eta : LearningRate}
    (s : FirstAssignmentLaunch.Input p eta) (d : FirstInstallationData p eta)
    (hstart : d.start = s.start)
    (hclock : CoordinatorPhaseClock.startRound p eta.val s.sigma
      (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok d.startRoundResult) :
    CoordinatorAssignmentRegisterInstall.FirstInstallation s := {
  start := d.start
  start_eq := hstart
  startRoundResult := d.startRoundResult
  startRound_eq := hclock
  registers := d.registers
  ownedRegisters := ⟨d.queue, d.previousService⟩
  followerBaseScore := d.followerBaseScore }

theorem FirstInstallationData.restore_ofInstallation {p : Parameters}
    {eta : LearningRate} {s : FirstAssignmentLaunch.Input p eta}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation s) :
    (FirstInstallationData.ofInstallation installed).restore s
      installed.start_eq installed.startRound_eq = installed := by
  cases installed
  rfl

/-- The data decoder recovers the complete installation data and arm from
every chosen raw outcome, including installations other than the actual one. -/
theorem decodeFirstDispatchObservation_chosen {p : Parameters}
    {x : CoordinatorRoundDispatch.FirstInput p}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput x))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights x.row) :
    decodeFirstDispatchObservation (observeFirstOutcome (.chosen installed selected)) =
      (FirstInstallationData.ofInstallation installed, some selected.arm) := by
  classical
  have hqueue : (fun j : FastArm installed.registers.payload.slowSet =>
      if ha : j.1 ∈ fastArmFinset installed.registers.payload.slowSet then
        installed.ownedRegisters.queue ⟨j.1, ha⟩ else 0) =
      installed.ownedRegisters.queue := by
    funext j
    simp only [dite_eq_left j.2]
  have hservice : (fun j : FastArm installed.registers.payload.slowSet =>
      if ha : j.1 ∈ fastArmFinset installed.registers.payload.slowSet then
        installed.ownedRegisters.previousService ⟨j.1, ha⟩ else 0) =
      installed.ownedRegisters.previousService := by
    funext j
    simp only [dite_eq_left j.2]
  dsimp only [decodeFirstDispatchObservation, observeFirstOutcome,
    FirstInstallationData.ofInstallation]
  rw [hqueue, hservice]

/-- Exact data reconstruction for this actual operation. Existence of the
chosen branch and its literal installation are proved, not supplied. -/
theorem decode_firstDispatchObservationAt (z : FirstDomain p) :
    decodeFirstDispatchObservation (firstDispatchObservationAt rate z) =
      (FirstInstallationData.ofInstallation
        (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)),
        some (firstOutcomeArmAt rate z)) := by
  obtain ⟨installed, selected, hchosen⟩ := firstOutcomeAt_chosen (rate := rate) z
  have hinstall := firstOutcomeAt_chosen_installation z installed selected hchosen
  change decodeFirstDispatchObservation (observeFirstOutcome (firstOutcomeAt rate z)) = _
  rw [hchosen, decodeFirstDispatchObservation_chosen]
  have harm : firstOutcomeArmAt rate z = selected.arm := by
    change firstOutcomeArm (firstOutcomeAt rate z) = _
    rw [hchosen]
    rfl
  exact Prod.ext (congrArg FirstInstallationData.ofInstallation hinstall)
    (congrArg some harm.symm)

/-- Proof irrelevance is the only loss when the two original installation
proof fields are omitted from the data observation. -/
theorem FirstInstallationData.restore_eq_of_data {p : Parameters}
    {eta : LearningRate} {s : FirstAssignmentLaunch.Input p eta}
    (d : FirstInstallationData p eta)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation s)
    (hdata : d = FirstInstallationData.ofInstallation installed)
    (hstart : d.start = s.start)
    (hclock : CoordinatorPhaseClock.startRound p eta.val s.sigma
      (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok d.startRoundResult) :
    d.restore s hstart hclock = installed := by
  cases hdata
  exact FirstInstallationData.restore_ofInstallation installed

/-- Exact restoration of the actual installation by the data decoder.
The omitted proof fields are supplied by proved equalities here, with no
success or reconstruction assumption on the caller. -/
theorem restore_firstDispatchObservationAt (z : FirstDomain p) :
    let d := (decodeFirstDispatchObservation (firstDispatchObservationAt rate z)).1
    ∃ (hstart : d.start = (firstLaunchInputAt rate z).start)
      (hclock : CoordinatorPhaseClock.startRound p rate.eta.val z.1
        (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok d.startRoundResult),
      d.restore (firstLaunchInputAt rate z) hstart hclock =
        CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z) := by
  let d := (decodeFirstDispatchObservation (firstDispatchObservationAt rate z)).1
  have hd : d = FirstInstallationData.ofInstallation
      (CoordinatorAssignmentRegisterInstall.installFirst (firstLaunchInputAt rate z)) :=
    congrArg Prod.fst (decode_firstDispatchObservationAt (rate := rate) z)
  have hs : d.start = (firstLaunchInputAt rate z).start := by
    rw [hd]
    rfl
  have hc : CoordinatorPhaseClock.startRound p rate.eta.val z.1
      (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok d.startRoundResult := by
    rw [hd]
    exact CoordinatorAssignmentRegisterInstall.first_start_round_success
      (firstLaunchInputAt rate z)
  exact ⟨hs, hc, FirstInstallationData.restore_eq_of_data d _ hd hs hc⟩

theorem firstChoiceAt_eq_some_actual (z : FirstDomain p) :
    firstChoiceAt rate z = some (firstOutcomeArmAt rate z) := by
  obtain ⟨installed, selected, hchosen⟩ := firstOutcomeAt_chosen (rate := rate) z
  have harm : firstOutcomeArmAt rate z = selected.arm := by
    change firstOutcomeArm (firstOutcomeAt rate z) = _
    rw [hchosen]
    rfl
  rw [harm]
  exact firstChoiceAt_eq_chosen_arm z installed selected hchosen

/-- The canonical same-round selection built from the proved local first
operation. Its dependent row is exactly `x.rows x.selected`. -/
def firstSelectionAt (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalStep.Selection x := {
  view := firstChoiceViewAt rate (x.time, x.row)
  started := firstStartResultAt rate (x.time, x.row)
  pending_eq := rfl
  cutoff_eq := rfl
  arm := firstOutcomeArmAt rate (x.time, x.row)
  choice_eq := firstChoiceAt_eq_some_actual (rate := rate) (x.time, x.row) }

private theorem selection_ext {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (left right : ReferenceActivePhysicalStep.Selection x)
    (hview : left.view = right.view) (hstarted : left.started = right.started)
    (harm : left.arm = right.arm) : left = right := by
  cases left
  cases right
  cases hview
  cases hstarted
  cases harm
  rfl

/-- Pointwise transfer to the existing physical step for every original
round input whose coordinator is first. No topology or measurable-space
structure is supplied for that round input or its state. -/
theorem dispatch_first_selection (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    (ReferenceActivePhysicalStep.dispatch x).selection = some (firstSelectionAt x) := by
  classical
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  change (ReferenceActivePhysicalStep.DispatchCut.first
    (firstOutcomeAt rate (x.time, x.row))).selection = _
  obtain ⟨installed, selected, hchosen⟩ :=
    firstOutcomeAt_chosen (rate := rate) (x.time, x.row)
  have hinstall := firstOutcomeAt_chosen_installation
    (x.time, x.row) installed selected hchosen
  have htime : installed.registers.time = x.time := by
    rw [hinstall]
    rfl
  have hview : firstInstalledChoiceView (x := firstInputAt rate (x.time, x.row))
      installed = firstChoiceViewAt rate (x.time, x.row) := by
    have h := firstOutcomeViewAt_eq_firstChoiceViewAt (rate := rate) (x.time, x.row)
    change firstOutcomeView (firstOutcomeAt rate (x.time, x.row)) = _ at h
    rw [hchosen] at h
    exact Option.some.inj h
  have hstarted : installed.startRoundResult =
      firstStartResultAt rate (x.time, x.row) := by
    rw [hinstall]
    rfl
  have harm : selected.arm = firstOutcomeArmAt rate (x.time, x.row) := by
    change _ = firstOutcomeArm (firstOutcomeAt rate (x.time, x.row))
    rw [hchosen]
    rfl
  rw [hchosen]
  simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime]
  congr 1
  exact selection_ext _ _ hview hstarted harm

theorem dispatch_first_downView (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    (ReferenceActivePhysicalStep.dispatch x).downView =
      firstOutcomeViewAt rate (x.time, x.row) := by
  rw [ReferenceActivePhysicalStep.DispatchCut.downView, dispatch_first_selection x hfirst,
    firstOutcomeViewAt_eq_firstChoiceViewAt]
  rfl

theorem dispatch_first_arm (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    (ReferenceActivePhysicalStep.dispatch x).arm =
      firstOutcomeArmAt rate (x.time, x.row) := by
  rw [ReferenceActivePhysicalStep.DispatchCut.arm, dispatch_first_selection x hfirst]
  rfl

/-- The started clock projected from the actual canonical selection is the
literal first clock, including its original clipped grid boundary. -/
theorem dispatch_first_startedClock (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    (ReferenceActivePhysicalStep.dispatch x).selection.map
      (fun selected => selected.started.clock) =
        some (firstStartedClockAt rate (x.time, x.row)) := by
  rw [dispatch_first_selection x hfirst]
  rfl

end Bandits.Support.ReferenceFirstDispatchMeasurability

end
