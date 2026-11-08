/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteCoordinatorOwnHistory
public import Bandits.Support.PlayerPrivateSampledProduct

/-!
# Actual coordinator readouts from its sampled private input

This file factors the existing coordinator initialization and ordinary local
readouts through the sampled coordinator input. The sampled input retains the
selected row, the complete block-target arm stream, and every original
calendar-round scalar. It is a deterministic factor of the original private
input; it asserts no measurability factorization, policy law, model membership,
or regret claim.

Sources, relative to `sources/zip4/manuscript/`: `01_introduction.tex:18-36`,
`07_public_setup.tex:27-38,55-114`,
`appendix_b_communication.tex:94-131`, and
`06_interruptions.tex:240-296`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open scoped Classical

namespace Bandits.Support.ActualCoordinatorSampledPrivateReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev GridRewardTable := ActualCompleteCoordinatorOwnHistory.GridRewardTable
abbrev OwnCoordinates := ActualInitializationCoordinatorOwnHistory.OwnCoordinates

/-- The exact sampled coordinator branch of the existing role-tagged input. -/
abbrev SampledCoordinatorInput (p : Parameters) :=
  Fin (M p) ×
    (BootstrapPrivateRoundStreams.CoordinatorTargetArms p ×
      BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)

abbrev GridHistory := ActualCompleteCoordinatorOwnHistory.GridHistory

variable {p : Parameters}
variable {rate : RateInput p}

/-- Begin the existing local block with an already sampled finite target arm.
All original row, IDs, monitor, constants, and reset operations are retained. -/
def beginTarget (block : Fin (n_boot p)) (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p) (carried : BootstrapPhysicalBlock.State p)
    (monitor : BootstrapCoordinatorLocalRound.UnlaunchedMonitor p)
    (a b : ℝ) (target : Fin p.K) : BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  ⟨⟨block, row, ids, target,
      BootstrapCoordinatorLocalRound.resetCoordinatorBlockState p carried, a, b⟩,
    monitor⟩

/-- Replacing the original target scalar by its prescribed sampled arm is
exactly the existing block-start operation. -/
theorem beginTarget_coordinatorTargetDraw (block : Fin (n_boot p))
    (row : CompletePublicTable.CompleteRow p) (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : BootstrapCoordinatorLocalRound.UnlaunchedMonitor p)
    (a b : ℝ) (v : PrivateSourceStreams.Scalar) :
    beginTarget block row ids carried monitor a b
        (BootstrapPrivateRoundStreams.coordinatorTargetDraw p v) =
      BootstrapCoordinatorLocalRound.beginBlock p block row ids carried monitor a b v := rfl

/-- Move to the supplied sampled target only at an actual calendar boundary.
The same-block branch preserves the complete carried prelaunch block. -/
def sampledAtRound (sampled : SampledCoordinatorInput p) (t : Fin p.T)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  if t ∈ calendarBlock p live.data.block then live
  else beginTarget (roundBlockIndex p t) live.data.row live.data.ids
    live.data.coordinator live.monitor live.data.C_star live.data.C_h
    (sampled.2.1 (roundBlockIndex p t))

/-- The sampled local block is the one containing the actual round. -/
theorem sampledAtRound_mem (sampled : SampledCoordinatorInput p) (t : Fin p.T)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    t ∈ calendarBlock p (sampledAtRound sampled t live).data.block := by
  unfold sampledAtRound
  split
  · assumption
  · exact BootstrapDimensions.round_mem_quotient_block p t

private theorem sampledAtRound_factor (raw : OwnCoordinates p) (t : Fin p.T)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    sampledAtRound (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) t live =
      ActualInitializationCoordinatorOwnHistory.atRound raw t live := by
  unfold sampledAtRound ActualInitializationCoordinatorOwnHistory.atRound
  by_cases hmem : t ∈ calendarBlock p live.data.block
  · simp only [ite_eq_left hmem]
  · simp only [ite_eq_right hmem, PlayerPrivateSampledProduct.sampleCoordinatorRawInput,
      BootstrapPrivateRoundStreams.coordinatorTargetArmMap]
    rfl

private theorem sampledPrepare_factor (raw : OwnCoordinates p) (t : Fin p.T)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    BootstrapCoordinatorLocalRound.prepare p
        (sampledAtRound (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) t live)
        t (sampledAtRound_mem (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) t live)
        ((PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw).2.2 t) =
      BootstrapCoordinatorLocalRound.prepare p
        (ActualInitializationCoordinatorOwnHistory.atRound raw t live) t
        (ActualInitializationCoordinatorOwnHistory.atRound_mem raw t live)
        (raw.2.1 t) := by
  have hAt := sampledAtRound_factor raw t live
  cases hAt
  have hmem :
      sampledAtRound_mem (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) t live =
        ActualInitializationCoordinatorOwnHistory.atRound_mem raw t live :=
    Subsingleton.elim _ _
  rw [hmem]
  rfl

/-- The source's original block-start target scalar is read only through its
already sampled arm in this readout. -/
def sampledInitial (published : CompletePublicTable.PublishedOutput p)
    (sampled : SampledCoordinatorInput p) (a b : ℝ) :
    BootstrapCoordinatorLocalRound.Continuation p :=
  .prelaunch (beginTarget (ActualInitializationRun.firstBlock p)
    (published.2 sampled.1) published.1 (BootstrapPhysicalBlock.initialState p)
    (ActualInitializationRun.initialUnlaunchedMonitor p) a b
    (sampled.2.1 (ActualInitializationRun.firstBlock p)))

private theorem sampledInitial_factor (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) (a b : ℝ) :
    sampledInitial published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) a b =
      ActualInitializationCoordinatorOwnHistory.replayInitial published raw a b := by
  simp [sampledInitial, ActualInitializationCoordinatorOwnHistory.replayInitial,
    PlayerPrivateSampledProduct.sampleCoordinatorRawInput,
    BootstrapPrivateRoundStreams.coordinatorTargetArmMap, beginTarget,
    BootstrapCoordinatorLocalRound.beginBlock]

/-- One finite own-feedback step on the existing initialization continuation.
Once launched, this initialization readout remains absorbing. -/
def sampledStep (sampled : SampledCoordinatorInput p) (t : Fin p.T)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) (y : Fin (D p + 1)) :
    BootstrapCoordinatorLocalRound.Continuation p :=
  match phase with
  | .launched launch => .launched launch
  | .prelaunch live =>
      (BootstrapCoordinatorLocalRound.observe
        (BootstrapCoordinatorLocalRound.prepare p (sampledAtRound sampled t live) t
          (sampledAtRound_mem sampled t live) (sampled.2.2 t)) y).next

private theorem sampledStep_factor (raw : OwnCoordinates p) (t : Fin p.T)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) (y : Fin (D p + 1)) :
    sampledStep (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) t phase y =
      ActualInitializationCoordinatorOwnHistory.replayStep raw t phase y := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      simp only [sampledStep, ActualInitializationCoordinatorOwnHistory.replayStep]
      rw [sampledPrepare_factor]

/-- The continuation after exactly the supplied finite feedback prefix. -/
def sampledRaw (published : CompletePublicTable.PublishedOutput p)
    (sampled : SampledCoordinatorInput p) (a b : ℝ) :
    (n : ℕ) → n ≤ p.T → (Fin n → Fin (D p + 1)) →
      BootstrapCoordinatorLocalRound.Continuation p
  | 0, _, _ => sampledInitial published sampled a b
  | n + 1, hn, feedback =>
      sampledStep sampled ⟨n, by omega⟩
        (sampledRaw published sampled a b n (by omega)
          (fun j => feedback j.castSucc))
        (feedback (Fin.last n))

/-- The initialization recursion factors through the sampled input for every
supplied feedback prefix, including prefixes ending at `T`. -/
theorem sampledRaw_factor (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) :
    sampledRaw published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
        a b n hn feedback =
      ActualInitializationCoordinatorOwnHistory.replayRaw published raw a b n hn feedback := by
  induction n with
  | zero =>
      simp only [sampledRaw, ActualInitializationCoordinatorOwnHistory.replayRaw]
      exact sampledInitial_factor published raw a b
  | succ n ih =>
      change sampledStep (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
          ⟨n, by omega⟩
          (sampledRaw published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
            a b n (by omega) (fun j => feedback j.castSucc))
          (feedback (Fin.last n)) =
        ActualInitializationCoordinatorOwnHistory.replayStep raw ⟨n, by omega⟩
          (ActualInitializationCoordinatorOwnHistory.replayRaw published raw a b n (by omega)
            (fun j => feedback j.castSucc))
          (feedback (Fin.last n))
      rw [ih (by omega) (fun j => feedback j.castSucc)]
      exact sampledStep_factor raw ⟨n, by omega⟩ _ _

/-- Prepare the existing continuation at a finite position. At the terminal
position `T`, preserve the actual terminal continuation unchanged. -/
def sampledAtPosition (sampled : SampledCoordinatorInput p) (n : ℕ)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    BootstrapCoordinatorLocalRound.Continuation p :=
  match phase with
  | .launched launch => .launched launch
  | .prelaunch live =>
      if hn : n < p.T then .prelaunch (sampledAtRound sampled ⟨n, hn⟩ live)
      else .prelaunch live

/-- The local continuation at the next choice, or the actual continuation at
`T` when the horizon has ended. -/
def sampledInit (published : CompletePublicTable.PublishedOutput p)
    (sampled : SampledCoordinatorInput p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) : BootstrapCoordinatorLocalRound.Continuation p :=
  sampledAtPosition sampled n (sampledRaw published sampled a b n hn feedback)

/-- Positioning the sampled prefix is exactly the existing initialization
positioning, including its terminal branch. -/
theorem sampledInit_factor (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) :
    sampledInit published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
        a b n hn feedback =
      ActualInitializationCoordinatorOwnHistory.initializationReplay
        published raw a b n hn feedback := by
  unfold sampledInit ActualInitializationCoordinatorOwnHistory.initializationReplay
  rw [sampledRaw_factor]
  cases hphase : ActualInitializationCoordinatorOwnHistory.replayRaw
      published raw a b n hn feedback with
  | prelaunch live =>
      by_cases htime : n < p.T
      · simp [sampledAtPosition, ActualInitializationCoordinatorOwnHistory.atPosition,
          htime, sampledAtRound_factor]
      · simp [sampledAtPosition, ActualInitializationCoordinatorOwnHistory.atPosition,
          htime]
  | launched launch =>
      simp [sampledAtPosition, ActualInitializationCoordinatorOwnHistory.atPosition]

/-- One ordinary observation uses the selected whole row and retains both the
updated ordinary configuration and the updated UP decoder bank. -/
def sampledOrdinaryStep (published : CompletePublicTable.PublishedOutput p)
    (sampled : SampledCoordinatorInput p) (t : Fin p.T)
    (code : ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate)
    (y : Fin (D p + 1)) : ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate :=
  let observed := OrdinaryCoordinatorObservationMeasurability.observeLocalCode
    ((code.1, (code.2, (published.2 sampled.1, t))), y)
  (observed.1, observed.2.1)

private theorem selectedRow_eq_sampledInput (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) :
    published.2 (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw).1 =
      ActualCompleteCoordinatorOwnHistory.selectedRow published raw := rfl

private theorem sampledOrdinaryStep_factor (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) (t : Fin p.T)
    (code : ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate)
    (y : Fin (D p + 1)) :
    sampledOrdinaryStep published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
        t code y =
      ActualCompleteCoordinatorOwnHistory.ordinaryCodeStep published raw t code y := by
  simp [sampledOrdinaryStep, ActualCompleteCoordinatorOwnHistory.ordinaryCodeStep,
    selectedRow_eq_sampledInput]

/-- The ordinary-code recursion holds the original initial code before launch,
then composes the existing complete observation at each actual round. -/
def sampledOrdinary (rate : RateInput p) (published : CompletePublicTable.PublishedOutput p)
    (sampled : SampledCoordinatorInput p) (a b : ℝ) :
    (n : ℕ) → n ≤ p.T → (Fin n → Fin (D p + 1)) →
      ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate
  | 0, _, _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
  | n + 1, hn, feedback =>
      match sampledInit published sampled a b n (by omega)
          (fun j => feedback j.castSucc) with
      | .prelaunch _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
      | .launched _ =>
          sampledOrdinaryStep published sampled ⟨n, by omega⟩
            (sampledOrdinary rate published sampled a b n (by omega)
              (fun j => feedback j.castSucc))
            (feedback (Fin.last n))

/-- The ordinary-code readout is exactly the existing recursion at the
sampled original input. -/
theorem sampledOrdinary_factor (rate : RateInput p)
    (published : CompletePublicTable.PublishedOutput p) (raw : OwnCoordinates p)
    (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) (feedback : Fin n → Fin (D p + 1)) :
    sampledOrdinary rate published (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw)
        a b n hn feedback =
      ActualCompleteCoordinatorOwnHistory.ordinaryReplayCode rate published raw a b n hn feedback := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (match sampledInit published
          (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) a b n (by omega)
          (fun j => feedback j.castSucc) with
        | .prelaunch _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
        | .launched _ =>
            sampledOrdinaryStep published
              (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) ⟨n, by omega⟩
              (sampledOrdinary rate published
                (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw) a b n (by omega)
                (fun j => feedback j.castSucc)) (feedback (Fin.last n)) ) =
        (match ActualInitializationCoordinatorOwnHistory.initializationReplay published raw a b n
            (by omega) (fun j => feedback j.castSucc) with
        | .prelaunch _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
        | .launched _ =>
            ActualCompleteCoordinatorOwnHistory.ordinaryCodeStep published raw ⟨n, by omega⟩
              (ActualCompleteCoordinatorOwnHistory.ordinaryReplayCode rate published raw a b n
                (by omega) (fun j => feedback j.castSucc)) (feedback (Fin.last n)))
      rw [sampledInit_factor]
      cases hphase : ActualInitializationCoordinatorOwnHistory.initializationReplay
          published raw a b n (by omega) (fun j => feedback j.castSucc) with
      | prelaunch live => simp
      | launched launch =>
          rw [ih (by omega) (fun j => feedback j.castSucc)]
          exact sampledOrdinaryStep_factor published raw ⟨n, by omega⟩ _ _

/-- Exact existing coordinator storage read from a sampled input and finite
grid history. Earlier supplied arms are ignored; only feedback is consumed. -/
def sampledGridReplay (rate : RateInput p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × GridHistory p n)) :
    ActualCompleteCoordinatorOwnHistory.CoordinatorStorage p rate :=
  match sampledInit x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2) with
  | .prelaunch live => .inl live
  | .launched _ =>
      .inr (ActualCompleteCoordinatorOwnHistory.decodeOrdinary
        (sampledOrdinary rate x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)))

/-- The phase code and ordinary code, on the same original continuous base. -/
def sampledGridReplayCode (rate : RateInput p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × GridHistory p n)) :
    ActualInitializationBlockMeasurability.ContinuationCode p ×
      ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate :=
  (ActualInitializationBlockMeasurability.continuationCodeOf
      (sampledInit x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)),
    sampledOrdinary rate x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2))

/-- The current actual coordinator arm. Its initialization branch is prepared
at this round; its ordinary branch uses the same selected row and time. -/
def sampledGridDecision (rate : RateInput p) (a b : ℝ) (t : Fin p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × GridHistory p t.val)) : Fin p.K :=
  match sampledInit x.1 x.2.1 a b t.val t.isLt.le (fun j => (x.2.2 j).2) with
  | .prelaunch live =>
      (BootstrapCoordinatorLocalRound.prepare p (sampledAtRound x.2.1 t live) t
        (sampledAtRound_mem x.2.1 t live) (x.2.1.2.2 t)).arm
  | .launched _ =>
      let storage := ActualCompleteCoordinatorOwnHistory.decodeOrdinary
        (sampledOrdinary rate x.1 x.2.1 a b t.val t.isLt.le
          (fun j => (x.2.2 j).2))
      (OrdinaryCoordinatorPhysicalInterface.prepareLocal storage.1 storage.2
        (x.1.2 x.2.1.1) t).arm

/-- Factoring sampled storage through the original sampled input reproduces
the complete existing coordinator replay for every finite grid history. -/
theorem sampledGridReplay_raw_eq (rate : RateInput p)
    (published : CompletePublicTable.PublishedOutput p) (raw : OwnCoordinates p)
    (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) (history : GridHistory p n) :
    sampledGridReplay rate a b n hn
        (published, (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw, history)) =
      ActualCompleteCoordinatorOwnHistory.coordinatorGridReplay rate published raw a b n hn history := by
  unfold sampledGridReplay ActualCompleteCoordinatorOwnHistory.coordinatorGridReplay
    ActualCompleteCoordinatorOwnHistory.replayFeedback
  rw [sampledInit_factor]
  cases hphase : ActualInitializationCoordinatorOwnHistory.initializationReplay
      published raw a b n hn (fun j => (history j).2) with
  | prelaunch live => rfl
  | launched launch =>
      rw [sampledOrdinary_factor]

/-- Factoring the code readout reproduces the existing code at the same
published output, original raw input, constants, and history. -/
theorem sampledGridReplayCode_raw_eq (rate : RateInput p)
    (published : CompletePublicTable.PublishedOutput p) (raw : OwnCoordinates p)
    (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) (history : GridHistory p n) :
    sampledGridReplayCode rate a b n hn
        (published, (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw, history)) =
      ActualCompleteCoordinatorOwnHistory.coordinatorGridReplayCode rate a b n hn
        (published, (raw, history)) := by
  unfold sampledGridReplayCode ActualCompleteCoordinatorOwnHistory.coordinatorGridReplayCode
    ActualInitializationCoordinatorOwnHistory.initializationReplayCode
  rw [sampledInit_factor, sampledOrdinary_factor]

private theorem selectedRow_eq_sampled (published : CompletePublicTable.PublishedOutput p)
    (raw : OwnCoordinates p) :
    ActualCompleteCoordinatorOwnHistory.selectedRow published raw =
      published.2 (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p raw).1 := rfl

/-- Factoring the current action through the sampled input reproduces the
existing finite-horizon coordinator decision for every finite grid history. -/
theorem sampledGridDecision_raw_eq (rate : RateInput p)
    (a b : ℝ) (t : Fin p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (OwnCoordinates p × GridHistory p t.val)) :
    sampledGridDecision rate a b t
        (x.1, (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p x.2.1, x.2.2)) =
      ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision rate a b t x := by
  unfold sampledGridDecision ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision
    ActualCompleteCoordinatorOwnHistory.decisionFeedback
  rw [sampledInit_factor, sampledOrdinary_factor]
  cases hphase : ActualInitializationCoordinatorOwnHistory.initializationReplay
      x.1 x.2.1 a b t.val t.isLt.le (fun j => (x.2.2 j).2) with
  | prelaunch live =>
      simp only [ActualInitializationCoordinatorOwnHistory.initializationPreparedRound, hphase]
      rw [sampledPrepare_factor]
  | launched launch =>
      simp only [ActualInitializationCoordinatorOwnHistory.initializationPreparedRound, hphase]
      rw [selectedRow_eq_sampled]

/-- Two sampled histories with the same public output, sampled private input,
and own feedback have the same storage readout. Arm entries are not inputs to
the replay recursion. -/
theorem sampledGridReplay_feedback_congr (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T)
    (published published' : CompletePublicTable.PublishedOutput p)
    (sampled sampled' : SampledCoordinatorInput p)
    (history history' : GridHistory p n)
    (hpublic : published = published') (hsampled : sampled = sampled')
    (hfeedback : ∀ j, (history j).2 = (history' j).2) :
    sampledGridReplay rate a b n hn (published, (sampled, history)) =
      sampledGridReplay rate a b n hn (published', (sampled', history')) := by
  cases hpublic
  cases hsampled
  have hy : (fun j => (history j).2) = fun j => (history' j).2 := funext hfeedback
  unfold sampledGridReplay
  rw [hy]

/-- The same sampled-input and feedback equality identifies the current arm,
independently of the arbitrary earlier arm entries in the supplied history. -/
theorem sampledGridDecision_feedback_congr (rate : RateInput p) (a b : ℝ)
    (t : Fin p.T)
    (published published' : CompletePublicTable.PublishedOutput p)
    (sampled sampled' : SampledCoordinatorInput p)
    (history history' : GridHistory p t.val)
    (hpublic : published = published') (hsampled : sampled = sampled')
    (hfeedback : ∀ j, (history j).2 = (history' j).2) :
    sampledGridDecision rate a b t (published, (sampled, history)) =
      sampledGridDecision rate a b t (published', (sampled', history')) := by
  cases hpublic
  cases hsampled
  have hy : (fun j => (history j).2) = fun j => (history' j).2 := funext hfeedback
  unfold sampledGridDecision
  rw [hy]

/-- The original source's complete sampled coordinator input is precisely the
left branch of its existing role-tagged private input. -/
theorem sampledCoordinatorInput_source_eq (source : SourceInput p) :
    Sum.inl (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source)) =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
        (ActiveRoundActions.coordinator p.two_le_m) source := by
  have hcoordinator : ActiveRoundActions.coordinator p.two_le_m =
      ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m⟩ := by
    apply Fin.ext
    rfl
  simp only [PlayerPrivateSampledProduct.sampleCoordinatorRawInput,
    ActualInitializationCoordinatorOwnHistory.ownCoordinates]
  rw [hcoordinator, BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_coordinator]
  simp [
    BootstrapPrivateRoundStreams.sourceCoordinatorIndex,
    BootstrapPrivateRoundStreams.sourceCoordinatorTargetArms]
  funext t
  rfl

private theorem sourceOwnArms_length (rate : RateInput p) (source : SourceInput p)
    (rewards : GridRewardTable p) (a b : ℝ) :
    (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b).length = p.T := by
  dsimp only [ActualCompleteCoordinatorOwnHistory.sourceOwnArms,
    ActualCompleteCoordinatorOwnHistory.actualHistory]
  exact (List.length_map _).trans
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
      p rate source rewards a b).2.1

/-- On each actual round, the sampled decision is the coordinator's literal
own arm entry, with its horizon length supplied by the actual history theorem. -/
theorem sourceInitialized_sampledGridDecision (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (a b : ℝ)
    (t : Fin p.T) :
    sampledGridDecision rate a b t
        (source.1,
          (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
            (ActualInitializationCoordinatorOwnHistory.ownCoordinates source),
            ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b
              t.val t.isLt.le)) =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b)[t.val]'(
        by rw [sourceOwnArms_length rate source rewards a b]; exact t.isLt) := by
  calc
    _ = ActualCompleteCoordinatorOwnHistory.coordinatorGridDecision rate a b t
        (source.1,
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
            ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b
              t.val t.isLt.le)) :=
      sampledGridDecision_raw_eq rate a b t
        (source.1,
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
            ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b
              t.val t.isLt.le))
    _ = (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b)[t.val]'(
        by rw [sourceOwnArms_length rate source rewards a b]; exact t.isLt) := by
      simpa only [ActualCompleteCoordinatorOwnHistory.sourceOwnArms] using
        ActualCompleteCoordinatorOwnHistory.sourceInitialized_coordinatorGridDecision
          rate source rewards a b t

/-- The produced source feedback prefix is determined by the take-n list of
actual own grid feedback. -/
private theorem sourceFeedbackPrefix_eq_of_take (rate : RateInput p)
    (source other : SourceInput p) (rewards otherRewards : GridRewardTable p)
    (a b : ℝ) (n k : ℕ) (hn : n ≤ p.T) (hkn : k ≤ n)
    (hpast : (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback
        rate source rewards a b).take n =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback
        rate other otherRewards a b).take n) :
    ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix
        rate source rewards a b k (by omega) =
      ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix
        rate other otherRewards a b k (by omega) := by
  apply List.ofFn_injective
  rw [ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list,
    ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list]
  simpa only [List.take_take, Nat.min_eq_left hkn,
    ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback,
    ActualCompleteCoordinatorOwnHistory.actualHistory] using
      congrArg (List.take k) hpast

/-- A current actual arm follows from the sampled input and the actual strict
own-feedback prefix. -/
private theorem sourceOwnArm_get_eq (rate : RateInput p)
    (source other : SourceInput p) (rewards otherRewards : GridRewardTable p)
    (a b : ℝ) (t : Fin p.T)
    (hpublic : source.1 = other.1)
    (hsampled : PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) =
      PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
    (hfeedback : ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix
        rate source rewards a b t.val t.isLt.le =
      ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix
        rate other otherRewards a b t.val t.isLt.le) :
    (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b)[t.val]'(
      by rw [sourceOwnArms_length rate source rewards a b]; exact t.isLt) =
    (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other otherRewards a b)[t.val]'(
      by rw [sourceOwnArms_length rate other otherRewards a b]; exact t.isLt) := by
  have hdecision := sampledGridDecision_feedback_congr rate a b t
    source.1 other.1
    (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source))
    (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
    (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b
      t.val t.isLt.le)
    (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate other otherRewards a b
      t.val t.isLt.le)
    hpublic hsampled (by intro j; exact congrFun hfeedback j)
  have hleft := sourceInitialized_sampledGridDecision rate source rewards a b t
  have hright := sourceInitialized_sampledGridDecision rate other otherRewards a b t
  rw [hleft, hright] at hdecision
  exact hdecision

/-- On every original source, the sampled replay returns C's accepted actual
before-storage readout, including the actual terminal continuation at `T`. -/
theorem sourceInitialized_sampledGridReplay (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    sampledGridReplay rate a b n hn
        (source.1,
          (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
            (ActualInitializationCoordinatorOwnHistory.ownCoordinates source),
            ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b n hn)) =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source rewards a b n hn := by
  calc
    _ = ActualCompleteCoordinatorOwnHistory.coordinatorGridReplay rate source.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
        (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b n hn) :=
      sampledGridReplay_raw_eq rate source.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
        (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b n hn)
    _ = ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source rewards a b n hn :=
      ActualCompleteCoordinatorOwnHistory.sourceInitialized_coordinatorGridReplay
        rate source rewards a b n hn

/-- Two arbitrary original sources have equal actual coordinator storage and
own arms from only public output, the existing role-correct sampled private
input, and the take-n actual own grid-feedback list. -/
theorem sourceInitialized_sampledPrivate_own_history (rate : RateInput p)
    (source other : SourceInput p) (rewards otherRewards : GridRewardTable p)
    (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1)
    (hprivate : BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
        (ActiveRoundActions.coordinator p.two_le_m) source =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
        (ActiveRoundActions.coordinator p.two_le_m) other)
    (hpast : (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback
        rate source rewards a b).take n =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnFeedback
        rate other otherRewards a b).take n) :
    ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source rewards a b n hn =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate other otherRewards a b n hn ∧
    (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b).take n =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other otherRewards a b).take n ∧
    ∀ ht : n < p.T,
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b)[n]'(
        by rw [sourceOwnArms_length rate source rewards a b]; exact ht) =
        (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other otherRewards a b)[n]'(
          by rw [sourceOwnArms_length rate other otherRewards a b]; exact ht) ∧
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b).take (n + 1) =
        (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other otherRewards a b).take (n + 1) := by
  have htagLeft := sampledCoordinatorInput_source_eq (p := p) source
  have htagRight := sampledCoordinatorInput_source_eq (p := p) other
  have hsampled : PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) =
    PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates other) :=
    Sum.inl.inj (htagLeft.trans (hprivate.trans htagRight.symm))
  have hfeedback := sourceFeedbackPrefix_eq_of_take rate source other rewards otherRewards
    a b n n hn le_rfl hpast
  have hstorage := sampledGridReplay_feedback_congr rate a b n hn
    source.1 other.1
    (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source))
    (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
    (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate source rewards a b n hn)
    (ActualCompleteCoordinatorOwnHistory.sourceGridHistory rate other otherRewards a b n hn)
    hpublic hsampled (by intro j; exact congrFun hfeedback j)
  have hsourceLeft := sourceInitialized_sampledGridReplay rate source rewards a b n hn
  have hsourceRight := sourceInitialized_sampledGridReplay rate other otherRewards a b n hn
  have hArmsLengthLeft := sourceOwnArms_length rate source rewards a b
  have hArmsLengthRight := sourceOwnArms_length rate other otherRewards a b
  have htake :
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source rewards a b).take n =
        (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other otherRewards a b).take n := by
    apply List.ext_getElem
    · simp only [List.length_take, hArmsLengthLeft, hArmsLengthRight]
    · intro j hj _
      have hjn : j < n := by
        have hj' : j < min n p.T := by simpa only [List.length_take, hArmsLengthLeft] using hj
        omega
      have hprefix := sourceFeedbackPrefix_eq_of_take rate source other rewards otherRewards
        a b n j hn (by omega) hpast
      have harm := sourceOwnArm_get_eq rate source other rewards otherRewards a b
        ⟨j, lt_of_lt_of_le hjn hn⟩ hpublic hsampled hprefix
      simpa only [List.getElem_take] using harm
  refine ⟨hsourceLeft.symm.trans (hstorage.trans hsourceRight), htake, ?_⟩
  intro ht
  have hcurrent := sourceOwnArm_get_eq rate source other rewards otherRewards a b
    ⟨n, ht⟩ hpublic hsampled hfeedback
  refine ⟨hcurrent, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_take, hArmsLengthLeft, hArmsLengthRight]
  · intro j hj _
    have hjle : j ≤ n := by
      have hj' : j < min (n + 1) p.T := by
        simpa only [List.length_take, hArmsLengthLeft] using hj
      omega
    by_cases hlast : j = n
    · subst j
      simpa only [List.getElem_take] using hcurrent
    · have hjn : j < n := by omega
      have hprefix := sourceFeedbackPrefix_eq_of_take rate source other rewards otherRewards
        a b n j hn (by omega) hpast
      have hentry := sourceOwnArm_get_eq rate source other rewards otherRewards a b
        ⟨j, lt_of_lt_of_le hjn hn⟩ hpublic hsampled hprefix
      simpa only [List.getElem_take] using hentry

end Bandits.Support.ActualCoordinatorSampledPrivateReplay

end
