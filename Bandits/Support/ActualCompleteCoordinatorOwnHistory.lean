/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationCoordinatorOwnHistory

/-!
# The actual complete coordinator from its own finite grid history

The initialization replay supplies the phase and the launch cut. After that
cut, the recursion below calls the existing ordinary local preparation and
whole observation, retaining both configuration and UP decoder bank. These
are local readouts of the existing storages, not another physical execution.

Sources, relative to `sources/zip4/manuscript/`:
`01_introduction.tex:18-36`, `07_public_setup.tex:55-114`,
`appendix_b_communication.tex:94-131`, `06_interruptions.tex:240-296`, and
`appendix_a_local_protocol.tex:6-14,28-79`.

The named consumer is the complete finite-grid actual local-policy
representation, after exact acceptance of the separate follower locality,
bounded-history, and player-private-product producers. The results here do
not assert an all-natural-time real-history policy, a private product law,
or regret.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open scoped Classical

namespace Bandits.Support.ActualCompleteCoordinatorOwnHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev OwnCoordinates := ActualInitializationCoordinatorOwnHistory.OwnCoordinates
abbrev Configuration (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStep.CoordinatorConfiguration p rate
abbrev Bank (p : Parameters) := CoordinatorUpReception.UpDecoderBank p
abbrev OrdinaryStorage (p : Parameters) (rate : RateInput p) := Configuration p rate × Bank p
abbrev OrdinaryCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate × Bank p

/-- The phase-tagged readout retains the entire existing local storage.
The ordinary alternative contains both configuration and decoder bank. -/
abbrev CoordinatorStorage (p : Parameters) (rate : RateInput p) :=
  PrelaunchBlock p ⊕ OrdinaryStorage p rate

/-- The published output and original private coordinates are never quotiented. -/
abbrev FeedbackInput (p : Parameters) (n : ℕ) :=
  CompletePublicTable.PublishedOutput p × (OwnCoordinates p × (Fin n → Fin (D p + 1)))

abbrev GridHistory (p : Parameters) (n : ℕ) := Fin n → (Fin p.K × Fin (D p + 1))
abbrev GridInput (p : Parameters) (n : ℕ) :=
  CompletePublicTable.PublishedOutput p × (OwnCoordinates p × GridHistory p n)

variable {p : Parameters} {rate : RateInput p}

local instance localCodeDiscrete : DiscreteMeasurableSpace
    (BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) := ⟨fun _ => trivial⟩

local instance optionDiscrete {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    DiscreteMeasurableSpace (Option A) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit A
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

def initialOrdinaryCode (rate : RateInput p) : OrdinaryCode p rate :=
  (ReferenceActivePhysicalStepMeasurability.encodeCoordinator .first, CoordinatorUpReception.initialUpDecoderBank p)

def decodeOrdinary (code : OrdinaryCode p rate) : OrdinaryStorage p rate :=
  (ReferenceActivePhysicalStepMeasurability.decodeCoordinator code.1, code.2)

def selectedRow (published : CompletePublicTable.PublishedOutput p) (own : OwnCoordinates p) :
    CompletePublicTable.CompleteRow p :=
  published.2 (PrivateSourceStreams.coordinatorIndex p own.1)

/-- Every ordinary step uses the original selected complete row and the
actual calendar time. The observer's two storage projections are retained. -/
def ordinaryCodeStep (published : CompletePublicTable.PublishedOutput p) (own : OwnCoordinates p)
    (t : Fin p.T) (code : OrdinaryCode p rate) (y : Fin (D p + 1)) : OrdinaryCode p rate :=
  let observed := OrdinaryCoordinatorObservationMeasurability.observeLocalCode ((code.1, (code.2, (selectedRow
    published own, t))), y)
  (observed.1, observed.2.1)

theorem decode_ordinaryCodeStep (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (t : Fin p.T) (code : OrdinaryCode p rate) (y : Fin (D p + 1)) :
    decodeOrdinary (ordinaryCodeStep published own t code y) =
      let observed := OrdinaryCoordinatorPhysicalInterface.observeLocal
        (OrdinaryCoordinatorPhysicalInterface.prepareLocal (decodeOrdinary code).1 (decodeOrdinary code).2
          (selectedRow published own) t) y
      (observed.configuration, observed.upDecoderBank) := by
  exact congrArg (fun observed : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
    (observed.configuration, observed.upDecoderBank))
      (OrdinaryCoordinatorObservationMeasurability.decode_observeLocalCode (code.1, (code.2, (selectedRow published
        own, t))) y)

/-- Finite ordinary recursion. Before launch the existing first configuration
and initial bank are held without an ordinary operation. At launch they are
therefore installed once; every later round uses the whole ordinary observer. -/
def ordinaryReplayCode (rate : RateInput p) (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) :
    (n : ℕ) → n ≤ p.T → (Fin n → Fin (D p + 1)) → OrdinaryCode p rate
  | 0, _, _ => initialOrdinaryCode rate
  | n + 1, hn, feedback =>
      match ActualInitializationCoordinatorOwnHistory.initializationReplay published own a b n (by omega) (fun j =>
        feedback j.castSucc) with
      | .prelaunch _ => initialOrdinaryCode rate
      | .launched _ => ordinaryCodeStep published own ⟨n, by omega⟩
          (ordinaryReplayCode rate published own a b n (by omega) (fun j => feedback j.castSucc))
          (feedback (Fin.last n))

/-- Exact local storage before the next choice, or terminal storage at `T`. -/
def replayFeedback (rate : RateInput p) (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) : CoordinatorStorage p rate :=
  match ActualInitializationCoordinatorOwnHistory.initializationReplay published own a b n hn feedback with
  | .prelaunch live => .inl live
  | .launched _ => .inr (decodeOrdinary (ordinaryReplayCode rate published own a b n hn feedback))

/-- Earlier arm entries are ignored: the operations recompute their choices
and consume only the supplied own observations. No action is produced at `T`. -/
def coordinatorGridReplay (rate : RateInput p) (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (history : GridHistory p n) : CoordinatorStorage p rate :=
  replayFeedback rate published own a b n hn (fun j => (history j).2)

def decisionFeedback (rate : RateInput p) (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (t : Fin p.T)
    (feedback : Fin t.val → Fin (D p + 1)) : Fin p.K :=
  match ActualInitializationCoordinatorOwnHistory.initializationPreparedRound published own a b t feedback with
  | some prepared => prepared.arm
  | none =>
      let storage := decodeOrdinary (ordinaryReplayCode rate published own a b t.val t.isLt.le feedback)
      (OrdinaryCoordinatorPhysicalInterface.prepareLocal storage.1 storage.2 (selectedRow published own) t).arm

/-- The actual finite-grid decision interface, with no off-horizon branch. -/
def coordinatorGridDecision (rate : RateInput p) (a b : ℝ) (t : Fin p.T)
    (x : GridInput p t.val) : Fin p.K :=
  decisionFeedback rate x.1 x.2.1 a b t (fun j => (x.2.2 j).2)

/-- Lossless storage code relative to the original published/own input. The
initializer code retains its existing continuous base through that input. -/
def coordinatorGridReplayCode (rate : RateInput p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : GridInput p n) : ActualInitializationBlockMeasurability.ContinuationCode p × OrdinaryCode p rate :=
  (ActualInitializationCoordinatorOwnHistory.initializationReplayCode a b n hn (x.1, (x.2.1, fun j => (x.2.2 j).2)),
    ordinaryReplayCode rate x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2))

private theorem measurable_selectedRow {X : Type*} [MeasurableSpace X]
    (published : X → CompletePublicTable.PublishedOutput p) (own : X → OwnCoordinates p)
    (hpublic : Measurable published) (hown : Measurable own) :
    Measurable (fun x => selectedRow (published x) (own x)) := by
  have hj := (PrivateSourceStreams.measurable_coordinatorIndex p).comp (measurable_fst.comp hown)
  intro s hs
  rw [show (fun x => selectedRow (published x) (own x)) ⁻¹' s =
      ⋃ j : Fin (M p), {x | PrivateSourceStreams.coordinatorIndex p (own x).1 = j} ∩
        {x | (published x).2 j ∈ s} by ext x; simp [selectedRow]]
  exact MeasurableSet.iUnion fun j => (measurableSet_eq_fun hj measurable_const).inter
    (((measurable_pi_apply j).comp (measurable_snd.comp hpublic)) hs)

private theorem measurable_ordinaryCodeStep {X : Type*} [MeasurableSpace X]
    (published : X → CompletePublicTable.PublishedOutput p) (own : X → OwnCoordinates p)
    (code : X → OrdinaryCode p rate) (y : X → Fin (D p + 1)) (t : Fin p.T)
    (hpublic : Measurable published) (hown : Measurable own)
    (hcode : Measurable code) (hy : Measurable y) :
    Measurable (fun x => ordinaryCodeStep (published x) (own x) t (code x) (y x)) := by
  have hrow := measurable_selectedRow published own hpublic hown
  have hinput : Measurable (fun x : X =>
      ((code x).1, ((code x).2, (selectedRow (published x) (own x), t))) :
        X → OrdinaryCoordinatorLocalMeasurability.LocalInput p rate) := (measurable_fst.comp hcode).prodMk
    ((measurable_snd.comp hcode).prodMk (hrow.prodMk (measurable_const (a := t))))
  have hobs := OrdinaryCoordinatorObservationMeasurability.measurable_observeLocalCode.comp (hinput.prodMk hy)
  exact (measurable_fst.comp hobs).prodMk (measurable_fst.comp (measurable_snd.comp hobs))

private theorem measurable_ordinaryReplayCode (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun x : FeedbackInput p n => ordinaryReplayCode rate x.1 x.2.1 a b n hn x.2.2) := by
  classical
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let restrict : FeedbackInput p (n + 1) → FeedbackInput p n :=
        fun x => (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      have hr : Measurable restrict := measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          (Measurable.of_eval fun j => (measurable_pi_apply j.castSucc).comp
            (measurable_snd.comp measurable_snd)))
      have hc := (ActualInitializationCoordinatorOwnHistory.measurable_initializationReplayCode a b n (by omega)).comp
        hr
      have hs : MeasurableSet {x : FeedbackInput p (n + 1) |
          (ActualInitializationCoordinatorOwnHistory.initializationReplayCode a b n (by omega) (restrict x)).2.2.2.2 =
            none} :=
        measurableSet_eq_fun
          ((measurable_of_countable fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
            c.2.2.2.2).comp hc) measurable_const
      have hstep := measurable_ordinaryCodeStep Prod.fst (fun x : FeedbackInput p (n + 1) => x.2.1)
        (fun x => ordinaryReplayCode rate (restrict x).1 (restrict x).2.1 a b n (by omega) (restrict x).2.2)
        (fun x => x.2.2 (Fin.last n)) ⟨n, by omega⟩ measurable_fst
        (measurable_fst.comp measurable_snd) ((ih (by omega)).comp hr)
        ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))
      have hite : Measurable (fun x : FeedbackInput p (n + 1) =>
          if (ActualInitializationCoordinatorOwnHistory.initializationReplayCode a b n
              (by omega) (restrict x)).2.2.2.2 = none then initialOrdinaryCode rate
          else ordinaryCodeStep x.1 x.2.1 ⟨n, by omega⟩
            (ordinaryReplayCode rate (restrict x).1 (restrict x).2.1 a b n
              (by omega) (restrict x).2.2) (x.2.2 (Fin.last n))) :=
        Measurable.ite hs measurable_const hstep
      convert hite using 1
      funext x
      dsimp only [ordinaryReplayCode]
      cases he : ActualInitializationCoordinatorOwnHistory.initializationReplay x.1 x.2.1 a b n (by omega) (fun j =>
        x.2.2 j.castSucc) <;>
        simp only [ActualInitializationCoordinatorOwnHistory.initializationReplayCode, restrict, he,
          ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData, Option.some_ne_none, ↓reduceIte]

private theorem measurable_gridFeedback (n : ℕ) : Measurable
    (fun x : GridInput p n => (x.1, (x.2.1, fun j => (x.2.2 j).2)) : GridInput p n → FeedbackInput p n) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (Measurable.of_eval fun j => measurable_snd.comp
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))))

theorem measurable_coordinatorGridReplayCode (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (coordinatorGridReplayCode (p := p) rate a b n hn) :=
  ((ActualInitializationCoordinatorOwnHistory.measurable_initializationReplayCode a b n hn).comp
    (measurable_gridFeedback n)).prodMk
    ((measurable_ordinaryReplayCode rate a b n hn).comp (measurable_gridFeedback n))

private theorem measurable_decisionFeedback (rate : RateInput p) (a b : ℝ) (t : Fin p.T) :
    Measurable (fun x : FeedbackInput p t.val => decisionFeedback rate x.1 x.2.1 a b t x.2.2) := by
  classical
  have hp := ActualInitializationCoordinatorOwnHistory.measurable_initializationPreparedCode (p := p) a b t
  have hc := measurable_ordinaryReplayCode (p := p) rate a b t.val t.isLt.le
  have hrow := measurable_selectedRow (p := p) (Prod.fst : FeedbackInput p t.val → _)
    (fun x => x.2.1) measurable_fst (measurable_fst.comp measurable_snd)
  have hinput : Measurable (fun x : FeedbackInput p t.val =>
      ((ordinaryReplayCode rate x.1 x.2.1 a b t.val t.isLt.le x.2.2).1,
        ((ordinaryReplayCode rate x.1 x.2.1 a b t.val t.isLt.le x.2.2).2,
          (selectedRow x.1 x.2.1, t))) :
        FeedbackInput p t.val → OrdinaryCoordinatorLocalMeasurability.LocalInput p rate) :=
    (measurable_fst.comp hc).prodMk
    ((measurable_snd.comp hc).prodMk (hrow.prodMk (measurable_const (a := t))))
  have harm := OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_prepareLocalArm.comp hinput
  let read : Option (BootstrapCoordinatorRoundMeasurability.PreparedRoundCode p) × Fin p.K → Fin p.K :=
    fun pair => pair.1.elim pair.2 (fun c => c.2.2)
  have hread := (measurable_of_countable read).comp (hp.prodMk harm)
  convert hread using 1
  funext x
  unfold decisionFeedback
  cases he : ActualInitializationCoordinatorOwnHistory.initializationPreparedRound x.1 x.2.1 a b t x.2.2 <;>
    simp only [Function.comp_def, ActualInitializationCoordinatorOwnHistory.initializationPreparedCode, he,
      Option.map_none, Option.map_some, read, Option.elim,
      BootstrapCoordinatorRoundMeasurability.encodePreparedRound]
  rfl

/-- Joint Borel measurability on the actual published/own/finite grid-history
product, using the original continuous rows, weights, and scalar spaces. -/
theorem measurable_coordinatorGridDecision (rate : RateInput p) (a b : ℝ) (t : Fin p.T) :
    Measurable (coordinatorGridDecision (p := p) rate a b t) :=
  (measurable_decisionFeedback rate a b t).comp (measurable_gridFeedback t.val)

/-- Restore the local phase-tagged storage from its existing codes and the
original continuous base. A malformed prelaunch monitor is rejected rather
than replaced by a protocol state. This decoder is not an action interface. -/
def decodeCoordinatorGridReplayCode (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (code : ActualInitializationBlockMeasurability.ContinuationCode p ×
      OrdinaryCode p rate) :
    Option (CoordinatorStorage p rate) :=
  if code.1.2.2.2.2 = none then
    if hm : code.1.2.2.2.1.crossingBlock = none ∧ code.1.2.2.2.1.launchPosition = p.T then
      some (.inl (BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
        ((selectedRow published own, published.1), (a, b))
        ⟨code.1.1, code.1.2.1, code.1.2.2.1, ⟨code.1.2.2.2.1, hm⟩⟩))
    else none
  else some (.inr (decodeOrdinary code.2))

private def continuationBase (phase : Continuation p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorContinuousBase p :=
  (((ActualInitializationRun.continuationData p phase).row,
      (ActualInitializationRun.continuationData p phase).ids),
    ((ActualInitializationRun.continuationData p phase).C_star,
      (ActualInitializationRun.continuationData p phase).C_h))

private theorem atRound_base (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p) :
    (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p (ActualInitializationCoordinatorOwnHistory.atRound
      own t live)).1 =
      (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1 := by
  unfold ActualInitializationCoordinatorOwnHistory.atRound
  split <;> rfl

private theorem replay_step_base (own : OwnCoordinates p) (t : Fin p.T)
    (phase : Continuation p) (y : Fin (D p + 1)) :
    continuationBase (ActualInitializationCoordinatorOwnHistory.replayStep own t phase y) = continuationBase phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      unfold ActualInitializationCoordinatorOwnHistory.replayStep observe prepare continuationBase
      rw [ActualInitializationRun.continuationAfterObservation_data]
      exact atRound_base own t live

private theorem position_base (own : OwnCoordinates p) (n : ℕ) (phase : Continuation p) :
    continuationBase (ActualInitializationCoordinatorOwnHistory.atPosition own n phase) = continuationBase phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      by_cases hn : n < p.T
      · simp only [ActualInitializationCoordinatorOwnHistory.atPosition, hn, ↓reduceDIte]
        exact atRound_base own ⟨n, hn⟩ live
      · simp only [ActualInitializationCoordinatorOwnHistory.atPosition, hn, ↓reduceDIte]

private theorem initialization_base (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) :
    continuationBase (ActualInitializationCoordinatorOwnHistory.initializationReplay published own a b n hn feedback) =
      ((selectedRow published own, published.1), (a, b)) := by
  have hraw : continuationBase (ActualInitializationCoordinatorOwnHistory.replayRaw published own a b n hn feedback) =
      ((selectedRow published own, published.1), (a, b)) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [ActualInitializationCoordinatorOwnHistory.replayRaw, replay_step_base, ih]
  exact (position_base own n _).trans hraw

/-- Full reconstruction of the phase-tagged readout on every finite supplied
history, not just on histories realized by a source. The unchanged continuous
base and the prelaunch monitor conditions are proved inside the recursion. -/
theorem decode_coordinatorGridReplayCode (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) (x : GridInput p n) :
    decodeCoordinatorGridReplayCode x.1 x.2.1 a b (coordinatorGridReplayCode rate a b n hn x) =
      some (coordinatorGridReplay rate x.1 x.2.1 a b n hn x.2.2) := by
  have hb := initialization_base x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)
  unfold coordinatorGridReplayCode ActualInitializationCoordinatorOwnHistory.initializationReplayCode
    coordinatorGridReplay replayFeedback
  cases he : ActualInitializationCoordinatorOwnHistory.initializationReplay x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)
    with
  | prelaunch live =>
      rw [he] at hb
      unfold decodeCoordinatorGridReplayCode
      split
      · split
        · change some (Sum.inl (BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
            ((selectedRow x.1 x.2.1, x.1.1), (a, b))
            (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2)) = some (Sum.inl live)
          rw [← hb]
          exact congrArg (fun state : PrelaunchBlock p => some (Sum.inl state))
            (BootstrapCoordinatorRoundMeasurability.reconstructPrelaunch p live)
        · rename_i hmonitor
          exact (hmonitor live.monitor.property).elim
      · rename_i htag
        exact (htag rfl).elim
  | launched launch =>
      simp only [decodeCoordinatorGridReplayCode, ActualInitializationBlockMeasurability.continuationCodeOf,
        Option.some_ne_none, ↓reduceIte]

/-- Every reached ordinary code is the actual encoding of its decoded storage.
The observation producer constructs this encoding anew at each successor. -/
theorem ordinaryReplayCode_canonical (rate : RateInput p)
    (published : CompletePublicTable.PublishedOutput p) (own : OwnCoordinates p)
    (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) (feedback : Fin n → Fin (D p + 1)) :
    let code := ordinaryReplayCode rate published own a b n hn feedback
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (decodeOrdinary code).1, (decodeOrdinary code).2) =
      code := by
  dsimp only
  cases n with
  | zero => rfl
  | succ n =>
      unfold ordinaryReplayCode
      cases ActualInitializationCoordinatorOwnHistory.initializationReplay published own a b n (by omega) (fun j =>
        feedback j.castSucc) with
      | prelaunch live => rfl
      | launched launch =>
          simp only [ordinaryCodeStep, OrdinaryCoordinatorObservationMeasurability.observeLocalCode,
            ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation,
            decodeOrdinary, ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator]

/-- Read only the existing coordinator coordinates of a retained physical record. -/
def recordStorage {source : SourceInput p} {rewards : GridRewardTable p} :
    ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards → CoordinatorStorage p rate
  | .initialization record => .inl record.coordinatorBefore
  | .postlaunch record => .inr (record.input.state.coordinator, record.input.state.upDecoderBank)

/-- The terminal local storage of an existing suffix. This traverses only its
already constructed traces and introduces no transition or action. -/
def suffixTerminal {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)} {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0} :
    ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards block state → OrdinaryStorage p rate
  | .final trace _ => (trace.finalState.coordinator, trace.finalState.upDecoderBank)
  | .successor _ _ _ _ tail => suffixTerminal tail

/-- At the final boundary a launch retains the installed first storage; an
exhausted initialization retains its actual live block. Neither produces an arm. -/
def terminalStorage {source : SourceInput p} {rewards : GridRewardTable p} {a b : ℝ} :
    ActualCompletePhysicalHistory.CompleteHistory p rate source rewards a b → CoordinatorStorage p rate
  | .launchedBefore _ _ _ _ suffix => .inr (suffixTerminal suffix)
  | .launchedAtHorizon _ _ _ _ => .inr (decodeOrdinary (initialOrdinaryCode rate))
  | .exhausted live _ => .inl live

variable (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p) (a b : ℝ)

abbrev actualHistory := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards a b
abbrev actualFeedback (n : ℕ) (hn : n ≤ p.T) :=
  ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix rate source rewards a b n hn
abbrev actualOrdinary (n : ℕ) (hn : n ≤ p.T) :=
  decodeOrdinary (ordinaryReplayCode rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a
    b n hn
    (actualFeedback rate source rewards a b n hn))
abbrev actualReplay (n : ℕ) (hn : n ≤ p.T) :=
  replayFeedback rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
    (actualFeedback rate source rewards a b n hn)

private theorem actual_feedback_restrict (n : ℕ) (hn : n + 1 ≤ p.T) :
    (fun j : Fin n => actualFeedback rate source rewards a b (n + 1) hn j.castSucc) =
      actualFeedback rate source rewards a b n (by omega) := rfl

private theorem ordinary_before_launch (n : ℕ) (hn : n ≤ p.T)
    (hprefix : n ≤ (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length) :
    ordinaryReplayCode rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
      (actualFeedback rate source rewards a b n hn) = initialOrdinaryCode rate := by
  induction n with
  | zero => rfl
  | succ n _ =>
      have ht : n < p.T := by omega
      have hc := (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_component_counts p rate source
        rewards a b
        (actualHistory rate source rewards a b)).1
      change (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length =
        (actualHistory rate source rewards a b).prefixRoundCount at hc
      obtain ⟨live, hlive⟩ :=
        (ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_prelaunch_iff
        rate source rewards a b n ht).mpr (by
          change n < (actualHistory rate source rewards a b).prefixRoundCount
          rw [← hc]
          omega)
      simp only [ordinaryReplayCode, actual_feedback_restrict, hlive]

private theorem consecutiveNat_get (start count i : ℕ) (hi : i < count) :
    (ActualInitializationHorizon.consecutiveNat start count)[i]'(by
      rw [ActualInitializationHorizon.consecutiveNat_length]; exact hi) = start + i := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (ActualInitializationHorizon.consecutiveNat (start + 1) count)[i]'(by
            rw [ActualInitializationHorizon.consecutiveNat_length]; omega) = start + (i + 1)
          rw [ih (start + 1) i (by omega)]
          omega

private theorem actual_record_time (i : ℕ)
    (hi : i < (ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b)).length) :
    (ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b))[i].time.val = i := by
  have hlength := (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards
    a b).1
  change (ActualCompletePhysicalHistory.physicalHistoryRecords
    (actualHistory rate source rewards a b)).length = p.T at hlength
  have hc := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_times_values p rate source rewards a b
  have he := congrArg (fun times : List ℕ => times[i]?) hc
  have hiT : i < p.T := by omega
  have hl : i < (ActualInitializationHorizon.consecutiveNat 0 p.T).length := by
    rw [ActualInitializationHorizon.consecutiveNat_length]; exact hiT
  simpa only [ActualCompletePhysicalHistory.times, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    List.getElem?_eq_getElem hl, consecutiveNat_get 0 p.T i hiT, Nat.zero_add, Option.some.injEq] using he

private theorem actual_record_at_time (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source
  rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b)) :
    (ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b))[record.time.val]'(by
      rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1]
      exact record.time.isLt) = record := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  have ht : record.time.val = i := by
    rw [← he]
    exact actual_record_time rate source rewards a b i hi
  simpa only [ht] using he

private theorem actual_feedback_at_record (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source
  rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b)) :
    actualFeedback rate source rewards a b (record.time.val + 1) (by omega) (Fin.last record.time.val) =
      record.feedback (ActiveRoundActions.coordinator p.two_le_m) := by
  have he := actual_record_at_time rate source rewards a b record hmem
  dsimp only [actualFeedback, ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix]
  simp only [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
    ActualCompletePhysicalHistory.feedbackHistory, List.getElem_map, Fin.val_last, he]

private theorem postlaunch_mem (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate source rewards a b)) :
    ActualCompletePhysicalHistory.PhysicalHistoryRecord.postlaunch record ∈
      ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b) := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨record, hmem, rfl⟩)

private theorem actual_ordinary_step (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate source rewards a b))
    (launch : LaunchedBlock p)
    (hphase : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalFold.phase =
      .launched launch)
    (hprefix : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
      record.time.val)
    (hstorage : actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
      (record.input.state.coordinator, record.input.state.upDecoderBank)) :
    actualOrdinary rate source rewards a b (record.time.val + 1) (by omega) =
      (record.result.nextState.coordinator, record.result.nextState.upDecoderBank) := by
  have hi := (ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_of_ge_prefix rate
    source rewards a b
    record.time.val record.time.isLt.le hprefix).trans hphase
  change decodeOrdinary (ordinaryReplayCode _ _ _ _ _ _ _ _) = _
  rw [ordinaryReplayCode, actual_feedback_restrict, hi, decode_ordinaryCodeStep]
  dsimp only
  change decodeOrdinary _ = _ at hstorage
  rw [hstorage]
  have hy := actual_feedback_at_record rate source rewards a b (.postlaunch record)
    (postlaunch_mem rate source rewards a b record hmem)
  dsimp only [ActualCompletePhysicalHistory.PhysicalHistoryRecord.time,
    ActualCompletePhysicalHistory.PhysicalHistoryRecord.feedback] at hy
  rw [hy, ActualPostlaunchPhysicalStep.RoundResult.nextState_coordinator,
    ActualPostlaunchPhysicalStep.RoundResult.nextState_bank,
    record.result_eq, ActualPostlaunchPhysicalStep.step_coordinator_observation]
  have hrow : selectedRow source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) =
      record.input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p record.input.source) := by
    rw [record.input_source]
    rfl
  rw [hrow]
  simp only [ActualCompletePhysicalHistory.MixedRoundRecord.feedback, record.result_eq]
  rfl

private theorem block_trace_replay {block : Fin (n_boot p)} {cursor stop : ℕ}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards block cursor state stop)
    (hstop : BootstrapObservedFollower.blockStart p block + stop ≤ p.T)
    (launch : LaunchedBlock p)
    (hphase : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalFold.phase =
      .launched launch)
    (hprefix : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
      BootstrapObservedFollower.blockStart p block + cursor)
    (hmem : ∀ record ∈ trace.records, record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate
      source rewards a b))
    (hstorage : actualOrdinary rate source rewards a b
        (BootstrapObservedFollower.blockStart p block + cursor) (by
          have hc : cursor ≤ stop := by cases trace <;> omega
          omega) = (state.coordinator, state.upDecoderBank)) :
    (∀ record ∈ trace.records,
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
        record.time.val ∧ actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
      (record.input.state.coordinator, record.input.state.upDecoderBank)) ∧
    actualOrdinary rate source rewards a b (BootstrapObservedFollower.blockStart p block + stop) hstop =
      (trace.finalState.coordinator, trace.finalState.upDecoderBank) := by
  induction trace with
  | done state => exact ⟨by simp only [ActualCompletePhysicalHistory.MixedBlockTrace.records, List.not_mem_nil,
    false_implies, implies_true],
      hstorage⟩
  | @step cursor stop state input hstate hsource hrewards result heq tail hlt ih =>
      let record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards :=
        ⟨block, cursor, input, hsource, hrewards, result, heq⟩
      have ht : record.time.val = BootstrapObservedFollower.blockStart p block + cursor := rfl
      have hs : actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
          (input.state.coordinator, input.state.upDecoderBank) := by
        change actualOrdinary rate source rewards a b
          (BootstrapObservedFollower.blockStart p block + cursor) _ = _
        rw [hstate]
        exact hstorage
      have hn := actual_ordinary_step rate source rewards a b record
        (hmem record (List.mem_cons_self)) launch hphase (by omega) hs
      have htmem : ∀ record ∈ tail.records, record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory
        rate source rewards a b) :=
        fun record hr => hmem record (List.mem_cons_of_mem _ hr)
      have hnext : actualOrdinary rate source rewards a b
          (BootstrapObservedFollower.blockStart p block + (cursor + 1)) (by omega) =
          (result.nextState.coordinator, result.nextState.upDecoderBank) := by
        simpa only [ht, Nat.add_assoc] using hn
      have htail := ih hstop (by omega) htmem hnext
      refine ⟨?_, htail.2⟩
      intro current hcurrent
      rcases List.mem_cons.mp hcurrent with he | he
      · subst current
        change _ ≤ record.time.val ∧ _
        exact ⟨by rw [ht]; exact hprefix, hs⟩
      · exact htail.1 current he

private theorem successor_start {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (heq : next = ActualInitializationRun.successorBlock p block hnext) :
    BootstrapObservedFollower.blockStart p next = BootstrapObservedFollower.blockStop p block := by
  have hv : next.val = block.val + 1 := by rw [heq]; rfl
  have ha := ActualInitializationHorizon.nextActivationRound_eq_successor_start (p := p) block next hv
  change BootstrapObservedFollower.blockStop p block + 1 =
    BootstrapObservedFollower.blockStart p next + 1 at ha
  omega

private theorem suffix_replay {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards block state)
    (launch : LaunchedBlock p)
    (hphase : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalFold.phase =
      .launched launch)
    (hprefix : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
      BootstrapObservedFollower.blockStart p block)
    (hmem : ∀ record ∈ suffix.records, record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate
      source rewards a b))
    (hstorage : actualOrdinary rate source rewards a b (BootstrapObservedFollower.blockStart p block)
      (le_trans (BootstrapObservedFollower.blockStart_lt_blockStop p block).le (Nat.min_le_left _ _)) =
        (state.coordinator, state.upDecoderBank)) :
    (∀ record ∈ suffix.records,
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
        record.time.val ∧ actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
          (record.input.state.coordinator, record.input.state.upDecoderBank)) ∧
    actualOrdinary rate source rewards a b p.T le_rfl = suffixTerminal suffix := by
  induction suffix with
  | @final block state trace last =>
      have hend := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hT := BootstrapObservedFollower.finalBlock_endpoint_eq_T p block last
      have hr := block_trace_replay rate source rewards a b trace (by omega) launch hphase
        (by simpa only [Nat.add_zero] using hprefix) hmem hstorage
      refine ⟨hr.1, ?_⟩
      simpa only [hend, hT, suffixTerminal] using hr.2
  | @successor block state trace hnext next heq tail ih =>
      have hend := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hbound : BootstrapObservedFollower.blockStop p block ≤ p.T := Nat.min_le_left _ _
      have hr := block_trace_replay rate source rewards a b trace (by omega) launch hphase
        (by simpa only [Nat.add_zero] using hprefix)
        (fun record hrecord => hmem record (List.mem_append_left _ hrecord)) hstorage
      have hstart := successor_start (p := p) hnext heq
      have hs : actualOrdinary rate source rewards a b (BootstrapObservedFollower.blockStart p next) (by omega) =
          ((ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext heq source trace.finalState).coordinator,
            (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext heq source trace.finalState).upDecoderBank) := by
        simpa only [hstart, hend, ActualPostlaunchPhysicalStep.crossSuccessorBoundary_coordinator,
          ActualPostlaunchPhysicalStep.crossSuccessorBoundary_bank] using hr.2
      have ht := ih (by
          have hp := BootstrapObservedFollower.blockStart_lt_blockStop p block
          omega) (fun record hrecord => hmem record (List.mem_append_right _ hrecord)) hs
      refine ⟨?_, ht.2⟩
      intro record hrecord
      rcases List.mem_append.mp hrecord with hrecord | hrecord
      · exact hr.1 record hrecord
      · exact ht.1 record hrecord

private theorem actual_launch_phase (launch : LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalDisposition =
      .launched launch seed) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalFold.phase =
      .launched launch ∧
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length =
      launch.monitor.launchPosition := by
  have ht := ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_terminal_cases rate
    source rewards a b
  dsimp only at ht
  rw [hlaunch] at ht
  have he := ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_of_ge_prefix rate source
    rewards a b p.T le_rfl
    (ActualInitializationCoordinatorOwnHistory.sourceInitializationRecordCount_le rate source rewards a b)
  exact ⟨he.symm.trans ht.1, ht.2⟩

private theorem launch_start (launch : LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalDisposition =
      .launched launch seed) (hbefore : launch.monitor.launchPosition < p.T) :
    BootstrapObservedFollower.blockStart p
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source rewards a b launch seed
        hlaunch hbefore) =
        launch.monitor.launchPosition := by
  have ht := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_time_val p rate source rewards a b
    launch seed hlaunch hbefore
  simpa only [ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput,
    ActualPostlaunchPhysicalStep.PhysicalInput.time,
    ActualInitializationRun.blockTime, Nat.add_zero] using ht

private theorem launched_suffix_replay (launch : LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalDisposition =
      .launched launch seed) (hbefore : launch.monitor.launchPosition < p.T)
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source rewards a b launch seed
        hlaunch hbefore)
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source rewards a b launch seed
        hlaunch hbefore).state)
    (hh : actualHistory rate source rewards a b = .launchedBefore launch seed hlaunch hbefore suffix) :
    (∀ record ∈ suffix.records,
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).records.length ≤
        record.time.val ∧ actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
          (record.input.state.coordinator, record.input.state.upDecoderBank)) ∧
    actualOrdinary rate source rewards a b p.T le_rfl = suffixTerminal suffix := by
  have hp := actual_launch_phase rate source rewards a b launch seed hlaunch
  have hs := launch_start rate source rewards a b launch seed hlaunch hbefore
  apply suffix_replay rate source rewards a b suffix launch hp.1 (by omega)
  · intro record hrecord
    rw [hh]
    exact hrecord
  · have hb := ordinary_before_launch rate source rewards a b
      (BootstrapObservedFollower.blockStart p
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source rewards a b launch seed
          hlaunch hbefore))
      (by omega) (by omega)
    change decodeOrdinary _ = _
    rw [hb]
    exact (Prod.ext
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_coordinator p rate source rewards a b launch
        seed hlaunch hbefore)
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_bank p rate source rewards a b launch seed
        hlaunch hbefore)).symm

/-- Single-source identification, obtained by induction through every actual
mixed block and both coordinator fields of every successor boundary adapter. -/
theorem sourceInitialized_postlaunch_coordinator_storage
    (record : ActualCompletePhysicalHistory.MixedRoundRecord p rate source rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate source rewards a b)) :
    ∃ launch, ActualInitializationCoordinatorOwnHistory.initializationReplay source.1
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b record.time.val record.time.isLt.le
        (actualFeedback rate source rewards a b record.time.val record.time.isLt.le) = .launched launch ∧
      actualOrdinary rate source rewards a b record.time.val record.time.isLt.le =
        (record.input.state.coordinator, record.input.state.upDecoderBank) := by
  cases hh : actualHistory rate source rewards a b with
  | launchedBefore launch seed hlaunch hbefore suffix =>
      have hm : record ∈ suffix.records := by simpa only [hh, ActualCompletePhysicalHistory.postlaunchRecords] using
        hmem
      have hs := (launched_suffix_replay rate source rewards a b launch seed hlaunch hbefore suffix hh).1 record hm
      exact ⟨launch, (ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_of_ge_prefix
        rate source rewards a b
        record.time.val record.time.isLt.le hs.1).trans
          (actual_launch_phase rate source rewards a b launch seed hlaunch).1, hs.2⟩
  | launchedAtHorizon launch seed hlaunch hat =>
      simp only [hh, ActualCompletePhysicalHistory.postlaunchRecords, List.not_mem_nil] at hmem
  | exhausted live hexhausted =>
      simp only [hh, ActualCompletePhysicalHistory.postlaunchRecords, List.not_mem_nil] at hmem

/-- Full before-storage reconstruction at every retained actual physical round. -/
theorem sourceInitialized_coordinator_record_replay
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b)) :
    actualReplay rate source rewards a b record.time.val record.time.isLt.le = recordStorage record := by
  cases record with
  | initialization record =>
      have hm : record ∈ ActualCompletePhysicalHistory.initializationRecords (actualHistory rate source rewards a b)
        := by
        rcases List.mem_append.mp hmem with hm | hm
        · obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
          cases he
          exact ho
        · obtain ⟨other, _, he⟩ := List.mem_map.mp hm
          cases he
      dsimp only [ActualCompletePhysicalHistory.PhysicalHistoryRecord.time]
      unfold actualReplay replayFeedback
      rw [ActualInitializationCoordinatorOwnHistory.sourceInitialized_initialization_coordinator_replay rate source
        rewards a b record hm]
      rfl
  | postlaunch record =>
      have hm : record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate source rewards a b) := by
        rcases List.mem_append.mp hmem with hm | hm
        · obtain ⟨other, _, he⟩ := List.mem_map.mp hm
          cases he
        · obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
          cases he
          exact ho
      obtain ⟨launch, hp, hs⟩ := sourceInitialized_postlaunch_coordinator_storage rate source rewards a b record hm
      dsimp only [ActualCompletePhysicalHistory.PhysicalHistoryRecord.time]
      unfold actualReplay replayFeedback
      rw [hp]
      exact congrArg Sum.inr hs

/-- The same reconstruction includes terminal storage at `T`, including a
launch at the final boundary and exhaustion without launch. -/
theorem sourceInitialized_coordinator_terminal_replay :
    actualReplay rate source rewards a b p.T le_rfl = terminalStorage (actualHistory rate source rewards a b) := by
  have ht := ActualInitializationCoordinatorOwnHistory.sourceInitialized_initializationReplay_terminal_cases rate
    source rewards a b
  dsimp only at ht
  cases hh : actualHistory rate source rewards a b with
  | launchedBefore launch seed hlaunch hbefore suffix =>
      rw [hlaunch] at ht
      unfold actualReplay replayFeedback
      rw [ht.1]
      exact congrArg Sum.inr
        (launched_suffix_replay rate source rewards a b launch seed hlaunch hbefore suffix hh).2
  | launchedAtHorizon launch seed hlaunch hat =>
      rw [hlaunch] at ht
      unfold actualReplay replayFeedback
      rw [ht.1]
      change Sum.inr (decodeOrdinary _) = _
      rw [ordinary_before_launch rate source rewards a b p.T le_rfl (by omega)]
      rfl
  | exhausted live hexhausted =>
      rw [hexhausted] at ht
      unfold actualReplay replayFeedback
      rw [ht.1]
      rfl

/-- The actual before-storage readout at a calendar position, with a separate
terminal branch. The list index is justified by the actual complete length. -/
def actualBeforeStorage (n : ℕ) (_hn : n ≤ p.T) : CoordinatorStorage p rate :=
  if ht : n < p.T then recordStorage
    ((ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b))[n]'(by
      rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1]
      exact ht))
  else terminalStorage (actualHistory rate source rewards a b)

/-- Single-source reconstruction precedes any comparison of two worlds. -/
theorem actual_complete_coordinator_replay (n : ℕ) (hn : n ≤ p.T) :
    actualReplay rate source rewards a b n hn = actualBeforeStorage rate source rewards a b n hn := by
  unfold actualBeforeStorage
  split
  · rename_i ht
    let record := (ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b))[n]'(by
      rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1]
      exact ht)
    have hm : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b) :=
      List.getElem_mem _
    have he := sourceInitialized_coordinator_record_replay rate source rewards a b record hm
    have htime : record.time.val = n := actual_record_time rate source rewards a b n (by
      rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1];
        exact ht)
    simpa only [htime] using he
  · have he : n = p.T := by omega
    subst n
    exact sourceInitialized_coordinator_terminal_replay rate source rewards a b

private theorem decision_at_record (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards)
    (hmem : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b)) :
    decisionFeedback rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b record.time
      (actualFeedback rate source rewards a b record.time.val record.time.isLt.le) =
        record.actions (ActiveRoundActions.coordinator p.two_le_m) := by
  cases record with
  | initialization record =>
      have hm : record ∈ ActualCompletePhysicalHistory.initializationRecords (actualHistory rate source rewards a b)
        := by
        rcases List.mem_append.mp hmem with hm | hm
        · obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
          cases he
          exact ho
        · obtain ⟨other, _, he⟩ := List.mem_map.mp hm
          cases he
      have ha := ActualInitializationCoordinatorOwnHistory.sourceInitialized_initialization_prepared_arm rate source
        rewards a b record hm
      dsimp only [ActualCompletePhysicalHistory.PhysicalHistoryRecord.time,
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions]
      unfold decisionFeedback
      cases he : ActualInitializationCoordinatorOwnHistory.initializationPreparedRound source.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b record.time
          (actualFeedback rate source rewards a b record.time.val record.time.isLt.le) with
      | none => rw [he] at ha; cases ha
      | some prepared => exact Option.some.inj (by simpa only [he, Option.map_some] using ha)
  | postlaunch record =>
      have hm : record ∈ ActualCompletePhysicalHistory.postlaunchRecords (actualHistory rate source rewards a b) := by
        rcases List.mem_append.mp hmem with hm | hm
        · obtain ⟨other, _, he⟩ := List.mem_map.mp hm
          cases he
        · obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
          cases he
          exact ho
      obtain ⟨launch, hp, hs⟩ := sourceInitialized_postlaunch_coordinator_storage rate source rewards a b record hm
      dsimp only [ActualCompletePhysicalHistory.PhysicalHistoryRecord.time,
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions]
      unfold decisionFeedback ActualInitializationCoordinatorOwnHistory.initializationPreparedRound
      rw [hp]
      change (OrdinaryCoordinatorPhysicalInterface.prepareLocal (actualOrdinary rate source rewards a b
        record.time.val record.time.isLt.le).1
        (actualOrdinary rate source rewards a b record.time.val record.time.isLt.le).2
        (selectedRow source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source)) record.time).arm = _
      rw [hs]
      have hrow : selectedRow source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) =
          record.input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p record.input.source) := by
        rw [record.input_source]; rfl
      rw [hrow]
      change _ = record.actions (ActiveRoundActions.coordinator p.two_le_m)
      rw [ActualCompletePhysicalHistory.MixedRoundRecord.actions,
        ActualPostlaunchPhysicalStep.actionProfile_coordinator, record.result.prepared.coordinator_eq]
      rfl

/-- Actual own arm/feedback entries, on exactly the finite strict-past domain. -/
def sourceGridHistory (n : ℕ) (hn : n ≤ p.T) : GridHistory p n := fun j =>
  ((ActualCompletePhysicalHistory.playerArmHistory (actualHistory rate source rewards a b)
      (ActiveRoundActions.coordinator p.two_le_m))[j.val]'(by
        have hlength := (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source
          rewards a b).2.1
        change j.val < ((ActualCompletePhysicalHistory.actionHistory (actualHistory rate source rewards a b)).map
          (fun profile => profile (ActiveRoundActions.coordinator p.two_le_m))).length
        rw [List.length_map, hlength]
        exact lt_of_lt_of_le j.isLt hn), actualFeedback rate source rewards a b n hn j)

/-- The operational decision agrees with the current actual pre-choice arm. -/
theorem sourceInitialized_coordinatorGridDecision (t : Fin p.T) :
    coordinatorGridDecision rate a b t
      (source.1, (ActualInitializationCoordinatorOwnHistory.ownCoordinates source, sourceGridHistory rate source
        rewards a b t.val t.isLt.le)) =
    (ActualCompletePhysicalHistory.playerArmHistory (actualHistory rate source rewards a b)
      (ActiveRoundActions.coordinator p.two_le_m))[t.val]'(by
        rw [ActualCompletePhysicalHistory.playerArmHistory, List.length_map,
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).2.1]
        exact t.isLt) := by
  let record := (ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a
    b))[t.val]'(by
    rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1];
      exact t.isLt)
  have hm : record ∈ ActualCompletePhysicalHistory.physicalHistoryRecords (actualHistory rate source rewards a b) :=
    List.getElem_mem _
  have ht : record.time = t := Fin.ext (actual_record_time rate source rewards a b t.val (by
    rw [(ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).1];
      exact t.isLt))
  have ha := decision_at_record rate source rewards a b record hm
  rw [ht] at ha
  change decisionFeedback rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b t
    (actualFeedback rate source rewards a b t.val t.isLt.le) = _
  rw [ha]
  simp only [ActualCompletePhysicalHistory.playerArmHistory, ActualCompletePhysicalHistory.actionHistory,
    List.getElem_map]
  rfl

/-- The coordinator's actual action list, without observations of other players. -/
abbrev sourceOwnArms := ActualCompletePhysicalHistory.playerArmHistory (actualHistory rate source rewards a b)
  (ActiveRoundActions.coordinator p.two_le_m)

/-- The coordinator's own actual grid feedback list. -/
abbrev sourceOwnFeedback := ActualCompletePhysicalHistory.playerGridFeedbackHistory (actualHistory rate source rewards
  a b)
  (ActiveRoundActions.coordinator p.two_le_m)

private theorem own_arms_length : (sourceOwnArms rate source rewards a b).length = p.T := by
  exact (List.length_map _).trans
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards a b).2.1

variable (other : SourceInput p) (otherRewards : GridRewardTable p)

private theorem feedback_local (n : ℕ) (hn : n ≤ p.T)
    (hpast : (sourceOwnFeedback rate source rewards a b).take n =
      (sourceOwnFeedback rate other otherRewards a b).take n) :
    actualFeedback rate source rewards a b n hn = actualFeedback rate other otherRewards a b n hn := by
  exact List.ofFn_injective
    ((ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list rate source rewards a b n hn).trans
      (hpast.trans (ActualInitializationCoordinatorOwnHistory.sourceOwnFeedbackPrefix_list rate other otherRewards a b
        n hn).symm))

private theorem earlier_feedback (n k : ℕ) (hkn : k ≤ n)
    (hpast : (sourceOwnFeedback rate source rewards a b).take n =
      (sourceOwnFeedback rate other otherRewards a b).take n) :
    (sourceOwnFeedback rate source rewards a b).take k =
      (sourceOwnFeedback rate other otherRewards a b).take k := by
  have he := congrArg (List.take k) hpast
  simpa only [List.take_take, Nat.min_eq_left hkn] using he

private theorem current_arm_local (t : Fin p.T)
    (hpublic : source.1 = other.1) (hown : ActualInitializationCoordinatorOwnHistory.ownCoordinates source =
      ActualInitializationCoordinatorOwnHistory.ownCoordinates other)
    (hpast : (sourceOwnFeedback rate source rewards a b).take t.val =
      (sourceOwnFeedback rate other otherRewards a b).take t.val) :
    (sourceOwnArms rate source rewards a b)[t.val]'(by rw [own_arms_length]; exact t.isLt) =
      (sourceOwnArms rate other otherRewards a b)[t.val]'(by rw [own_arms_length]; exact t.isLt) := by
  have hf := feedback_local rate source rewards a b other otherRewards t.val t.isLt.le hpast
  have hs := sourceInitialized_coordinatorGridDecision rate source rewards a b t
  have ho := sourceInitialized_coordinatorGridDecision rate other otherRewards a b t
  change decisionFeedback rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b t
    (actualFeedback rate source rewards a b t.val t.isLt.le) = _ at hs
  change decisionFeedback rate other.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates other) a b t
    (actualFeedback rate other otherRewards a b t.val t.isLt.le) = _ at ho
  rw [← hs, ← ho, hpublic, hown, hf]

private theorem earlier_arms_local (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ActualInitializationCoordinatorOwnHistory.ownCoordinates source =
      ActualInitializationCoordinatorOwnHistory.ownCoordinates other)
    (hpast : (sourceOwnFeedback rate source rewards a b).take n =
      (sourceOwnFeedback rate other otherRewards a b).take n) :
    (sourceOwnArms rate source rewards a b).take n = (sourceOwnArms rate other otherRewards a b).take n := by
  apply List.ext_getElem
  · simp only [List.length_take, own_arms_length]
  · intro j hj hk
    have hjn : j < n := lt_of_lt_of_le hj (by simp only [List.length_take]; exact Nat.min_le_left _ _)
    have hjT : j < p.T := lt_of_lt_of_le hjn hn
    have he := current_arm_local rate source rewards a b other otherRewards ⟨j, hjT⟩ hpublic hown
      (earlier_feedback rate source rewards a b other otherRewards n j hjn.le hpast)
    simpa only [List.getElem_take] using he

/-- Two arbitrary sources and whole reward tables have equal entire actual
before-storage and every earlier own arm from exactly public, own-coordinate,
and strict-past own-feedback equality. No launch, safety, success, follower,
reference-execution, or agreement premise is supplied. -/
theorem sourceInitialized_coordinator_own_history (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ActualInitializationCoordinatorOwnHistory.ownCoordinates source =
      ActualInitializationCoordinatorOwnHistory.ownCoordinates other)
    (hpast : (sourceOwnFeedback rate source rewards a b).take n =
      (sourceOwnFeedback rate other otherRewards a b).take n) :
    actualBeforeStorage rate source rewards a b n hn = actualBeforeStorage rate other otherRewards a b n hn ∧
    (sourceOwnArms rate source rewards a b).take n = (sourceOwnArms rate other otherRewards a b).take n ∧
    ∀ ht : n < p.T,
      (sourceOwnArms rate source rewards a b)[n]'(by rw [own_arms_length]; exact ht) =
        (sourceOwnArms rate other otherRewards a b)[n]'(by rw [own_arms_length]; exact ht) ∧
      (sourceOwnArms rate source rewards a b).take (n + 1) =
        (sourceOwnArms rate other otherRewards a b).take (n + 1) := by
  have hf := feedback_local rate source rewards a b other otherRewards n hn hpast
  have hs : actualReplay rate source rewards a b n hn = actualReplay rate other otherRewards a b n hn := by
    unfold actualReplay
    rw [hpublic, hown, hf]
  refine ⟨(actual_complete_coordinator_replay rate source rewards a b n hn).symm.trans
    (hs.trans (actual_complete_coordinator_replay rate other otherRewards a b n hn)),
    earlier_arms_local rate source rewards a b other otherRewards n hn hpublic hown hpast, ?_⟩
  intro ht
  have hc := current_arm_local rate source rewards a b other otherRewards ⟨n, ht⟩ hpublic hown hpast
  refine ⟨hc, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_take, own_arms_length]
  · intro j hj hk
    have hjn : j ≤ n := by
      have hj' : j < min (n + 1) p.T := by simpa only [List.length_take, own_arms_length] using hj
      omega
    by_cases he : j = n
    · subst j
      simpa only [List.getElem_take] using hc
    · have hjT : j < p.T := lt_of_le_of_lt hjn ht
      have heq := current_arm_local rate source rewards a b other otherRewards ⟨j, hjT⟩ hpublic hown
        (earlier_feedback rate source rewards a b other otherRewards n j hjn hpast)
      simpa only [List.getElem_take] using heq

/-- On actual histories, the grid replay reconstructs the same entire storage
at every position, including `T`. The supplied earlier arm entries are irrelevant. -/
theorem sourceInitialized_coordinatorGridReplay (n : ℕ) (hn : n ≤ p.T) :
    coordinatorGridReplay rate source.1 (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
      (sourceGridHistory rate source rewards a b n hn) = actualBeforeStorage rate source rewards a b n hn :=
  actual_complete_coordinator_replay rate source rewards a b n hn

/-- The strict own past produces the phase in both worlds. In the prelaunch
alternative no equality of future launch cuts is asserted. In the launched
alternative the actual terminal launches and complete-history cuts agree. -/
theorem sourceInitialized_coordinator_launch_alternative (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ActualInitializationCoordinatorOwnHistory.ownCoordinates source =
      ActualInitializationCoordinatorOwnHistory.ownCoordinates other)
    (hpast : (sourceOwnFeedback rate source rewards a b).take n =
      (sourceOwnFeedback rate other otherRewards a b).take n) :
    (∃ live, ActualInitializationCoordinatorOwnHistory.initializationReplay source.1
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
        (actualFeedback rate source rewards a b n hn) = .prelaunch live ∧
      ActualInitializationCoordinatorOwnHistory.initializationReplay other.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates other) a b n hn
        (actualFeedback rate other otherRewards a b n hn) = .prelaunch live) ∨
    (∃ launch, ActualInitializationCoordinatorOwnHistory.initializationReplay source.1
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
        (actualFeedback rate source rewards a b n hn) = .launched launch ∧
      ActualInitializationCoordinatorOwnHistory.initializationReplay other.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates other) a b n hn
        (actualFeedback rate other otherRewards a b n hn) = .launched launch ∧
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards a b).terminalFold.phase =
        .launched launch ∧
      (ActualInitializationHorizon.sourceInitializedRun p rate other otherRewards a b).terminalFold.phase =
        .launched launch ∧
      ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount (actualHistory rate source rewards a b) =
        ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount (actualHistory rate other otherRewards a b)) :=
          by
  have he := ActualInitializationCoordinatorOwnHistory.initialization_replay_own_history_local rate source rewards a b
    other otherRewards n hn
    hpublic hown hpast
  cases hp : ActualInitializationCoordinatorOwnHistory.initializationReplay source.1
    (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
      (actualFeedback rate source rewards a b n hn) with
  | prelaunch live => exact Or.inl ⟨live, rfl, he.symm.trans hp⟩
  | launched launch =>
      have hc := ActualInitializationCoordinatorOwnHistory.initialization_launched_own_history_local rate source
        rewards a b other otherRewards
        n hn hpublic hown hpast launch hp
      exact Or.inr ⟨launch, rfl, he.symm.trans hp, hc⟩

end Bandits.Support.ActualCompleteCoordinatorOwnHistory

end
