/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.PrivateRoundFreshness
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.ReferenceInitializationCausality
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.CompletePublicTable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Private player-round freshness at the actual reference launch

For fixed public inputs and one fixed complete row, the actual corrected
reference launch depends on the original player-round scalar array only
through its strict past.  The side/past view retains every original block
triple, the separate coordinator scalar, every coordinator-target scalar, and
exactly the strict-past player-round scalars.  Its complement is the entire
future player-round scalar vector, including every player in the launch round.

The source law is the existing continuous product on
`ExtendedPrivateCoordinates`.  The completion below is only an event evaluator;
it is never installed into a physical run.  This module makes no freshness
claim for block triples or coordinator targets, and fixes the complete public
row throughout.  `PrivateRoundFreshness` exposes a strict-past/current/strict-
future split for one `Fin T` round.  Here the launch-round coordinates join
the full future vector, so the same dependent-product split is applied directly
at the `Fin (T + 1)` source index; at `T` the future label subtype is empty.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,55-113,123-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationCausality
open Bandits.Support.ReferenceInitializationPrefixInvariance
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ReferencePrelaunchFollower
open scoped ENNReal

namespace Bandits.Support.ReferenceLaunchPrivateRoundLaw

abbrev Parameters := ConstructorDimensions.Parameters

/-- The original continuous scalar carrier shared with the existing
round-freshness API. -/
abbrev Scalar := PrivateRoundFreshness.Scalar

/-- The source stopping index: a source launch round `t` has index `t - 1`.
In particular the common source sentinel `T + 1` has index `T`. -/
abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)

/-- Original player-round scalar labels strictly before the source index. -/
abbrev PastPlayerRoundLabel (p : Parameters) (σ : LaunchIndex p) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    label.2.val < σ.val}

/-- Original player-round scalar labels at or after the source index. -/
abbrev FuturePlayerRoundLabel (p : Parameters) (σ : LaunchIndex p) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    ¬ label.2.val < σ.val}

theorem futurePlayerRoundLabel_time_ge (p : Parameters) (σ : LaunchIndex p)
    (label : FuturePlayerRoundLabel p σ) : σ.val ≤ label.1.2.val :=
  le_of_not_gt label.2

theorem futurePlayerRoundLabel_iff_time_ge (p : Parameters)
    (σ : LaunchIndex p) (label : FuturePlayerRoundLabel p σ) :
    (¬ label.1.2.val < σ.val) ↔ σ.val ≤ label.1.2.val := by
  constructor
  · intro h
    exact le_of_not_gt h
  · exact not_lt_of_ge

/-- Strict-past original player-round scalars. -/
abbrev PastPlayerRoundScalars (p : Parameters) (σ : LaunchIndex p) :=
  PastPlayerRoundLabel p σ → Scalar

/-- The whole future original player-round scalar vector. -/
abbrev FuturePlayerRoundScalars (p : Parameters) (σ : LaunchIndex p) :=
  FuturePlayerRoundLabel p σ → Scalar

/-- All existing private coordinates and all separate target scalars, paired
with exactly the strict-past player-round scalar array. -/
abbrev SidePast (p : Parameters) (σ : LaunchIndex p) :=
  PrivateSourceStreams.PrivateCoordinates p ×
    (PastPlayerRoundScalars p σ × CoordinatorTargetScalars p)

/-- Literal product law of the original strict-past player-round scalars. -/
noncomputable def pastPlayerRoundScalarLaw (p : Parameters)
    (σ : LaunchIndex p) : Measure (PastPlayerRoundScalars p σ) :=
  Measure.pi (fun _ : PastPlayerRoundLabel p σ =>
    ContinuousCategorical.uniform)

instance pastPlayerRoundScalarLaw_probability (p : Parameters)
    (σ : LaunchIndex p) : IsProbabilityMeasure (pastPlayerRoundScalarLaw p σ) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : PastPlayerRoundLabel p σ =>
      ContinuousCategorical.uniform))
  infer_instance

/-- Literal continuous product law of every original player-round scalar at
or after the source index.  At `σ = T`, its label subtype is empty. -/
noncomputable def futurePlayerRoundScalarLaw (p : Parameters)
    (σ : LaunchIndex p) : Measure (FuturePlayerRoundScalars p σ) :=
  Measure.pi (fun _ : FuturePlayerRoundLabel p σ =>
    ContinuousCategorical.uniform)

instance futurePlayerRoundScalarLaw_probability (p : Parameters)
    (σ : LaunchIndex p) : IsProbabilityMeasure (futurePlayerRoundScalarLaw p σ) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : FuturePlayerRoundLabel p σ =>
      ContinuousCategorical.uniform))
  infer_instance

/-- Literal side/past product law, keeping the original private product and
the separate target product unchanged. -/
noncomputable def sidePastLaw (p : Parameters)
    (σ : LaunchIndex p) : Measure (SidePast p σ) :=
  (PrivateSourceStreams.privateCoordinatesLaw p).prod
    ((pastPlayerRoundScalarLaw p σ).prod
      (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p))

instance sidePastLaw_probability (p : Parameters) (σ : LaunchIndex p) :
    IsProbabilityMeasure (sidePastLaw p σ) := by
  dsimp [sidePastLaw]
  infer_instance

/-- Split the original player-round array by the source calendar index using
Mathlib's dependent-product subtype equivalence. -/
def playerRoundLaunchSplitEquiv (p : Parameters)
    (σ : LaunchIndex p) :
    BootstrapPrivateRoundStreams.PlayerRoundScalars p ≃ᵐ
      (PastPlayerRoundScalars p σ × FuturePlayerRoundScalars p σ) :=
  MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
      BootstrapPrivateRoundStreams.Scalar)
    (fun label => label.2.val < σ.val)

/-- The split copies each original scalar into the unique subtype containing
its unchanged `(player, calendar-round)` label. -/
theorem playerRoundLaunchSplitEquiv_past (p : Parameters)
    (σ : LaunchIndex p) (x : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (label : PastPlayerRoundLabel p σ) :
    (playerRoundLaunchSplitEquiv p σ x).1 label = x label.1 := by
  change x label.1 = x label.1
  rfl

theorem playerRoundLaunchSplitEquiv_future (p : Parameters)
    (σ : LaunchIndex p) (x : BootstrapPrivateRoundStreams.PlayerRoundScalars p)
    (label : FuturePlayerRoundLabel p σ) :
    (playerRoundLaunchSplitEquiv p σ x).2 label = x label.1 := by
  change x label.1 = x label.1
  rfl

/-- The player-round split preserves the original genuine `[0,1)` product law,
including both endpoint subtypes. -/
theorem measurePreserving_playerRoundLaunchSplit (p : Parameters)
    (σ : LaunchIndex p) :
    MeasurePreserving (playerRoundLaunchSplitEquiv p σ)
      (BootstrapPrivateRoundStreams.playerRoundScalarLaw p)
      ((pastPlayerRoundScalarLaw p σ).prod
        (futurePlayerRoundScalarLaw p σ)) := by
  exact measurePreserving_piEquivPiSubtypeProd
    (fun _ : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
      ContinuousCategorical.uniform)
    (fun label => label.2.val < σ.val)

/-- Split the entire existing extended private array into the permitted
side/past factor and the whole future player-round scalar factor.  The inverse
is the literal product reconstruction from the unchanged labels. -/
def extendedPrivateLaunchSplitEquiv (p : Parameters)
    (σ : LaunchIndex p) :
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p ≃ᵐ
      (SidePast p σ × FuturePlayerRoundScalars p σ) := by
  let eRoundTarget : MeasurableEquiv
      (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
        CoordinatorTargetScalars p)
      ((PastPlayerRoundScalars p σ × CoordinatorTargetScalars p) ×
        FuturePlayerRoundScalars p σ) :=
    ((MeasurableEquiv.prodCongr (playerRoundLaunchSplitEquiv p σ)
      (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc).trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
          MeasurableEquiv.prodComm).trans MeasurableEquiv.prodAssoc.symm
  exact (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (PrivateSourceStreams.PrivateCoordinates p))
      eRoundTarget).trans MeasurableEquiv.prodAssoc.symm

/-- The split leaves every original follower block triple and the separate
coordinator-J scalar in the first side coordinate. -/
theorem extendedPrivateLaunchSplitEquiv_private (p : Parameters)
    (σ : LaunchIndex p)
    (z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateLaunchSplitEquiv p σ z).1.1 = z.1 := rfl

/-- Every strict-past scalar in the split is the corresponding original
`(player, round)` scalar. -/
theorem extendedPrivateLaunchSplitEquiv_past (p : Parameters)
    (σ : LaunchIndex p)
    (z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (label : PastPlayerRoundLabel p σ) :
    (extendedPrivateLaunchSplitEquiv p σ z).1.2.1 label =
      z.2.1 label.1 := by
  change (playerRoundLaunchSplitEquiv p σ z.2.1).1 label = z.2.1 label.1
  exact playerRoundLaunchSplitEquiv_past p σ z.2.1 label

/-- Every future scalar in the split is the corresponding original
`(player, round)` scalar. -/
theorem extendedPrivateLaunchSplitEquiv_future (p : Parameters)
    (σ : LaunchIndex p)
    (z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (label : FuturePlayerRoundLabel p σ) :
    (extendedPrivateLaunchSplitEquiv p σ z).2 label = z.2.1 label.1 := by
  change (playerRoundLaunchSplitEquiv p σ z.2.1).2 label = z.2.1 label.1
  exact playerRoundLaunchSplitEquiv_future p σ z.2.1 label

/-- All separate coordinator-target scalars remain in the side factor. -/
theorem extendedPrivateLaunchSplitEquiv_targets (p : Parameters)
    (σ : LaunchIndex p)
    (z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateLaunchSplitEquiv p σ z).1.2.2 = z.2.2 := rfl

/-- Exact inverse coordinate identity for the block triples and coordinator-J
scalar. -/
theorem extendedPrivateLaunchSplitEquiv_symm_private (p : Parameters)
    (σ : LaunchIndex p) (w : SidePast p σ × FuturePlayerRoundScalars p σ) :
    ((extendedPrivateLaunchSplitEquiv p σ).symm w).1 = w.1.1 := by
  have h := congrArg (fun z : SidePast p σ × FuturePlayerRoundScalars p σ =>
    z.1.1) ((extendedPrivateLaunchSplitEquiv p σ).apply_symm_apply w)
  simpa only [extendedPrivateLaunchSplitEquiv_private] using h

/-- Exact inverse identity for every strict-past player-round scalar. -/
theorem extendedPrivateLaunchSplitEquiv_symm_past (p : Parameters)
    (σ : LaunchIndex p) (w : SidePast p σ × FuturePlayerRoundScalars p σ)
    (label : PastPlayerRoundLabel p σ) :
    ((extendedPrivateLaunchSplitEquiv p σ).symm w).2.1 label.1 =
      w.1.2.1 label := by
  have h := congrArg (fun z : SidePast p σ × FuturePlayerRoundScalars p σ =>
    z.1.2.1 label) ((extendedPrivateLaunchSplitEquiv p σ).apply_symm_apply w)
  simpa only [extendedPrivateLaunchSplitEquiv_past] using h

/-- Exact inverse identity for every future player-round scalar. -/
theorem extendedPrivateLaunchSplitEquiv_symm_future (p : Parameters)
    (σ : LaunchIndex p) (w : SidePast p σ × FuturePlayerRoundScalars p σ)
    (label : FuturePlayerRoundLabel p σ) :
    ((extendedPrivateLaunchSplitEquiv p σ).symm w).2.1 label.1 =
      w.2 label := by
  have h := congrArg (fun z : SidePast p σ × FuturePlayerRoundScalars p σ =>
    z.2 label) ((extendedPrivateLaunchSplitEquiv p σ).apply_symm_apply w)
  simpa only [extendedPrivateLaunchSplitEquiv_future] using h

/-- Exact inverse identity for all coordinator-target scalars. -/
theorem extendedPrivateLaunchSplitEquiv_symm_targets (p : Parameters)
    (σ : LaunchIndex p) (w : SidePast p σ × FuturePlayerRoundScalars p σ) :
    ((extendedPrivateLaunchSplitEquiv p σ).symm w).2.2 = w.1.2.2 := by
  have h := congrArg (fun z : SidePast p σ × FuturePlayerRoundScalars p σ =>
    z.1.2.2) ((extendedPrivateLaunchSplitEquiv p σ).apply_symm_apply w)
  simpa only [extendedPrivateLaunchSplitEquiv_targets] using h

/-- The source extended-private law pushes forward to the exact independent
side/past and whole-future product. -/
theorem measurePreserving_extendedPrivateLaunchSplit (p : Parameters)
    (σ : LaunchIndex p) :
    MeasurePreserving (extendedPrivateLaunchSplitEquiv p σ)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      ((sidePastLaw p σ).prod (futurePlayerRoundScalarLaw p σ)) := by
  let μPast := pastPlayerRoundScalarLaw p σ
  let μFuture := futurePlayerRoundScalarLaw p σ
  let μTarget := BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p
  let μPrivate := PrivateSourceStreams.privateCoordinatesLaw p
  have hRound := measurePreserving_playerRoundLaunchSplit p σ
  have hTarget : MeasurePreserving id μTarget μTarget := MeasurePreserving.id _
  have hRoundTarget := hRound.prod hTarget
  have hAssoc := measurePreserving_prodAssoc μPast μFuture μTarget
  have hSwap : MeasurePreserving Prod.swap (μFuture.prod μTarget)
      (μTarget.prod μFuture) := Measure.measurePreserving_swap
  have hAssocBack := (measurePreserving_prodAssoc μPast μTarget μFuture).symm
  have hReorder := hAssocBack.comp <|
    ((MeasurePreserving.id μPast).prod hSwap).comp (hAssoc.comp hRoundTarget)
  have hPrivate := (MeasurePreserving.id μPrivate).prod hReorder
  have hOuter := (measurePreserving_prodAssoc μPrivate (μPast.prod μTarget)
    μFuture).symm.comp hPrivate
  change MeasurePreserving (extendedPrivateLaunchSplitEquiv p σ)
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
    ((sidePastLaw p σ).prod μFuture)
  convert hOuter using 1 <;> rfl

/-- At the sentinel source index, no original player-round label lies in the
future subtype. -/
def terminalLaunchIndex (p : Parameters) : LaunchIndex p :=
  ⟨p.T, Nat.lt_succ_self _⟩

theorem futurePlayerRoundLabel_at_terminal_isEmpty (p : Parameters) :
    IsEmpty (FuturePlayerRoundLabel p (terminalLaunchIndex p)) := by
  refine ⟨fun label => ?_⟩
  have hround := label.1.2.isLt
  exact label.2 hround

/-- The exact existing fixed-row input assembled from the original
`inputOfCoordinates` constructor. -/
def actualInput (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Input p :=
  ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
    (ids, (row, coordinates))

/-- The existing source launch round shifted by one into `Fin (T + 1)`. -/
def actualLaunchIndex (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    LaunchIndex p :=
  ⟨ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta coordinates) - 1, by
        have hb := ReferenceInitializationRun.launchRound_bounds
          (actualInput p ids row rewards C_star C_h eta coordinates)
        omega⟩

theorem actualLaunchIndex_source_shift (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (actualLaunchIndex p ids row rewards C_star C_h eta coordinates).val =
      ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta coordinates) - 1 := rfl

theorem actualLaunchIndex_bounds (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    0 ≤ (actualLaunchIndex p ids row rewards C_star C_h eta coordinates).val ∧
      (actualLaunchIndex p ids row rewards C_star C_h eta coordinates).val ≤ p.T := by
  have hlt := (actualLaunchIndex p ids row rewards C_star C_h eta coordinates).isLt
  omega

theorem actualLaunchIndex_source_eq (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (σ : LaunchIndex p) :
    actualLaunchIndex p ids row rewards C_star C_h eta coordinates = σ ↔
      ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta coordinates) = σ.val + 1 := by
  have hb := ReferenceInitializationRun.launchRound_bounds
    (actualInput p ids row rewards C_star C_h eta coordinates)
  simp only [Fin.ext_iff, actualLaunchIndex]
  omega

/-- The existing launch rule assigns the same source sentinel when the
stopped output has no crossing. -/
theorem source_no_launch_sentinel (p : Parameters)
    (x : ReferenceInitializationRun.Input p)
    (hcross : (ReferenceInitializationRun.output x).crossing.isSome = false) :
    ReferenceInitializationRun.launchRound x = p.T + 1 := by
  simp [ReferenceInitializationRun.launchRound, hcross]

/-- A crossing at the final calendar boundary also has source value `T+1`,
the same exact sentinel as no launch. -/
theorem source_terminal_crossing_sentinel (p : Parameters)
    (x : ReferenceInitializationRun.Input p)
    (hcross : (ReferenceInitializationRun.output x).crossing.isSome = true)
    (hboundary : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed = p.T) :
    ReferenceInitializationRun.launchRound x = p.T + 1 := by
  simp [ReferenceInitializationRun.launchRound, hcross, hboundary]

theorem actualLaunchIndex_sentinel (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hsource : ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta coordinates) = p.T + 1) :
    actualLaunchIndex p ids row rewards C_star C_h eta coordinates =
      terminalLaunchIndex p := by
  apply Fin.ext
  simp only [actualLaunchIndex, terminalLaunchIndex, Fin.val_mk]
  omega

/-- Reconstruct an extended private point from side/past and an arbitrary
whole-future array. -/
def extendedPrivateFromSidePastFuture (p : Parameters)
    (σ : LaunchIndex p) (side : SidePast p σ)
    (future : FuturePlayerRoundScalars p σ) :
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p :=
  (extendedPrivateLaunchSplitEquiv p σ).symm (side, future)

/-- A fixed genuine scalar completes only the event evaluator's missing
future coordinates. -/
def eventCompletionScalar : BootstrapPrivateRoundStreams.Scalar :=
  ⟨0, by norm_num⟩

def completedExtendedPrivate (p : Parameters) (σ : LaunchIndex p)
    (side : SidePast p σ) :
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p :=
  extendedPrivateFromSidePastFuture p σ side (fun _ => eventCompletionScalar)

theorem measurable_completedExtendedPrivate (p : Parameters)
    (σ : LaunchIndex p) : Measurable (completedExtendedPrivate p σ) := by
  exact (extendedPrivateLaunchSplitEquiv p σ).symm.measurable.comp
    (measurable_id.prodMk measurable_const)

/-- The event functional of the permitted side/past view, evaluated by the
fixed measurable completion of future private scalars. -/
def launchEventAt (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p) :
    SidePast p σ → Bool := fun side =>
      decide (ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta
          (completedExtendedPrivate p σ side)) = σ.val + 1)

theorem measurable_launchEventAt (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p) :
    Measurable (launchEventAt p ids row rewards C_star C_h eta σ) := by
  have hcoords := measurable_completedExtendedPrivate p σ
  have hinput : Measurable (fun side : SidePast p σ =>
      (ids, (row, completedExtendedPrivate p σ side))) :=
    measurable_const.prodMk (measurable_const.prodMk hcoords)
  exact (measurable_of_countable (fun n : ℕ => decide (n = σ.val + 1))).comp
    ((ReferenceInitializationMeasurability.measurable_launchRound
      p C_star C_h eta rewards).comp hinput)

/-- A launch sublevel event depends only on the existing strict-prefix input.
This helper follows the accepted source lemma at both thresholds used below. -/
private theorem launchRound_event_eq_of_sublevels (p : Parameters)
    (σ : LaunchIndex p) (x y : ReferenceInitializationRun.Input p)
    (hminus : ReferenceInitializationRun.launchRound x ≤ σ.val ↔
      ReferenceInitializationRun.launchRound y ≤ σ.val)
    (hplus : ReferenceInitializationRun.launchRound x ≤ σ.val + 1 ↔
      ReferenceInitializationRun.launchRound y ≤ σ.val + 1) :
    decide (ReferenceInitializationRun.launchRound x = σ.val + 1) =
      decide (ReferenceInitializationRun.launchRound y = σ.val + 1) := by
  have hevent : ReferenceInitializationRun.launchRound x = σ.val + 1 ↔
      ReferenceInitializationRun.launchRound y = σ.val + 1 := by
    constructor
    · intro hx
      have hyplus := hplus.mp (by omega)
      have hxnot : ¬ ReferenceInitializationRun.launchRound x ≤ σ.val := by omega
      have hynot : ¬ ReferenceInitializationRun.launchRound y ≤ σ.val :=
        fun hy => hxnot (hminus.mpr hy)
      omega
    · intro hy
      have hxplus := hplus.mpr (by omega)
      have hynot : ¬ ReferenceInitializationRun.launchRound y ≤ σ.val := by omega
      have hxnot : ¬ ReferenceInitializationRun.launchRound x ≤ σ.val :=
        fun hx => hynot (hminus.mp hx)
      omega
  by_cases hx : ReferenceInitializationRun.launchRound x = σ.val + 1
  · have hy := hevent.mp hx
    simp [hx, hy]
  · have hy : ReferenceInitializationRun.launchRound y ≠ σ.val + 1 :=
      fun hy => hx (hevent.mpr hy)
    simp [hx, hy]

/-- Two arbitrary completions of the same side/past view produce the same
actual launch event.  The hypotheses to the accepted prefix theorem are
derived from exact inverse-coordinate identities. -/
theorem launchEvent_completion_invariant (p : Parameters)
    (ids : IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (side : SidePast p σ) (future₁ future₂ : FuturePlayerRoundScalars p σ) :
    decide (ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta
        (extendedPrivateFromSidePastFuture p σ side future₁)) = σ.val + 1) =
    decide (ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta
        (extendedPrivateFromSidePastFuture p σ side future₂)) = σ.val + 1) := by
  let x := actualInput p ids row rewards C_star C_h eta
    (extendedPrivateFromSidePastFuture p σ side future₁)
  let y := actualInput p ids row rewards C_star C_h eta
    (extendedPrivateFromSidePastFuture p σ side future₂)
  have hprefix {n : ℕ} (hn : n ≤ σ.val + 1) :
      ReferenceInitializationCausality.launchPrefixInputEq x y n := by
    dsimp [ReferenceInitializationCausality.launchPrefixInputEq, x, y,
      actualInput, ReferenceInitializationMeasurability.inputOfCoordinates]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro t ht
      constructor
      · intro u
        rfl
      · rfl
    · intro s hs
      constructor
      · intro j
        rfl
      · rfl
    · intro i t ht
      have htime : t.val < σ.val := by omega
      let label : PastPlayerRoundLabel p σ := ⟨(i, t), htime⟩
      exact (extendedPrivateLaunchSplitEquiv_symm_past p σ
        (side, future₁) label).trans
          (extendedPrivateLaunchSplitEquiv_symm_past p σ
            (side, future₂) label).symm
  have hminus := launchSublevel_eq_of_launchPrefixInputEq x y
    (n := σ.val) (by omega) (hprefix (n := σ.val) (by omega))
  have hplus := launchSublevel_eq_of_launchPrefixInputEq x y
    (n := σ.val + 1) (by have := σ.isLt; omega)
      (hprefix (n := σ.val + 1) (by omega))
  exact launchRound_event_eq_of_sublevels p σ x y hminus hplus

/-- The produced event functional equals the actual source launch event for
every original extended-private coordinate array. -/
theorem launchEventAt_eq_actual (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    launchEventAt p ids row rewards C_star C_h eta σ
        (extendedPrivateLaunchSplitEquiv p σ coordinates).1 =
      decide (ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta coordinates) = σ.val + 1) := by
  let w := (extendedPrivateLaunchSplitEquiv p σ coordinates).1
  let future := (extendedPrivateLaunchSplitEquiv p σ coordinates).2
  have hinv := launchEvent_completion_invariant p ids row rewards C_star C_h eta σ
    w (fun _ => eventCompletionScalar) future
  have hrec : extendedPrivateFromSidePastFuture p σ w future = coordinates := by
    apply (extendedPrivateLaunchSplitEquiv p σ).injective
    exact (extendedPrivateLaunchSplitEquiv p σ).apply_symm_apply
      ((extendedPrivateLaunchSplitEquiv p σ) coordinates)
  change decide (ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta
        (extendedPrivateFromSidePastFuture p σ w (fun _ => eventCompletionScalar))) =
      σ.val + 1) = _
  rw [hinv, hrec]

/-- The terminal future is genuinely a singleton function space over an empty
subtype, with no fabricated `Fin T` scalar. -/
theorem futurePlayerRoundScalars_at_terminal_subsingleton (p : Parameters) :
    Subsingleton (FuturePlayerRoundScalars p (terminalLaunchIndex p)) := by
  let hlabels := futurePlayerRoundLabel_at_terminal_isEmpty p
  exact ⟨fun f g => funext (fun label => False.elim (hlabels.false label))⟩

theorem source_sentinel_has_empty_future (p : Parameters) :
    IsEmpty (FuturePlayerRoundLabel p (terminalLaunchIndex p)) :=
  futurePlayerRoundLabel_at_terminal_isEmpty p

/-- Exact launch-event factorization for the actual source launch, fixed
complete row, original private law, and complete future scalar vector. -/
theorem actual_launch_event_factorization
    (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (SidePast p σ)) (hA : MeasurableSet A)
    (B : Set (FuturePlayerRoundScalars p σ)) (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      {z | ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
        (extendedPrivateLaunchSplitEquiv p σ z).1 ∈ A ∧
        (extendedPrivateLaunchSplitEquiv p σ z).2 ∈ B} =
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      {z | ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
        (extendedPrivateLaunchSplitEquiv p σ z).1 ∈ A} *
      (futurePlayerRoundScalarLaw p σ) B := by
  let split := extendedPrivateLaunchSplitEquiv p σ
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let μSide := sidePastLaw p σ
  let μFuture := futurePlayerRoundScalarLaw p σ
  let E : Set (SidePast p σ) :=
    {w | launchEventAt p ids row rewards C_star C_h eta σ w = true}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage
      (measurable_launchEventAt p ids row rewards C_star C_h eta σ)
  have hsplit := measurePreserving_extendedPrivateLaunchSplit p σ
  have hproduct := hsplit.map_eq
  have hset :
      {z | ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
        (split z).1 ∈ A ∧ (split z).2 ∈ B} =
      (split ⁻¹' ((A ∩ E) ×ˢ B)) := by
    ext z
    change (ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
      (split z).1 ∈ A ∧ (split z).2 ∈ B) ↔
      ((split z).1 ∈ A ∧
        launchEventAt p ids row rewards C_star C_h eta σ (split z).1 = true) ∧
        (split z).2 ∈ B
    have hevent := launchEventAt_eq_actual p ids row rewards C_star C_h eta σ z
    change launchEventAt p ids row rewards C_star C_h eta σ (split z).1 =
      decide (ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1) at hevent
    rw [hevent]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hlaunch, hA', hB'⟩
      exact ⟨⟨hA', hlaunch⟩, hB'⟩
    · rintro ⟨⟨hA', hlaunch⟩, hB'⟩
      exact ⟨hlaunch, hA', hB'⟩
  have hfactor : μ (split ⁻¹' ((A ∩ E) ×ˢ B)) =
      μSide (A ∩ E) * μFuture B := by
    calc
      μ (split ⁻¹' ((A ∩ E) ×ˢ B)) = (μ.map split) ((A ∩ E) ×ˢ B) := by
        rw [Measure.map_apply_of_aemeasurable split.measurable.aemeasurable
          ((hA.inter hE).prod hB)]
      _ = (μSide.prod μFuture) ((A ∩ E) ×ˢ B) := by rw [hproduct]
      _ = μSide (A ∩ E) * μFuture B := Measure.prod_prod _ _
  have hmassSet :
      {z | ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
        (split z).1 ∈ A} = (split ⁻¹' ((A ∩ E) ×ˢ Set.univ)) := by
    ext z
    have hevent := launchEventAt_eq_actual p ids row rewards C_star C_h eta σ z
    change launchEventAt p ids row rewards C_star C_h eta σ (split z).1 =
      decide (ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1) at hevent
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
      Set.mem_inter_iff, Set.mem_univ, and_true, E]
    have hprop :
        (ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1) ↔
          launchEventAt p ids row rewards C_star C_h eta σ (split z).1 = true := by
      rw [hevent]
      simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hlaunch, hA'⟩
      exact ⟨hA', hprop.mp hlaunch⟩
    · rintro ⟨hA', hlaunch⟩
      exact ⟨hprop.mpr hlaunch, hA'⟩
  have hmass : μ {z | ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 ∧
        (split z).1 ∈ A} = μSide (A ∩ E) := by
    rw [hmassSet]
    calc
      μ (split ⁻¹' ((A ∩ E) ×ˢ Set.univ)) =
          (μ.map split) ((A ∩ E) ×ˢ Set.univ) := by
            rw [Measure.map_apply_of_aemeasurable split.measurable.aemeasurable
              ((hA.inter hE).prod MeasurableSet.univ)]
      _ = (μSide.prod μFuture) ((A ∩ E) ×ˢ Set.univ) := by rw [hproduct]
      _ = μSide (A ∩ E) * μFuture Set.univ := Measure.prod_prod _ _
      _ = μSide (A ∩ E) := by rw [(futurePlayerRoundScalarLaw_probability p σ).measure_univ, mul_one]
  rw [hset, hfactor, ← hmass]

/-- Bounded measurable side/past and future tests factor at the actual launch.
The future test is of the entire original continuous scalar vector. -/
theorem actual_launch_bounded_test_integral_factorization
    (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (f : SidePast p σ → ℝ) (hf : Measurable f) (Cf : ℝ)
    (_hCf : ∀ x, ‖f x‖ ≤ Cf)
    (g : FuturePlayerRoundScalars p σ → ℝ) (hg : Measurable g) (Cg : ℝ)
    (_hCg : ∀ y, ‖g y‖ ≤ Cg) :
    ∫ z, (if ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 then
          f (extendedPrivateLaunchSplitEquiv p σ z).1 *
            g (extendedPrivateLaunchSplitEquiv p σ z).2 else 0)
        ∂(BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      (∫ w, (if launchEventAt p ids row rewards C_star C_h eta σ w = true
          then f w else 0) ∂(sidePastLaw p σ)) *
        ∫ y, g y ∂(futurePlayerRoundScalarLaw p σ) := by
  let split := extendedPrivateLaunchSplitEquiv p σ
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let μSide := sidePastLaw p σ
  let μFuture := futurePlayerRoundScalarLaw p σ
  let fEvent : SidePast p σ → ℝ := fun w =>
    if launchEventAt p ids row rewards C_star C_h eta σ w = true then f w else 0
  let H : SidePast p σ × FuturePlayerRoundScalars p σ → ℝ :=
    fun z => fEvent z.1 * g z.2
  have hEventSet : MeasurableSet
      {w | launchEventAt p ids row rewards C_star C_h eta σ w = true} :=
    (measurableSet_singleton true).preimage
      (measurable_launchEventAt p ids row rewards C_star C_h eta σ)
  have hfEvent : Measurable fEvent :=
    Measurable.ite hEventSet hf measurable_const
  have hH : Measurable H :=
    (hfEvent.comp measurable_fst).mul (hg.comp measurable_snd)
  have hsplit := measurePreserving_extendedPrivateLaunchSplit p σ
  have hintegrand : (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      if ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1 then
        f (split z).1 * g (split z).2 else 0) = fun z => H (split z) := by
    funext z
    have hevent := launchEventAt_eq_actual p ids row rewards C_star C_h eta σ z
    simp only [H, fEvent]
    by_cases h : ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1
    · rw [hevent]
      simp [h]
    · rw [hevent]
      simp [h]
  calc
    _ = ∫ z, H (split z) ∂μ := by rw [hintegrand]
    _ = ∫ z, H z ∂(μSide.prod μFuture) :=
      hsplit.integral_comp split.measurableEmbedding H
    _ = (∫ w, fEvent w ∂μSide) * ∫ y, g y ∂μFuture :=
      integral_prod_mul fEvent g

/-- The event-restricted whole future marginal is exactly the original future
product whenever the actual launch-index event has positive mass. -/
theorem actual_launch_normalized_future_marginal
    (p : Parameters) (ids : IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (hpos : 0 < (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      {z | ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1})
    (B : Set (FuturePlayerRoundScalars p σ)) (hB : MeasurableSet B) :
    ((((BootstrapPrivateRoundStreams.extendedPrivateLaw p).restrict
      {z | ReferenceInitializationRun.launchRound
        (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1}).map
        (fun z => (extendedPrivateLaunchSplitEquiv p σ z).2)) B) /
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
        {z | ReferenceInitializationRun.launchRound
          (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1} =
      (futurePlayerRoundScalarLaw p σ) B := by
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let split := extendedPrivateLaunchSplitEquiv p σ
  let E : Set (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
    {z | ReferenceInitializationRun.launchRound
      (actualInput p ids row rewards C_star C_h eta z) = σ.val + 1}
  have hproj : Measurable (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (split z).2) := measurable_snd.comp split.measurable
  have hmap : (μ.restrict E).map (fun z => (split z).2) B =
      μ {z | z ∈ E ∧ (split z).2 ∈ B} := by
    rw [Measure.map_apply_of_aemeasurable hproj.aemeasurable hB,
      Measure.restrict_apply (hproj hB)]
    congr 1
    ext z
    simp [E, Set.mem_inter_iff, and_comm]
  have hjoint := actual_launch_event_factorization p ids row rewards C_star C_h eta σ
    Set.univ MeasurableSet.univ B hB
  have hjoint' : μ {z | z ∈ E ∧ (split z).2 ∈ B} = μ E *
      futurePlayerRoundScalarLaw p σ B := by
    simpa [μ, E, split] using hjoint
  calc
    (μ.restrict E).map (fun z => (split z).2) B / μ E =
        (μ E * futurePlayerRoundScalarLaw p σ B) / μ E := by rw [hmap, hjoint']
    _ = futurePlayerRoundScalarLaw p σ B := by
      rw [mul_comm (μ E) (futurePlayerRoundScalarLaw p σ B)]
      exact ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top μ E)

end Bandits.Support.ReferenceLaunchPrivateRoundLaw

end
