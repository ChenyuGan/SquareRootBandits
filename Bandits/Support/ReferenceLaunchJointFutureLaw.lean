/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaunchRowLaw
public import Bandits.Support.ReferenceLaunchPrivateRoundLaw

/-!
# Joint original row and player-round future at the actual reference launch

The original law is literally `extendedPrivateLaw.prod completeRowMeasure`.
The accepted calendar and private-coordinate equivalences, followed only by
product association and commutation, split it into joint past and joint future.
Every forward-ID bit, continuous control and affine coordinate remains in its
original calendar entry; every private player-round scalar keeps its label.
The enlarged side retains all block triples, the separate coordinator scalar,
all targets, and exactly the player-round times strictly before the index.
No freshness of the retained block or target coordinates is asserted.

Launch-event invariance is proved from the actual source prefix theorem for
arbitrary simultaneous row and private future completions. Constant completions
only evaluate that measurable event. They do not define a physical execution.
The results concern the whole joint future, before complete numerical row
revelation, including all launch-round coordinates and the genuine empty future
at the source sentinel. They are internal constructions, not source anchors or
manuscript closure.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,123-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePrelaunchFollower
open scoped ENNReal

namespace Bandits.Support.ReferenceLaunchJointFutureLaw

abbrev Parameters := ConstructorDimensions.Parameters

abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)

/-- The existing original private/row carrier, in that order. -/
abbrev OriginalCoordinates (p : Parameters) :=
  ExtendedPrivateCoordinates p × CompletePublicTable.CompleteRow p

/-- All retained private side coordinates and both strict-past arrays. -/
abbrev JointPast (p : Parameters) (σ : LaunchIndex p) :=
  ReferenceLaunchPrivateRoundLaw.SidePast p σ × PastArray p σ

/-- Entire future calendar entries paired with all future player-round scalars. -/
abbrev JointFuture (p : Parameters) (σ : LaunchIndex p) :=
  FutureArray p σ × ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ

/-- The original continuous product, without resampling or extra randomness. -/
def originalLaw (p : Parameters) : Measure (OriginalCoordinates p) :=
  (extendedPrivateLaw p).prod (completeRowMeasure p)

/-- Literal joint side/past product. -/
def jointPastLaw (p : Parameters) (σ : LaunchIndex p) : Measure (JointPast p σ) :=
  (ReferenceLaunchPrivateRoundLaw.sidePastLaw p σ).prod (pastArrayLaw p σ)

/-- Literal product of the two entire future arrays. -/
def jointFutureLaw (p : Parameters) (σ : LaunchIndex p) : Measure (JointFuture p σ) :=
  (futureArrayLaw p σ).prod
    (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)

instance originalLaw_probability (p : Parameters) : IsProbabilityMeasure (originalLaw p) := by
  dsimp [originalLaw]
  infer_instance

instance jointPastLaw_probability (p : Parameters) (σ : LaunchIndex p) :
    IsProbabilityMeasure (jointPastLaw p σ) := by
  dsimp [jointPastLaw]
  infer_instance

instance jointFutureLaw_probability (p : Parameters) (σ : LaunchIndex p) :
    IsProbabilityMeasure (jointFutureLaw p σ) := by
  dsimp [jointFutureLaw]
  infer_instance

/-- Only product association and commutation, after the two accepted splits. -/
def regroupEquiv (p : Parameters) (σ : LaunchIndex p) :
    ((ReferenceLaunchPrivateRoundLaw.SidePast p σ ×
        ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ) ×
      (PastArray p σ × FutureArray p σ)) ≃ᵐ
        (JointPast p σ × JointFuture p σ) :=
  (MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc))).trans
        MeasurableEquiv.prodAssoc.symm

/-- Explicit split of the original coordinates, with the complete future kept
as one joint factor rather than two separate marginal assertions. -/
def jointSplitEquiv (p : Parameters) (σ : LaunchIndex p) :
    OriginalCoordinates p ≃ᵐ (JointPast p σ × JointFuture p σ) :=
  (MeasurableEquiv.prodCongr
    (ReferenceLaunchPrivateRoundLaw.extendedPrivateLaunchSplitEquiv p σ)
    ((calendarizeRowEquiv p).trans (calendarSplitEquiv p σ))).trans
      (regroupEquiv p σ)

/-- The regrouping preserves exactly the four original product factors. -/
theorem measurePreserving_regroup (p : Parameters) (σ : LaunchIndex p) :
    MeasurePreserving (regroupEquiv p σ)
      (((ReferenceLaunchPrivateRoundLaw.sidePastLaw p σ).prod
        (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)).prod
          ((pastArrayLaw p σ).prod (futureArrayLaw p σ)))
      ((jointPastLaw p σ).prod (jointFutureLaw p σ)) := by
  let μS := ReferenceLaunchPrivateRoundLaw.sidePastLaw p σ
  let μU := ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ
  let μP := pastArrayLaw p σ
  let μR := futureArrayLaw p σ
  have h₁ := measurePreserving_prodAssoc μS μU (μP.prod μR)
  have hswap : MeasurePreserving Prod.swap (μU.prod (μP.prod μR))
      ((μP.prod μR).prod μU) := Measure.measurePreserving_swap
  have h₂ := (MeasurePreserving.id μS).prod
    ((measurePreserving_prodAssoc μP μR μU).comp hswap)
  have h₃ := (measurePreserving_prodAssoc μS μP (μR.prod μU)).symm
  convert h₃.comp (h₂.comp h₁) using 1 <;> rfl

/-- Exact preservation of the existing original measure under the joint split. -/
theorem measurePreserving_jointSplit (p : Parameters) (σ : LaunchIndex p) :
    MeasurePreserving (jointSplitEquiv p σ) (originalLaw p)
      ((jointPastLaw p σ).prod (jointFutureLaw p σ)) := by
  have hprivate := ReferenceLaunchPrivateRoundLaw.measurePreserving_extendedPrivateLaunchSplit p σ
  have hrow := (measurePreserving_calendarSplit p σ).comp
    (measurePreserving_calendarizeRow p)
  convert (measurePreserving_regroup p σ).comp (hprivate.prod hrow) using 1 <;> rfl

theorem map_jointSplit (p : Parameters) (σ : LaunchIndex p) :
    (originalLaw p).map (jointSplitEquiv p σ) =
      (jointPastLaw p σ).prod (jointFutureLaw p σ) :=
  (measurePreserving_jointSplit p σ).map_eq

/-- All block triples and the separate coordinator scalar are unchanged. -/
theorem jointSplit_private (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) : (jointSplitEquiv p σ z).1.1.1 = z.1.1 := rfl

/-- Every coordinator target remains in the side factor unchanged. -/
theorem jointSplit_targets (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) : (jointSplitEquiv p σ z).1.1.2.2 = z.1.2.2 := rfl

theorem jointSplit_private_past (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p)
    (label : ReferenceLaunchPrivateRoundLaw.PastPlayerRoundLabel p σ) :
    (jointSplitEquiv p σ z).1.1.2.1 label = z.1.2.1 label.1 :=
  ReferenceLaunchPrivateRoundLaw.extendedPrivateLaunchSplitEquiv_past p σ z.1 label

theorem jointSplit_private_future (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    (jointSplitEquiv p σ z).2.2 label = z.1.2.1 label.1 :=
  ReferenceLaunchPrivateRoundLaw.extendedPrivateLaunchSplitEquiv_future p σ z.1 label

/-- The full original calendar entry, including the entire forward-ID vector
and all affine coordinates, is copied into the strict-past subtype. -/
theorem jointSplit_row_past (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) (t : PastIndex p σ) :
    (jointSplitEquiv p σ z).1.2 t = calendarizeRow p z.2 t.1 := rfl

theorem jointSplit_row_future (p : Parameters) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) (t : FutureIndex p σ) :
    (jointSplitEquiv p σ z).2.1 t = calendarizeRow p z.2 t.1 := rfl

theorem jointSplit_symm_private (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ) :
    ((jointSplitEquiv p σ).symm w).1.1 = w.1.1.1 := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.1.1.1)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_private] using h

theorem jointSplit_symm_targets (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ) :
    ((jointSplitEquiv p σ).symm w).1.2.2 = w.1.1.2.2 := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.1.1.2.2)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_targets] using h

theorem jointSplit_symm_private_past (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ)
    (label : ReferenceLaunchPrivateRoundLaw.PastPlayerRoundLabel p σ) :
    ((jointSplitEquiv p σ).symm w).1.2.1 label.1 = w.1.1.2.1 label := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.1.1.2.1 label)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_private_past] using h

theorem jointSplit_symm_private_future (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    ((jointSplitEquiv p σ).symm w).1.2.1 label.1 = w.2.2 label := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.2.2 label)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_private_future] using h

theorem jointSplit_symm_row_past (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ) (t : PastIndex p σ) :
    calendarizeRow p ((jointSplitEquiv p σ).symm w).2 t.1 = w.1.2 t := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.1.2 t)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_row_past] using h

theorem jointSplit_symm_row_future (p : Parameters) (σ : LaunchIndex p)
    (w : JointPast p σ × JointFuture p σ) (t : FutureIndex p σ) :
    calendarizeRow p ((jointSplitEquiv p σ).symm w).2 t.1 = w.2.1 t := by
  have h := congrArg (fun z : JointPast p σ × JointFuture p σ => z.2.1 t)
    ((jointSplitEquiv p σ).apply_symm_apply w)
  simpa only [jointSplit_row_future] using h

/-- The actual accepted input, with fixed public data and original coordinates. -/
abbrev actualInput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) :=
  ReferenceLaunchRowLaw.actualInput p ids rewards C_star C_h eta z.1 z.2

theorem actualInput_eq_private_input (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) :
    actualInput p ids rewards C_star C_h eta z =
      ReferenceLaunchPrivateRoundLaw.actualInput p ids z.2 rewards C_star C_h eta z.1 := rfl

/-- Compatibility of both accepted launch-index APIs on the original point. -/
theorem launchIndex_compatibility (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) :
    ReferenceLaunchRowLaw.actualLaunchStop p ids rewards C_star C_h eta z =
      ReferenceLaunchPrivateRoundLaw.actualLaunchIndex p ids z.2 rewards C_star C_h eta z.1 := rfl

theorem launchIndex_source_shift (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) :
    (ReferenceLaunchRowLaw.actualLaunchStop p ids rewards C_star C_h eta z).val =
      ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z) - 1 := rfl

theorem launchIndex_source_eq (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) (σ : LaunchIndex p) :
    ReferenceLaunchRowLaw.actualLaunchStop p ids rewards C_star C_h eta z = σ ↔
      ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z) =
        σ.val + 1 :=
  ReferenceLaunchPrivateRoundLaw.actualLaunchIndex_source_eq p ids z.2 rewards C_star C_h eta z.1 σ

theorem terminalLaunchIndex_compatibility (p : Parameters) :
    ReferenceLaunchPrivateRoundLaw.terminalLaunchIndex p = horizonStoppingIndex p := rfl

/-- The common source sentinel is exactly the same index in both APIs. -/
theorem source_sentinel_compatibility (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (z : OriginalCoordinates p) :
    (ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z) =
        p.T + 1) ↔
      (ReferenceLaunchRowLaw.actualLaunchStop p ids rewards C_star C_h eta z =
          horizonStoppingIndex p ∧
        ReferenceLaunchPrivateRoundLaw.actualLaunchIndex p ids z.2 rewards C_star C_h eta z.1 =
          ReferenceLaunchPrivateRoundLaw.terminalLaunchIndex p) := by
  rw [← launchIndex_compatibility, terminalLaunchIndex_compatibility, and_self,
    launchIndex_source_eq]
  rfl

theorem measurable_sourceLaunchRound (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) :
    Measurable (fun z : OriginalCoordinates p =>
      ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z)) :=
  (ReferenceInitializationMeasurability.measurable_launchRound p C_star C_h eta rewards).comp
    (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))

/-- Arbitrary simultaneous completion of the two original future arrays. -/
def coordinatesFromPastFuture (p : Parameters) (σ : LaunchIndex p)
    (past : JointPast p σ) (future : JointFuture p σ) : OriginalCoordinates p :=
  (jointSplitEquiv p σ).symm (past, future)

/-- All inputs read by the accepted source launch prefix agree for two
arbitrary simultaneous completions of the same joint past. -/
theorem launchPrefixInputEq_of_joint_past (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (past : JointPast p σ) (future₁ future₂ : JointFuture p σ)
    {n : ℕ} (hn : n ≤ σ.val + 1) :
    ReferenceInitializationCausality.launchPrefixInputEq
      (actualInput p ids rewards C_star C_h eta
        (coordinatesFromPastFuture p σ past future₁))
      (actualInput p ids rewards C_star C_h eta
        (coordinatesFromPastFuture p σ past future₂)) n := by
  dsimp [ReferenceInitializationCausality.launchPrefixInputEq, actualInput,
    ReferenceLaunchRowLaw.actualInput, ReferenceInitializationMeasurability.inputOfCoordinates,
    coordinatesFromPastFuture]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro t ht
    let q : PastIndex p σ := ⟨t, by omega⟩
    have he := (jointSplit_symm_row_past p σ (past, future₁) q).trans
      (jointSplit_symm_row_past p σ (past, future₂) q).symm
    exact ⟨fun u => congrArg (fun e : CalendarEntry p => e.1 u) he,
      congrArg Prod.snd he⟩
  · intro s _hs
    constructor
    · intro j
      rw [jointSplit_symm_private, jointSplit_symm_private]
    · rw [jointSplit_symm_targets, jointSplit_symm_targets]
  · intro i t ht
    let label : ReferenceLaunchPrivateRoundLaw.PastPlayerRoundLabel p σ :=
      ⟨(i, t), by change t.val < σ.val; omega⟩
    exact (jointSplit_symm_private_past p σ (past, future₁) label).trans
      (jointSplit_symm_private_past p σ (past, future₂) label).symm

/-- Actual source prefix invariance, jointly for EVERY choice of both future
arrays. No stopping-time or freshness premise is assumed. -/
theorem launchEvent_completion_invariant (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (past : JointPast p σ) (future₁ future₂ : JointFuture p σ) :
    decide (ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta
        (coordinatesFromPastFuture p σ past future₁)) = σ.val + 1) =
    decide (ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta
        (coordinatesFromPastFuture p σ past future₂)) = σ.val + 1) := by
  let x := actualInput p ids rewards C_star C_h eta (coordinatesFromPastFuture p σ past future₁)
  let y := actualInput p ids rewards C_star C_h eta (coordinatesFromPastFuture p σ past future₂)
  have hprefix {n : ℕ} (hn : n ≤ σ.val + 1) :
      ReferenceInitializationCausality.launchPrefixInputEq x y n :=
    launchPrefixInputEq_of_joint_past p ids rewards C_star C_h eta σ past future₁ future₂ hn
  have hminus := ReferenceInitializationPrefixInvariance.launchSublevel_eq_of_launchPrefixInputEq
    x y (n := σ.val) (by have := σ.isLt; omega) (hprefix (by omega))
  have hplus := ReferenceInitializationPrefixInvariance.launchSublevel_eq_of_launchPrefixInputEq
    x y (n := σ.val + 1) (by have := σ.isLt; omega) (hprefix le_rfl)
  exact decide_eq_decide.mpr (by change
    ReferenceInitializationRun.launchRound x = σ.val + 1 ↔
      ReferenceInitializationRun.launchRound y = σ.val + 1; omega)

/-- Administrative constant completion used solely to evaluate the event. -/
def eventCompletion (p : Parameters) (σ : LaunchIndex p) : JointFuture p σ :=
  ((fun _ => ReferenceLaunchRowLaw.tailEntry p),
    fun _ => ReferenceLaunchPrivateRoundLaw.eventCompletionScalar)

/-- Measurable functional of precisely the enlarged joint past. -/
def launchEventAt (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p) : JointPast p σ → Bool :=
  fun past => decide (ReferenceInitializationRun.launchRound
    (actualInput p ids rewards C_star C_h eta
      (coordinatesFromPastFuture p σ past (eventCompletion p σ))) = σ.val + 1)

theorem measurable_launchEventAt (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p) :
    Measurable (launchEventAt p ids rewards C_star C_h eta σ) := by
  exact (measurable_of_countable (fun n : ℕ => decide (n = σ.val + 1))).comp
    ((measurable_sourceLaunchRound p ids rewards C_star C_h eta).comp
      ((jointSplitEquiv p σ).symm.measurable.comp
        (measurable_id.prodMk measurable_const)))

theorem launchEventAt_eq_actual (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) :
    launchEventAt p ids rewards C_star C_h eta σ (jointSplitEquiv p σ z).1 =
      decide (ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1) := by
  have h := launchEvent_completion_invariant p ids rewards C_star C_h eta σ
    (jointSplitEquiv p σ z).1 (eventCompletion p σ) (jointSplitEquiv p σ z).2
  change _ = decide (ReferenceInitializationRun.launchRound
    (actualInput p ids rewards C_star C_h eta
      ((jointSplitEquiv p σ).symm (jointSplitEquiv p σ z))) = σ.val + 1) at h
  rw [(jointSplitEquiv p σ).symm_apply_apply] at h
  exact h

theorem launchEventAt_eq_true_iff (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) :
    launchEventAt p ids rewards C_star C_h eta σ (jointSplitEquiv p σ z).1 = true ↔
      ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z) =
        σ.val + 1 := by
  rw [launchEventAt_eq_actual, decide_eq_true_eq]

/-- The event evaluator also agrees pointwise with both accepted launch APIs. -/
theorem launchEventAt_eq_indices (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (z : OriginalCoordinates p) :
    (launchEventAt p ids rewards C_star C_h eta σ (jointSplitEquiv p σ z).1 = true) ↔
      (ReferenceLaunchRowLaw.actualLaunchStop p ids rewards C_star C_h eta z = σ ∧
        ReferenceLaunchPrivateRoundLaw.actualLaunchIndex p ids z.2 rewards C_star C_h eta z.1 = σ) := by
  rw [← launchIndex_compatibility, and_self, launchIndex_source_eq,
    launchEventAt_eq_true_iff]

/-- Joint independence under the original law, for every measurable event of
the entire joint future (including nonrectangular events within that factor). -/
theorem joint_past_future_event_factorization (p : Parameters) (σ : LaunchIndex p)
    (A : Set (JointPast p σ)) (hA : MeasurableSet A)
    (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    originalLaw p ((jointSplitEquiv p σ) ⁻¹' (A ×ˢ B)) =
      jointPastLaw p σ A * jointFutureLaw p σ B := by
  calc
    _ = ((originalLaw p).map (jointSplitEquiv p σ)) (A ×ˢ B) := by
      rw [Measure.map_apply_of_aemeasurable
        (jointSplitEquiv p σ).measurable.aemeasurable (hA.prod hB)]
    _ = ((jointPastLaw p σ).prod (jointFutureLaw p σ)) (A ×ˢ B) := by
      rw [map_jointSplit]
    _ = _ := Measure.prod_prod _ _

/-- The actual launch-and-past event has exactly its joint-past mass. -/
theorem actual_launch_past_event_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (JointPast p σ)) (hA : MeasurableSet A) :
    originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A} =
    jointPastLaw p σ (A ∩ {past | launchEventAt p ids rewards C_star C_h eta σ past = true}) := by
  let E : Set (JointPast p σ) :=
    {past | launchEventAt p ids rewards C_star C_h eta σ past = true}
  have hE : MeasurableSet E := (measurableSet_singleton true).preimage
    (measurable_launchEventAt p ids rewards C_star C_h eta σ)
  have hset : {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A} =
      (jointSplitEquiv p σ) ⁻¹' ((A ∩ E) ×ˢ Set.univ) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff,
      Set.mem_univ, and_true, E, launchEventAt_eq_true_iff]
    exact and_comm
  rw [hset, joint_past_future_event_factorization p σ (A ∩ E) (hA.inter hE)
    Set.univ MeasurableSet.univ, measure_univ, mul_one]

/-- Exact factorization for the actual source launch and an arbitrary event
of the ENTIRE joint future. No positive-mass premise is needed. -/
theorem actual_launch_event_factorization (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (JointPast p σ)) (hA : MeasurableSet A)
    (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A ∧ (jointSplitEquiv p σ z).2 ∈ B} =
    originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A} * jointFutureLaw p σ B := by
  let E : Set (JointPast p σ) :=
    {past | launchEventAt p ids rewards C_star C_h eta σ past = true}
  have hE : MeasurableSet E := (measurableSet_singleton true).preimage
    (measurable_launchEventAt p ids rewards C_star C_h eta σ)
  have hset : {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A ∧ (jointSplitEquiv p σ z).2 ∈ B} =
      (jointSplitEquiv p σ) ⁻¹' ((A ∩ E) ×ˢ B) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff,
      E, launchEventAt_eq_true_iff]
    constructor
    · rintro ⟨hl, ha, hb⟩
      exact ⟨⟨ha, hl⟩, hb⟩
    · rintro ⟨⟨ha, hl⟩, hb⟩
      exact ⟨hl, ha, hb⟩
  rw [hset, joint_past_future_event_factorization p σ (A ∩ E) (hA.inter hE) B hB,
    actual_launch_past_event_mass p ids rewards C_star C_h eta σ A hA]

/-- Bounded measurable tests of joint past and entire joint future factor
at the actual launch. Integrability follows from the stated bounds. -/
theorem actual_launch_bounded_test_integral_factorization
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (f : JointPast p σ → ℝ) (hf : Measurable f) (Cf : ℝ) (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (g : JointFuture p σ → ℝ) (hg : Measurable g) (Cg : ℝ) (hCg : ∀ y, ‖g y‖ ≤ Cg) :
    ∫ z, (if ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 then
      f (jointSplitEquiv p σ z).1 * g (jointSplitEquiv p σ z).2 else 0) ∂(originalLaw p) =
      (∫ past, (if launchEventAt p ids rewards C_star C_h eta σ past = true then
        f past else 0) ∂(jointPastLaw p σ)) * ∫ future, g future ∂(jointFutureLaw p σ) := by
  let fEvent : JointPast p σ → ℝ := fun past =>
    if launchEventAt p ids rewards C_star C_h eta σ past = true then f past else 0
  have hE : MeasurableSet {past | launchEventAt p ids rewards C_star C_h eta σ past = true} :=
    (measurableSet_singleton true).preimage
      (measurable_launchEventAt p ids rewards C_star C_h eta σ)
  have hfEvent : Measurable fEvent := Measurable.ite hE hf measurable_const
  have hfBound : ∀ past, ‖fEvent past‖ ≤ Cf := by
    intro past
    by_cases h : launchEventAt p ids rewards C_star C_h eta σ past = true
    · simpa only [fEvent, ite_eq_left h] using hCf past
    · simpa only [fEvent, ite_eq_right h, norm_zero] using (norm_nonneg (f past)).trans (hCf past)
  have hfInt : Integrable fEvent (jointPastLaw p σ) :=
    Integrable.of_bound hfEvent.aestronglyMeasurable Cf (Filter.Eventually.of_forall hfBound)
  have hgInt : Integrable g (jointFutureLaw p σ) :=
    Integrable.of_bound hg.aestronglyMeasurable Cg (Filter.Eventually.of_forall hCg)
  let H : JointPast p σ × JointFuture p σ → ℝ := fun w => fEvent w.1 * g w.2
  have hintegrand : (fun z : OriginalCoordinates p =>
      if ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z) =
        σ.val + 1 then f (jointSplitEquiv p σ z).1 * g (jointSplitEquiv p σ z).2 else 0) =
      fun z => H (jointSplitEquiv p σ z) := by
    funext z
    dsimp [H, fEvent]
    rw [launchEventAt_eq_actual]
    by_cases h : ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1
    · simp only [h, decide_true, ite_true]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, zero_mul]
  calc
    _ = ∫ z, H (jointSplitEquiv p σ z) ∂(originalLaw p) := by rw [hintegrand]
    _ = ∫ w, H w ∂((jointPastLaw p σ).prod (jointFutureLaw p σ)) :=
      (measurePreserving_jointSplit p σ).integral_comp (jointSplitEquiv p σ).measurableEmbedding H
    _ = _ := by
      rw [integral_prod _ (hfInt.mul_prod hgInt)]
      simp only [fEvent, integral_const_mul, integral_mul_const]

/-- The normalized restriction by launch and any measurable joint-past event
has the exact entire joint-future marginal, whenever its mass is positive. -/
theorem actual_launch_past_event_normalized_future_marginal
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (JointPast p σ)) (hA : MeasurableSet A)
    (hpos : 0 < originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A})
    (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    (((originalLaw p).restrict {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
      (jointSplitEquiv p σ z).1 ∈ A}).map (fun z => (jointSplitEquiv p σ z).2)) B /
      originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
        (jointSplitEquiv p σ z).1 ∈ A} = jointFutureLaw p σ B := by
  let E : Set (OriginalCoordinates p) := {z | ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
    (jointSplitEquiv p σ z).1 ∈ A}
  have hproj : Measurable (fun z : OriginalCoordinates p => (jointSplitEquiv p σ z).2) :=
    measurable_snd.comp (jointSplitEquiv p σ).measurable
  have hmap : ((originalLaw p).restrict E).map (fun z => (jointSplitEquiv p σ z).2) B =
      originalLaw p {z | ReferenceInitializationRun.launchRound
          (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
        (jointSplitEquiv p σ z).1 ∈ A ∧ (jointSplitEquiv p σ z).2 ∈ B} := by
    rw [Measure.map_apply_of_aemeasurable hproj.aemeasurable hB,
      Measure.restrict_apply (hproj hB)]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, E]
    constructor
    · rintro ⟨hb, hl, ha⟩
      exact ⟨hl, ha, hb⟩
    · rintro ⟨hl, ha, hb⟩
      exact ⟨hb, hl, ha⟩
  rw [hmap, actual_launch_event_factorization p ids rewards C_star C_h eta σ A hA B hB]
  rw [mul_comm (originalLaw p E)]
  exact ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top (originalLaw p) E)

/-- In particular, normalize by the launch event alone. -/
theorem actual_launch_normalized_future_marginal
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (σ : LaunchIndex p)
    (hpos : 0 < originalLaw p {z | ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta z) = σ.val + 1})
    (B : Set (JointFuture p σ)) (hB : MeasurableSet B) :
    (((originalLaw p).restrict {z | ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta z) = σ.val + 1}).map
        (fun z => (jointSplitEquiv p σ z).2)) B /
      originalLaw p {z | ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z) = σ.val + 1} = jointFutureLaw p σ B := by
  have hpos' : 0 < originalLaw p {z | ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta z) = σ.val + 1 ∧
    (jointSplitEquiv p σ z).1 ∈ Set.univ} := by
    simpa only [Set.mem_univ, and_true] using hpos
  simpa only [Set.mem_univ, and_true] using
    actual_launch_past_event_normalized_future_marginal p ids rewards C_star C_h eta σ
      Set.univ MeasurableSet.univ hpos' B hB

/-- Every player and every full row entry at the launch index belongs to the
future, whenever that source round lies within the actual calendar. -/
theorem launch_round_in_joint_future (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (i : Fin p.m) :
    ∃ t : FutureIndex p σ,
      ∃ label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ,
        t.1.val = σ.val ∧ label.1 = (i, t.1) := by
  let t : Fin p.T := ⟨σ.val, hσ⟩
  exact ⟨⟨t, by change ¬ σ.val < σ.val; exact lt_irrefl _⟩,
    ⟨(i, t), by change ¬ σ.val < σ.val; exact lt_irrefl _⟩, rfl, rfl⟩

/-- Both future label subtypes are genuinely empty at the common sentinel. -/
theorem joint_future_labels_at_terminal_isEmpty (p : Parameters) :
    IsEmpty (FutureIndex p (horizonStoppingIndex p)) ∧
      IsEmpty (ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p (horizonStoppingIndex p)) :=
  ⟨futureIndexAtHorizon_isEmpty p,
    ReferenceLaunchPrivateRoundLaw.futurePlayerRoundLabel_at_terminal_isEmpty p⟩

/-- The unique empty pair of future functions; no `Fin T` round is fabricated. -/
def terminalFuture (p : Parameters) : JointFuture p (horizonStoppingIndex p) :=
  ((fun t => False.elim ((joint_future_labels_at_terminal_isEmpty p).1.false t)),
    fun label => False.elim ((joint_future_labels_at_terminal_isEmpty p).2.false label))

theorem jointFuture_at_terminal_subsingleton (p : Parameters) :
    Subsingleton (JointFuture p (horizonStoppingIndex p)) := by
  refine ⟨fun a b => Prod.ext ?_ ?_⟩
  · exact (futureArrayAtHorizon_subsingleton p).elim a.1 b.1
  · exact (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalars_at_terminal_subsingleton p).elim a.2 b.2

theorem jointFuture_at_terminal_eq (p : Parameters)
    (future : JointFuture p (horizonStoppingIndex p)) : future = terminalFuture p :=
  (jointFuture_at_terminal_subsingleton p).elim _ _

/-- The genuine empty-future law is a Dirac law on its unique function pair. -/
theorem jointFutureLaw_at_terminal_eq_dirac (p : Parameters) :
    jointFutureLaw p (horizonStoppingIndex p) = Measure.dirac (terminalFuture p) := by
  let := (joint_future_labels_at_terminal_isEmpty p).1
  let := (joint_future_labels_at_terminal_isEmpty p).2
  change (Measure.pi (fun _ : FutureIndex p (horizonStoppingIndex p) => calendarEntryLaw p)).prod
    (Measure.pi (fun _ : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p
      (horizonStoppingIndex p) => ContinuousCategorical.uniform)) = _
  rw [Measure.pi_of_empty _ (terminalFuture p).1,
    Measure.pi_of_empty _ (terminalFuture p).2, Measure.dirac_prod_dirac]

/-- Every original point has precisely that unique empty future at the
sentinel, independently of whether the source reached a final crossing. -/
theorem jointSplit_at_terminal_future (p : Parameters) (z : OriginalCoordinates p) :
    (jointSplitEquiv p (horizonStoppingIndex p) z).2 = terminalFuture p :=
  jointFuture_at_terminal_eq p _

/-- The same exact construction on the original row-then-private carrier,
using only actual measurable product commutation. -/
def rowPrivateJointSplitEquiv (p : Parameters) (σ : LaunchIndex p) :
    (CompletePublicTable.CompleteRow p × ExtendedPrivateCoordinates p) ≃ᵐ
      (JointPast p σ × JointFuture p σ) :=
  MeasurableEquiv.prodComm.trans (jointSplitEquiv p σ)

theorem rowPrivateJointSplitEquiv_apply (p : Parameters) (σ : LaunchIndex p)
    (z : CompletePublicTable.CompleteRow p × ExtendedPrivateCoordinates p) :
    rowPrivateJointSplitEquiv p σ z = jointSplitEquiv p σ (z.2, z.1) := rfl

theorem measurePreserving_rowPrivateJointSplit (p : Parameters) (σ : LaunchIndex p) :
    MeasurePreserving (rowPrivateJointSplitEquiv p σ)
      ((completeRowMeasure p).prod (extendedPrivateLaw p))
      ((jointPastLaw p σ).prod (jointFutureLaw p σ)) :=
  (measurePreserving_jointSplit p σ).comp Measure.measurePreserving_swap

end Bandits.Support.ReferenceLaunchJointFutureLaw

end
