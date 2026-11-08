/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompleteRowStoppingLaw
public import Bandits.Support.GeneratedBlockDrawLaw
public import Bandits.Support.ReferenceInitializationCausality
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint law at a generated block start

For one fixed block opportunity, this module regroups the original complete
row and the original extended-private draw into retained private data and the
strict-past calendar, followed by the actual fresh block profile, target
scalar, and entire future calendar. The boundary factor is evaluated from the
actual stopped reference run; the section used to view it on retained data is
proved equal to that run by prefix invariance.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-40,63-112` and
`sources/zip4/manuscript/appendix_b_communication.tex:376-395,485-506,658-675`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationCausality
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ReferenceInitializationPrefixInvariance
open Bandits.Support.GeneratedBlockDrawLaw

namespace Bandits.Support.GeneratedBlockStartLaw

abbrev Parameters := ConstructorDimensions.Parameters

/-- The source row/private coordinate pair, in the order used by the law. -/
abbrev OriginalCoordinates (p : Parameters) :=
  CompletePublicTable.CompleteRow p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p

/-- The literal fixed-public law of the original row and private coordinates. -/
noncomputable def originalCoordinatesLaw (p : Parameters) :
    Measure (OriginalCoordinates p) :=
  (CompletePublicTable.completeRowMeasure p).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)

instance originalCoordinatesLaw_probability (p : Parameters) :
    IsProbabilityMeasure (originalCoordinatesLaw p) := by
  dsimp [originalCoordinatesLaw]
  infer_instance

/-- Calendar index at the actual elapsed boundary before block `s`. -/
def blockStartIndex (p : Parameters) (s : Fin (n_boot p)) : Fin (p.T + 1) :=
  ⟨ReferenceInitializationRun.elapsed p s.val,
    Nat.lt_succ_of_le (ReferenceInitializationRun.elapsed_le_T p s.val)⟩

theorem blockStartIndex_val (p : Parameters) (s : Fin (n_boot p)) :
    (blockStartIndex p s).val = ReferenceInitializationRun.elapsed p s.val := rfl

theorem blockStartIndex_bound (p : Parameters) (s : Fin (n_boot p)) :
    (blockStartIndex p s).val ≤ p.T :=
  ReferenceInitializationRun.elapsed_le_T p s.val

abbrev FollowerTripleProfile (p : Parameters) :=
  GeneratedBlockDrawLaw.FollowerTripleProfile p

abbrev CurrentCoordinates (p : Parameters) :=
  GeneratedBlockDrawLaw.CurrentBlockCoordinates p

abbrev OtherCoordinates (p : Parameters) (s : Fin (n_boot p)) :=
  GeneratedBlockDrawLaw.OtherPrivateCoordinates p s

abbrev SidePast (p : Parameters) (s : Fin (n_boot p)) :=
  OtherCoordinates p s ×
    CompleteRowStoppingLaw.PastArray p (blockStartIndex p s)

abbrev FutureCoordinates (p : Parameters) (s : Fin (n_boot p)) :=
  (CurrentCoordinates p) ×
    CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)

/-- A calendar entry used only to complete a strict-past analysis section. -/
def sectionScalar : ContinuousLearningRows.Scalar := ⟨0, by norm_num⟩

def sectionTimeControl (p : Parameters) : ContinuousLearningRows.TimeControl p :=
  ((fun _ : ContinuousLearningRows.Label p => sectionScalar),
    fun _ : ContinuousLearningRows.Channel p =>
      ((fun _ : Fin (ContinuousLearningRows.B p) => (0 : AffineChannelLaw.Bit)),
        (0 : AffineChannelLaw.Bit)))

def sectionEntry (p : Parameters) : CompleteRowStoppingLaw.CalendarEntry p :=
  ((fun _ : Fin (A_id p) => false), sectionTimeControl p)

/-- Complete a strict past only to define a measurable section. This row is
never installed in a run; the boundary theorem below proves independence from
all current and future coordinates. -/
def completedCalendar (p : Parameters) (σ : Fin (p.T + 1))
    (past : CompleteRowStoppingLaw.PastArray p σ) :
    CompleteRowStoppingLaw.CalendarArray p :=
  (CompleteRowStoppingLaw.calendarSplitEquiv p σ).symm
    (past, fun _ => sectionEntry p)

def completedRow (p : Parameters) (σ : Fin (p.T + 1))
    (past : CompleteRowStoppingLaw.PastArray p σ) :
    CompletePublicTable.CompleteRow p :=
  (CompleteRowStoppingLaw.calendarizeRowEquiv p).symm
    (completedCalendar p σ past)

theorem measurable_completedCalendar (p : Parameters) (σ : Fin (p.T + 1)) :
    Measurable (completedCalendar p σ) := by
  exact ((CompleteRowStoppingLaw.calendarSplitEquiv p σ).symm.measurable).comp
    (measurable_id.prodMk measurable_const)

theorem measurable_completedRow (p : Parameters) (σ : Fin (p.T + 1)) :
    Measurable (completedRow p σ) := by
  exact (CompleteRowStoppingLaw.calendarizeRowEquiv p).symm.measurable.comp
    (measurable_completedCalendar p σ)

theorem calendarize_completedRow (p : Parameters) (σ : Fin (p.T + 1))
    (past : CompleteRowStoppingLaw.PastArray p σ) :
    CompleteRowStoppingLaw.calendarizeRow p (completedRow p σ past) =
      completedCalendar p σ past :=
  (CompleteRowStoppingLaw.calendarizeRowEquiv p).apply_symm_apply _

theorem completedRow_agrees_on_past (p : Parameters) (σ : Fin (p.T + 1))
    (past : CompleteRowStoppingLaw.PastArray p σ)
    (t : CompleteRowStoppingLaw.PastIndex p σ) :
    CompleteRowStoppingLaw.calendarizeRow p (completedRow p σ past) t.1 = past t := by
  have hsplit := (CompleteRowStoppingLaw.calendarSplitEquiv p σ).apply_symm_apply
    (past, fun _ => sectionEntry p)
  have hpast := congrArg Prod.fst hsplit
  rw [calendarize_completedRow]
  exact congrFun hpast t

/-- Reorder `(current × past) × future` as `past × (current × future)`. -/
def currentPastMoveEquiv (Current Past Future : Type*)
    [MeasurableSpace Current] [MeasurableSpace Past] [MeasurableSpace Future] :
    Current × (Past × Future) ≃ᵐ Past × (Current × Future) :=
  MeasurableEquiv.prodAssoc.symm.trans <|
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
      (MeasurableEquiv.refl Future)).trans MeasurableEquiv.prodAssoc

/-- Reorder the current private draws beside the future calendar while
retaining other private coordinates beside the strict past. -/
def analysisRegroupEquiv (Other Current Past Future : Type*)
    [MeasurableSpace Other] [MeasurableSpace Current]
    [MeasurableSpace Past] [MeasurableSpace Future] :
    (Other × Current) × (Past × Future) ≃ᵐ
      (Other × Past) × (Current × Future) :=
  MeasurableEquiv.prodAssoc.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Other)
      (currentPastMoveEquiv Current Past Future)).trans
        MeasurableEquiv.prodAssoc.symm

def rowCalendarSplitEquiv (p : Parameters) (s : Fin (n_boot p)) :
    CompletePublicTable.CompleteRow p ≃ᵐ
      (CompleteRowStoppingLaw.PastArray p (blockStartIndex p s) ×
        CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)) :=
  (CompleteRowStoppingLaw.calendarizeRowEquiv p).trans
    (CompleteRowStoppingLaw.calendarSplitEquiv p (blockStartIndex p s))

/-- The full measurable regrouping of the original `(row,rho)` coordinates. -/
def analysisSplitEquiv (p : Parameters) (s : Fin (n_boot p)) :
    OriginalCoordinates p ≃ᵐ (SidePast p s × FutureCoordinates p s) :=
  (MeasurableEquiv.prodComm).trans <|
    (MeasurableEquiv.prodCongr
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s)
      (rowCalendarSplitEquiv p s)).trans <|
        analysisRegroupEquiv (OtherCoordinates p s) (CurrentCoordinates p)
          (CompleteRowStoppingLaw.PastArray p (blockStartIndex p s))
          (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))

theorem measurePreserving_currentPastMoveEquiv
    (Current Past Future : Type*) [MeasurableSpace Current]
    [MeasurableSpace Past] [MeasurableSpace Future]
    (μCurrent : Measure Current) (μPast : Measure Past) (μFuture : Measure Future)
    [SFinite μCurrent] [SFinite μPast] [SFinite μFuture] :
    MeasurePreserving (currentPastMoveEquiv Current Past Future)
      (μCurrent.prod (μPast.prod μFuture))
      (μPast.prod (μCurrent.prod μFuture)) := by
  let hAssoc := (measurePreserving_prodAssoc μCurrent μPast μFuture).symm
  let hSwap : MeasurePreserving
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl Future))
      ((μCurrent.prod μPast).prod μFuture)
      ((μPast.prod μCurrent).prod μFuture) := by
    exact Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
  let hAssocFinal := measurePreserving_prodAssoc μPast μCurrent μFuture
  exact hAssocFinal.comp (hSwap.comp hAssoc)

theorem measurePreserving_analysisRegroupEquiv
    (Other Current Past Future : Type*) [MeasurableSpace Other]
    [MeasurableSpace Current] [MeasurableSpace Past] [MeasurableSpace Future]
    (μOther : Measure Other) (μCurrent : Measure Current)
    (μPast : Measure Past) (μFuture : Measure Future)
    [SFinite μOther] [SFinite μCurrent] [SFinite μPast] [SFinite μFuture] :
    MeasurePreserving (analysisRegroupEquiv Other Current Past Future)
      ((μOther.prod μCurrent).prod (μPast.prod μFuture))
      ((μOther.prod μPast).prod (μCurrent.prod μFuture)) := by
  let hAssoc := measurePreserving_prodAssoc μOther μCurrent (μPast.prod μFuture)
  let hMove := measurePreserving_currentPastMoveEquiv
    Current Past Future μCurrent μPast μFuture
  let hOuter := (MeasurePreserving.id μOther).prod hMove
  let hAssocFinal := (measurePreserving_prodAssoc μOther μPast
    (μCurrent.prod μFuture)).symm
  exact hAssocFinal.comp (hOuter.comp hAssoc)

noncomputable def sidePastLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (SidePast p s) :=
  (GeneratedBlockDrawLaw.otherPrivateLaw p s).prod
    (CompleteRowStoppingLaw.pastArrayLaw p (blockStartIndex p s))

noncomputable def profileTargetFutureLaw (p : Parameters)
    (s : Fin (n_boot p)) : Measure (FutureCoordinates p s) :=
  ((PrivateSourceStreams.blockScalarProfileLaw p).prod
    ContinuousCategorical.uniform).prod
    (CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s))

noncomputable def regroupedCoordinatesLaw (p : Parameters)
    (s : Fin (n_boot p)) : Measure (SidePast p s × FutureCoordinates p s) :=
  (sidePastLaw p s).prod (profileTargetFutureLaw p s)

instance otherPrivateLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (GeneratedBlockDrawLaw.otherPrivateLaw p s) := by
  dsimp [GeneratedBlockDrawLaw.otherPrivateLaw]
  infer_instance

instance sidePastLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (sidePastLaw p s) := by
  dsimp [sidePastLaw]
  infer_instance

instance profileTargetFutureLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (profileTargetFutureLaw p s) := by
  dsimp [profileTargetFutureLaw]
  infer_instance

theorem measurePreserving_analysisSplitEquiv (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (analysisSplitEquiv p s) (originalCoordinatesLaw p)
      (regroupedCoordinatesLaw p s) := by
  let hPrivate := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_measurePreserving p s
  let hRow := (CompleteRowStoppingLaw.measurePreserving_calendarSplit p
      (blockStartIndex p s)).comp
    (CompleteRowStoppingLaw.measurePreserving_calendarizeRow p)
  let hSwap : MeasurePreserving MeasurableEquiv.prodComm
      ((CompletePublicTable.completeRowMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
      ((BootstrapPrivateRoundStreams.extendedPrivateLaw p).prod
        (CompletePublicTable.completeRowMeasure p)) :=
    Measure.measurePreserving_swap
  let hSplit := hPrivate.prod hRow
  let hRegroup := measurePreserving_analysisRegroupEquiv
    (OtherCoordinates p s) (CurrentCoordinates p)
    (CompleteRowStoppingLaw.PastArray p (blockStartIndex p s))
    (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))
    (GeneratedBlockDrawLaw.otherPrivateLaw p s)
    ((PrivateSourceStreams.blockScalarProfileLaw p).prod ContinuousCategorical.uniform)
    (CompleteRowStoppingLaw.pastArrayLaw p (blockStartIndex p s))
    (CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s))
  change MeasurePreserving (analysisRegroupEquiv _ _ _ _ ∘
    (MeasurableEquiv.prodCongr _ _ ∘ MeasurableEquiv.prodComm)) _ _
  exact hRegroup.comp (hSplit.comp hSwap)

/-- Evaluation of the regrouping shows that every output field is the same
original labelled coordinate, routed to its unique side of the split. -/
theorem analysisSplitEquiv_apply (p : Parameters) (s : Fin (n_boot p))
    (e : OriginalCoordinates p) :
    analysisSplitEquiv p s e =
      (((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1,
        (CompleteRowStoppingLaw.calendarSplitEquiv p (blockStartIndex p s)
          (CompleteRowStoppingLaw.calendarizeRow p e.1)).1),
       ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).2,
        (CompleteRowStoppingLaw.calendarSplitEquiv p (blockStartIndex p s)
          (CompleteRowStoppingLaw.calendarizeRow p e.1)).2)) := by
  rfl

theorem analysisSplitEquiv_currentProfile (p : Parameters)
    (s : Fin (n_boot p)) (e : OriginalCoordinates p) :
    (analysisSplitEquiv p s e).2.1.1 = e.2.1.1 s := by
  rw [analysisSplitEquiv_apply]
  exact GeneratedBlockDrawLaw.extendedPrivateBlockSplit_profile p s e.2

theorem analysisSplitEquiv_currentTargetScalar (p : Parameters)
    (s : Fin (n_boot p)) (e : OriginalCoordinates p) :
    (analysisSplitEquiv p s e).2.1.2 = e.2.2.2 s := by
  rw [analysisSplitEquiv_apply]
  exact GeneratedBlockDrawLaw.extendedPrivateBlockSplit_target p s e.2

theorem analysisSplitEquiv_strictPastRow (p : Parameters)
    (s : Fin (n_boot p)) (e : OriginalCoordinates p)
    (t : CompleteRowStoppingLaw.PastIndex p (blockStartIndex p s)) :
    (analysisSplitEquiv p s e).1.2 t =
      CompleteRowStoppingLaw.calendarizeRow p e.1 t.1 := by
  rw [analysisSplitEquiv_apply]
  simp [CompleteRowStoppingLaw.calendarSplitEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd]

theorem analysisSplitEquiv_entireFutureRow (p : Parameters)
    (s : Fin (n_boot p)) (e : OriginalCoordinates p)
    (t : CompleteRowStoppingLaw.FutureIndex p (blockStartIndex p s)) :
    (analysisSplitEquiv p s e).2.2 t =
      CompleteRowStoppingLaw.calendarizeRow p e.1 t.1 := by
  rw [analysisSplitEquiv_apply]
  simp [CompleteRowStoppingLaw.calendarSplitEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd]

/-- The inverse regrouping recovers the original full raw follower-triple
profile at label `s`, not a sampled replacement. -/
theorem analysisSplitEquiv_symm_currentProfile (p : Parameters)
    (s : Fin (n_boot p)) (w : SidePast p s)
    (profile : FollowerTripleProfile p)
    (target : BootstrapPrivateRoundStreams.Scalar)
    (future : CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)) :
    ((analysisSplitEquiv p s).symm (w, ((profile, target), future))).2.1.1 s =
      profile := by
  let e := (analysisSplitEquiv p s).symm (w, ((profile, target), future))
  have h := (analysisSplitEquiv p s).apply_symm_apply
    (w, ((profile, target), future))
  have hprivate : GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2 =
      (w.1, (profile, target)) := by
    have hparts := congrArg (fun q : SidePast p s × FutureCoordinates p s =>
      (q.1.1, q.2.1)) h
    simpa only [analysisSplitEquiv_apply] using hparts
  have hprofile := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_profile p s e.2
  rw [hprivate] at hprofile
  exact hprofile.symm

/-- The inverse regrouping recovers the original separately-labelled
coordinator-target scalar at label `s`. -/
theorem analysisSplitEquiv_symm_currentTargetScalar (p : Parameters)
    (s : Fin (n_boot p)) (w : SidePast p s)
    (profile : FollowerTripleProfile p)
    (target : BootstrapPrivateRoundStreams.Scalar)
    (future : CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)) :
    ((analysisSplitEquiv p s).symm (w, ((profile, target), future))).2.2.2 s =
      target := by
  let e := (analysisSplitEquiv p s).symm (w, ((profile, target), future))
  have h := (analysisSplitEquiv p s).apply_symm_apply
    (w, ((profile, target), future))
  have hprivate : GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2 =
      (w.1, (profile, target)) := by
    have hparts := congrArg (fun q : SidePast p s × FutureCoordinates p s =>
      (q.1.1, q.2.1)) h
    simpa only [analysisSplitEquiv_apply] using hparts
  have htarget := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_target p s e.2
  rw [hprivate] at htarget
  exact htarget.symm

/-- The inverse regrouping recovers both entire row subarrays with their
original calendar labels. -/
theorem analysisSplitEquiv_symm_calendar (p : Parameters)
    (s : Fin (n_boot p)) (w : SidePast p s)
    (current : CurrentCoordinates p)
    (future : CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)) :
    rowCalendarSplitEquiv p s
      ((analysisSplitEquiv p s).symm (w, (current, future))).1 = (w.2, future) := by
  let e := (analysisSplitEquiv p s).symm (w, (current, future))
  have h := (analysisSplitEquiv p s).apply_symm_apply (w, (current, future))
  have hrow : rowCalendarSplitEquiv p s e.1 = (w.2, future) := by
    have hparts := congrArg (fun q : SidePast p s × FutureCoordinates p s =>
      (q.1.2, q.2.2)) h
    change CompleteRowStoppingLaw.calendarSplitEquiv p (blockStartIndex p s)
      (CompleteRowStoppingLaw.calendarizeRow p e.1) = (w.2, future)
    simpa only [analysisSplitEquiv_apply] using hparts
  exact hrow

/-- Actual generated boundary as a function on the original complete row and
extended-private pair. -/
def boundaryAtOriginal (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : OriginalCoordinates p) :
    ReferenceInitializationRun.Boundary p :=
  GeneratedBlockDrawLaw.generatedBoundary p s ids e.1 rewards C_star C_h eta e.2

/-- Section value of the actual generated boundary on retained private data
and the strict-past row. It only supplies missing coordinates to the accepted
run; its equality with every original completion is proved below. -/
def boundaryFromSide (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (w : SidePast p s) :
    ReferenceInitializationRun.Boundary p :=
  GeneratedBlockDrawLaw.generatedBoundary p s ids
    (completedRow p (blockStartIndex p s) w.2) rewards C_star C_h eta
    ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm
      (w.1, GeneratedBlockDrawLaw.zeroCurrentBlockCoordinates p))

theorem measurable_boundaryAtOriginal (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (boundaryAtOriginal p s ids rewards C_star C_h eta) := by
  have hcoords : Measurable
      (fun e : OriginalCoordinates p => (ids, (e.1, e.2))) :=
    measurable_const.prodMk measurable_id
  change Measurable (fun e : OriginalCoordinates p => ReferenceInitializationRun.run
    (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (ids, (e.1, e.2))) s.val)
  exact (ReferenceInitializationMeasurability.measurable_run
    p C_star C_h eta rewards s.val).comp hcoords

theorem measurable_boundaryAtOriginal_atom (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet {e : OriginalCoordinates p |
      boundaryAtOriginal p s ids rewards C_star C_h eta e = b} :=
  (measurableSet_singleton b).preimage
    (measurable_boundaryAtOriginal p s ids rewards C_star C_h eta)

theorem measurable_boundaryFromSide (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (boundaryFromSide p s ids rewards C_star C_h eta) := by
  have hrow : Measurable (fun w : SidePast p s =>
      completedRow p (blockStartIndex p s) w.2) :=
    (measurable_completedRow p (blockStartIndex p s)).comp measurable_snd
  have hprivate : Measurable (fun w : SidePast p s =>
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm
        (w.1, GeneratedBlockDrawLaw.zeroCurrentBlockCoordinates p)) :=
    (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm.measurable.comp
      (measurable_fst.prodMk measurable_const)
  have hcoords : Measurable (fun w : SidePast p s =>
      (ids, (completedRow p (blockStartIndex p s) w.2,
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm
          (w.1, GeneratedBlockDrawLaw.zeroCurrentBlockCoordinates p)))) := by
    exact measurable_const.prodMk (hrow.prodMk hprivate)
  change Measurable (fun w : SidePast p s => ReferenceInitializationRun.run
    (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (ids, (completedRow p (blockStartIndex p s) w.2,
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm
          (w.1, GeneratedBlockDrawLaw.zeroCurrentBlockCoordinates p)))) s.val)
  exact (ReferenceInitializationMeasurability.measurable_run
    p C_star C_h eta rewards s.val).comp hcoords

theorem measurable_boundaryFromSide_atom (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet {w : SidePast p s |
      boundaryFromSide p s ids rewards C_star C_h eta w = b} :=
  (measurableSet_singleton b).preimage
    (measurable_boundaryFromSide p s ids rewards C_star C_h eta)

/-- The generated boundary on every original completion equals the section
value on its retained coordinates. The proof constructs the exact accepted
`runPrefixInputEq`: row symbols at and after the elapsed boundary and the
current profile/target are omitted, while all earlier original triples,
targets, player-round scalars, and strict-past row entries are identified. -/
theorem boundaryAtOriginal_eq_boundaryFromSide (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : OriginalCoordinates p) :
    boundaryAtOriginal p s ids rewards C_star C_h eta e =
      boundaryFromSide p s ids rewards C_star C_h eta
        (analysisSplitEquiv p s e).1 := by
  let rho := e.2
  let w := (analysisSplitEquiv p s e).1
  let row0 := completedRow p (blockStartIndex p s) w.2
  let rho0 := (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s).symm
    (w.1, GeneratedBlockDrawLaw.zeroCurrentBlockCoordinates p)
  let x := GeneratedBlockDrawLaw.fixedReferenceInput p ids e.1 rewards C_star C_h eta rho
  let y := GeneratedBlockDrawLaw.fixedReferenceInput p ids row0 rewards C_star C_h eta rho0
  have hsplit := analysisSplitEquiv_apply p s e
  have hprivateOrig :
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1 = w.1 := by
    have h := congrArg (fun q : SidePast p s × FutureCoordinates p s => q.1.1) hsplit
    simpa [w] using h.symm
  have hprivateSection :
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho0).1 = w.1 := by
    simp [rho0]
  have hrest :
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1 =
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho0).1 :=
    hprivateOrig.trans hprivateSection.symm
  have hblocks : ∀ r : Fin (n_boot p), r.val < s.val →
      rho.1.1 r = rho0.1.1 r := by
    intro r hr
    have hne : r ≠ s := by
      intro heq
      subst r
      omega
    let rr : GeneratedBlockDrawLaw.OtherBlockLabels p s := ⟨r, hne⟩
    have hO := congrArg
      (fun q : OtherCoordinates p s => q.1.1.1) hrest
    have hO' := congrFun hO rr
    have hrho := congrArg Prod.fst
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_block p s rho rr)
    have hrho0 := congrArg Prod.fst
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_block p s rho0 rr)
    calc
      rho.1.1 r =
          (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1.1.1.1 rr :=
        hrho.symm
      _ = (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho0).1.1.1.1 rr :=
        hO'
      _ = rho0.1.1 r := hrho0
  have htargets : ∀ r : Fin (n_boot p), r.val < s.val →
      rho.2.2 r = rho0.2.2 r := by
    intro r hr
    have hne : r ≠ s := by
      intro heq
      subst r
      omega
    let rr : GeneratedBlockDrawLaw.OtherBlockLabels p s := ⟨r, hne⟩
    have hO := congrArg (fun q : OtherCoordinates p s => q.2) hrest
    have hO' := congrFun hO rr
    have hrho := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_target p s rho rr
    have hrho0 := GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_target p s rho0 rr
    calc
      rho.2.2 r =
          (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho).1.2 rr :=
        hrho.symm
      _ = (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s rho0).1.2 rr := hO'
      _ = rho0.2.2 r := hrho0
  have hrounds : ∀ i : Fin p.m, ∀ t : Fin p.T,
      rho.2.1 (i, t) = rho0.2.1 (i, t) := by
    have hR := congrArg (fun q : OtherCoordinates p s => q.1.2) hrest
    intro i t
    exact congrFun hR (i, t)
  have hPast :
      (analysisSplitEquiv p s e).1.2 =
        (CompleteRowStoppingLaw.calendarSplitEquiv p (blockStartIndex p s)
          (CompleteRowStoppingLaw.calendarizeRow p e.1)).1 := by
    have h := congrArg (fun q : SidePast p s × FutureCoordinates p s => q.1.2) hsplit
    simpa using h
  have hprefix : ReferenceInitializationCausality.runPrefixInputEq x y s.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have htσ : t.val < (blockStartIndex p s).val := by
        rw [blockStartIndex_val]
        exact ht
      let tt : CompleteRowStoppingLaw.PastIndex p (blockStartIndex p s) :=
        ⟨t, htσ⟩
      have hrow : CompleteRowStoppingLaw.calendarizeRow p row0 tt.1 =
          CompleteRowStoppingLaw.calendarizeRow p e.1 tt.1 := by
        calc
          CompleteRowStoppingLaw.calendarizeRow p row0 tt.1 = w.2 tt :=
            completedRow_agrees_on_past p (blockStartIndex p s) w.2 tt
          _ = CompleteRowStoppingLaw.calendarizeRow p e.1 tt.1 :=
            congrFun hPast tt
      constructor
      · intro u
        simpa [x, y, GeneratedBlockDrawLaw.fixedReferenceInput,
          CompleteRowStoppingLaw.calendarizeRow] using
          congrArg (fun q : CompleteRowStoppingLaw.CalendarEntry p => q.1 u) hrow.symm
      · simpa [x, y, GeneratedBlockDrawLaw.fixedReferenceInput,
          CompleteRowStoppingLaw.calendarizeRow] using congrArg Prod.snd hrow.symm
    · intro r hr j
      exact congrFun (hblocks r hr) j
    · intro r hr
      exact htargets r hr
    · intro i t ht
      exact hrounds i t
  change ReferenceInitializationRun.run x s.val = ReferenceInitializationRun.run y s.val
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq
    x y s.val hprefix

/-- Simultaneously changing the current labelled profile, target scalar and
all calendar entries at or after the boundary leaves the actual boundary
unchanged whenever the retained analysis side is fixed. -/
theorem boundaryAtOriginal_eq_of_sameSide (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (e e' : OriginalCoordinates p)
    (hside : (analysisSplitEquiv p s e).1 = (analysisSplitEquiv p s e').1) :
    boundaryAtOriginal p s ids rewards C_star C_h eta e =
      boundaryAtOriginal p s ids rewards C_star C_h eta e' := by
  rw [boundaryAtOriginal_eq_boundaryFromSide, boundaryAtOriginal_eq_boundaryFromSide, hside]

/-- Retained analysis side for the original coordinates. It includes all
player-round scalars and every other block's triples and targets; it is not a
player information state, source filtration, or new private-scalar law. -/
def analysisSideOf (p : Parameters) (s : Fin (n_boot p))
    (e : OriginalCoordinates p) : SidePast p s :=
  (analysisSplitEquiv p s e).1

/-- Entire original selected-row calendar at or after the actual block start. -/
def futureRowOf (p : Parameters) (s : Fin (n_boot p))
    (e : OriginalCoordinates p) :
    CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s) :=
  (analysisSplitEquiv p s e).2.2

theorem measurable_analysisSideOf (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (analysisSideOf p s) :=
  measurable_fst.comp (analysisSplitEquiv p s).measurable

theorem measurable_futureRowOf (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (futureRowOf p s) := by
  exact measurable_snd.comp (measurable_snd.comp
    (analysisSplitEquiv p s).measurable)

theorem boundaryAtOriginal_eq_fromAnalysisSide (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : OriginalCoordinates p) :
    boundaryAtOriginal p s ids rewards C_star C_h eta e =
      boundaryFromSide p s ids rewards C_star C_h eta (analysisSideOf p s e) :=
  boundaryAtOriginal_eq_boundaryFromSide p s ids rewards C_star C_h eta e

/-- The raw profile event before applying the genuine state-dependent draw
map. -/
def rawProfileEvent (p : Parameters) (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) :
    Set (FollowerTripleProfile p) :=
  {profile | PrivateSourceStreams.blockDrawProfileMap p b.numerators
    b.weight_ge_one profile = c}

/-- Target-scalar event for the existing coordinator target map. -/
def targetScalarEvent (p : Parameters) (z : Fin p.K) :
    Set BootstrapPrivateRoundStreams.Scalar :=
  {u | BootstrapPrivateRoundStreams.coordinatorTargetDraw p u = z}

theorem measurableSet_rawProfileEvent (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) :
    MeasurableSet (rawProfileEvent p b c) := by
  change MeasurableSet {profile | PrivateSourceStreams.blockDrawProfileMap p
    b.numerators b.weight_ge_one profile = c}
  exact measurableSet_eq_fun
    (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators b.weight_ge_one)
    measurable_const

theorem measurableSet_targetScalarEvent (p : Parameters) (z : Fin p.K) :
    MeasurableSet (targetScalarEvent p z) := by
  change MeasurableSet
    (BootstrapPrivateRoundStreams.fullArmScalarDraw p ⁻¹' ({z} : Set (Fin p.K)))
  exact measurableSet_preimage
    (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p)
    (measurableSet_singleton z)

theorem rawProfileEvent_mass (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) :
    PrivateSourceStreams.blockScalarProfileLaw p (rawProfileEvent p b c) =
      BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c := by
  calc
    _ = (PrivateSourceStreams.blockScalarProfileLaw p).map
        (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one) {c} := by
          symm
          exact Measure.map_apply
            (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators
              b.weight_ge_one) (measurableSet_singleton c)
    _ = (BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
        b.weight_ge_one).toMeasure {c} := by
          rw [PrivateSourceStreams.blockDrawProfileMap_law]
    _ = BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
        b.weight_ge_one c :=
          PMF.toMeasure_apply_singleton _ c (measurableSet_singleton c)

theorem targetScalarEvent_mass (p : Parameters) (z : Fin p.K) :
    ContinuousCategorical.uniform (targetScalarEvent p z) =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  change ContinuousCategorical.uniform
    (BootstrapPrivateRoundStreams.fullArmScalarDraw p ⁻¹' ({z} : Set (Fin p.K))) = _
  exact BootstrapPrivateRoundStreams.fullArmScalarDraw_uniform_atom p z

/-- Joint event for a boundary atom, full labelled current profile, target arm,
and an arbitrary measurable set in the entire future row. -/
def generatedBoundaryProfileTargetFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))) :
    Set (OriginalCoordinates p) :=
  {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b ∧
    GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2 = c ∧
    GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 = z ∧
    futureRowOf p s e ∈ C}

theorem measurableSet_generatedBoundaryProfileTargetFutureEvent
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    MeasurableSet (generatedBoundaryProfileTargetFutureEvent p s ids rewards
      C_star C_h eta b c z C) := by
  have hprofile : Measurable
      (fun e : OriginalCoordinates p =>
        GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) :=
    (GeneratedBlockDrawLaw.measurable_generatedCurrentBlockProfile p s b).comp
      measurable_snd
  have htarget : Measurable
      (fun e : OriginalCoordinates p =>
        GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2) :=
    (GeneratedBlockDrawLaw.measurable_generatedCurrentTarget p s).comp measurable_snd
  exact measurable_boundaryAtOriginal_atom p s ids rewards C_star C_h eta b |>.inter <|
    (measurableSet_eq_fun hprofile measurable_const).inter <|
      (measurableSet_eq_fun htarget measurable_const).inter <|
        hC.preimage (measurable_futureRowOf p s)

/-- The enlarged side-past event includes any measurable analysis-side event
and the actual boundary atom. -/
def sideBoundaryEvent (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : Set (SidePast p s)) (b : ReferenceInitializationRun.Boundary p) :
    Set (SidePast p s) :=
  {w | w ∈ A ∧ boundaryFromSide p s ids rewards C_star C_h eta w = b}

theorem measurableSet_sideBoundaryEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet (sideBoundaryEvent p s ids rewards C_star C_h eta A b) :=
  hA.inter (measurable_boundaryFromSide_atom p s ids rewards C_star C_h eta b)

/-- The same joint event with an arbitrary measurable test on the enlarged
analysis side. -/
def generatedBoundaryProfileTargetFutureEventWithSide (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : Set (SidePast p s)) (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))) :
    Set (OriginalCoordinates p) :=
  {e | analysisSideOf p s e ∈ A ∧
    e ∈ generatedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h eta b c z C}

theorem measurableSet_generatedBoundaryProfileTargetFutureEventWithSide
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    MeasurableSet (generatedBoundaryProfileTargetFutureEventWithSide p s ids rewards
      C_star C_h eta A b c z C) := by
  exact (hA.preimage (measurable_analysisSideOf p s)).inter <|
    measurableSet_generatedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h
      eta b c z C hC

theorem boundaryAtom_mass_eq_sidePast_mass (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) :
    originalCoordinatesLaw p
      {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b} =
    sidePastLaw p s
      {w | boundaryFromSide p s ids rewards C_star C_h eta w = b} := by
  let sideAtom : Set (SidePast p s) :=
    {w | boundaryFromSide p s ids rewards C_star C_h eta w = b}
  let imageSet : Set (SidePast p s × FutureCoordinates p s) := sideAtom ×ˢ Set.univ
  have hside : MeasurableSet sideAtom :=
    measurable_boundaryFromSide_atom p s ids rewards C_star C_h eta b
  have himage : MeasurableSet imageSet :=
    MeasurableSet.prod hside MeasurableSet.univ
  have hpreimage : (analysisSplitEquiv p s) ⁻¹' imageSet =
      {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b} := by
    ext e
    simp only [Set.mem_preimage, imageSet, Set.mem_prod, Set.mem_univ, sideAtom,
      Set.mem_ofPred_eq, and_true]
    change boundaryFromSide p s ids rewards C_star C_h eta
        (analysisSideOf p s e) = b ↔
      boundaryAtOriginal p s ids rewards C_star C_h eta e = b
    rw [← boundaryAtOriginal_eq_fromAnalysisSide p s ids rewards C_star C_h eta e]
  calc
    _ = originalCoordinatesLaw p ((analysisSplitEquiv p s) ⁻¹' imageSet) := by
      rw [hpreimage]
    _ = (originalCoordinatesLaw p).map (analysisSplitEquiv p s) imageSet := by
      symm
      rw [Measure.map_apply (analysisSplitEquiv p s).measurable himage]
    _ = regroupedCoordinatesLaw p s imageSet := by
      rw [(measurePreserving_analysisSplitEquiv p s).map_eq]
    _ = sidePastLaw p s sideAtom := by
      simp [imageSet, sideAtom, regroupedCoordinatesLaw, profileTargetFutureLaw,
        Measure.prod_prod]

/-- Unnormalized joint factorization, with any measurable event in the
enlarged retained side intersected with the boundary atom. No division or
positive-mass condition is used. -/
theorem generatedBoundary_jointProfileTargetFuture_factorization_with_side
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    originalCoordinatesLaw p
      (generatedBoundaryProfileTargetFutureEventWithSide p s ids rewards C_star C_h
        eta A b c z C) =
      originalCoordinatesLaw p
        {e | analysisSideOf p s e ∈ A ∧
          boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s) C := by
  let sideEvent : Set (SidePast p s) :=
    sideBoundaryEvent p s ids rewards C_star C_h eta A b
  let profileTargetEvent : Set (CurrentCoordinates p ×
      CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)) :=
    ((rawProfileEvent p b c ×ˢ targetScalarEvent p z) ×ˢ C)
  let imageSet : Set (SidePast p s × FutureCoordinates p s) :=
    sideEvent ×ˢ profileTargetEvent
  have hside : MeasurableSet sideEvent :=
    measurableSet_sideBoundaryEvent p s ids rewards C_star C_h eta A hA b
  have hcurrent : MeasurableSet (rawProfileEvent p b c ×ˢ targetScalarEvent p z) :=
    MeasurableSet.prod (measurableSet_rawProfileEvent p b c)
      (measurableSet_targetScalarEvent p z)
  have hprofileTarget : MeasurableSet profileTargetEvent :=
    MeasurableSet.prod hcurrent hC
  have himage : MeasurableSet imageSet := MeasurableSet.prod hside hprofileTarget
  have hpreimage : (analysisSplitEquiv p s) ⁻¹' imageSet =
      generatedBoundaryProfileTargetFutureEventWithSide p s ids rewards C_star C_h
        eta A b c z C := by
    ext e
    have hboundary := boundaryAtOriginal_eq_fromAnalysisSide
      p s ids rewards C_star C_h eta e
    have hboundary' : boundaryAtOriginal p s ids rewards C_star C_h eta e =
        boundaryFromSide p s ids rewards C_star C_h eta (analysisSplitEquiv p s e).1 := by
      simpa only [analysisSideOf] using hboundary
    simp only [Set.mem_preimage, imageSet, Set.mem_prod, sideEvent,
      profileTargetEvent, sideBoundaryEvent,
      generatedBoundaryProfileTargetFutureEventWithSide,
      generatedBoundaryProfileTargetFutureEvent, rawProfileEvent, targetScalarEvent,
      analysisSideOf, futureRowOf, Set.mem_ofPred_eq]
    rw [← hboundary',
      analysisSplitEquiv_currentProfile p s e,
      analysisSplitEquiv_currentTargetScalar p s e]
    simp [GeneratedBlockDrawLaw.generatedCurrentBlockProfile,
      GeneratedBlockDrawLaw.generatedCurrentTarget, and_assoc]
  have hsideMass : originalCoordinatesLaw p
      {e | analysisSideOf p s e ∈ A ∧
        boundaryAtOriginal p s ids rewards C_star C_h eta e = b} =
      sidePastLaw p s sideEvent := by
    have hsection : (analysisSplitEquiv p s) ⁻¹' (sideEvent ×ˢ
        (Set.univ : Set (FutureCoordinates p s))) =
        {e | analysisSideOf p s e ∈ A ∧
          boundaryAtOriginal p s ids rewards C_star C_h eta e = b} := by
      ext e
      simp [Set.mem_preimage, Set.mem_prod, sideEvent, sideBoundaryEvent,
        analysisSideOf, boundaryAtOriginal_eq_fromAnalysisSide]
    have hsectionMeas : MeasurableSet (sideEvent ×ˢ
        (Set.univ : Set (FutureCoordinates p s))) :=
      MeasurableSet.prod hside MeasurableSet.univ
    calc
      originalCoordinatesLaw p
          {e | analysisSideOf p s e ∈ A ∧
            boundaryAtOriginal p s ids rewards C_star C_h eta e = b} =
          originalCoordinatesLaw p
            ((analysisSplitEquiv p s) ⁻¹' (sideEvent ×ˢ
              (Set.univ : Set (FutureCoordinates p s)))) := by
              rw [hsection]
      _ = (originalCoordinatesLaw p).map (analysisSplitEquiv p s)
          (sideEvent ×ˢ (Set.univ : Set (FutureCoordinates p s))) := by
            symm
            rw [Measure.map_apply (analysisSplitEquiv p s).measurable hsectionMeas]
      _ = regroupedCoordinatesLaw p s (sideEvent ×ˢ Set.univ) := by
            rw [(measurePreserving_analysisSplitEquiv p s).map_eq]
      _ = sidePastLaw p s sideEvent := by
            simp [regroupedCoordinatesLaw, Measure.prod_prod]
  have hprofileMass := rawProfileEvent_mass p b c
  have htargetMass := targetScalarEvent_mass p z
  calc
    originalCoordinatesLaw p
        (generatedBoundaryProfileTargetFutureEventWithSide p s ids rewards C_star C_h
          eta A b c z C) =
      (originalCoordinatesLaw p).map (analysisSplitEquiv p s) imageSet := by
        rw [← hpreimage]
        symm
        rw [Measure.map_apply (analysisSplitEquiv p s).measurable himage]
    _ = regroupedCoordinatesLaw p s imageSet := by
      rw [(measurePreserving_analysisSplitEquiv p s).map_eq]
    _ = sidePastLaw p s sideEvent *
        ((PrivateSourceStreams.blockScalarProfileLaw p (rawProfileEvent p b c) *
            ContinuousCategorical.uniform (targetScalarEvent p z)) *
          CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s) C) := by
      simp [imageSet, profileTargetEvent, regroupedCoordinatesLaw, profileTargetFutureLaw,
        Measure.prod_prod]
    _ = originalCoordinatesLaw p
        {e | analysisSideOf p s e ∈ A ∧
          boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s) C := by
      rw [hprofileMass, htargetMass, ← hsideMass]
      simp only [mul_assoc]

/-- Requested boundary/profile/target/future factorization. Boundary atoms
may be null or unreachable; the proof uses no conditional probability. -/
theorem generatedBoundary_jointProfileTargetFuture_factorization
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    originalCoordinatesLaw p
      (generatedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h eta b c z C) =
      originalCoordinatesLaw p {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s) C := by
  have h := generatedBoundary_jointProfileTargetFuture_factorization_with_side
    p s ids rewards C_star C_h eta Set.univ MeasurableSet.univ b c z C hC
  simpa [generatedBoundaryProfileTargetFutureEventWithSide,
    generatedBoundaryProfileTargetFutureEvent, analysisSideOf] using h

/-- Event for a genuinely processed current block, recording the original
full labelled profile, target, complete future row, and the physical triple
and target of an incoming follower/coordinator. Its hypotheses are the
accepted ordinary-boundary guards; it is undefined for stopped or informed
branches rather than manufacturing physical fields there. -/
def generatedProcessedBoundaryProfileTargetFutureEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))) :
    Set (OriginalCoordinates p) :=
  {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b ∧
    GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2 = c ∧
    GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 = z ∧
    futureRowOf p s e ∈ C ∧
    GeneratedBlockDrawLaw.generatedPhysicalBlockDraw p s ids e.1 rewards C_star C_h eta
      b hcompleted hnotStopped i e.2 =
        c (BootstrapPhysicalInput.sourceFollowerIndex p i.1) ∧
    GeneratedBlockDrawLaw.generatedPhysicalBlockTarget p s ids e.1 rewards C_star C_h eta
      b hcompleted hnotStopped e.2 = z}

/-- On the guarded ordinary block path, the selected physical follower triple
and coordinator target are exactly the entries in the original full profile
and target map. -/
theorem generatedProcessedBoundaryEvent_eq (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s))) :
    generatedProcessedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h eta
      b hcompleted hnotStopped i c z C =
    generatedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h eta b c z C := by
  ext e
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨hboundary, hprofile, htarget, hfuture⟩
    have hfields := GeneratedBlockDrawLaw.actualProcessedBlock_draw_fields p s ids e.1
      rewards C_star C_h eta e.2 b (by simpa [boundaryAtOriginal] using hboundary)
      hcompleted hnotStopped
    rcases hfields with ⟨_, hphysical, hphysicalTarget⟩
    refine ⟨hboundary, hprofile, htarget, hfuture, ?_, ?_⟩
    · calc
        GeneratedBlockDrawLaw.generatedPhysicalBlockDraw p s ids e.1 rewards C_star C_h eta
            b hcompleted hnotStopped i e.2 =
          GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2
            (BootstrapPhysicalInput.sourceFollowerIndex p i.1) := by
              simpa [GeneratedBlockDrawLaw.generatedPhysicalBlockDraw] using hphysical i
        _ = c (BootstrapPhysicalInput.sourceFollowerIndex p i.1) :=
          congrFun hprofile (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    · calc
        GeneratedBlockDrawLaw.generatedPhysicalBlockTarget p s ids e.1 rewards C_star C_h eta
            b hcompleted hnotStopped e.2 =
          GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 := by
            simpa [GeneratedBlockDrawLaw.generatedPhysicalBlockTarget] using hphysicalTarget
        _ = z := htarget

theorem measurableSet_generatedProcessedBoundaryProfileTargetFutureEvent
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    MeasurableSet (generatedProcessedBoundaryProfileTargetFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped i c z C) := by
  rw [generatedProcessedBoundaryEvent_eq p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i c z C]
  exact measurableSet_generatedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h
    eta b c z C hC

/-- The joint future factorization restricted to a true processed block and a
specified incoming follower. The profile law still derives all arm weights
from the actual boundary's `weight_ge_one` certificate. -/
theorem generatedProcessedBoundary_jointProfileTargetFuture_factorization
    (p : Parameters) (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K)
    (C : Set (CompleteRowStoppingLaw.FutureArray p (blockStartIndex p s)))
    (hC : MeasurableSet C) :
    originalCoordinatesLaw p
      (generatedProcessedBoundaryProfileTargetFutureEvent p s ids rewards C_star C_h eta
        b hcompleted hnotStopped i c z C) =
      originalCoordinatesLaw p
        {e | boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p (blockStartIndex p s) C := by
  rw [generatedProcessedBoundaryEvent_eq p s ids rewards C_star C_h eta b hcompleted
    hnotStopped i c z C]
  exact generatedBoundary_jointProfileTargetFuture_factorization p s ids rewards C_star C_h
    eta b c z C hC
