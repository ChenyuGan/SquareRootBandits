/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationNativeJointLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Finite killed replay of the actual post-invocation joint observation

The full observation exposes the physical source, so replay retains that
source and samples only the two not-yet-exposed auxiliary scalars. The initial
measure is the actual produced post-cell law, with its original append and
both installation labels. Killing is before the date being advanced; the
terminal boundary does not require a physical control at T.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
These are internal joint-law results, without a manuscript closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt)
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationNativeJointLaw
open ReferenceFirstNextLiftFutureAuxiliaryPairLaw

namespace Bandits.Support.ReferencePostInvocationKilledJointLaw

variable {p : ConstructorDimensions.Parameters}

abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) := by
  unfold ContinuousLearningRows.TimeControl
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

private theorem measurable_getLast? {A : Type*} [MeasurableSpace A] :
    Measurable (List.getLast? : List A → Option A) := by
  have he : Measurable (fun x : ℕ × (ℕ → Unit ⊕ A) => x.2 (x.1 - 1)) := by
    apply measurable_from_prod_countable_right
    intro n
    exact measurable_pi_apply (n - 1)
  have ht : Measurable (fun x : Unit ⊕ A =>
      Sum.elim (fun _ => (none : Option A)) some x) :=
    measurable_const.sumElim
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert ht.comp (he.comp ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates) using 1
  funext L
  rw [List.getLast?_eq_getElem?]
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt]
  cases h : L[L.length - 1]? <;> rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The two fresh scalar labels, with their original independent laws. -/
def auxiliaryPairLaw : Measure (Scalar × Scalar) :=
  ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw

instance auxiliaryPairLaw_probability : IsProbabilityMeasure (auxiliaryPairLaw) := by
  unfold auxiliaryPairLaw
  infer_instance

/-- A date-local array notation. Only the two coordinates at the current date
are consumed; its independence of all other coordinates is proved below. -/
def dateAuxiliary (x : Scalar × Scalar) : Auxiliary p :=
  fun j => if j.2 = 0 then x.1 else x.2

theorem measurable_dateAuxiliary : Measurable (dateAuxiliary (p := p)) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j.2 = 0
  · simpa only [dateAuxiliary, h, ite_true] using
      (measurable_fst : Measurable (Prod.fst : Scalar × Scalar → Scalar))
  · simpa only [dateAuxiliary, h, ite_false] using
      (measurable_snd : Measurable (Prod.snd : Scalar × Scalar → Scalar))

theorem appendNoncallDate_dateAuxiliary (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (a : Auxiliary p)
    (s : SlowSet p × List (LogicalCell p rate)) :
    appendNoncallDate rate rewards C_star C_h q z
        (dateAuxiliary (auxiliaryPair q a)) s =
      appendNoncallDate rate rewards C_star C_h q z a s := by
  unfold appendNoncallDate
  rw [noncallDateCell_auxiliary_ext rate rewards C_star C_h q z s.1
    (dateAuxiliary (auxiliaryPair q a)) a (by rfl) (by rfl)]

/-- Extend the actual post-cell readout to its first PRE boundary. The seed
is the residual of the original produced last cell; no new cell is installed. -/
def initialExtension (t : Fin p.T) (o : InitialObservation rate t) :
    PrefixObservation rate t t.succ :=
  (o, (fun i => o.2.1 ⟨i.val, by have hi := i.property; change i.val.1.val < t.val + 1 at hi; omega⟩,
    (prefixNumerical rate rewards C_star C_h t.succ o.1.1.2,
      o.2.2.getLast?.map (fun c => (c.nextSlowSet, o.2.2)))))

theorem measurable_initialExtension (t : Fin p.T) :
    Measurable (initialExtension rate rewards C_star C_h t) := by
  have ha : Measurable (fun o : InitialObservation rate t =>
      fun i : PrefixAuxiliaryIndex t.succ =>
        o.2.1 ⟨i.val, by have hi := i.property; change i.val.1.val < t.val + 1 at hi; omega⟩) :=
    Measurable.of_eval (fun i => (measurable_pi_apply _).comp measurable_snd.fst)
  have hn : Measurable (fun o : InitialObservation rate t =>
      prefixNumerical rate rewards C_star C_h t.succ o.1.1.2) :=
    (measurable_prefixNumerical rate rewards C_star C_h t.succ).comp measurable_fst.fst.snd
  have hl : Measurable (fun o : InitialObservation rate t =>
      o.2.2.getLast?.map (fun c => (c.nextSlowSet, o.2.2))) := by
    convert measurable_option_cases _ (measurable_getLast?.comp measurable_snd.snd)
      (fun _ : InitialObservation rate t => none) measurable_const
      (fun v : InitialObservation rate t × LogicalCell p rate => some (v.2.nextSlowSet, v.1.2.2))
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
        (((measurable_logicalCell_nextSlowSet.comp measurable_snd).mono le_rfl le_top).prodMk
          measurable_fst.snd.snd)) using 1
    funext o
    dsimp only [Function.comp_apply]
    cases o.2.2.getLast? <;> rfl
  exact measurable_id.prodMk (ha.prodMk (hn.prodMk hl))

variable (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t : Fin p.T)

local notation "Lift" => BranchLift rate rewards C_star C_h b u t
local notation "Lambda" => branchLaw rate rewards C_star C_h control0 b u t
local notation "O" => branchObservation rate rewards C_star C_h control0 b u t

instance branchLaw_finite : IsFiniteMeasure (Lambda) := by
  cases b
  · exact ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw_finite rate rewards C_star C_h u t control0
  · exact ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_finite rate rewards C_star C_h u t

/-- Literal initial readout, with the original sources, vector, append and labels. -/
def branchInitial : Lift → InitialObservation rate t := match b with
  | false => nonrenewedInitialObservation rate rewards C_star C_h control0 u t
  | true => renewedInitialObservation rate rewards C_star C_h control0 u t

/-- The accepted unnormalized post-cell measure, selected by the literal branch. -/
def postCellLaw : Measure (InitialObservation rate t) := match b with
  | false => nonrenewedPostCellLaw rate rewards C_star C_h control0 u t
  | true => renewedPostCellLaw rate rewards C_star C_h control0 u t

theorem measurable_branchInitial :
    Measurable (branchInitial rate rewards C_star C_h control0 b u t) := by
  cases b
  · exact measurable_nonrenewedInitialObservation rate rewards C_star C_h control0 u t
  · exact measurable_renewedInitialObservation rate rewards C_star C_h control0 u t

theorem postCellLaw_eq_map :
    postCellLaw rate rewards C_star C_h control0 b u t =
      (Lambda).map (branchInitial rate rewards C_star C_h control0 b u t) := by
  cases b <;> rfl

theorem branchObservation_initial (w : Lift) :
    O t.succ w = initialExtension rate rewards C_star C_h t
      (branchInitial rate rewards C_star C_h control0 b u t w) := by
  cases b
  all_goals
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    change postInvocationPrefix rate rewards C_star C_h t t.succ _ _ = _
    simp only [postInvocationPrefix, Fin.val_succ]
    rw [noncallCalendar_initial rate rewards C_star C_h t _ _ _ (t.val + 1) le_rfl]
    change some (_, postHistory _) = (postHistory _).getLast?.map _
    rw [postHistory_last]
    rfl

theorem branchObservation_source (n : Fin (p.T + 1)) (w : Lift) :
    (O n w).1.1.1.2 = insertedPhysicalSource rate
      (branchTransition rate rewards C_star C_h control0 b u t w) := by
  cases b <;> rfl

theorem branchObservation_prefix (n : Fin (p.T + 1)) (w : Lift) :
    (O n w).2.2.2 = postInvocationPrefix rate rewards C_star C_h t n
      (branchTransition rate rewards C_star C_h control0 b u t w) w.1.2 := by
  cases b <;> rfl

/-- The actual survival event on [t+1,n), without a boundary-n test. -/
def survival (n : Fin (p.T + 1)) : Set Lift :=
  {w | NoCallBetween rate rewards C_star C_h t n (O n w).1.1.1.2}

theorem measurableSet_survival (n : Fin (p.T + 1)) :
    MeasurableSet (survival rate rewards C_star C_h control0 b u t n) :=
  (measurableSet_noCallBetween rate rewards C_star C_h control0 t n).preimage
    ((measurable_branchObservation rate rewards C_star C_h control0 b u t n).fst.fst.fst.snd)

theorem survival_iff_prefix (n : Fin (p.T + 1)) (w : Lift) :
    w ∈ survival rate rewards C_star C_h control0 b u t n ↔
      (O n w).2.2.2.isSome = true := by
  rw [survival, Set.mem_ofPred_eq, branchObservation_prefix, postInvocationPrefix,
    noncallCalendar_isSome, branchObservation_source]

theorem survival_initial :
    survival rate rewards C_star C_h control0 b u t t.succ = Set.univ := by
  ext w
  exact iff_true_intro (noCallBetween_initial rate rewards C_star C_h t _)

section Successor

variable (q : Fin p.T)

/-- Append exactly one date to the used auxiliary coordinates. -/
def extendAuxiliary (a : PrefixAuxiliaryIndex q.castSucc → Scalar) (x : Scalar × Scalar) :
    PrefixAuxiliaryIndex q.succ → Scalar := fun i =>
  if h : i.val.1.val < q.val then a ⟨i.val, h⟩
  else if i.val.2 = 0 then x.1 else x.2

theorem measurable_extendAuxiliary : Measurable (fun ax :
    (PrefixAuxiliaryIndex q.castSucc → Scalar) × (Scalar × Scalar) => extendAuxiliary q ax.1 ax.2) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : i.val.1.val < q.val
  · simp only [extendAuxiliary, dite_eq_left h]
    exact (measurable_pi_apply (⟨i.val, h⟩ : PrefixAuxiliaryIndex q.castSucc)).comp measurable_fst
  · by_cases hl : i.val.2 = 0
    · simpa only [extendAuxiliary, h, dite_false, hl, ite_true] using
        (measurable_snd.fst : Measurable (fun ax :
          (PrefixAuxiliaryIndex q.castSucc → Scalar) × (Scalar × Scalar) => ax.2.1))
    · simpa only [extendAuxiliary, h, dite_false, hl, ite_false] using
        (measurable_snd.snd : Measurable (fun ax :
          (PrefixAuxiliaryIndex q.castSucc → Scalar) × (Scalar × Scalar) => ax.2.2))

/-- Source-preserving replay: numerical completion reads the full physical
word, and the logical list appends the accepted current cell if one exists. -/
def successor (ox : PrefixObservation rate t q.castSucc × (Scalar × Scalar)) :
    PrefixObservation rate t q.succ :=
  (ox.1.1, (extendAuxiliary q ox.1.2.1 ox.2,
    (prefixNumerical rate rewards C_star C_h q.succ ox.1.1.1.1.2,
      ox.1.2.2.2.map (appendNoncallDate rate rewards C_star C_h q
        ox.1.1.1.1.2 (dateAuxiliary ox.2)))))

theorem measurable_successor (control0 : ContinuousLearningRows.TimeControl p) : Measurable (successor rate rewards C_star C_h t q) := by
  let X := PrefixObservation rate t q.castSucc × (Scalar × Scalar)
  have ha : Measurable (fun ox : X => extendAuxiliary q ox.1.2.1 ox.2) :=
    (measurable_extendAuxiliary q).comp (measurable_fst.snd.fst.prodMk measurable_snd)
  have hn : Measurable (fun ox : X => prefixNumerical rate rewards C_star C_h q.succ ox.1.1.1.1.2) :=
    (measurable_prefixNumerical rate rewards C_star C_h q.succ).comp
    (measurable_fst.fst.fst.fst.snd : Measurable (fun ox : X => ox.1.1.1.1.2))
  have hl : Measurable (fun ox : X => ox.1.2.2.2.map
      (appendNoncallDate rate rewards C_star C_h q ox.1.1.1.1.2 (dateAuxiliary ox.2))) := by
    have hm := (measurable_appendNoncallDate rate rewards C_star C_h control0 q).comp
      ((measurable_fst.fst.fst.fst.fst.snd.prodMk
        (measurable_dateAuxiliary.comp measurable_fst.snd)).prodMk measurable_snd :
        Measurable (fun v : X × (SlowSet p × List (LogicalCell p rate)) =>
          ((v.1.1.1.1.1.2, dateAuxiliary v.1.2), v.2)))
    convert measurable_option_cases _ measurable_fst.snd.snd.snd
      (fun _ : X => none) measurable_const _
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hm) using 1
    funext ox
    dsimp only [Function.comp_apply]
    cases ox.1.2.2.2 <;> rfl
  exact measurable_fst.fst.prodMk (ha.prodMk (hn.prodMk hl))

theorem successor_actual (htq : t.val < q.val) (w : Lift)
    (hc : noCallAt rate rewards C_star C_h q (O q.castSucc w).1.1.1.2) :
    successor rate rewards C_star C_h t q (O q.castSucc w, auxiliaryPair q w.1.2) = O q.succ w := by
  apply Prod.ext
  · cases b <;> rfl
  apply Prod.ext
  · funext i
    dsimp only [successor, extendAuxiliary]
    split
    · cases b <;> rfl
    next h =>
      have hv : i.val.1 = q := Fin.ext (by have hi := i.property; change i.val.1.val < q.val + 1 at hi; omega)
      cases b <;> change (if i.val.2 = 0 then w.1.2 (q, 0) else w.1.2 (q, 1)) = w.1.2 i.val
      all_goals
        rcases i with ⟨⟨v, l⟩, hi⟩
        dsimp only at hv
        subst v
        fin_cases l <;> rfl
  apply Prod.ext
  · cases b <;> rfl
  change (O q.castSucc w).2.2.2.map _ = (O q.succ w).2.2.2
  rw [branchObservation_prefix, branchObservation_prefix, branchObservation_source]
  simp only [postInvocationPrefix, Fin.val_castSucc, Fin.val_succ]
  conv_rhs => rw [noncallCalendar]
  rw [branchObservation_source] at hc
  have hdate : t.val < q.val ∧ q.val < p.T := ⟨htq, q.isLt⟩
  simp only [dite_eq_left hdate, hc, ite_true]
  cases h : noncallCalendar rate rewards C_star C_h t
      (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w))
      w.1.2 (postSeed rate (branchTransition rate rewards C_star C_h control0 b u t w),
        postHistory (branchTransition rate rewards C_star C_h control0 b u t w)) q.val with
  | none => rfl
  | some s =>
      exact congrArg some (appendNoncallDate_dateAuxiliary rate rewards C_star C_h q _ w.1.2 s)

end Successor

section ReplayKernel

variable (q : Fin p.T)

/-- Replay of a full observation uses its SOURCE-DEPENDENT Dirac control,
and the two fresh auxiliary labels. The successor retains the same source. -/
def replayLaw (o : PrefixObservation rate t q.castSucc) :
    Measure (PrefixObservation rate t q.succ) :=
  ((replayControlLaw rate t q q.castSucc o).prod auxiliaryPairLaw).map
    (fun ω => successor rate rewards C_star C_h t q (o, ω.2))

include control0 in
theorem replayLaw_eq (o : PrefixObservation rate t q.castSucc) :
    replayLaw rate rewards C_star C_h t q o =
      auxiliaryPairLaw.map (fun x => successor rate rewards C_star C_h t q (o, x)) := by
  have hs : Measurable (fun ω : Innovation p => successor rate rewards C_star C_h t q (o, ω.2)) :=
    (measurable_successor rate rewards C_star C_h t q control0).comp
      (measurable_const.prodMk measurable_snd)
  rw [replayLaw, replayControlLaw, Measure.dirac_prod,
    Measure.map_map hs measurable_prodMk_left]
  rfl

include control0 in
theorem measurable_replayLaw : Measurable (replayLaw rate rewards C_star C_h t q) := by
  have hs := measurable_successor rate rewards C_star C_h t q control0
  have hm : Measurable (fun o : PrefixObservation rate t q.castSucc =>
      (auxiliaryPairLaw.map (Prod.mk o)).map (successor rate rewards C_star C_h t q)) :=
    (Measure.measurable_map _ hs).comp Measurable.map_prodMk_left
  convert hm using 1
  funext o
  rw [replayLaw_eq rate rewards C_star C_h control0 t q,
    Measure.map_map hs measurable_prodMk_left]
  rfl

/-- The Borel, source-compatible full-observation replay kernel. -/
def replayKernel : ProbabilityTheory.Kernel (PrefixObservation rate t q.castSucc)
    (PrefixObservation rate t q.succ) :=
  ⟨replayLaw rate rewards C_star C_h t q,
    measurable_replayLaw rate rewards C_star C_h control0 t q⟩

/-- Kill BEFORE invocation at q; there is no POST-clear or POST-overflow guard. -/
def killedKernel : ProbabilityTheory.Kernel (PrefixObservation rate t q.castSucc)
    (PrefixObservation rate t q.succ) :=
  ProbabilityTheory.Kernel.piecewise
    ((ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
      rate rewards C_star C_h control0 q).preimage measurable_fst.fst.fst.snd)
    (replayKernel rate rewards C_star C_h control0 t q) 0

/-- The product-and-map recurrence is exactly composition with the Borel
killed replay kernel, for every finite input measure. -/
theorem killedKernel_bind (μ : Measure (PrefixObservation rate t q.castSucc)) [IsFiniteMeasure μ] :
    μ.bind (killedKernel rate rewards C_star C_h control0 t q) =
      (((μ.restrict {o | noCallAt rate rewards C_star C_h q o.1.1.1.2}).prod
        auxiliaryPairLaw).map (successor rate rewards C_star C_h t q)) := by
  have hkill : MeasurableSet {o : PrefixObservation rate t q.castSucc |
      noCallAt rate rewards C_star C_h q o.1.1.1.2} :=
    (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
      rate rewards C_star C_h control0 q).preimage measurable_fst.fst.fst.snd
  apply Measure.ext_of_lintegral
  intro Phi hPhi
  have hF : Measurable (fun z : PrefixObservation rate t q.castSucc × (Scalar × Scalar) =>
      Phi (successor rate rewards C_star C_h t q z)) :=
    hPhi.comp (measurable_successor rate rewards C_star C_h t q control0)
  rw [Measure.lintegral_bind (ProbabilityTheory.Kernel.aemeasurable _) hPhi.aemeasurable,
    lintegral_map hPhi (measurable_successor rate rewards C_star C_h t q control0),
    lintegral_prod _ hF.aemeasurable,
    ← lintegral_indicator hkill]
  apply lintegral_congr
  intro o
  simp only [killedKernel, ProbabilityTheory.Kernel.piecewise_apply, Set.mem_preimage, Set.mem_ofPred_eq]
  by_cases hc : noCallAt rate rewards C_star C_h q o.1.1.1.2
  · simp only [Set.indicator, Set.mem_ofPred_eq, hc, ite_true]
    change (∫⁻ y, Phi y ∂replayLaw rate rewards C_star C_h t q o) = _
    rw [replayLaw_eq rate rewards C_star C_h control0 t q o]
    exact lintegral_map hPhi
      ((measurable_successor rate rewards C_star C_h t q control0).comp measurable_prodMk_left)
  · simp only [Set.indicator, Set.mem_ofPred_eq, hc, ite_false, zero_apply, lintegral_zero_measure]

theorem replayKernel_bind (μ : Measure (PrefixObservation rate t q.castSucc)) [IsFiniteMeasure μ] :
    μ.bind (replayKernel rate rewards C_star C_h control0 t q) =
      (μ.prod auxiliaryPairLaw).map (successor rate rewards C_star C_h t q) := by
  apply Measure.ext_of_lintegral
  intro Phi hPhi
  have hF : Measurable (fun z : PrefixObservation rate t q.castSucc × (Scalar × Scalar) =>
      Phi (successor rate rewards C_star C_h t q z)) :=
    hPhi.comp (measurable_successor rate rewards C_star C_h t q control0)
  rw [Measure.lintegral_bind (ProbabilityTheory.Kernel.aemeasurable _) hPhi.aemeasurable,
    lintegral_map hPhi (measurable_successor rate rewards C_star C_h t q control0),
    lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro o
  change (∫⁻ y, Phi y ∂replayLaw rate rewards C_star C_h t q o) = _
  rw [replayLaw_eq rate rewards C_star C_h control0 t q o]
  exact lintegral_map hPhi
    ((measurable_successor rate rewards C_star C_h t q control0).comp measurable_prodMk_left)

end ReplayKernel

section Iteration

variable (q : Fin p.T) (htq : t.val < q.val)

/-- Erasing a later auxiliary pair changes none of the full PRE observations.
The physical sources remain literal, rather than being erased freshness data. -/
theorem branchObservation_auxiliary_pair (n : Fin (p.T + 1))
    (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : BranchSource rate rewards C_star C_h b u t) (a a' : Auxiliary p)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (h : ∀ j, j.1 ≠ q → a j = a' j) :
    O n ((z, a), v) = O n ((z, a'), v) := by
  have hp := branchPast_auxiliary_pair rate rewards C_star C_h control0 b u t q n
    htn hnq z a a' v h
  apply Prod.ext
  · apply Prod.ext
    · cases b <;> rfl
    · simpa only [branchPast, pastProjection] using
        congrArg (fun o : PrefixObservation rate t n => o.1.2) hp
  · simpa only [branchPast, pastProjection] using
      congrArg (fun o : PrefixObservation rate t n => o.2) hp

include htq in
theorem branchObservation_eraseLift (w : Lift) :
    O q.castSucc (eraseLift q w) = O q.castSucc w := by
  apply branchObservation_auxiliary_pair rate rewards C_star C_h control0 b u t q
    q.castSucc htq le_rfl w.1.1 _ _ w.2
  intro j hj
  exact eraseAuxiliaryPair_apply_other q w.1.2 j
    (fun he => hj (congrArg Prod.fst he)) (fun he => hj (congrArg Prod.fst he))

include htq in
/-- Only the fresh auxiliary pair factors from the full source observation.
No independently sampled physical control occurs on the right. -/
theorem branchObservation_pair_product :
    (Lambda).map (fun w => (O q.castSucc w, auxiliaryPair q w.1.2)) =
      ((Lambda).map (O q.castSucc)).prod auxiliaryPairLaw := by
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have herase : Measurable (eraseLift (Z := BranchSource rate rewards C_star C_h b u t) q) :=
    measurable_eraseLift q
  have hpair : Measurable (fun w : Lift => auxiliaryPair q w.1.2) :=
    (measurable_auxiliaryPair q).comp measurable_fst.snd
  have hj : (Lambda).map (fun w => (eraseLift q w, auxiliaryPair q w.1.2)) =
      ((Lambda).map (eraseLift q)).prod auxiliaryPairLaw := by
    cases b
    · exact nonrenewedLiftLaw_erase_pair rate rewards C_star C_h u t q htq control0
    · exact renewalLiftLaw_erase_pair rate rewards C_star C_h u t q htq
  have hm := congrArg (fun μ : Measure (Lift × (Scalar × Scalar)) =>
    μ.map (Prod.map (O q.castSucc) id)) hj
  rw [Measure.map_map (hO.prodMap measurable_id) (herase.prodMk hpair)] at hm
  have hprod := Measure.map_prod_map ((Lambda).map (eraseLift q)) auxiliaryPairLaw hO measurable_id
  rw [Measure.map_id] at hprod
  rw [← hprod, Measure.map_map hO herase] at hm
  simpa only [Function.comp_def, Prod.map_apply, id_eq,
    branchObservation_eraseLift rate rewards C_star C_h control0 b u t q htq] using hm

include htq in
/-- Independence survives restriction by any Borel event of the full PRE
observation, retaining the original unnormalized event and index masses. -/
theorem branchObservation_pair_restrict (S : Set (PrefixObservation rate t q.castSucc))
    (hS : MeasurableSet S) :
    (((Lambda).map (O q.castSucc)).restrict S).prod auxiliaryPairLaw =
      ((Lambda).restrict ((O q.castSucc) ⁻¹' S)).map
        (fun w => (O q.castSucc w, auxiliaryPair q w.1.2)) := by
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hpair : Measurable (fun w : Lift => auxiliaryPair q w.1.2) :=
    (measurable_auxiliaryPair q).comp measurable_fst.snd
  rw [Measure.restrict_prod_eq_prod_univ,
    ← branchObservation_pair_product rate rewards C_star C_h control0 b u t q htq,
    Measure.restrict_map (hO.prodMk hpair) (hS.prod MeasurableSet.univ)]
  have hpre : (fun w : Lift => (O q.castSucc w, auxiliaryPair q w.1.2)) ⁻¹'
      (S ×ˢ Set.univ) = (O q.castSucc) ⁻¹' S := by
    ext w
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [hpre]

include htq in
theorem survival_successor_iff (w : Lift) :
    w ∈ survival rate rewards C_star C_h control0 b u t q.succ ↔
      w ∈ survival rate rewards C_star C_h control0 b u t q.castSucc ∧
        noCallAt rate rewards C_star C_h q (O q.castSucc w).1.1.1.2 := by
  have hs : (O q.succ w).1.1.1.2 = (O q.castSucc w).1.1.1.2 := by cases b <;> rfl
  change NoCallBetween rate rewards C_star C_h t q.succ _ ↔ _
  rw [hs, noCallBetween_succ]
  simp only [htq, true_implies]
  rfl

include htq in
/-- The actual killed one-date measure equality, before finite iteration. -/
theorem killed_successor_map :
    (((((Lambda).restrict (survival rate rewards C_star C_h control0 b u t q.castSucc)).map
      (O q.castSucc)).restrict {o | noCallAt rate rewards C_star C_h q o.1.1.1.2}).prod
        auxiliaryPairLaw).map (successor rate rewards C_star C_h t q) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t q.succ)).map (O q.succ) := by
  let S : Set (PrefixObservation rate t q.castSucc) :=
    {o | NoCallBetween rate rewards C_star C_h t q.succ o.1.1.1.2}
  have hS : MeasurableSet S :=
    (measurableSet_noCallBetween rate rewards C_star C_h control0 t q.succ).preimage
      measurable_fst.fst.fst.snd
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hkill : MeasurableSet {o : PrefixObservation rate t q.castSucc |
      noCallAt rate rewards C_star C_h q o.1.1.1.2} :=
    (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
      rate rewards C_star C_h control0 q).preimage measurable_fst.fst.fst.snd
  have hE : (O q.castSucc) ⁻¹' S = survival rate rewards C_star C_h control0 b u t q.succ := by
    ext w
    have hs : (O q.castSucc w).1.1.1.2 = (O q.succ w).1.1.1.2 := by cases b <;> rfl
    change NoCallBetween rate rewards C_star C_h t q.succ _ ↔ NoCallBetween rate rewards C_star C_h t q.succ _
    rw [hs]
  have hleft : (((Lambda).restrict
      (survival rate rewards C_star C_h control0 b u t q.castSucc)).map (O q.castSucc)).restrict
        {o | noCallAt rate rewards C_star C_h q o.1.1.1.2} =
      ((Lambda).map (O q.castSucc)).restrict S := by
    rw [Measure.restrict_map hO hkill, Measure.restrict_restrict (hkill.preimage hO),
      Measure.restrict_map hO hS, hE]
    apply congrArg (fun E : Set Lift => ((Lambda).restrict E).map (O q.castSucc))
    ext w
    exact and_comm.trans (survival_successor_iff rate rewards C_star C_h control0 b u t q htq w).symm
  rw [hleft, branchObservation_pair_restrict rate rewards C_star C_h control0 b u t q htq S hS, hE]
  have hJ : Measurable (fun w : Lift => (O q.castSucc w, auxiliaryPair q w.1.2)) :=
    hO.prodMk ((measurable_auxiliaryPair q).comp measurable_fst.snd)
  refine (Measure.map_map (measurable_successor rate rewards C_star C_h t q control0) hJ).trans ?_
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_survival rate rewards C_star C_h control0 b u t q.succ)] with w hw
  exact successor_actual rate rewards C_star C_h control0 b u t q htq w
    ((survival_successor_iff rate rewards C_star C_h control0 b u t q htq w).mp hw).2

end Iteration

/-- Boundary after k physical dates following the produced installation. -/
def boundary (t : Fin p.T) (k : ℕ) (hk : t.val + 1 + k ≤ p.T) : Fin (p.T + 1) :=
  ⟨t.val + 1 + k, Nat.lt_succ_of_le hk⟩

/-- Actual finite killed recurrence. Its only initial pushforward is from the
accepted post-cell law; later dates use the preceding measure and fresh pair. -/
def betaAux : (k : ℕ) → (hk : t.val + 1 + k ≤ p.T) →
    Measure (PrefixObservation rate t (boundary t k hk))
  | 0, _ => (postCellLaw rate rewards C_star C_h control0 b u t).map
      (initialExtension rate rewards C_star C_h t)
  | k + 1, hk =>
      let q : Fin p.T := ⟨t.val + 1 + k, by omega⟩
      (((betaAux k (by omega)).restrict
        {o | noCallAt rate rewards C_star C_h q o.1.1.1.2}).prod auxiliaryPairLaw).map
          (successor rate rewards C_star C_h t q)

/-- The recurrence retains the SAME generated history at every finite date. -/
theorem actual_map_eq_betaAux : ∀ k (hk : t.val + 1 + k ≤ p.T),
    ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t (boundary t k hk))).map
      (O (boundary t k hk)) = betaAux rate rewards C_star C_h control0 b u t k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      change ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t t.succ)).map
        (O t.succ) = (postCellLaw rate rewards C_star C_h control0 b u t).map
          (initialExtension rate rewards C_star C_h t)
      rw [survival_initial, Measure.restrict_univ, postCellLaw_eq_map,
        Measure.map_map (measurable_initialExtension rate rewards C_star C_h t)
          (measurable_branchInitial rate rewards C_star C_h control0 b u t)]
      congr 1
      exact funext (branchObservation_initial rate rewards C_star C_h control0 b u t)
  | succ k ih =>
      intro hk
      let q : Fin p.T := ⟨t.val + 1 + k, by omega⟩
      have htk : t.val < q.val := by dsimp only [q]; omega
      have hprev := ih (by omega : t.val + 1 + k ≤ p.T)
      change ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t q.castSucc)).map
        (O q.castSucc) = betaAux rate rewards C_star C_h control0 b u t k (by omega) at hprev
      change ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t q.succ)).map
        (O q.succ) = (((betaAux rate rewards C_star C_h control0 b u t k (by omega)).restrict
          {o | noCallAt rate rewards C_star C_h q o.1.1.1.2}).prod auxiliaryPairLaw).map
            (successor rate rewards C_star C_h t q)
      rw [← hprev]
      exact (killed_successor_map rate rewards C_star C_h control0 b u t q htk).symm

/-- Finite killed law on the canonical boundary carrier, including n=T. -/
def beta (n : Fin (p.T + 1)) (htn : t.val < n.val) : Measure (PrefixObservation rate t n) :=
  let k := n.val - (t.val + 1)
  have hk : t.val + 1 + k ≤ p.T := by dsimp only [k]; have hn := n.isLt; omega
  have he : boundary t k hk = n := Fin.ext (by dsimp only [boundary, k]; omega)
  he ▸ betaAux rate rewards C_star C_h control0 b u t k hk

private theorem transport_actual_map (n m : Fin (p.T + 1)) (h : n = m) :
    (h ▸ (((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map (O n)) :
      Measure (PrefixObservation rate t m)) =
        ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t m)).map (O m) := by
  cases h
  rfl

/-- Equality with the actual restricted pushforward is a theorem of the
finite recurrence, rather than its definition. -/
theorem actual_map_eq_beta (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map (O n) =
      beta rate rewards C_star C_h control0 b u t n htn := by
  let k := n.val - (t.val + 1)
  have hk : t.val + 1 + k ≤ p.T := by dsimp only [k]; have hn := n.isLt; omega
  have he : boundary t k hk = n := Fin.ext (by dsimp only [boundary, k]; omega)
  have hb := actual_map_eq_betaAux rate rewards C_star C_h control0 b u t k hk
  have htransport := congrArg (fun μ : Measure (PrefixObservation rate t (boundary t k hk)) =>
    (he ▸ μ : Measure (PrefixObservation rate t n))) hb
  exact (transport_actual_map rate rewards C_star C_h control0 b u t _ _ he).symm.trans htransport

theorem beta_boundary (k : ℕ) (hk : t.val + 1 + k ≤ p.T) :
    beta rate rewards C_star C_h control0 b u t (boundary t k hk) (by dsimp only [boundary]; omega) =
      betaAux rate rewards C_star C_h control0 b u t k hk :=
  (actual_map_eq_beta rate rewards C_star C_h control0 b u t (boundary t k hk)
    (by dsimp only [boundary]; omega)).symm.trans
      (actual_map_eq_betaAux rate rewards C_star C_h control0 b u t k hk)

theorem beta_initial :
    beta rate rewards C_star C_h control0 b u t t.succ (Nat.lt_succ_self _) =
      (postCellLaw rate rewards C_star C_h control0 b u t).map
        (initialExtension rate rewards C_star C_h t) :=
  beta_boundary rate rewards C_star C_h control0 b u t 0 (by have ht := t.isLt; omega)

/-- A literal one-date killed recurrence on the full canonical state. -/
theorem beta_successor (q : Fin p.T) (htq : t.val < q.val) :
    beta rate rewards C_star C_h control0 b u t q.succ (by change t.val < q.val + 1; omega) =
      (((beta rate rewards C_star C_h control0 b u t q.castSucc htq).restrict
        {o | noCallAt rate rewards C_star C_h q o.1.1.1.2}).prod auxiliaryPairLaw).map
          (successor rate rewards C_star C_h t q) := by
  rw [← actual_map_eq_beta, ← actual_map_eq_beta]
  exact (killed_successor_map rate rewards C_star C_h control0 b u t q htq).symm

instance beta_finite (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    IsFiniteMeasure (beta rate rewards C_star C_h control0 b u t n htn) := by
  rw [← actual_map_eq_beta]
  infer_instance

theorem beta_successor_kernel (q : Fin p.T) (htq : t.val < q.val) :
    beta rate rewards C_star C_h control0 b u t q.succ (by change t.val < q.val + 1; omega) =
      (beta rate rewards C_star C_h control0 b u t q.castSucc htq).bind
        (killedKernel rate rewards C_star C_h control0 t q) := by
  rw [killedKernel_bind, beta_successor]

/-- Every bounded Borel test of the complete observation has its actual
unnormalized surviving integral under the recursively generated law. -/
theorem joint_test (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (Phi : PrefixObservation rate t n → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (O n w) ∂(Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)) =
      ∫ o, Phi o ∂beta rate rewards C_star C_h control0 b u t n htn := by
  have hi : Integrable Phi (((Lambda).restrict
      (survival rate rewards C_star C_h control0 b u t n)).map (O n)) :=
    Integrable.of_bound hPhi.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [← actual_map_eq_beta]
  exact (integral_map
    (measurable_branchObservation rate rewards C_star C_h control0 b u t n).aemeasurable
      hi.aestronglyMeasurable).symm

/-- The nonrenewed identity uses its ORIGINAL fibre-weighted lift law. -/
theorem nonrenewed_joint_test (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (Phi : PrefixObservation rate t n → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n w)
      ∂(ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0).restrict
        {w | NoCallBetween rate rewards C_star C_h t n
          (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n w).1.1.1.2}) =
      ∫ o, Phi o ∂beta rate rewards C_star C_h control0 false u t n htn :=
  joint_test rate rewards C_star C_h control0 false u t n htn Phi hPhi B hB

/-- The renewed identity retains label one's installation draw and label
zero's residual, the same full vector, original arrays and private index. -/
theorem renewed_joint_test (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (Phi : PrefixObservation rate t n → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (renewedGeneratedObservation rate rewards C_star C_h control0 u t n w)
      ∂(ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).restrict
        {w | NoCallBetween rate rewards C_star C_h t n
          (renewedGeneratedObservation rate rewards C_star C_h control0 u t n w).1.1.1.2}) =
      ∫ o, Phi o ∂beta rate rewards C_star C_h control0 true u t n htn :=
  joint_test rate rewards C_star C_h control0 true u t n htn Phi hPhi B hB

/-- No normalization by survival or original event mass. -/
theorem beta_mass (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    beta rate rewards C_star C_h control0 b u t n htn Set.univ =
      (Lambda) (survival rate rewards C_star C_h control0 b u t n) := by
  rw [← actual_map_eq_beta,
    Measure.map_apply (measurable_branchObservation rate rewards C_star C_h control0 b u t n)
      MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply_univ]

theorem constant_one_test (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    (∫ _w, (1 : ℝ) ∂(Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)) =
      ∫ _o, (1 : ℝ) ∂beta rate rewards C_star C_h control0 b u t n htn :=
  joint_test rate rewards C_star C_h control0 b u t n htn (fun _ => 1) measurable_const 1
    (fun _ => by norm_num)

theorem nonrenewed_mass (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    beta rate rewards C_star C_h control0 false u t n htn Set.univ =
      (ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0)
        {w | NoCallBetween rate rewards C_star C_h t n
          (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n w).1.1.1.2} :=
  beta_mass rate rewards C_star C_h control0 false u t n htn

theorem renewed_mass (n : Fin (p.T + 1)) (htn : t.val < n.val) :
    beta rate rewards C_star C_h control0 true u t n htn Set.univ =
      (ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t)
        {w | NoCallBetween rate rewards C_star C_h t n
          (renewedGeneratedObservation rate rewards C_star C_h control0 u t n w).1.1.1.2} :=
  beta_mass rate rewards C_star C_h control0 true u t n htn

section Projections

variable (n : Fin (p.T + 1)) (htn : t.val < n.val)

/-- Every Borel projection is a consequence of the SAME joint law. -/
theorem projection_map {A : Type*} [MeasurableSpace A]
    (f : PrefixObservation rate t n → A) (hf : Measurable f) :
    (beta rate rewards C_star C_h control0 b u t n htn).map f =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => f (O n w)) := by
  rw [← actual_map_eq_beta]
  exact Measure.map_map hf (measurable_branchObservation rate rewards C_star C_h control0 b u t n)

theorem fullSource_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => o.1.1.1) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => (w.1.1.val, insertedPhysicalSource rate
          (branchTransition rate rewards C_star C_h control0 b u t w))) := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _ measurable_fst.fst.fst]
  congr 1
  funext w
  cases b <;> rfl

theorem installedVector_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => o.1.1.2) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map Prod.snd := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _ measurable_fst.fst.snd]
  congr 1
  funext w
  cases b <;> rfl

theorem producedAppend_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => o.1.2.2) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => postHistory (branchTransition rate rewards C_star C_h control0 b u t w)) := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _ measurable_fst.snd.snd]
  congr 1
  funext w
  cases b <;> rfl

theorem usedAuxiliary_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => (o.1.2.1, o.2.1)) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => (usedAuxiliary t w.1.2, fun i : PrefixAuxiliaryIndex n => w.1.2 i.val)) := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _
    (measurable_fst.snd.fst.prodMk measurable_snd.fst)]
  congr 1
  funext w
  cases b <;> rfl

theorem numerical_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => o.2.2.1) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => prefixNumerical rate rewards C_star C_h n (insertedPhysicalSource rate
          (branchTransition rate rewards C_star C_h control0 b u t w))) := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _ measurable_snd.snd.fst]
  congr 1
  funext w
  cases b <;> rfl

theorem generatedHistory_map :
    (beta rate rewards C_star C_h control0 b u t n htn).map (fun o => o.2.2.2) =
      ((Lambda).restrict (survival rate rewards C_star C_h control0 b u t n)).map
        (fun w => postInvocationPrefix rate rewards C_star C_h t n
          (branchTransition rate rewards C_star C_h control0 b u t w) w.1.2) := by
  rw [projection_map rate rewards C_star C_h control0 b u t n htn _ measurable_snd.snd.snd]
  congr 1
  funext w
  exact branchObservation_prefix rate rewards C_star C_h control0 b u t n w

end Projections

section NativeCompatibility

variable (q : Fin p.T) (htq : t.val < q.val) (i : Fin (M p))

local notation "Observer" => SupportedObserver rate rewards C_star C_h control0 b u t q htq i
local notation "restore" => restoreSupported rate rewards C_star C_h control0 b u t q htq i
local notation "mu" => innovationLaw (p := p)

theorem restored_pre_auxiliary_pair (d : Observer)
    (c : ContinuousLearningRows.TimeControl p) (x y : Scalar × Scalar) :
    O q.castSucc (restore (d, (c, x))) = O q.castSucc (restore (d, (c, y))) := by
  let w := restore (d, (c, x))
  let w' := restore (d, (c, y))
  have hz : w.1.1 = w'.1.1 := rfl
  have hv : w.2 = w'.2 := rfl
  have ha : ∀ j, j.1 ≠ q → w.1.2 j = w'.1.2 j := by
    intro j hj
    change (restore (d, (c, x))).1.2 j = (restore (d, (c, y))).1.2 j
    rw [restoreSupported_auxiliary rate rewards C_star C_h control0 b u t q htq i d (c, x) (c, y)]
    exact fillAuxiliaryPair_apply_other q _ x j
      (fun h => hj (congrArg Prod.fst h)) (fun h => hj (congrArg Prod.fst h))
  change O q.castSucc ((w.1.1, w.1.2), w.2) = O q.castSucc ((w'.1.1, w'.1.2), w'.2)
  rw [hz, hv]
  exact branchObservation_auxiliary_pair rate rewards C_star C_h control0 b u t q
    q.castSucc htq le_rfl w'.1.1 w.1.2 w'.1.2 w'.2 ha

/-- Conditional on the ERASED supported observer, only the restored
control is in the full PRE source; the current auxiliary pair remains fresh. -/
theorem restored_pre_pair_product (d : Observer) :
    (mu).map (fun ω => (O q.castSucc (restore (d, ω)), ω.2)) =
      ((mu).map (fun ω => O q.castSucc (restore (d, ω)))).prod auxiliaryPairLaw := by
  let R : ContinuousLearningRows.TimeControl p → PrefixObservation rate t q.castSucc :=
    fun c => O q.castSucc (restore (d, (c, (referenceInnovation control0).2)))
  have hrestore := measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hR : Measurable R := hO.comp (hrestore.comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hread : (fun ω : Innovation p => O q.castSucc (restore (d, ω))) = R ∘ Prod.fst := by
    funext ω
    exact restored_pre_auxiliary_pair rate rewards C_star C_h control0 b u t q htq i d ω.1 ω.2 _
  have hmarg : (mu).map (fun ω => O q.castSucc (restore (d, ω))) =
      (ContinuousLearningRows.timeControlLaw p).map R := by
    rw [hread, ← Measure.map_map hR measurable_fst, innovationLaw, Measure.map_fst_prod,
      measure_univ, one_smul]
  rw [hmarg]
  have hprod := Measure.map_prod_map (ContinuousLearningRows.timeControlLaw p) auxiliaryPairLaw hR measurable_id
  rw [Measure.map_id] at hprod
  rw [hprod]
  change ((ContinuousLearningRows.timeControlLaw p).prod auxiliaryPairLaw).map _ =
    ((ContinuousLearningRows.timeControlLaw p).prod auxiliaryPairLaw).map _
  congr 1
  funext ω
  exact Prod.ext
    (restored_pre_auxiliary_pair rate rewards C_star C_h control0 b u t q htq i d ω.1 ω.2 _) rfl

/-- Native finite fibres reconstruct the SAME full-state replay. Native
masses are used only on the erased observer. After restoring a control, the
replay kernel uses its source-dependent Dirac and fresh auxiliary scalars. -/
theorem nativeLiftFibre_replay_compatibility
    (d : SurvivingObserver rate rewards C_star C_h control0 b u t q htq i) :
    (∑ a, nativeMass rate rewards C_star C_h control0 b u t q htq i d.val a •
      nativeLiftFibre rate rewards C_star C_h control0 b u t q htq i d.val a).map (O q.succ) =
      ((mu).map (fun ω => O q.castSucc (restore (d.val, ω)))).bind
        (replayKernel rate rewards C_star C_h control0 t q) := by
  have hr : Measurable (fun ω : Innovation p => restore (d.val, ω)) :=
    (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i).comp
      (measurable_const.prodMk measurable_id)
  have hOpre := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hOpost := measurable_branchObservation rate rewards C_star C_h control0 b u t q.succ
  have hJ : Measurable (fun ω : Innovation p => (O q.castSucc (restore (d.val, ω)), ω.2)) :=
    (hOpre.comp hr).prodMk measurable_snd
  rw [nativeLiftFibre_reconstruction, replayKernel_bind,
    ← restored_pre_pair_product rate rewards C_star C_h control0 b u t q htq i d.val]
  refine (Measure.map_map hOpost hr).trans ?_
  refine Eq.trans ?_ (Measure.map_map
    (measurable_successor rate rewards C_star C_h t q control0) hJ).symm
  apply Measure.map_congr
  apply Filter.Eventually.of_forall
  intro ω
  have hdom := (survivingDomain_restoreSupported rate rewards C_star C_h control0 b u t q htq i d.val ω).mpr d.property
  have hc : noCallAt rate rewards C_star C_h q (O q.castSucc (restore (d.val, ω))).1.1.1.2 := by
    rw [branchObservation_source]
    exact hdom.2
  have hs := successor_actual rate rewards C_star C_h control0 b u t q htq (restore (d.val, ω)) hc
  rw [(restoreSupported_coordinates rate rewards C_star C_h control0 b u t q htq i d.val ω).2] at hs
  exact hs.symm

include htq in
theorem survival_eq_survivingDomain :
    survival rate rewards C_star C_h control0 b u t q.succ =
      survivingDomain rate rewards C_star C_h control0 b u t q := by
  ext w
  rw [survival_iff_prefix, branchObservation_prefix]
  exact (survivingDomain_iff_next_prefix rate rewards C_star C_h control0 b u t q htq w).symm

/-- The actual recurrence agrees with the native observer-level integral;
this is proved after, rather than assumed as an input to, finite replay. -/
theorem beta_native_joint_integral (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ o, Phi o ∂beta rate rewards C_star C_h control0 b u t q.succ (by change t.val < q.val + 1; omega)) =
      ∑ j : Fin (M p),
        ∫ d in observerGate rate rewards C_star C_h control0 b u t q htq j,
          ∑ a, (nativeMass rate rewards C_star C_h control0 b u t q htq j d a).toReal *
            ∫ ω, Phi (O q.succ (restoreSupported rate rewards C_star C_h control0 b u t q htq j (d, ω)))
              ∂FiniteFibreLift.fibreMeasure (innovationLaw (p := p))
                (fun ω => outcomeOnSupported rate rewards C_star C_h control0 b u t q htq j (d, ω)) a
          ∂supportedObserverLaw rate rewards C_star C_h control0 b u t q htq j := by
  rw [← joint_test rate rewards C_star C_h control0 b u t q.succ
    (by change t.val < q.val + 1; omega) Phi hPhi B hB,
      survival_eq_survivingDomain rate rewards C_star C_h control0 b u t q htq]
  exact surviving_native_joint_integral rate rewards C_star C_h control0 b u t q htq Phi hPhi B hB

/-- Literal nonrenewed reconciliation with the accepted native full-source
identity. The finite iteration has already supplied its left-hand law. -/
theorem nonrenewed_beta_native_joint_integral (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ o, Phi o ∂beta rate rewards C_star C_h control0 false u t q.succ (by change t.val < q.val + 1; omega)) =
      ∑ j : Fin (M p),
        ∫ d in observerGate rate rewards C_star C_h control0 false u t q htq j,
          ∑ a, (nativeMass rate rewards C_star C_h control0 false u t q htq j d a).toReal *
            ∫ ω, Phi (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ
              (restoreSupported rate rewards C_star C_h control0 false u t q htq j (d, ω)))
              ∂FiniteFibreLift.fibreMeasure (innovationLaw (p := p))
                (fun ω => outcomeOnSupported rate rewards C_star C_h control0 false u t q htq j (d, ω)) a
          ∂supportedObserverLaw rate rewards C_star C_h control0 false u t q htq j := by
  have hE : survival rate rewards C_star C_h control0 false u t q.succ =
      {w : BranchLift rate rewards C_star C_h false u t |
        (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true} := by
    ext w
    exact survival_iff_prefix rate rewards C_star C_h control0 false u t q.succ w
  rw [← joint_test rate rewards C_star C_h control0 false u t q.succ
    (by change t.val < q.val + 1; omega) Phi hPhi B hB, hE]
  exact nonrenewed_surviving_native_joint_integral
    rate rewards C_star C_h control0 u t q htq Phi hPhi B hB

/-- Literal renewed reconciliation retains the same installation vector and
both original auxiliary labels, without normalizing any native atom. -/
theorem renewed_beta_native_joint_integral (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ o, Phi o ∂beta rate rewards C_star C_h control0 true u t q.succ (by change t.val < q.val + 1; omega)) =
      ∑ j : Fin (M p),
        ∫ d in observerGate rate rewards C_star C_h control0 true u t q htq j,
          ∑ a, (nativeMass rate rewards C_star C_h control0 true u t q htq j d a).toReal *
            ∫ ω, Phi (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ
              (restoreSupported rate rewards C_star C_h control0 true u t q htq j (d, ω)))
              ∂FiniteFibreLift.fibreMeasure (innovationLaw (p := p))
                (fun ω => outcomeOnSupported rate rewards C_star C_h control0 true u t q htq j (d, ω)) a
          ∂supportedObserverLaw rate rewards C_star C_h control0 true u t q htq j := by
  have hE : survival rate rewards C_star C_h control0 true u t q.succ =
      {w : BranchLift rate rewards C_star C_h true u t |
        (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true} := by
    ext w
    exact survival_iff_prefix rate rewards C_star C_h control0 true u t q.succ w
  rw [← joint_test rate rewards C_star C_h control0 true u t q.succ
    (by change t.val < q.val + 1; omega) Phi hPhi B hB, hE]
  exact renewed_surviving_native_joint_integral
    rate rewards C_star C_h control0 u t q htq Phi hPhi B hB

end NativeCompatibility

section CompleteNumericalWord

variable (n : Fin (p.T + 1)) (htn : t.val < n.val)

/-- Numerical projection is the COMPLETE actual calendar word, including
all disabled dates and the first detecting overflow update. -/
theorem nonrenewed_numericalWord_map :
    (beta rate rewards C_star C_h control0 false u t n htn).map (fun o => o.2.2.1) =
      ((ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0).restrict
        (survival rate rewards C_star C_h control0 false u t n)).map (fun w =>
          let z := ReferenceFirstNextInvocationJointLift.insertedSource t w.1.1.val w.2
          let hl := _root_.Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u t z
            (_root_.Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_insertVector_mem rate rewards C_star C_h u t w.1.1.val w.1.1.property.1 w.2)
          some (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((_root_.Bandits.Support.ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z hl).take
              (n.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)))) := by
  rw [projection_map rate rewards C_star C_h control0 false u t n htn _ measurable_snd.snd.fst]
  congr 1
  funext w
  exact nonrenewedGeneratedObservation_numerical rate rewards C_star C_h control0 u t n htn w

/-- The renewed law uses that SAME complete-word producer on its actual
inserted source; the last enabled logical cell never replaces this word. -/
theorem renewed_numericalWord_map :
    (beta rate rewards C_star C_h control0 true u t n htn).map (fun o => o.2.2.1) =
      ((ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).restrict
        (survival rate rewards C_star C_h control0 true u t n)).map (fun w =>
          let z := (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t w).2
          let hl := _root_.Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u t z.val z.property.1
          some (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((_root_.Bandits.Support.ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl).take
              (n.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)))) := by
  rw [projection_map rate rewards C_star C_h control0 true u t n htn _ measurable_snd.snd.fst]
  congr 1
  funext w
  exact renewedGeneratedObservation_numerical rate rewards C_star C_h control0 u t n htn w

end CompleteNumericalWord

end Bandits.Support.ReferencePostInvocationKilledJointLaw

end
