/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEndpointMixture

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Joint refill and native rebase of the generated calendar

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

All samples and readouts below use the admitted generated calendar. The original
first branch remains unnormalized. Refilling analytical coordinates regenerates
the archived observer; that observer is never declared independent of its tape.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceFirstNextLiftFutureAuxiliaryPairLaw (auxiliaryPair measurable_auxiliaryPair)

namespace Bandits.Support.ReferenceGeneratedCalendarJointRebase

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Control" => ContinuousLearningRows.TimeControl p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "uniform" => ContinuousControlSlice.assignmentLaw p.K
local notation "insert" => ReferenceFirstCollectionRenewalVectorInsertion.insert
local notation "replace" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace Control :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance sumMeasurableSingleton {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] : MeasurableSingletonClass (X ⊕ Y) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
    | inr a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inr_image
local instance optionMeasurableSingleton {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit X))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit X) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit X).injective.eq_iff.symm
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem compProd_restrict_fst {B V : Type*} [MeasurableSpace B] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (kernel : ProbabilityTheory.Kernel B V)
    [ProbabilityTheory.IsMarkovKernel kernel] (E : Set B) (hE : MeasurableSet E) :
    (mu.compProd kernel).restrict (Prod.fst ⁻¹' E) = (mu.restrict E).compProd kernel := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.compProd_apply (hS.inter (hE.preimage measurable_fst)),
    Measure.compProd_apply hS, ← lintegral_indicator hE]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ E <;> simp [Set.preimage, hw]

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "withAux" => calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0
local notation "lastFlags" => calendarLastFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "sectionEvent" => calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
local notation "mixtureErase" => calendarMixtureErase rate rewards C_star C_h b0 u0 t0
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h

include control0

/-- The actual current complete source ignores analytical refill. The archived
logical observer is deliberately absent from this equality. -/
theorem calendarCurrentSource_mixtureErase (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    current k hk.le (mixtureErase renewed bs s k hk w) = current k hk.le w := by
  cases renewed
  · exact (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0
      k hk.le w _).2
  · change current k hk.le (calendarErasePair rate rewards C_star C_h b0 u0 t0 _ k w) = _
    rw [calendarErasePair_eq_withAuxiliary]
    exact (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0
      k hk.le w _).2

/-- The source part of the literal native splice. Calls insert the complete
vector; a noncall keeps the complete source. -/
theorem calendarCurrentSource_succ (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (wv : Sample k × Vector) :
    current (k + 1) (by omega) wv =
      if callFlag k (by omega) wv.1 then
        insert ⟨t0.val + 1 + k, hk⟩ (current k hk.le wv.1) wv.2
      else current k hk.le wv.1 := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le wv.1
  let a := (original k wv.1).1.2
  by_cases hc : callFlag k (by omega) wv.1 = true
  · have hE : (o.2, (a, wv.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
    change (calendarStep rate rewards C_star C_h control0 q (o, (a, wv.2))).2.val.1.1.1.2 = _
    rw [calendarStep, dite_eq_left hE, ite_eq_left hc]
    rfl
  · have hE : ¬ (o.2, (a, wv.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
    change (calendarStep rate rewards C_star C_h control0 q (o, (a, wv.2))).2.val.1.1.1.2 = _
    rw [calendarStep, dite_eq_right hE, ite_eq_right hc]
    rfl

/-- Whole-source tests on either actual active section follow from the admitted
full-vector law and source nonuse, rather than an archive independence claim. -/
theorem calendarLaw_section_currentSource_test (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (current (k + 1) (by omega) wv)
      ∂(law (k + 1) (by omega)).restrict
        (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)) =
      ∫⁻ w, ∫⁻ v, F (insert ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) v) ∂uniform
        ∂(law k hk.le).restrict (sectionEvent renewed bs clear s k hk) := by
  let E := sectionEvent renewed bs clear s k hk
  let f : Sample k × Vector → ℝ≥0∞ := fun wv =>
    F (insert ⟨t0.val + 1 + k, hk⟩ (current k hk.le wv.1) wv.2)
  have hf : Measurable f := hF.comp
    ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := ⟨t0.val + 1 + k, hk⟩)).comp
      (((measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp
        measurable_fst).prodMk measurable_snd))
  have he : Measurable (mixtureErase renewed bs s k hk) := by
    cases renewed
    · exact measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k
    · exact measurable_calendarErasePair rate rewards C_star C_h b0 u0 t0 _ k
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
    renewed bs clear s k hk
  calc
    _ = ∫⁻ wv, f (mixtureErase renewed bs s k hk wv.1, wv.2)
        ∂(law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' E) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hE.preimage measurable_fst)] with wv hwv
      change Sample k × Vector at wv
      rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk,
        ite_eq_left hwv.2.1]
      dsimp only [f]
      rw [calendarCurrentSource_mixtureErase]
    _ = ∫⁻ w, ∫⁻ v, f (w, v) ∂uniform
        ∂((law k hk.le).restrict E).map (mixtureErase renewed bs s k hk) :=
      calendarLaw_endpoint_vector_test rate rewards C_star C_h control0 b0 u0 t0
        renewed bs clear s k hk hs f hf
    _ = _ := by
      rw [lintegral_map hf.lintegral_prod_right' he]
      apply lintegral_congr
      intro w
      dsimp only [f]
      rw [calendarCurrentSource_mixtureErase]

/-- Actual call with a present, not-yet-stopped numerical PRE. -/
def calendarActiveEvent (k : ℕ) (hk : t0.val + 1 + k < p.T) : Set (Sample k) :=
  {w | callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = true}

local notation "active" => calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0

theorem measurableSet_calendarActiveEvent (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    MeasurableSet (active k hk) :=
  (measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    measurable_const).inter (measurableSet_eq_fun
      (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega)).snd
      measurable_const)

private theorem section_pairwise (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Pairwise (fun i j : Bool × Bool × Bool × Fin p.T =>
      Disjoint (sectionEvent i.1 i.2.1 i.2.2.1 i.2.2.2 k hk)
        (sectionEvent j.1 j.2.1 j.2.2.1 j.2.2.2 k hk)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro w hi hj
  apply hij
  have hr : i.1 = j.1 := congrArg (fun b : Bool × Bool => b.1) (hi.2.2.symm.trans hj.2.2)
  have hb : i.2.1 = j.2.1 := congrArg (fun b : Bool × Bool => b.1) (hi.1.2.symm.trans hj.1.2)
  have hc : i.2.2.1 = j.2.2.1 := congrArg (fun b : Bool × Bool => b.2) (hi.1.2.symm.trans hj.1.2)
  exact Prod.ext hr (Prod.ext hb (Prod.ext hc (hi.1.1.symm.trans hj.1.1)))

/-- Exhaustive partition of active calls by their own local orientation,
native date and native PRE flag. These labels are read from the same run. -/
theorem calendarActiveEvent_partition (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    active k hk = ⋃ i : Bool × Bool × Bool × Fin p.T,
      sectionEvent i.1 i.2.1 i.2.2.1 i.2.2.2 k hk := by
  ext w
  constructor
  · intro hw
    refine Set.mem_iUnion.mpr ⟨((pending k (by omega) w).1,
      (lastFlags k hk.le w).1, (lastFlags k hk.le w).2, (observe k hk.le w).1), ?_⟩
    exact ⟨⟨rfl, rfl⟩, hw.1, Prod.ext rfl hw.2⟩
  · intro hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    exact ⟨hi.2.1, congrArg Prod.snd hi.2.2⟩

private theorem section_empty_of_date (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : ¬ s.val < t0.val + 1 + k) :
    sectionEvent renewed bs clear s k hk = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hd := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  rw [hw.1.1] at hd
  exact hs hd

/-- Full active-call source identity, including every retained and renewed
native section. Impossible dates and null sections contribute their zero mass. -/
theorem calendarLaw_active_currentSource_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (current (k + 1) (by omega) wv)
      ∂(law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' active k hk)) =
      ∫⁻ w, ∫⁻ v, F (insert ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) v) ∂uniform
        ∂(law k hk.le).restrict (active k hk) := by
  let H : Sample k × Vector → ℝ≥0∞ := fun wv => F (current (k + 1) (by omega) wv)
  let mu : Measure (Sample k × Vector) := (law k hk.le).compProd (extension k (by omega))
  change (∫⁻ wv in Prod.fst ⁻¹' active k hk, H wv ∂mu) = _
  let E := fun i : Bool × Bool × Bool × Fin p.T =>
    sectionEvent i.1 i.2.1 i.2.2.1 i.2.2.2 k hk
  have hE : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
      i.1 i.2.1 i.2.2.1 i.2.2.2 k hk
  have hd := section_pairwise rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hdp : Pairwise (fun i j => Disjoint
      ((Prod.fst : Sample k × Vector → Sample k) ⁻¹' E i) (Prod.fst ⁻¹' E j)) :=
    fun i j hij => (hd hij).preimage _
  rw [calendarActiveEvent_partition, Set.preimage_iUnion,
    lintegral_iUnion (fun i => (hE i).preimage measurable_fst) hdp,
    lintegral_iUnion hE hd]
  apply tsum_congr
  intro i
  by_cases hs : i.2.2.2.val < t0.val + 1 + k
  · exact calendarLaw_section_currentSource_test rate rewards C_star C_h control0 b0 u0 t0
      i.1 i.2.1 i.2.2.1 i.2.2.2 k hk hs F hF
  · have hempty := section_empty_of_date rate rewards C_star C_h control0 b0 u0 t0
      i.1 i.2.1 i.2.2.1 i.2.2.2 k hk hs
    simp only [E, hempty, Set.preimage_empty, Measure.restrict_empty, lintegral_zero_measure]

/-- All exceptional inputs: no call, absent PRE, or stopped PRE. The native
physical continuation is retained, including calls after first overflow. -/
theorem calendarLaw_exceptional_currentSource_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (current (k + 1) (by omega) wv)
      ∂(law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' (active k hk)ᶜ)) =
      ∫⁻ w, F (current k hk.le w) ∂(law k hk.le).restrict (active k hk)ᶜ := by
  have hA := measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hFcur : Measurable (fun wv : Sample k × Vector => F (current (k + 1) (by omega) wv)) :=
    hF.comp (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
  change (∫⁻ wv : Sample k × Vector, F (current (k + 1) (by omega) wv)
    ∂((law k hk.le).compProd (extension k (by omega))).restrict (Prod.fst ⁻¹' (active k hk)ᶜ)) = _
  rw [compProd_restrict_fst _ _ _ hA.compl, Measure.lintegral_compProd hFcur]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hA.compl] with w hw
  have hkernel : extension k (by omega) w = Measure.dirac
      (ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)) := by
    by_cases hc : callFlag k (by omega) w = true
    · have hp : (pending k (by omega) w).2 = false := by
        cases hp : (pending k (by omega) w).2
        · rfl
        · exact (hw ⟨hc, hp⟩).elim
      exact calendarExtensionKernel_preStopped rate rewards C_star C_h control0 b0 u0 t0 k hk w hp
    · exact calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk w
        (Option.not_isSome_iff_eq_none.mp hc)
  rw [hkernel, lintegral_dirac, calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk]
  split
  · exact congrArg F (ReferenceFirstCollectionRenewalVectorInsertion.insert_original_vector _ _)
  · rfl

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem controlVectorReplacement_map :
    ((ContinuousLearningRows.timeControlLaw p).prod uniform).map
      (fun cv => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (cv.2, ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) cv.1).2)) =
          ContinuousLearningRows.timeControlLaw p := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let tc := ContinuousLearningRows.timeControlLaw p
  let nr := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  have he := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hm : Measurable (fun c : Control => (e c).2) := e.measurable.snd
  have hr : tc.map (fun c => (e c).2) = nr := by
    change tc.map (Prod.snd ∘ e) = nr
    rw [← Measure.map_map measurable_snd e.measurable, he.map_eq, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hp : (tc.map (fun c => (e c).2)).prod uniform =
      (tc.prod uniform).map (Prod.map (fun c => (e c).2) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map tc uniform hm measurable_id
  calc
    _ = (((tc.prod uniform).map (Prod.map (fun c => (e c).2) id)).map Prod.swap).map e.symm := by
      rw [Measure.map_map e.symm.measurable measurable_swap,
        Measure.map_map (e.symm.measurable.comp measurable_swap) (hm.prodMap measurable_id)]
      rfl
    _ = ((nr.prod uniform).map Prod.swap).map e.symm := by rw [← hp, hr]
    _ = ((uniform).prod nr).map e.symm := by rw [Measure.prod_swap]
    _ = tc := by rw [← he.map_eq]; exact e.map_symm_map

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem insert_replace_current (q : Fin p.T) (z : Source) (c : Control) (v : Vector) :
    insert q (replace q z c) v = replace q z
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (v, ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) c).2)) := by
  have hc : ReferenceFirstCollectionRenewalVectorInsertion.c q (replace q z c) = c := by
    simp only [ReferenceFirstCollectionRenewalVectorInsertion.c,
      ReferenceFirstCollectionRenewalVectorInsertion.q,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  rw [ReferenceFirstCollectionRenewalVectorInsertion.insert,
    ReferenceFirstCollectionRenewalVectorInsertion.ctrl, hc]
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    Function.update_self, Function.update_idem]

private theorem restored_branch_source (q : Fin p.T) (htq : t0.val < q.val) (i : Fin (M p))
    (r : RemainderLift rate rewards C_star C_h control0 b0 u0 t0 q i) (c : Control) :
    (branchObservation rate rewards C_star C_h control0 b0 u0 t0 q.castSucc
      (restoreControl rate rewards C_star C_h control0 b0 u0 t0 q htq i (r, c))).1.1.1.2 =
    replace q (branchObservation rate rewards C_star C_h control0 b0 u0 t0 q.castSucc
      (restoreControl rate rewards C_star C_h control0 b0 u0 t0 q htq i (r, control0))).1.1.1.2 c := by
  cases b0
  · exact congrArg (fun x : ((Source × Source) × Auxiliary) × Vector => x.1.1.2)
      (ReferenceFirstNextLiftFutureControl.nonrenewedRestoreLift_readout
        rate rewards C_star C_h control0 u0 t0 q htq i r.1.1 r.1.2 r.2 c)
  · exact congrArg (fun x : ((Source × Source) × Auxiliary) × Vector => x.1.1.2)
      (ReferenceFirstNextLiftFutureControl.renewedRestoreLift_readout
        rate rewards C_star C_h control0 u0 t0 q htq i r.1.1 r.1.2 r.2 c)

private theorem branch_source_uniform_replacement (q : Fin p.T) (htq : t0.val < q.val)
    (D : Set Source) (hD : MeasurableSet D)
    (hgate : ∀ z c, replace q z c ∈ D ↔ z ∈ D)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in D, ∫⁻ v, F (insert q z v) ∂uniform
      ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0)) =
      ∫⁻ z in D, F z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  let S := fun w : BranchLift rate rewards C_star C_h b0 u0 t0 =>
    (branchObservation rate rewards C_star C_h control0 b0 u0 t0 q.castSucc w).1.1.1.2
  have hS : Measurable S :=
    (measurable_branchObservation rate rewards C_star C_h control0 b0 u0 t0 q.castSucc).fst.fst.fst.snd
  have hFi : Measurable (fun zv : Source × Vector => F (insert q zv.1 zv.2)) :=
    hF.comp (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q))
  have hG : Measurable (fun z : Source => ∫⁻ v, F (insert q z v) ∂uniform) :=
    hFi.lintegral_prod_right'
  rw [← lintegral_indicator hD, ← lintegral_indicator hD,
    ← ReferenceNextInsertedSourceMarginal.branchLaw_map_source rate rewards C_star C_h control0 b0 u0 t0 q,
    lintegral_map (hG.indicator hD) hS, lintegral_map (hF.indicator hD) hS]
  let f : BranchLift rate rewards C_star C_h b0 u0 t0 → ℝ≥0∞ :=
    fun w => D.indicator (fun z => ∫⁻ v, F (insert q z v) ∂uniform) (S w)
  let g : BranchLift rate rewards C_star C_h b0 u0 t0 → ℝ≥0∞ := fun w => D.indicator F (S w)
  have hf : Measurable f := (hG.indicator hD).comp hS
  have hg : Measurable g := (hF.indicator hD).comp hS
  change (∫⁻ w, f w ∂branchLaw rate rewards C_star C_h control0 b0 u0 t0) =
    ∫⁻ w, g w ∂branchLaw rate rewards C_star C_h control0 b0 u0 t0
  rw [branchLaw_eq_sum_restore_control rate rewards C_star C_h control0 b0 u0 t0 q htq,
    lintegral_sum_measure, lintegral_sum_measure]
  apply tsum_congr
  intro i
  let restore := restoreControl rate rewards C_star C_h control0 b0 u0 t0 q htq i
  have hr := measurable_restoreControl rate rewards C_star C_h control0 b0 u0 t0 q htq i
  rw [lintegral_map hf hr, lintegral_map hg hr]
  change (∫⁻ a, (f ∘ restore) a ∂(remainderLaw rate rewards C_star C_h control0 b0 u0 t0 q htq i).prod
      (ContinuousLearningRows.timeControlLaw p)) =
    ∫⁻ a, (g ∘ restore) a ∂(remainderLaw rate rewards C_star C_h control0 b0 u0 t0 q htq i).prod
      (ContinuousLearningRows.timeControlLaw p)
  rw [lintegral_prod _ (hf.comp hr).aemeasurable, lintegral_prod _ (hg.comp hr).aemeasurable]
  apply lintegral_congr
  intro r
  let z := S (restore (r, control0))
  have hsrc (c : Control) : S (restore (r, c)) = replace q z c :=
    restored_branch_source rate rewards C_star C_h control0 b0 u0 t0 q htq i r c
  change (∫⁻ c, D.indicator (fun z => ∫⁻ v, F (insert q z v) ∂uniform)
      (S (restore (r, c))) ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ c, D.indicator F (S (restore (r, c))) ∂ContinuousLearningRows.timeControlLaw p
  simp_rw [hsrc]
  simp only [Set.indicator, hgate]
  by_cases hz : z ∈ D
  · simp only [hz, ite_true]
    let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    let put := fun cv : Control × Vector => e.symm (cv.2, (e cv.1).2)
    have hp : Measurable put := e.symm.measurable.comp
      (measurable_snd.prodMk (e.measurable.snd.comp measurable_fst))
    let R := fun c : Control => F (replace q z c)
    have hR : Measurable R := by
      convert hF.comp (hS.comp (hr.comp ((measurable_const (a := r)).prodMk measurable_id))) using 1
      funext c
      exact congrArg F (hsrc c).symm
    calc
      _ = ∫⁻ c, ∫⁻ v, R (put (c, v)) ∂uniform ∂ContinuousLearningRows.timeControlLaw p := by
        simp_rw [insert_replace_current]
        rfl
      _ = ∫⁻ cv, R (put cv) ∂(ContinuousLearningRows.timeControlLaw p).prod uniform :=
        (lintegral_prod _ (hR.comp hp).aemeasurable).symm
      _ = ∫⁻ c, R c ∂((ContinuousLearningRows.timeControlLaw p).prod uniform).map put :=
        (lintegral_map hR hp).symm
      _ = _ := by rw [controlVectorReplacement_map]
  · simp only [hz, ite_false, lintegral_zero]

omit b0 u0 t0 in
/-- A physical call whose complete numerical PRE has not stopped. The event
uses the current complete source, including the first overflowing update. -/
def physicalActiveCall (q : Fin p.T) : Set Source :=
  {z | (sourceCall q z).isSome = true ∧
    (prefixNumerical rate rewards C_star C_h q.castSucc z).any (fun S => !S.overflow) = true}

local notation "physicalActive" => physicalActiveCall rate rewards C_star C_h

omit b0 u0 t0 in
theorem measurableSet_physicalActiveCall (q : Fin p.T) : MeasurableSet (physicalActive q) := by
  have his : Measurable (Option.isSome : ReferenceCalendarCollectionCallControlLaw.CallAt p → Bool) := by
    convert ((measurable_const : Measurable (fun _ : Fin p.T ×
      AssignmentParameterFibreKernel.Theta p => true)).sumElim
      (measurable_const : Measurable (fun _ : PUnit => false))).comp
        (comap_measurable (Equiv.optionEquivSumPUnit _)) using 1
    funext o
    cases o <;> rfl
  exact (measurableSet_eq_fun (his.comp
    ((ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (q.val + 1)) le_rfl))
    measurable_const).inter (measurableSet_eq_fun
      ((measurable_of_countable (fun S : Option (RecordedQueueRun.RunState p.K) =>
        S.any (fun R : RecordedQueueRun.RunState p.K => !R.overflow))).comp
          (measurable_prefixNumerical rate rewards C_star C_h q.castSucc)) measurable_const)

omit b0 u0 t0 in
theorem physicalActiveCall_replace (q : Fin p.T) (z : Source) (c : Control) :
    replace q z c ∈ physicalActive q ↔ z ∈ physicalActive q := by
  have hcall : sourceCall q (replace q z c) = sourceCall q z := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q]
  have hn : prefixNumerical rate rewards C_star C_h q.castSucc (replace q z c) =
      prefixNumerical rate rewards C_star C_h q.castSucc z := by
    rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]
  simp only [physicalActiveCall, Set.mem_ofPred_eq, hcall, hn]

theorem calendarActiveEvent_eq_preimage (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    active k hk = current k hk.le ⁻¹' physicalActive ⟨t0.val + 1 + k, hk⟩ := by
  ext w
  change (_ ∧ (observe k hk.le w).2.val.2.2.1.any (fun S => !S.overflow) = true) ↔ (_ ∧ _)
  rw [calendarObservation_numerical]
  rfl

/-- The CURRENT complete physical source has its original first-branch law
at every finite generated boundary. This is an unnormalized law, and makes
no exhaustiveness assertion about the family of original first branches. -/
theorem calendarLaw_map_currentSource (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    (law k hk).map (current k hk) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  induction k with
  | zero =>
      have h := ReferenceNextInsertedSourceMarginal.branchLaw_map_source
        rate rewards C_star C_h control0 b0 u0 t0 t0
      simp_rw [branchObservation_source] at h
      change (branchLaw rate rewards C_star C_h control0 b0 u0 t0).map
        (fun w => (branchObservation rate rewards C_star C_h control0 b0 u0 t0 t0.succ w).1.1.1.2) = _
      simpa only [branchObservation_source] using h
  | succ k ih =>
      have hk' : t0.val + 1 + k < p.T := by omega
      let q : Fin p.T := ⟨t0.val + 1 + k, hk'⟩
      have hA := measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk'
      have hD := measurableSet_physicalActiveCall rate rewards C_star C_h control0 q
      have hcur := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk'.le
      have hmap : ((law k hk'.le).restrict (active k hk')).map (current k hk'.le) =
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (branchEvent rate rewards C_star C_h b0 u0 t0)).restrict (physicalActive q) := by
        rw [calendarActiveEvent_eq_preimage, ← Measure.restrict_map hcur hD, ih hk'.le]
      refine Measure.ext_of_lintegral _ (fun F hF => ?_)
      have hFi : Measurable (fun zv : Source × Vector => F (insert q zv.1 zv.2)) :=
        hF.comp (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q))
      let H : Sample k × Vector → ℝ≥0∞ := fun wv => F (current (k + 1) hk wv)
      let mu : Measure (Sample k × Vector) := law (k + 1) hk
      rw [lintegral_map hF
        (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) hk)]
      calc
        _ = (∫⁻ wv in Prod.fst ⁻¹' active k hk', F (current (k + 1) hk wv) ∂law (k + 1) hk) +
            ∫⁻ wv in Prod.fst ⁻¹' (active k hk')ᶜ, F (current (k + 1) hk wv) ∂law (k + 1) hk := by
          change (∫⁻ wv, H wv ∂mu) =
            (∫⁻ wv in Prod.fst ⁻¹' active k hk', H wv ∂mu) +
              ∫⁻ wv in Prod.fst ⁻¹' (active k hk')ᶜ, H wv ∂mu
          rw [← lintegral_add_measure, Set.preimage_compl,
            Measure.restrict_add_restrict_compl (μ := mu) (hA.preimage measurable_fst)]
        _ = (∫⁻ w in active k hk', ∫⁻ v, F (insert q (current k hk'.le w) v) ∂uniform ∂law k hk'.le) +
            ∫⁻ w in (active k hk')ᶜ, F (current k hk'.le w) ∂law k hk'.le := by
          rw [calendarLaw_active_currentSource_test rate rewards C_star C_h control0 b0 u0 t0 k hk' F hF,
            calendarLaw_exceptional_currentSource_test rate rewards C_star C_h control0 b0 u0 t0 k hk' F hF]
        _ = (∫⁻ w in active k hk', F (current k hk'.le w) ∂law k hk'.le) +
            ∫⁻ w in (active k hk')ᶜ, F (current k hk'.le w) ∂law k hk'.le := by
          congr 1
          calc
            _ = ∫⁻ z, ∫⁻ v, F (insert q z v) ∂uniform
                ∂((law k hk'.le).restrict (active k hk')).map (current k hk'.le) :=
              (lintegral_map hFi.lintegral_prod_right' hcur).symm
            _ = ∫⁻ z, F z ∂((law k hk'.le).restrict (active k hk')).map (current k hk'.le) := by
              rw [hmap]
              exact branch_source_uniform_replacement rate rewards C_star C_h control0 b0 u0 t0 q
                (by dsimp only [q]; omega) (physicalActive q) hD
                (physicalActiveCall_replace rate rewards C_star C_h control0 q) F hF
            _ = _ := lintegral_map hF hcur
        _ = ∫⁻ w, F (current k hk'.le w) ∂law k hk'.le := by
          rw [← lintegral_add_measure,
            Measure.restrict_add_restrict_compl (μ := law k hk'.le) hA]
        _ = _ := by rw [← lintegral_map hF hcur, ih hk'.le]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem compProd_restore {B X V : Type*}
    [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (mu : Measure B) [SFinite mu] (nu : Measure X) [SFinite nu]
    (kernel : ProbabilityTheory.Kernel B V) [ProbabilityTheory.IsMarkovKernel kernel]
    (fill : X → B) (hfill : Measurable fill) (hrestore : mu = nu.map fill) :
    mu.compProd kernel =
      (nu.compProd (kernel.comap fill hfill)).map (Prod.map fill id) := by
  refine Measure.ext_of_lintegral _ (fun F hF => ?_)
  have hG : Measurable (fun w => ∫⁻ v, F (w, v) ∂kernel w) :=
    hF.lintegral_kernel_prod_right'
  rw [lintegral_map hF (hfill.prodMap measurable_id)]
  change (∫⁻ a, F a ∂mu.compProd kernel) =
    ∫⁻ a, (F ∘ Prod.map fill id) a ∂nu.compProd (kernel.comap fill hfill)
  rw [Measure.lintegral_compProd (hF.comp (hfill.prodMap measurable_id)),
    Measure.lintegral_compProd hF, hrestore, lintegral_map hG hfill]
  rfl

omit rate rewards C_star C_h control0 b0 u0 t0 in
/-- Retained calls refill their actual residual block; renewed calls refill
only their actual current pair. -/
def CalendarRefill : (renewed bs : Bool) → Fin p.T → Type
  | false, bs, s => RefreshAuxiliary bs s
  | true, _, _ => Scalar × Scalar

omit rate rewards C_star C_h control0 b0 u0 t0 in
instance calendarRefillMeasurableSpace (renewed bs : Bool) (s : Fin p.T) :
    MeasurableSpace (CalendarRefill renewed bs s) :=
  match renewed with
  | false => inferInstanceAs (MeasurableSpace (RefreshAuxiliary bs s))
  | true => inferInstanceAs (MeasurableSpace (Scalar × Scalar))

omit rate rewards C_star C_h control0 b0 u0 t0 in
/-- The original product law on precisely the coordinates being refilled. -/
def calendarRefillLaw (renewed bs : Bool) (s : Fin p.T) : Measure (CalendarRefill renewed bs s) :=
  match renewed with
  | false => refreshAuxiliaryLaw bs s
  | true => auxiliaryPairLaw

omit rate rewards C_star C_h control0 b0 u0 t0 in
instance calendarRefillLaw_probability (renewed bs : Bool) (s : Fin p.T) :
    IsProbabilityMeasure (calendarRefillLaw renewed bs s) := by
  cases renewed
  · change IsProbabilityMeasure (refreshAuxiliaryLaw bs s)
    infer_instance
  · change IsProbabilityMeasure auxiliaryPairLaw
    infer_instance

/-- Literal raw-sample refill. All earlier vectors, physical arrays and J
survive; the complete observer is regenerated afterwards. -/
def calendarMixtureFill (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Sample k × CalendarRefill renewed bs s → Sample k :=
  match renewed with
  | false => calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k
  | true => calendarFillPair rate rewards C_star C_h b0 u0 t0 ⟨t0.val + 1 + k, hk⟩ k

local notation "mixtureFill" => calendarMixtureFill rate rewards C_star C_h b0 u0 t0

omit control0 in
theorem measurable_calendarMixtureFill (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Measurable (mixtureFill renewed bs s k hk) := by
  cases renewed
  · exact measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k
  · exact measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 _ k

theorem calendarLaw_section_eq_restoreMixture (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    (law k hk.le).restrict (sectionEvent renewed bs clear s k hk) =
      ((((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map
        (mixtureErase renewed bs s k hk)).prod (calendarRefillLaw renewed bs s)).map
          (mixtureFill renewed bs s k hk) := by
  cases renewed
  · exact calendarLaw_section_eq_restoreBlock rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs
  · exact calendarLaw_section_eq_restorePair rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk hs

/-- The output retains the entire augmented raw sample, its archived PRE
observer, and its native POST observer jointly. -/
abbrev CalendarJointOutput (k : ℕ) (hk : t0.val + 1 + k < p.T) :=
  (Sample k × Vector) × (TaggedPrefix rate (calendarBoundary t0 k hk.le) ×
    TaggedPrefix rate (calendarBoundary t0 (k + 1) (by omega)))

local notation "Joint" => CalendarJointOutput rate rewards C_star C_h b0 u0 t0

/-- The literal native sampler graph on the same raw sample. Its first
observer is un-erased and therefore retains correlation with refill. -/
def calendarJointReadout (k : ℕ) (hk : t0.val + 1 + k < p.T) (wv : Sample k × Vector) : Joint k hk :=
  (wv, (observe k hk.le wv.1,
    calendarStep rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩
      (observe k hk.le wv.1, ((original k wv.1).1.2, wv.2))))

local notation "joint" => calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarJointReadout (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (joint k hk) := by
  have ho := (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp
    (measurable_fst : Measurable (Prod.fst : Sample k × Vector → Sample k))
  have ha := (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd.comp
    (measurable_fst : Measurable (Prod.fst : Sample k × Vector → Sample k))
  exact measurable_id.prodMk (ho.prodMk
    ((measurable_calendarStep rate rewards C_star C_h control0 _).comp
      (ho.prodMk (ha.prodMk measurable_snd))))

theorem calendarJointReadout_observers (k : ℕ) (hk : t0.val + 1 + k < p.T) (wv : Sample k × Vector) :
    (joint k hk wv).2 = (observe k hk.le wv.1, observe (k + 1) (by omega) wv) := rfl

/-- Native refill followed by the actual conditional full-vector sampler.
The archived observer is evaluated only AFTER refill. This target is built
from the erased section, original refill law and admitted sampler kernel. -/
def calendarSectionRefillLaw (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Measure ((Sample k × CalendarRefill renewed bs s) × Vector) :=
  (((((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map
    (mixtureErase renewed bs s k hk)).prod (calendarRefillLaw renewed bs s)).compProd
      ((extension k (by omega)).comap (mixtureFill renewed bs s k hk)
        (measurable_calendarMixtureFill rate rewards C_star C_h b0 u0 t0 renewed bs s k hk)))

local notation "refillLaw" => calendarSectionRefillLaw rate rewards C_star C_h control0 b0 u0 t0

/-- Correlated joint target, with the complete archived and native observers
on the very same refilled sample. No marginal independence is imposed. -/
def calendarSectionJointLaw (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Measure (Joint k hk) :=
  (refillLaw renewed bs clear s k hk).map
    (fun wxv => joint k hk (mixtureFill renewed bs s k hk wxv.1, wxv.2))

local notation "sectionJointLaw" => calendarSectionJointLaw rate rewards C_star C_h control0 b0 u0 t0

private theorem calendarLaw_section_raw_refill (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    (law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk) =
      (refillLaw renewed bs clear s k hk).map (Prod.map (mixtureFill renewed bs s k hk) id) := by
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
    renewed bs clear s k hk
  change ((law k hk.le).compProd (extension k (by omega))).restrict
    (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk) = _
  rw [compProd_restrict_fst _ _ _ hE]
  exact compProd_restore _ _ _ _
    (measurable_calendarMixtureFill rate rewards C_star C_h b0 u0 t0 renewed bs s k hk)
    (calendarLaw_section_eq_restoreMixture rate rewards C_star C_h control0 b0 u0 t0
      renewed bs clear s k hk hs)

/-- The actual complete-source / un-erased archived-observer / native-POST
joint law on each retained or renewed generated section. -/
theorem calendarLaw_section_joint_rebase (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    ((law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)).map (joint k hk) =
        sectionJointLaw renewed bs clear s k hk := by
  have h := congrArg (fun mu : Measure (Sample k × Vector) => mu.map (joint k hk))
    (calendarLaw_section_raw_refill rate rewards C_star C_h control0 b0 u0 t0
      renewed bs clear s k hk hs)
  exact h.trans (Measure.map_map
    (measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)
    ((measurable_calendarMixtureFill rate rewards C_star C_h b0 u0 t0 renewed bs s k hk).prodMap
      measurable_id))

/-- The refill target satisfies the actual sampler fibre graph almost
everywhere, including the admitted null-fibre and absent-endpoint conventions. -/
theorem ae_calendarSectionRefillLaw_fibreMatch (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    ∀ᵐ wxv ∂refillLaw renewed bs clear s k hk,
      calendarFibreMatch rate rewards C_star C_h control0 b0 u0 t0 k hk
        (mixtureFill renewed bs s k hk wxv.1, wxv.2) = true := by
  have h := ae_calendarLaw_section_fibreMatch rate rewards C_star C_h control0 b0 u0 t0
    renewed bs clear s k hk hs
  rw [calendarLaw_section_raw_refill rate rewards C_star C_h control0 b0 u0 t0
    renewed bs clear s k hk hs] at h
  exact (ae_map_iff
    ((measurable_calendarMixtureFill rate rewards C_star C_h b0 u0 t0 renewed bs s k hk).prodMap
      measurable_id).aemeasurable
    (measurableSet_eq_fun
      (measurable_calendarFibreMatch rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const)).mp h

/-- Arbitrary joint Borel tests retain the un-erased archive inside the
refill integral and the sampler fibre integral. All event masses stay inside
the measure; no division by a section probability occurs. -/
theorem calendarLaw_section_joint_test (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k)
    (F : Joint k hk → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (joint k hk wv) ∂(law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)) =
    ∫⁻ w, ∫⁻ x, ∫⁻ v, F (joint k hk (mixtureFill renewed bs s k hk (w, x), v))
      ∂extension k (by omega) (mixtureFill renewed bs s k hk (w, x))
      ∂calendarRefillLaw renewed bs s
      ∂((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map
        (mixtureErase renewed bs s k hk) := by
  have hj := measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hr := measurable_calendarMixtureFill rate rewards C_star C_h b0 u0 t0 renewed bs s k hk
  let G : (Sample k × CalendarRefill renewed bs s) × Vector → ℝ≥0∞ :=
    fun wxv => F (joint k hk (mixtureFill renewed bs s k hk wxv.1, wxv.2))
  have hG : Measurable G := hF.comp (hj.comp (hr.prodMap measurable_id))
  have hinner : Measurable (fun wx : Sample k × CalendarRefill renewed bs s =>
      ∫⁻ v, G (wx, v) ∂extension k (by omega) (mixtureFill renewed bs s k hk wx)) :=
    hG.lintegral_kernel_prod_right'
      (κ := (extension k (by omega)).comap (mixtureFill renewed bs s k hk) hr)
  calc
    _ = ∫⁻ z, F z ∂sectionJointLaw renewed bs clear s k hk := by
      rw [← calendarLaw_section_joint_rebase rate rewards C_star C_h control0 b0 u0 t0
        renewed bs clear s k hk hs]
      exact (lintegral_map hF hj).symm
    _ = ∫⁻ wxv, G wxv ∂refillLaw renewed bs clear s k hk :=
      lintegral_map hF (hj.comp (hr.prodMap measurable_id))
    _ = _ := by
      change (∫⁻ wxv, G wxv ∂(((((law k hk.le).restrict
        (sectionEvent renewed bs clear s k hk)).map (mixtureErase renewed bs s k hk)).prod
          (calendarRefillLaw renewed bs s)).compProd
            ((extension k (by omega)).comap (mixtureFill renewed bs s k hk) hr))) = _
      rw [Measure.lintegral_compProd hG]
      exact lintegral_prod _ hinner.aemeasurable

/-- Explicit conditional sampler used in the correlated refill target.
Its inherited empty/null/none branches are retained verbatim. -/
theorem calendarMixtureFill_kernel (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (wx : Sample k × CalendarRefill renewed bs s) :
    let w := mixtureFill renewed bs s k hk wx
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le w
    let i : NextInput rate o.1 q := (o.2.val, auxiliaryPair q (original k w).1.2)
    extension k (by omega) w =
      match installationSelection rate rewards C_star C_h (t := o.1) q i with
      | none => Measure.dirac (currentVector rate (t := o.1) q i)
      | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2 := by
  dsimp only
  rw [calendarExtensionKernel_apply, calendarVectorKernel_apply, nextVectorKernel_apply]
  rfl

/-- The new native initializer, numerical POST and appended PRE list all
come from the same call transition. This is a single-step rebase, independent
of the separate archived-path continuity induction. -/
theorem calendarJointReadout_call_rebase (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (wv : Sample k × Vector) (hc : callFlag k (by omega) wv.1 = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let o := observe k hk.le wv.1
    let a := (original k wv.1).1.2
    let x : calendarCallEvent rate rewards C_star C_h o.1 q := ⟨(o.2, (a, wv.2)), hc⟩
    let d := calendarCallTransition rate rewards C_star C_h control0 o.1 q x
    (joint k hk wv).2.2 = ⟨q, calendarCallPrefix rate rewards C_star C_h control0 o.1 q x⟩ ∧
      (calendarCallPrefix rate rewards C_star C_h control0 o.1 q x).val.2.2.1 = some d.2.2.2.after ∧
      (calendarCallPrefix rate rewards C_star C_h control0 o.1 q x).val.2.2.2 =
        some (d.2.2.2.nextSlowSet, (o.2.val.2.2.2.get o.2.property).2 ++ [d.2.2.2]) := by
  dsimp only
  constructor
  · change calendarStep rate rewards C_star C_h control0 _ _ = _
    exact dite_eq_left hc
  · exact calendarCallPrefix_alignment rate rewards C_star C_h control0 _ _ _

private theorem extension_exceptional (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∉ active k hk) :
    extension k (by omega) w = Measure.dirac
      (ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)) := by
  by_cases hc : callFlag k (by omega) w = true
  · have hp : (pending k (by omega) w).2 = false := by
      cases hp : (pending k (by omega) w).2
      · rfl
      · exact (hw ⟨hc, hp⟩).elim
    exact calendarExtensionKernel_preStopped rate rewards C_star C_h control0 b0 u0 t0 k hk w hp
  · exact calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk w
      (Option.not_isSome_iff_eq_none.mp hc)

private theorem measurable_exceptional_vector (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (fun w : Sample k => ReferenceFirstCollectionRenewalVectorInsertion.av
      ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)) := by
  exact (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (((ReferenceSourceCurrentControlFreshness.measurable_u_t ⟨t0.val + 1 + k, hk⟩).fst).comp
      (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le))

/-- The no-call/stopped/absent-PRE joint target. Native physical continuation
uses the original complete vector, while the analytical observer still advances. -/
def calendarExceptionalJointLaw (k : ℕ) (hk : t0.val + 1 + k < p.T) : Measure (Joint k hk) :=
  ((law k hk.le).restrict (active k hk)ᶜ).map (fun w => joint k hk
    (w, ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)))

local notation "exceptionalJointLaw" => calendarExceptionalJointLaw rate rewards C_star C_h control0 b0 u0 t0

theorem calendarLaw_exceptional_joint (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    ((law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' (active k hk)ᶜ)).map (joint k hk) =
      exceptionalJointLaw k hk := by
  change (((law k hk.le).compProd (extension k (by omega))).restrict
    (Prod.fst ⁻¹' (active k hk)ᶜ)).map (joint k hk) = _
  have hA := measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hj := measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
  have he := measurable_exceptional_vector rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hex : Measurable (fun w : Sample k => joint k hk
      (w, ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w))) :=
    hj.comp (measurable_id.prodMk he)
  rw [calendarExceptionalJointLaw]
  refine Measure.ext_of_lintegral _ (fun F hF => ?_)
  rw [lintegral_map hF hj, lintegral_map hF hex]
  change (∫⁻ wv, (F ∘ joint k hk) wv ∂((law k hk.le).compProd
    (extension k (by omega))).restrict (Prod.fst ⁻¹' (active k hk)ᶜ)) = _
  rw [compProd_restrict_fst _ _ _ hA.compl, Measure.lintegral_compProd (hF.comp hj)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hA.compl] with w hw
  rw [extension_exceptional rate rewards C_star C_h control0 b0 u0 t0 k hk w hw, lintegral_dirac]
  rfl

private theorem sectionJointLaw_empty (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : ¬ s.val < t0.val + 1 + k) :
    sectionJointLaw renewed bs clear s k hk = 0 := by
  have hE := section_empty_of_date rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs
  simp only [calendarSectionJointLaw, calendarSectionRefillLaw, hE, Measure.restrict_empty,
    Measure.map_zero, Measure.zero_prod, Measure.compProd_zero_left]

/-- The section identity also includes impossible native dates, whose
unnormalized measures are zero. No endpoint/date witness is a caller input. -/
theorem calendarLaw_section_joint_rebase_all_dates (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) :
    ((law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)).map (joint k hk) =
        sectionJointLaw renewed bs clear s k hk := by
  change (((law k hk.le).compProd (extension k (by omega))).restrict
    (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)).map (joint k hk) = _
  by_cases hs : s.val < t0.val + 1 + k
  · exact calendarLaw_section_joint_rebase rate rewards C_star C_h control0 b0 u0 t0
      renewed bs clear s k hk hs
  · rw [sectionJointLaw_empty rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs,
      section_empty_of_date rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs]
    simp only [Set.preimage_empty, Measure.restrict_empty, Measure.map_zero]

/-- Exhaustive native joint splice: actual active sections plus every
exceptional branch. The first-root branch is still the fixed `b0,u0,t0`. -/
def calendarJointSpliceLaw (k : ℕ) (hk : t0.val + 1 + k < p.T) : Measure (Joint k hk) :=
  (Measure.sum fun i : Bool × Bool × Bool × Fin p.T =>
    sectionJointLaw i.1 i.2.1 i.2.2.1 i.2.2.2 k hk) + exceptionalJointLaw k hk

local notation "spliceLaw" => calendarJointSpliceLaw rate rewards C_star C_h control0 b0 u0 t0

/-- Actual generated complete-source and correlated archive/native joint law,
with all exceptional inputs included and without any event normalization. -/
theorem calendarLaw_joint_splice (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    (law (k + 1) (by omega)).map (joint k hk) = spliceLaw k hk := by
  have hA := measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hj := measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
  let E := fun i : Bool × Bool × Bool × Fin p.T =>
    sectionEvent i.1 i.2.1 i.2.2.1 i.2.2.2 k hk
  have hE : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0
      i.1 i.2.1 i.2.2.1 i.2.2.2 k hk
  have hd := section_pairwise rate rewards C_star C_h control0 b0 u0 t0 k hk
  let mu : Measure (Sample k × Vector) := law (k + 1) (by omega)
  have hpartition : mu.restrict (Prod.fst ⁻¹' active k hk) =
      Measure.sum fun i => mu.restrict (Prod.fst ⁻¹' E i) := by
    rw [calendarActiveEvent_partition, Set.preimage_iUnion]
    exact Measure.restrict_iUnion (fun i j hij => (hd hij).preimage _)
      (fun i => (hE i).preimage measurable_fst)
  have hsplit : mu = (Measure.sum fun i => mu.restrict (Prod.fst ⁻¹' E i)) +
      mu.restrict (Prod.fst ⁻¹' (active k hk)ᶜ) := by
    rw [← hpartition, Set.preimage_compl, Measure.restrict_add_restrict_compl (hA.preimage measurable_fst)]
  change mu.map (joint k hk) = _
  rw [hsplit, Measure.map_add _ _ hj, Measure.map_sum hj.aemeasurable]
  apply congrArg₂ (· + ·)
  · apply congrArg Measure.sum
    funext i
    exact calendarLaw_section_joint_rebase_all_dates rate rewards C_star C_h control0 b0 u0 t0
      i.1 i.2.1 i.2.2.1 i.2.2.2 k hk
  · exact calendarLaw_exceptional_joint rate rewards C_star C_h control0 b0 u0 t0 k hk

/-- The native-stopped last-call sections have zero active-call mass. The
stopped samples themselves are kept in the exceptional joint component. -/
theorem calendarEndpointSection_native_stopped_empty (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : sectionEvent renewed bs false s k hk = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact Bool.false_ne_true (calendarEndpointSection_native_clear rate rewards C_star C_h control0
    b0 u0 t0 renewed bs false s k hk w hw)

/-- Arbitrary Borel cylinders in the complete augmented sample and BOTH
observers are evaluated by the constructed native joint splice. -/
theorem calendarLaw_joint_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : Joint k hk → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv, F (joint k hk wv) ∂law (k + 1) (by omega)) = ∫⁻ z, F z ∂spliceLaw k hk := by
  exact (lintegral_map hF
    (measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)).symm.trans
      (congrArg (fun mu : Measure (Joint k hk) => ∫⁻ z, F z ∂mu)
        (calendarLaw_joint_splice rate rewards C_star C_h control0 b0 u0 t0 k hk))

/-- The joint target's physical projection is the CURRENT complete source,
with precisely the original first-branch restriction and original mass. -/
theorem calendarJointSpliceLaw_map_currentSource (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    (spliceLaw k hk).map (fun x : Joint k hk => current (k + 1) (by omega) x.1) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  have hj := measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hs : Measurable (fun x : Joint k hk => current (k + 1) (by omega) x.1) :=
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)).comp
      measurable_fst
  let mu : Measure (Sample k × Vector) := (law k hk.le).compProd (extension k (by omega))
  calc
    _ = (mu.map (joint k hk)).map (fun x : Joint k hk => current (k + 1) (by omega) x.1) := by
      exact congrArg (fun m : Measure (Joint k hk) =>
        m.map (fun x : Joint k hk => current (k + 1) (by omega) x.1))
          (calendarLaw_joint_splice rate rewards C_star C_h control0 b0 u0 t0 k hk).symm
    _ = mu.map (fun wv : Sample k × Vector => current (k + 1) (by omega) wv) :=
      Measure.map_map hs hj
    _ = _ := calendarLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)

theorem calendarJointSpliceLaw_mass (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    spliceLaw k hk Set.univ = BootstrapPrivateRoundStreams.sourceInputLaw p
      (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  have hs : Measurable (fun x : Joint k hk => current (k + 1) (by omega) x.1) :=
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)).comp
      measurable_fst
  have h := congrArg (fun mu : Measure Source => mu Set.univ)
    (calendarJointSpliceLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 k hk)
  simpa only [Measure.map_apply hs MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ] using h

/-- The initial finite boundary retains the complete raw branch lift jointly
with its accepted native initializer and literal initial prefix. -/
theorem calendarLaw_root_joint_rebase :
    (law 0 (by omega)).map (fun w => (w,
      (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w, (observe 0 (by omega) w).2.val))) =
    (branchLaw rate rewards C_star C_h control0 b0 u0 t0).map (fun w => (w,
      (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w,
        initialExtension rate rewards C_star C_h t0
          (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w)))) := by
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun w => Prod.ext rfl (Prod.ext rfl
    (calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 (by omega) w))

/-- Arbitrary complete-source tests, including the terminal calendar boundary. -/
theorem calendarLaw_currentSource_test (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (current k hk w) ∂law k hk) =
      ∫⁻ z, F z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  rw [← lintegral_map hF
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk),
    calendarLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 k hk]

/-- Date-based form of the current-source marginal on the SAME admitted
finite calendar. In particular `n = T` requires no next physical round. -/
theorem generatedCalendarLaw_map_currentSource (n : Fin (p.T + 1)) (htn : t0.val < n.val) :
    (generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 n htn).map
      (current (n.val - (t0.val + 1)) (by omega)) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) :=
  calendarLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 _ _

theorem generatedCalendarLaw_currentSource_test (n : Fin (p.T + 1)) (htn : t0.val < n.val)
    (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (current (n.val - (t0.val + 1)) (by omega) w)
      ∂generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 n htn) =
      ∫⁻ z, F z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) :=
  calendarLaw_currentSource_test rate rewards C_star C_h control0 b0 u0 t0 _ _ F hF

/-- The accepted first initializer, presented as a tagged native prefix.
Only its present-prefix typing proof is transported from the same root run. -/
def calendarRootNativeObserver (w : Sample 0) : TaggedPrefix rate t0.succ :=
  ⟨t0, ⟨initialExtension rate rewards C_star C_h t0
    (branchInitial rate rewards C_star C_h control0 b0 u0 t0 w), by
      rw [← calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 (by omega) w]
      exact (observe 0 (by omega) w).2.property⟩⟩

local notation "rootNative" => calendarRootNativeObserver rate rewards C_star C_h control0 b0 u0 t0

theorem calendarRootNativeObserver_eq (w : Sample 0) : rootNative w = observe 0 (by omega) w := by
  change (⟨t0, _⟩ : TaggedPrefix rate t0.succ) = ⟨t0, _⟩
  apply congrArg (Sigma.mk t0)
  exact Subtype.ext (calendarObservation_initial rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).symm

/-- Joint native target at EVERY finite boundary. The root uses its accepted
initializer; each later boundary projects the correlated exhaustive splice.
The complete raw sample, including its original private arrays and tape,
is retained jointly with the complete current archived observer. -/
def calendarBoundarySpliceLaw : (k : ℕ) → (hk : t0.val + 1 + k ≤ p.T) →
    Measure (Sample k × TaggedPrefix rate (calendarBoundary t0 k hk))
  | 0, _ => (branchLaw rate rewards C_star C_h control0 b0 u0 t0).map (fun w => (w, rootNative w))
  | k + 1, _ => (spliceLaw k (by omega)).map (fun x => (x.1, x.2.2))

local notation "boundarySpliceLaw" => calendarBoundarySpliceLaw rate rewards C_star C_h control0 b0 u0 t0

/-- The native target equals the actual joint law on the original calendar
sample and observer, with no new history, endpoint or coverage input. -/
theorem calendarLaw_boundary_joint_rebase (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    (law k hk).map (fun w => (w, observe k hk w)) = boundarySpliceLaw k hk := by
  cases k with
  | zero =>
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w =>
        Prod.ext rfl (calendarRootNativeObserver_eq rate rewards C_star C_h control0 b0 u0 t0 w).symm
  | succ k =>
      have hk' : t0.val + 1 + k < p.T := by omega
      have hj := measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk'
      have hp : Measurable (fun x : Joint k hk' => (x.1, x.2.2)) :=
        measurable_fst.prodMk measurable_snd.snd
      have h := congrArg (fun mu : Measure (Joint k hk') => mu.map (fun x => (x.1, x.2.2)))
        (calendarLaw_joint_splice rate rewards C_star C_h control0 b0 u0 t0 k hk')
      have hm := Measure.map_map hp hj (μ := (law k hk'.le).compProd (extension k (by omega)))
      exact hm.symm.trans h

/-- Borel joint tests at every finite boundary, including the terminal one. -/
theorem calendarLaw_boundary_joint_test (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (F : Sample k × TaggedPrefix rate (calendarBoundary t0 k hk) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (w, observe k hk w) ∂law k hk) = ∫⁻ z, F z ∂boundarySpliceLaw k hk := by
  exact (lintegral_map hF (measurable_id.prodMk
    (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk))).symm.trans
      (congrArg (fun mu => ∫⁻ z, F z ∂mu)
        (calendarLaw_boundary_joint_rebase rate rewards C_star C_h control0 b0 u0 t0 k hk))

omit control0 in
private theorem measurable_prefix_transport {X : Type*} [MeasurableSpace X]
    {n m : Fin (p.T + 1)} (h : n = m) :
    Measurable (fun x : X × TaggedPrefix rate n => (x.1, h ▸ x.2)) := by
  cases h
  exact measurable_id

/-- Date-based native target. Transport only changes the displayed boundary
index, and retains the SAME complete raw sample. -/
def generatedCalendarJointSpliceLaw (n : Fin (p.T + 1)) (htn : t0.val < n.val) :
    Measure (Sample (n.val - (t0.val + 1)) × TaggedPrefix rate n) :=
  let k := n.val - (t0.val + 1)
  let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  let h : calendarBoundary t0 k hk = n := Fin.ext (by dsimp only [calendarBoundary, k]; omega)
  (boundarySpliceLaw k hk).map (fun x => (x.1, h ▸ x.2))

/-- The actual generated raw sample and its entire correlated archived
observer have the constructed native joint law at every requested finite
date, including `n=T`; no next-call witness is required. -/
theorem generatedCalendarLaw_joint_rebase (n : Fin (p.T + 1)) (htn : t0.val < n.val) :
    (generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 n htn).map
      (fun w => (w, generatedCalendarObservation rate rewards C_star C_h control0 b0 u0 t0 n htn w)) =
        generatedCalendarJointSpliceLaw rate rewards C_star C_h control0 b0 u0 t0 n htn := by
  let k := n.val - (t0.val + 1)
  let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  let h : calendarBoundary t0 k hk = n := Fin.ext (by dsimp only [calendarBoundary, k]; omega)
  have hp := measurable_prefix_transport rate (X := Sample k) h
  have ho := measurable_id.prodMk
    (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)
  have hm := Measure.map_map hp ho (μ := law k hk)
  have he := congrArg (fun mu : Measure (Sample k × TaggedPrefix rate (calendarBoundary t0 k hk)) =>
      mu.map (fun x => (x.1, h ▸ x.2)))
    (calendarLaw_boundary_joint_rebase rate rewards C_star C_h control0 b0 u0 t0 k hk)
  exact hm.symm.trans he

/-- The exceptional component is the disjoint union of actual noncalls
(including LIVE dates) and calls with stopped or missing numerical PRE. -/
theorem calendarExceptionalEvent_partition (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    (active k hk)ᶜ = {w | callFlag k (by omega) w = false} ∪
      {w | callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false} ∧
    Disjoint {w : Sample k | callFlag k (by omega) w = false}
      {w | callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false} := by
  constructor
  · ext w
    change (¬ (callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = true)) ↔
      callFlag k (by omega) w = false ∨
        (callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false)
    cases callFlag k (by omega) w <;> cases (pending k (by omega) w).2 <;> decide
  · exact Set.disjoint_left.mpr fun _ hn hs => Bool.false_ne_true (hn.symm.trans hs.1)

/-- Explicit no-call versus stopped/absent-PRE decomposition of the full
correlated exceptional target, retaining both original unnormalized masses. -/
theorem calendarExceptionalJointLaw_partition (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    let g := fun w : Sample k => joint k hk
      (w, ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w))
    exceptionalJointLaw k hk =
      ((law k hk.le).restrict {w | callFlag k (by omega) w = false}).map g +
      ((law k hk.le).restrict
        {w | callFlag k (by omega) w = true ∧ (pending k (by omega) w).2 = false}).map g := by
  dsimp only
  have hg : Measurable (fun w : Sample k => joint k hk
      (w, ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w))) :=
    (measurable_calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk).comp
      (measurable_id.prodMk (measurable_exceptional_vector rate rewards C_star C_h control0 b0 u0 t0 k hk))
  have hStopped := (measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := true))).inter (measurableSet_eq_fun
      (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega)).snd
      (measurable_const (a := false)))
  rw [calendarExceptionalJointLaw,
    (calendarExceptionalEvent_partition rate rewards C_star C_h control0 b0 u0 t0 k hk).1,
    Measure.restrict_union
      (calendarExceptionalEvent_partition rate rewards C_star C_h control0 b0 u0 t0 k hk).2 hStopped,
    Measure.map_add _ _ hg]

/-- Every finite-boundary native joint target has the prescribed CURRENT
complete physical-source marginal, as a consequence of the joint rebase. -/
theorem calendarBoundarySpliceLaw_map_currentSource (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    (boundarySpliceLaw k hk).map (fun x => current k hk x.1) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  have hc := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk
  have ho := measurable_id.prodMk
    (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)
  rw [← calendarLaw_boundary_joint_rebase rate rewards C_star C_h control0 b0 u0 t0 k hk]
  exact (Measure.map_map (hc.comp measurable_fst) ho (μ := law k hk)).trans
    (calendarLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 k hk)

/-- Full Borel joint tests on the date-based native target. -/
theorem generatedCalendarLaw_joint_test (n : Fin (p.T + 1)) (htn : t0.val < n.val)
    (F : Sample (n.val - (t0.val + 1)) × TaggedPrefix rate n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (w, generatedCalendarObservation rate rewards C_star C_h control0 b0 u0 t0 n htn w)
      ∂generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 n htn) =
        ∫⁻ z, F z ∂generatedCalendarJointSpliceLaw rate rewards C_star C_h control0 b0 u0 t0 n htn := by
  exact (lintegral_map hF (measurable_id.prodMk
    (measurable_generatedCalendarObservation rate rewards C_star C_h control0 b0 u0 t0 n htn))).symm.trans
      (congrArg (fun mu => ∫⁻ z, F z ∂mu)
        (generatedCalendarLaw_joint_rebase rate rewards C_star C_h control0 b0 u0 t0 n htn))

/-- Date-based physical projection of the actual correlated native target. -/
theorem generatedCalendarJointSpliceLaw_map_currentSource (n : Fin (p.T + 1)) (htn : t0.val < n.val) :
    (generatedCalendarJointSpliceLaw rate rewards C_star C_h control0 b0 u0 t0 n htn).map
      (fun x => current (n.val - (t0.val + 1)) (by omega) x.1) =
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (branchEvent rate rewards C_star C_h b0 u0 t0) := by
  have hc := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
    (n.val - (t0.val + 1)) (by omega)
  have ho := measurable_id.prodMk
    (measurable_generatedCalendarObservation rate rewards C_star C_h control0 b0 u0 t0 n htn)
  rw [← generatedCalendarLaw_joint_rebase rate rewards C_star C_h control0 b0 u0 t0 n htn]
  exact (Measure.map_map (hc.comp measurable_fst) ho
    (μ := generatedCalendarLaw rate rewards C_star C_h control0 b0 u0 t0 n htn)).trans
      (generatedCalendarLaw_map_currentSource rate rewards C_star C_h control0 b0 u0 t0 n htn)

end Bandits.Support.ReferenceGeneratedCalendarJointRebase
