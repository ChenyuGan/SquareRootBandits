/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedRankCalendarFoundation

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Original last-call residual and future auxiliary block

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

Erasure and refill act on the original auxiliary tape in the complete
`CalendarSample`. All physical coordinates and every inserted full vector
survive. Observations are recomputed from the resulting raw sample.

The block consists of the unused UPDATE label at the specified last native
call and both original labels at every later date. This is an internal
probability component, not an endpoint law or a manuscript closure claim.
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
open ReferenceGeneratedRankCalendarFoundation

namespace Bandits.Support.ReferenceGeneratedCalendarResidualBlock

variable {p : ConstructorDimensions.Parameters}

local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Coordinate" => ReferenceFirstCollectionAuxiliarySeeds.Coordinate p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "zeroScalar" => ReferenceFirstLiveActualRefreshTestLaw.scalarZero

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) :=
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

/-- Literal zeroing of precisely the last-call UPDATE coordinate and all
later original pairs. The used label at the last call is retained. -/
def eraseBlockAuxiliary (bs : Bool) (s : Fin p.T) (a : Auxiliary) : Auxiliary :=
  (refreshSplit bs s).symm ((refreshSplit bs s a).1, fun _ => zeroScalar)

/-- Refill the same finite block of the original analytical tape. -/
def fillBlockAuxiliary (bs : Bool) (s : Fin p.T)
    (ax : Auxiliary × RefreshAuxiliary bs s) : Auxiliary :=
  (refreshSplit bs s).symm ((refreshSplit bs s ax.1).1, ax.2)

theorem measurable_eraseBlockAuxiliary (bs : Bool) (s : Fin p.T) :
    Measurable (eraseBlockAuxiliary bs s) :=
  (refreshSplit bs s).symm.measurable.comp
    ((refreshSplit bs s).measurable.fst.prodMk measurable_const)

theorem measurable_fillBlockAuxiliary (bs : Bool) (s : Fin p.T) :
    Measurable (fillBlockAuxiliary bs s) :=
  (refreshSplit bs s).symm.measurable.comp
    (((refreshSplit bs s).measurable.fst.comp measurable_fst).prodMk measurable_snd)

theorem eraseBlockAuxiliary_apply (bs : Bool) (s : Fin p.T) (a : Auxiliary) (j : Coordinate) :
    eraseBlockAuxiliary bs s a j = if refreshCoordinate bs s j then zeroScalar else a j := by
  rfl

theorem fillBlockAuxiliary_apply (bs : Bool) (s : Fin p.T)
    (ax : Auxiliary × RefreshAuxiliary bs s) (j : Coordinate) :
    fillBlockAuxiliary bs s ax j =
      if h : refreshCoordinate bs s j then ax.2 ⟨j, h⟩ else ax.1 j := by
  rfl

/-- The scalar in the accepted native split has exactly this original
address: renewal UPDATE uses zero, retained UPDATE uses one. -/
theorem futureAuxiliarySplit_scalar (bs : Bool) (s : Fin p.T) (a : Auxiliary) :
    (futureAuxiliarySplit s bs a).2 = a (s, if bs then 0 else 1) := by
  cases bs
  · rfl
  · have hc := insertRenewalRefreshScalar_current s (renewalRefreshScalarSplit s a).1
      (renewalRefreshScalarSplit s a).2
    have he := congrArg (fun f : Auxiliary => f (s, 0))
      ((renewalRefreshScalarSplit s).symm_apply_apply a)
    exact hc.symm.trans he

theorem eraseBlockAuxiliary_usedLabel (bs : Bool) (s : Fin p.T) (a : Auxiliary) :
    eraseBlockAuxiliary bs s a (s, if bs then 1 else 0) = a (s, if bs then 1 else 0) := by
  cases bs <;> simp [eraseBlockAuxiliary_apply, refreshCoordinate]

theorem fillBlockAuxiliary_erase (bs : Bool) (s : Fin p.T) (a : Auxiliary) :
    fillBlockAuxiliary bs s (eraseBlockAuxiliary bs s a, (refreshSplit bs s a).2) = a := by
  dsimp only [fillBlockAuxiliary, eraseBlockAuxiliary]
  rw [(refreshSplit bs s).apply_symm_apply]
  exact (refreshSplit bs s).symm_apply_apply a

private theorem erased_off_block (bs : Bool) (s : Fin p.T) (a : Auxiliary)
    (j : Coordinate) (hj : ¬ refreshCoordinate bs s j) :
    eraseBlockAuxiliary bs s a j = a j := by
  rw [eraseBlockAuxiliary_apply, ite_eq_right hj]

/-- The full finite auxiliary product splits jointly, rather than only in
its pairwise marginals. -/
theorem auxiliaryUniformLaw_eraseBlock (bs : Bool) (s : Fin p.T) :
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (fun a => (eraseBlockAuxiliary bs s a, (refreshSplit bs s a).2)) =
    ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (eraseBlockAuxiliary bs s)).prod (refreshAuxiliaryLaw bs s) := by
  let put : OldAuxiliary bs s → Auxiliary := fun a =>
    (refreshSplit bs s).symm (a, fun _ => zeroScalar)
  have hp : Measurable put := (refreshSplit bs s).symm.measurable.comp
    (measurable_id.prodMk measurable_const)
  have hj : (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (fun a => (eraseBlockAuxiliary bs s a, (refreshSplit bs s a).2)) =
      ((oldAuxiliaryLaw bs s).map put).prod (refreshAuxiliaryLaw bs s) := by
    have hm := Measure.map_prod_map (oldAuxiliaryLaw bs s) (refreshAuxiliaryLaw bs s) hp measurable_id
    rw [Measure.map_id] at hm
    rw [hm, ← (refreshSplit_measurePreserving bs s).map_eq,
      Measure.map_map (hp.prodMap measurable_id) (refreshSplit bs s).measurable]
    rfl
  have hm := congrArg (fun m => m.map Prod.fst) hj
  rw [Measure.map_map measurable_fst
    ((measurable_eraseBlockAuxiliary bs s).prodMk (refreshSplit bs s).measurable.snd),
    (measurePreserving_fst (μ := (oldAuxiliaryLaw bs s).map put)
      (ν := refreshAuxiliaryLaw bs s)).map_eq] at hm
  exact hj.trans (congrArg (fun m => m.prod (refreshAuxiliaryLaw bs s)) hm.symm)

private theorem source_auxiliary_block {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) [IsFiniteMeasure mu] (bs : Bool) (s : Fin p.T) :
    (mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
      (fun za => ((za.1, eraseBlockAuxiliary bs s za.2), (refreshSplit bs s za.2).2)) =
    ((mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
      (fun za => (za.1, eraseBlockAuxiliary bs s za.2))).prod (refreshAuxiliaryLaw bs s) := by
  let alpha := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  have hj := Measure.map_prod_map mu alpha measurable_id
    ((measurable_eraseBlockAuxiliary bs s).prodMk (refreshSplit bs s).measurable.snd)
  rw [Measure.map_id, auxiliaryUniformLaw_eraseBlock] at hj
  have he := Measure.map_prod_map mu alpha measurable_id (measurable_eraseBlockAuxiliary bs s)
  rw [Measure.map_id] at he
  change mu.prod (alpha.map (eraseBlockAuxiliary bs s)) =
    (mu.prod alpha).map (fun za => (za.1, eraseBlockAuxiliary bs s za.2)) at he
  rw [← he]
  have ha := (measurePreserving_prodAssoc mu (alpha.map (eraseBlockAuxiliary bs s))
    (refreshAuxiliaryLaw bs s)).symm.map_eq
  rw [hj, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap
      ((measurable_eraseBlockAuxiliary bs s).prodMk (refreshSplit bs s).measurable.snd))] at ha
  exact ha

/- The transport lemma is private. Its base split and nonuse inputs are
proved for the actual calendar kernels below. -/
private theorem compProd_block_factorization
    {B X V : Type*} [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (nu : Measure X) [IsProbabilityMeasure nu]
    (kernel : ProbabilityTheory.Kernel B V) [ProbabilityTheory.IsMarkovKernel kernel]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu)
    (hnonuse : ∀ᵐ w ∂mu, kernel w = kernel (e w)) :
    (mu.compProd kernel).map (fun w => ((e w.1, w.2), x w.1)) =
      ((mu.compProd kernel).map (fun w => (e w.1, w.2))).prod nu := by
  have hE : Measurable (fun w : B × V => (e w.1, w.2)) := he.prodMap measurable_id
  have hJ : Measurable (fun w : B × V => ((e w.1, w.2), x w.1)) :=
    hE.prodMk (hx.comp measurable_fst)
  have hpush : (mu.compProd kernel).map (fun w => (e w.1, w.2)) =
      (mu.map e).compProd kernel := by
    ext S hS
    rw [Measure.map_apply hE hS, Measure.compProd_apply (hS.preimage hE),
      Measure.compProd_apply hS,
      lintegral_map (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hS) he]
    apply lintegral_congr_ae
    filter_upwards [hnonuse] with w hw
    exact congrArg (fun m : Measure V => m (Prod.mk (e w) ⁻¹' S)) hw
  rw [hpush]
  apply Measure.ext_prod
  intro S R hS hR
  let F : B → ℝ≥0∞ := fun w => kernel w (Prod.mk w ⁻¹' S)
  have hF : Measurable F := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hS
  let f : B × X → ℝ≥0∞ := fun wx => F wx.1 * R.indicator (fun _ => 1) wx.2
  have hf : Measurable f := (hF.comp measurable_fst).mul
    ((measurable_const.indicator hR).comp measurable_snd)
  rw [Measure.map_apply hJ (hS.prod hR), Measure.compProd_apply ((hS.prod hR).preimage hJ),
    Measure.prod_prod, Measure.compProd_apply hS]
  calc
    _ = ∫⁻ w, f (e w, x w) ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hnonuse] with w hw
      change kernel w {v | (e w, v) ∈ S ∧ x w ∈ R} =
        F (e w) * R.indicator (fun _ => 1) (x w)
      rw [hw]
      by_cases hr : x w ∈ R <;> simp [F, hr, Set.preimage]
    _ = ∫⁻ wx, f wx ∂mu.map (fun w => (e w, x w)) :=
      (lintegral_map hf (he.prodMk hx)).symm
    _ = ∫⁻ wx, f wx ∂(mu.map e).prod nu := by rw [hbase]
    _ = (∫⁻ w, F w ∂mu.map e) * nu R := by
      rw [lintegral_prod_mul hF.aemeasurable (measurable_const.indicator hR).aemeasurable,
        lintegral_indicator_const hR, one_mul]

private theorem restrict_block_factorization
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (mu : Measure B) (nu : Measure X) [SFinite mu] [SFinite nu]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu)
    (E : Set B) (hE : MeasurableSet E) (hinv : e ⁻¹' E = E) :
    (mu.restrict E).map (fun w => (e w, x w)) =
      ((mu.restrict E).map e).prod nu := by
  have hpre : (fun w => (e w, x w)) ⁻¹' (E ×ˢ Set.univ) = E := by
    ext w
    simpa only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] using Set.ext_iff.mp hinv w
  calc
    _ = (mu.map (fun w => (e w, x w))).restrict (E ×ˢ Set.univ) := by
      rw [Measure.restrict_map (he.prodMk hx) (hE.prod MeasurableSet.univ), hpre]
    _ = ((mu.map e).restrict E).prod nu := by
      rw [hbase, Measure.restrict_prod_eq_prod_univ]
    _ = _ := by rw [Measure.restrict_map he hE, hinv]

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0
local notation "callAt" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h

/-- Replace only the original auxiliary array. All complete sources and
all successive complete assignment vectors remain in the same carrier. -/
def calendarWithAuxiliary : (k : ℕ) → Sample k × Auxiliary → Sample k
  | 0, wa => ((wa.1.1.1, wa.2), wa.1.2)
  | k + 1, wa => (calendarWithAuxiliary k (wa.1.1, wa.2), wa.1.2)

local notation "withAux" => calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0

theorem measurable_calendarWithAuxiliary (k : ℕ) : Measurable (withAux k) := by
  induction k with
  | zero => exact (measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  | succ k ih => exact (ih.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd

theorem calendarOriginalLift_withAuxiliary (k : ℕ) (w : Sample k) (a : Auxiliary) :
    original k (withAux k (w, a)) = (((original k w).1.1, a), (original k w).2) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih w.1

theorem calendarWithAuxiliary_original (k : ℕ) (w : Sample k) :
    withAux k (w, (original k w).1.2) = w := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

/-- Erase the finite block in the raw sample, retaining every full vector. -/
def calendarEraseBlock (bs : Bool) (s : Fin p.T) (k : ℕ) (w : Sample k) : Sample k :=
  withAux k (w, eraseBlockAuxiliary bs s (original k w).1.2)

/-- Refill before regenerating any current or archived observation. -/
def calendarFillBlock (bs : Bool) (s : Fin p.T) (k : ℕ)
    (wx : Sample k × RefreshAuxiliary bs s) : Sample k :=
  withAux k (wx.1, fillBlockAuxiliary bs s ((original k wx.1).1.2, wx.2))

local notation "erase" => calendarEraseBlock rate rewards C_star C_h b0 u0 t0
local notation "fill" => calendarFillBlock rate rewards C_star C_h b0 u0 t0

theorem measurable_calendarEraseBlock (bs : Bool) (s : Fin p.T) (k : ℕ) :
    Measurable (erase bs s k) :=
  (measurable_calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k).comp
    (measurable_id.prodMk ((measurable_eraseBlockAuxiliary bs s).comp
      (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd))

theorem measurable_calendarFillBlock (bs : Bool) (s : Fin p.T) (k : ℕ) :
    Measurable (fill bs s k) :=
  (measurable_calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k).comp
    (measurable_fst.prodMk ((measurable_fillBlockAuxiliary bs s).comp
      (((measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd.comp
        measurable_fst).prodMk measurable_snd)))

theorem calendarEraseBlock_succ (bs : Bool) (s : Fin p.T) (k : ℕ) (w : Sample (k + 1)) :
    erase bs s (k + 1) w = (erase bs s k w.1, w.2) := rfl

theorem calendarFillBlock_succ (bs : Bool) (s : Fin p.T) (k : ℕ)
    (wx : Sample (k + 1) × RefreshAuxiliary bs s) :
    fill bs s (k + 1) wx = (fill bs s k (wx.1.1, wx.2), wx.1.2) := rfl

theorem calendarOriginalLift_eraseBlock (bs : Bool) (s : Fin p.T) (k : ℕ) (w : Sample k) :
    original k (erase bs s k w) =
      (((original k w).1.1, eraseBlockAuxiliary bs s (original k w).1.2), (original k w).2) :=
  calendarOriginalLift_withAuxiliary rate rewards C_star C_h b0 u0 t0 k w _

theorem calendarFillBlock_erase (bs : Bool) (s : Fin p.T) (k : ℕ) (w : Sample k) :
    fill bs s k (erase bs s k w, (refreshSplit bs s (original k w).1.2).2) = w := by
  induction k with
  | zero =>
      change ((w.1.1, fillBlockAuxiliary bs s
        (eraseBlockAuxiliary bs s w.1.2, (refreshSplit bs s w.1.2).2)), w.2) = w
      rw [fillBlockAuxiliary_erase]
      exact Prod.ext (Prod.ext rfl rfl) rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

private theorem initial_block_factorization (bs : Bool) (s : Fin p.T)
    (hts : t0.val ≤ s.val) (hbs : t0 = s → b0 = bs) (hk : t0.val + 1 ≤ p.T) :
    (law 0 hk).map (fun w => (erase bs s 0 w, (refreshSplit bs s w.1.2).2)) =
      ((law 0 hk).map (erase bs s 0)).prod (refreshAuxiliaryLaw bs s) := by
  change (branchLaw rate rewards C_star C_h control0 b0 u0 t0).map _ =
    ((branchLaw rate rewards C_star C_h control0 b0 u0 t0).map _).prod _
  rw [branchLaw_compProd]
  apply compProd_block_factorization _ _
    (originalVectorKernel rate rewards C_star C_h control0 b0 u0 t0)
    (fun za => (za.1, eraseBlockAuxiliary bs s za.2))
    (measurable_fst.prodMk ((measurable_eraseBlockAuxiliary bs s).comp measurable_snd))
    (fun za => (refreshSplit bs s za.2).2)
    ((refreshSplit bs s).measurable.snd.comp measurable_snd)
    (source_auxiliary_block _ bs s)
  apply Filter.Eventually.of_forall
  intro za
  apply originalVectorKernel_refresh_ext rate rewards C_star C_h control0 b0 u0 t0
  intro j hj
  symm
  apply erased_off_block
  intro hblock
  apply hj
  by_cases he : t0 = s
  · subst s
    rw [hbs rfl]
    exact hblock
  · have hlt : t0.val < s.val := by
      have hne : t0.val ≠ s.val := fun h => he (Fin.ext h)
      omega
    rcases hblock with hfuture | ⟨hs, _⟩
    · exact Or.inl (hlt.trans hfuture)
    · exact Or.inl (by rw [hs]; exact hlt)

/-- Actual root residual split in either original branch orientation. The
original unnormalized event weights, none atoms and full vector are retained. -/
theorem calendarLaw_rootResidualBlock (hk : t0.val + 1 ≤ p.T) :
    (law 0 hk).map (fun w => (erase b0 t0 0 w, (refreshSplit b0 t0 w.1.2).2)) =
      ((law 0 hk).map (erase b0 t0 0)).prod (refreshAuxiliaryLaw b0 t0) :=
  initial_block_factorization rate rewards C_star C_h control0 b0 u0 t0 b0 t0
    le_rfl (fun _ => rfl) hk

/-- The current complete physical source, with all earlier insertions. -/
def calendarCurrentSource (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) : Source :=
  (observe k hk w).2.val.1.1.1.2

local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0

private theorem measurable_sigma_elim {I X : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] [MeasurableSpace X]
    (f : Sigma B → X) (hf : ∀ i, Measurable (fun x : B i => f ⟨i, x⟩)) : Measurable f := by
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hU

theorem measurable_calendarCurrentSource (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (current k hk) := by
  have hs : Measurable (fun o : TaggedPrefix rate (calendarBoundary t0 k hk) =>
      o.2.val.1.1.1.2) :=
    measurable_sigma_elim _ (fun _ => measurable_subtype_coe.fst.fst.fst.snd)
  exact hs.comp (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)

private theorem calendarStep_source_tag_ext (q : Fin p.T)
    (o o' : TaggedPrefix rate q.castSucc) (a a' : Auxiliary) (v : Vector)
    (ht : o.1 = o'.1) (hz : o.2.val.1.1.1.2 = o'.2.val.1.1.1.2) :
    let l := calendarStep rate rewards C_star C_h control0 q (o, (a, v))
    let r := calendarStep rate rewards C_star C_h control0 q (o', (a', v))
    l.1 = r.1 ∧ l.2.val.1.1.1.2 = r.2.val.1.1.1.2 := by
  by_cases hc : (callAt q o.2.val.1.1.1.2).isSome = true
  · have hc' : (callAt q o'.2.val.1.1.1.2).isSome = true := by rwa [← hz]
    have hE : (o.2, (a, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
    have hE' : (o'.2, (a', v)) ∈ calendarCallEvent rate rewards C_star C_h o'.1 q := hc'
    dsimp only
    rw [calendarStep, dite_eq_left hE, calendarStep, dite_eq_left hE']
    exact ⟨rfl, congrArg (fun z => ReferenceFirstCollectionRenewalVectorInsertion.insert q z v) hz⟩
  · have hc' : ¬ (callAt q o'.2.val.1.1.1.2).isSome = true := by rwa [← hz]
    have hE : ¬ (o.2, (a, v)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
    have hE' : ¬ (o'.2, (a', v)) ∈ calendarCallEvent rate rewards C_star C_h o'.1 q := hc'
    dsimp only
    rw [calendarStep, dite_eq_right hE, calendarStep, dite_eq_right hE']
    exact ⟨ht, hz⟩

/-- Call selection and the current physical source ignore the analytical
tape pointwise. Logical seeds, lists and archived observers are not equated. -/
theorem calendarObservation_withAuxiliary_source_tag (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) (a : Auxiliary) :
    (observe k hk (withAux k (w, a))).1 = (observe k hk w).1 ∧
      current k hk (withAux k (w, a)) = current k hk w := by
  induction k with
  | zero => cases b0 <;> exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨ht, hz⟩ := ih (by omega) w.1
      exact calendarStep_source_tag_ext rate rewards C_star C_h control0 _ _ _ _ _ _ ht hz

private theorem finite_coordinate_ext {I X Y : Type*} [Fintype I] [DecidableEq I]
    (f : (I → X) → Y) (S : Set I) [DecidablePred (· ∈ S)]
    (hf : ∀ a i, i ∈ S → ∀ x, f (Function.update a i x) = f a)
    (a a' : I → X) (ha : ∀ i, i ∉ S → a i = a' i) : f a = f a' := by
  have hfinite : ∀ U : Finset I, (∀ i ∈ U, i ∈ S) →
      f (fun i => if i ∈ U then a' i else a i) = f a := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simp only [Finset.notMem_empty, ite_false]
    | @insert i U hi ih =>
        intro hU
        have he : (fun j => if j ∈ insert i U then a' j else a j) =
            Function.update (fun j => if j ∈ U then a' j else a j) i (a' i) := by
          funext j
          by_cases hj : j = i
          · subst j; simp only [Finset.mem_insert_self, ite_true, Function.update_self]
          · simp only [Finset.mem_insert, hj, false_or, Function.update_of_ne hj]
        rw [he, hf _ i (hU i (Finset.mem_insert_self _ _))]
        exact ih (fun j hj => hU j (Finset.mem_insert_of_mem hj))
  let U := Finset.univ.filter (· ∈ S)
  have he : (fun i => if i ∈ U then a' i else a i) = a' := by
    funext i
    by_cases hi : i ∈ S
    · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_true]
    · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_false]
      exact ha i hi
  have h := hfinite U (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [he] at h
  exact h.symm

private theorem branch_initial_auxiliary_ext
    (z : BranchSource rate rewards C_star C_h b0 u0 t0) (a a' : Auxiliary) (v : Vector)
    (ha : ∀ j : Coordinate, j.1.val ≤ t0.val → a j = a' j) :
    branchObservation rate rewards C_star C_h control0 b0 u0 t0 t0.succ ((z, a), v) =
      branchObservation rate rewards C_star C_h control0 b0 u0 t0 t0.succ ((z, a'), v) := by
  apply finite_coordinate_ext (fun a =>
    branchObservation rate rewards C_star C_h control0 b0 u0 t0 t0.succ ((z, a), v))
    {j | t0.val < j.1.val} _ a a' (fun j hj => ha j (Nat.le_of_not_gt hj))
  intro a j hj x
  change t0.val < j.1.val at hj
  apply branchObservation_auxiliary_pair rate rewards C_star C_h control0 b0 u0 t0 j.1
    t0.succ (Nat.lt_succ_self _) (Nat.succ_le_of_lt hj)
  intro i hi
  exact Function.update_of_ne (fun he => hi (congrArg Prod.fst he)) x a

/-- Before the specified block starts, the whole generated observer reads
only the original auxiliary prefix. -/
theorem calendarObservation_withAuxiliary_prefix (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) (a : Auxiliary)
    (ha : ∀ j : Coordinate, j.1.val < t0.val + 1 + k → a j = (original k w).1.2 j) :
    observe k hk (withAux k (w, a)) = observe k hk w := by
  induction k with
  | zero =>
      apply congrArg (Sigma.mk t0)
      apply Subtype.ext
      exact branch_initial_auxiliary_ext rate rewards C_star C_h control0 b0 u0 t0
        w.1.1 a w.1.2 w.2 (fun j hj => ha j (by omega))
  | succ k ih =>
      change calendarStep rate rewards C_star C_h control0 ⟨t0.val + 1 + k, by omega⟩
        (observe k (by omega) (withAux k (w.1, a)),
          ((original k (withAux k (w.1, a))).1.2, w.2)) = _
      rw [ih (by omega) w.1 (fun j hj => ha j (by omega)), calendarOriginalLift_withAuxiliary]
      apply calendarStep_auxiliary_ext
      intro j hj
      exact ha j (by change j.1.val ≤ t0.val + 1 + k at hj; omega)

theorem calendarObservation_eraseBlock_before (bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : t0.val + 1 + k ≤ s.val) (w : Sample k) :
    observe k hk (erase bs s k w) = observe k hk w := by
  apply calendarObservation_withAuxiliary_prefix
  intro j hj
  apply erased_off_block
  rintro (h | ⟨he, _⟩)
  · omega
  · have := congrArg Fin.val he
    omega

/-- Literal PRE overflow test for the root invocation, before its UPDATE.
The complete current source still has its native strict physical prefix. -/
def calendarRootPreClear (w : Sample 0) : Bool :=
  (prefixNumerical rate rewards C_star C_h t0.castSucc (current 0 (by omega) w)).any
    (fun S => !S.overflow)

local notation "rootClear" => calendarRootPreClear rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarRootPreClear : Measurable rootClear :=
  (measurable_of_countable (fun S : Option (RecordedQueueRun.RunState p.K) =>
    S.any (fun R : RecordedQueueRun.RunState p.K => !R.overflow))).comp
      ((measurable_prefixNumerical rate rewards C_star C_h t0.castSucc).comp
        (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)))

/-- The root PRE-clear readout is the actual native PRE overflow test,
including the first invocation after which overflow is detected. -/
theorem calendarRootPreClear_native (w : Sample 0) :
    rootClear w = !(ReferenceGeneratedInvocationCallSplice.nativeBefore rate rewards C_star C_h control0 t0
      ⟨current 0 (by omega) w,
        (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).2.1⟩).overflow := by
  let z : ReferenceGeneratedInvocationCallSplice.InvocationSource rate rewards C_star C_h t0 :=
    ⟨current 0 (by omega) w,
      (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).2.1⟩
  change (prefixNumerical rate rewards C_star C_h t0.castSucc z.val).any (fun S => !S.overflow) =
    !(ReferenceGeneratedInvocationCallSplice.nativeBefore rate rewards C_star C_h control0 t0 z).overflow
  rw [ReferenceGeneratedInvocationCallSplice.nativeBefore_prefix rate rewards C_star C_h control0 t0 z]
  rfl

/-- The selector at the next actual calendar date. -/
def calendarCallFlag (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T) (w : Sample k) : Bool :=
  (callAt ⟨t0.val + 1 + k, by omega⟩ (current k (by omega) w)).isSome

/-- The local renewal orientation and PRE-clear bit of this actual call.
Neither is inferred from an earlier root's branch tag. -/
def calendarPendingFlags (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T) (w : Sample k) : Bool × Bool :=
  let o := observe k (by omega) w
  (renewalFlag rate rewards C_star C_h (t := o.1) ⟨t0.val + 1 + k, by omega⟩ o.2.val,
    preClearFlag rate (t := o.1) ⟨t0.val + 1 + k, by omega⟩ o.2.val)

local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0

private theorem measurable_isSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  convert ((measurable_const : Measurable (fun _ : A => true)).sumElim
    (measurable_const : Measurable (fun _ : PUnit => false))).comp
      (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext a
  cases a <;> rfl

theorem measurable_calendarCallFlag (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T) :
    Measurable (callFlag k hk) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
  exact measurable_isSome.comp
    (((ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (q.val + 1)) le_rfl).comp
      (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k (by omega)))

theorem measurable_calendarPendingFlags (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T) :
    Measurable (pending k hk) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
  have h : Measurable (fun o : TaggedPrefix rate q.castSucc =>
      (renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val,
        preClearFlag rate (t := o.1) q o.2.val)) := by
    apply measurable_sigma_elim
    intro s
    exact ((measurable_renewalFlag rate rewards C_star C_h (t := s) q).comp measurable_subtype_coe).prodMk
      ((measurable_preClearFlag rate (t := s) q).comp measurable_subtype_coe)
  exact h.comp (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k (by omega))

theorem calendarCallFlag_withAuxiliary (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T)
    (w : Sample k) (a : Auxiliary) : callFlag k hk (withAux k (w, a)) = callFlag k hk w :=
  congrArg (fun z => (callAt ⟨t0.val + 1 + k, by omega⟩ z).isSome)
    (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k
      (by omega) w a).2

theorem calendarPendingFlags_withAuxiliary (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T)
    (w : Sample k) (a : Auxiliary) : pending k hk (withAux k (w, a)) = pending k hk w := by
  have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k
    (by omega) w a).2
  change (observe k (by omega) (withAux k (w, a))).2.val.1.1.1.2 =
    (observe k (by omega) w).2.val.1.1.1.2 at hz
  apply Prod.ext
  · dsimp only [calendarPendingFlags, renewalFlag]
    rw [hz]
  · dsimp only [calendarPendingFlags, preClearFlag]
    rw [calendarObservation_numerical, calendarObservation_numerical, hz]

/-- Read the local flags of the most recent actual call. This is a
deterministic readout of `CalendarSample`, not an additional process. -/
def calendarLastFlags : (k : ℕ) → (hk : t0.val + 1 + k ≤ p.T) → Sample k → Bool × Bool
  | 0, _, w => (b0, rootClear w)
  | k + 1, hk, w => if callFlag k hk w.1 then pending k hk w.1
      else calendarLastFlags k (by omega) w.1

local notation "lastFlags" => calendarLastFlags rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarLastFlags (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (lastFlags k hk) := by
  induction k with
  | zero =>
      exact measurable_const.prodMk
        (measurable_calendarRootPreClear rate rewards C_star C_h control0 b0 u0 t0)
  | succ k ih =>
      exact ((measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k hk).comp
        measurable_fst).ite
          (measurableSet_eq_fun ((measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k hk).comp
            measurable_fst) measurable_const)
          ((ih (by omega)).comp measurable_fst)

/-- Before s there is no extra condition. At s require its literal call,
local renewal and PRE-clear bits. Afterwards require the actual no-call
selector; this is the prescribed Dirac branch of the vector kernel. -/
def calendarResidualGate (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + (k + 1) ≤ p.T) : Set (Sample k) :=
  if t0.val + 1 + k < s.val then Set.univ
  else if t0.val + 1 + k = s.val then
    {w | callFlag k hk w = true ∧ pending k hk w = (bs, clear)}
  else {w | callFlag k hk w = false}

/-- Literal finite event on the raw produced samples. Pending dates allow
all samples; after s it records exactly the last-call/no-next event. -/
def calendarResidualEvent (bs clear : Bool) (s : Fin p.T) :
    (k : ℕ) → (hk : t0.val + 1 + k ≤ p.T) → Set (Sample k)
  | 0, _ => if t0.val < s.val then Set.univ
      else if t0 = s ∧ b0 = bs then {w | rootClear w = clear} else ∅
  | k + 1, hk => {w | w.1 ∈ calendarResidualEvent bs clear s k (by omega) ∧
      w.1 ∈ calendarResidualGate rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk}

local notation "gate" => calendarResidualGate rate rewards C_star C_h control0 b0 u0 t0
local notation "event" => calendarResidualEvent rate rewards C_star C_h control0 b0 u0 t0

theorem measurableSet_calendarResidualGate (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + (k + 1) ≤ p.T) : MeasurableSet (gate bs clear s k hk) := by
  unfold calendarResidualGate
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_eq_fun
      (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const).inter
      (measurableSet_eq_fun
        (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const)
  · exact measurableSet_eq_fun
      (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const

theorem measurableSet_calendarResidualEvent (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) : MeasurableSet (event bs clear s k hk) := by
  induction k with
  | zero =>
      unfold calendarResidualEvent
      split_ifs
      · exact MeasurableSet.univ
      · exact measurableSet_eq_fun
          (measurable_calendarRootPreClear rate rewards C_star C_h control0 b0 u0 t0) measurable_const
      · exact MeasurableSet.empty
  | succ k ih =>
      exact ((ih (by omega)).inter
        (measurableSet_calendarResidualGate rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk)).preimage
          measurable_fst

theorem calendarResidualGate_withAuxiliary (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + (k + 1) ≤ p.T) (w : Sample k) (a : Auxiliary) :
    withAux k (w, a) ∈ gate bs clear s k hk ↔ w ∈ gate bs clear s k hk := by
  unfold calendarResidualGate
  split_ifs
  · rfl
  · change callFlag k hk (withAux k (w, a)) = true ∧ pending k hk (withAux k (w, a)) = (bs, clear) ↔ _
    rw [calendarCallFlag_withAuxiliary, calendarPendingFlags_withAuxiliary]
    rfl
  · change callFlag k hk (withAux k (w, a)) = false ↔ _
    rw [calendarCallFlag_withAuxiliary]
    rfl

theorem calendarResidualEvent_withAuxiliary (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) (a : Auxiliary) :
    withAux k (w, a) ∈ event bs clear s k hk ↔ w ∈ event bs clear s k hk := by
  induction k with
  | zero =>
      have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0
        0 (by omega) w a).2
      unfold calendarResidualEvent
      split_ifs
      · rfl
      · change rootClear (withAux 0 (w, a)) = clear ↔ rootClear w = clear
        dsimp only [calendarRootPreClear]
        rw [hz]
      · rfl
  | succ k ih =>
      change withAux k (w.1, a) ∈ event bs clear s k (by omega) ∧
        withAux k (w.1, a) ∈ gate bs clear s k hk ↔ _
      rw [ih (by omega) w.1, calendarResidualGate_withAuxiliary]
      rfl

private theorem calendarVectorKernel_pair_ext (q : Fin p.T) (o : TaggedPrefix rate q.castSucc)
    (a a' : Auxiliary)
    (h : ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a =
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a') :
    calendarVectorKernel rate rewards C_star C_h control0 q (o, a) =
      calendarVectorKernel rate rewards C_star C_h control0 q (o, a') :=
  congrArg (fun x => nextVectorKernel rate rewards C_star C_h (t := o.1) (q := q) control0 (o.2.val, x)) h

private theorem calendarVectorKernel_noCall (q : Fin p.T) (o : TaggedPrefix rate q.castSucc)
    (a : Auxiliary) (hc : callAt q o.2.val.1.1.1.2 = none) :
    calendarVectorKernel rate rewards C_star C_h control0 q (o, a) =
      Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av q o.2.val.1.1.1.2) := by
  rw [calendarVectorKernel_apply, nextVectorKernel_apply]
  simp only [installationSelection, hc]
  rfl

/-- Actual nonuse at all three stages: before s; the UPDATE label at s
while renewal still reads label one; and the literal no-call Dirac branches
after s. No generated seed/list independence is asserted. -/
theorem calendarExtensionKernel_eraseBlock_onGate (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + (k + 1) ≤ p.T) (w : Sample k)
    (hw : w ∈ gate bs clear s k hk) :
    extension k hk (erase bs s k w) = extension k hk w := by
  let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
  let a := (original k w).1.2
  have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0
    k (by omega) w (eraseBlockAuxiliary bs s a)).2
  change current k (by omega) (erase bs s k w) = current k (by omega) w at hz
  change calendarVectorKernel rate rewards C_star C_h control0 q
      (observe k (by omega) (erase bs s k w), (original k (erase bs s k w)).1.2) =
    calendarVectorKernel rate rewards C_star C_h control0 q (observe k (by omega) w, a)
  rw [calendarOriginalLift_eraseBlock]
  by_cases hlt : t0.val + 1 + k < s.val
  · rw [calendarObservation_eraseBlock_before rate rewards C_star C_h control0 b0 u0 t0 bs s k
      (by omega) hlt.le]
    apply calendarVectorKernel_pair_ext
    apply Prod.ext <;> apply erased_off_block
    all_goals
      rintro (h | ⟨he, _⟩)
      · change s.val < t0.val + 1 + k at h
        omega
      · have h := congrArg Fin.val he
        change t0.val + 1 + k = s.val at h
        omega
  by_cases heq : t0.val + 1 + k = s.val
  · have hqs : q = s := Fin.ext heq
    have hg : callFlag k hk w = true ∧ pending k hk w = (bs, clear) := by
      simpa only [calendarResidualGate, ite_eq_right hlt, ite_eq_left heq, Set.mem_ofPred_eq] using hw
    have hb : renewalFlag rate rewards C_star C_h (t := (observe k (by omega) w).1) q
        (observe k (by omega) w).2.val = bs := congrArg Prod.fst hg.2
    rw [calendarObservation_eraseBlock_before rate rewards C_star C_h control0 b0 u0 t0 bs s k
      (by omega) heq.le]
    let a' := Function.update a (q, if bs then 0 else 1) zeroScalar
    have hp : ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q (eraseBlockAuxiliary bs s a) =
        ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a' := by
      dsimp only [a']
      rw [hqs]
      cases bs <;> apply Prod.ext <;>
        simp [ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair,
          eraseBlockAuxiliary_apply, refreshCoordinate]
    have hn := calendarVectorKernel_update_nonuse rate rewards C_star C_h control0 q
      (observe k (by omega) w) a zeroScalar
    dsimp only at hn
    rw [hb] at hn
    exact (calendarVectorKernel_pair_ext rate rewards C_star C_h control0 q _ _ a' hp).trans hn
  · have hg : callFlag k hk w = false := by
      simpa only [calendarResidualGate, hlt, ite_false, heq, Set.mem_ofPred_eq] using hw
    have hc : callAt q (current k (by omega) w) = none := by
      apply Option.not_isSome_iff_eq_none.mp
      rw [show (callAt q (current k (by omega) w)).isSome = false from hg]
      exact Bool.false_ne_true
    have hc' : callAt q (current k (by omega) (erase bs s k w)) = none := by rw [hz, hc]
    rw [calendarVectorKernel_noCall rate rewards C_star C_h control0 q _ _ hc',
      calendarVectorKernel_noCall rate rewards C_star C_h control0 q _ _ hc]
    exact congrArg (fun z => Measure.dirac (ReferenceFirstCollectionRenewalVectorInsertion.av q z)) hz

private theorem compProd_restrict_fst {B V : Type*} [MeasurableSpace B] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (kernel : ProbabilityTheory.Kernel B V)
    [ProbabilityTheory.IsMarkovKernel kernel] (D : Set B) (hD : MeasurableSet D) :
    (mu.compProd kernel).restrict (Prod.fst ⁻¹' D) = (mu.restrict D).compProd kernel := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.compProd_apply (hS.inter (hD.preimage measurable_fst)),
    Measure.compProd_apply hS, ← lintegral_indicator hD]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ D <;> simp [Set.preimage, hw]

private theorem initial_restricted_block_factorization (bs clear : Bool) (s : Fin p.T)
    (hk : t0.val + 1 ≤ p.T) :
    ((law 0 hk).restrict (event bs clear s 0 hk)).map
        (fun w => (erase bs s 0 w, (refreshSplit bs s w.1.2).2)) =
      (((law 0 hk).restrict (event bs clear s 0 hk)).map (erase bs s 0)).prod
        (refreshAuxiliaryLaw bs s) := by
  by_cases h : t0.val ≤ s.val ∧ (t0 = s → b0 = bs)
  · apply restrict_block_factorization _ _ (erase bs s 0)
      (measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s 0)
      (fun w => (refreshSplit bs s w.1.2).2)
      ((refreshSplit bs s).measurable.snd.comp measurable_fst.snd)
      (initial_block_factorization rate rewards C_star C_h control0 b0 u0 t0 bs s h.1 h.2 hk)
      (event bs clear s 0 hk)
      (measurableSet_calendarResidualEvent rate rewards C_star C_h control0 b0 u0 t0 bs clear s 0 hk)
    ext w
    exact calendarResidualEvent_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 bs clear s 0 hk w _
  · have he : event bs clear s 0 hk = ∅ := by
      unfold calendarResidualEvent
      split_ifs with hlt hflags
      · exfalso
        apply h
        refine ⟨hlt.le, fun he => ?_⟩
        have := congrArg Fin.val he
        omega
      · exfalso
        exact h ⟨by rw [hflags.1], fun _ => hflags.2⟩
      · rfl
    rw [he, Measure.restrict_empty, Measure.map_zero, Measure.map_zero, Measure.zero_prod]

/-- Joint finite-block factorization under the actual produced calendar
law restricted to its literal last-call event. All event measures remain
unnormalized, including empty events and zero-mass/null branches. -/
theorem calendarLaw_restrict_eraseBlock (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) :
    ((law k hk).restrict (event bs clear s k hk)).map
        (fun w => (erase bs s k w, (refreshSplit bs s (original k w).1.2).2)) =
      (((law k hk).restrict (event bs clear s k hk)).map (erase bs s k)).prod
        (refreshAuxiliaryLaw bs s) := by
  induction k with
  | zero => exact initial_restricted_block_factorization rate rewards C_star C_h control0 b0 u0 t0 bs clear s hk
  | succ k ih =>
      let E := event bs clear s k (by omega)
      let G := gate bs clear s k hk
      have hE : MeasurableSet E :=
        measurableSet_calendarResidualEvent rate rewards C_star C_h control0 b0 u0 t0 bs clear s k (by omega)
      have hG : MeasurableSet G :=
        measurableSet_calendarResidualGate rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk
      have hGinv : (erase bs s k) ⁻¹' G = G := by
        ext w
        exact calendarResidualGate_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w _
      have hD : ((law k (by omega)).restrict E).restrict G =
          (law k (by omega)).restrict (E ∩ G) := by rw [Measure.restrict_restrict hG, Set.inter_comm]
      have hbase := restrict_block_factorization
        ((law k (by omega)).restrict E) (refreshAuxiliaryLaw bs s) (erase bs s k)
        (measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k)
        (fun w => (refreshSplit bs s (original k w).1.2).2)
        ((refreshSplit bs s).measurable.snd.comp
          (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)
        (ih (by omega)) G hG hGinv
      rw [hD] at hbase
      have hsuc : (law (k + 1) hk).restrict (event bs clear s (k + 1) hk) =
          ((law k (by omega)).restrict (E ∩ G)).compProd (extension k hk) :=
        compProd_restrict_fst _ _ (E ∩ G) (hE.inter hG)
      rw [hsuc]
      apply compProd_block_factorization _ _ (extension k hk) (erase bs s k)
        (measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k)
        (fun w => (refreshSplit bs s (original k w).1.2).2)
        ((refreshSplit bs s).measurable.snd.comp
          (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)
        hbase
      apply (ae_restrict_iff' (hE.inter hG)).mpr
      exact Filter.Eventually.of_forall fun w hw =>
        (calendarExtensionKernel_eraseBlock_onGate rate rewards C_star C_h control0 b0 u0 t0
          bs clear s k hk w hw.2).symm

private theorem calendarResidualEvent_before (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : t0.val + 1 + k ≤ s.val) :
    event bs clear s k hk = Set.univ := by
  induction k with
  | zero =>
      have hlt : t0.val < s.val := by omega
      rw [calendarResidualEvent, ite_eq_left hlt]
  | succ k ih =>
      have hlt : t0.val + 1 + k < s.val := by omega
      change {w : Sample (k + 1) | w.1 ∈ event bs clear s k (by omega) ∧
        w.1 ∈ gate bs clear s k hk} = Set.univ
      rw [ih (by omega) (by omega), calendarResidualGate, ite_eq_left hlt]
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ, and_self]

private theorem calendarObservation_tag_succ (k : ℕ) (hk : t0.val + 1 + (k + 1) ≤ p.T)
    (w : Sample (k + 1)) :
    (observe (k + 1) hk w).1 = if callFlag k hk w.1 then
      ⟨t0.val + 1 + k, by omega⟩ else (observe k (by omega) w.1).1 := by
  change Sample k × Vector at w
  have hk0 : t0.val + 1 + k ≤ p.T := by omega
  let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk0 w.1
  change (calendarStep rate rewards C_star C_h control0 q
    (o, ((original k w.1).1.2, w.2))).1 = if callFlag k hk w.1 then q else o.1
  by_cases hc : callFlag k hk w.1 = true
  · have hE : (o.2, ((original k w.1).1.2, w.2)) ∈
        calendarCallEvent rate rewards C_star C_h o.1 q := hc
    rw [calendarStep, dite_eq_left hE, ite_eq_left hc]
  · have hE : ¬ (o.2, ((original k w.1).1.2, w.2)) ∈
        calendarCallEvent rate rewards C_star C_h o.1 q := hc
    rw [calendarStep, dite_eq_right hE, ite_eq_right hc]

/-- The actual produced last native tag, its own local renewal orientation,
and its own PRE-clear bit. No law or history invariant is supplied. -/
def calendarLastCallEvent (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) : Set (Sample k) :=
  {w | (observe k hk w).1 = s ∧ lastFlags k hk w = (bs, clear)}

local notation "lastEvent" => calendarLastCallEvent rate rewards C_star C_h control0 b0 u0 t0

/-- After s, the recursive restrictions are exactly the actual last-call
event, rather than an externally supplied nonuse or no-next premise. -/
theorem calendarResidualEvent_iff_lastCall (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : s.val < t0.val + 1 + k) (w : Sample k) :
    w ∈ event bs clear s k hk ↔ w ∈ lastEvent bs clear s k hk := by
  induction k with
  | zero =>
      change w ∈ (if t0.val < s.val then Set.univ else
        if t0 = s ∧ b0 = bs then {w | rootClear w = clear} else ∅) ↔
          t0 = s ∧ (b0, rootClear w) = (bs, clear)
      have hlt : ¬ t0.val < s.val := by omega
      rw [ite_eq_right hlt]
      by_cases hts : t0 = s
      · by_cases hb : b0 = bs
        · rw [ite_eq_left ⟨hts, hb⟩]
          constructor
          · intro hw; exact ⟨hts, Prod.ext hb hw⟩
          · rintro ⟨_, hf⟩; exact congrArg Prod.snd hf
        · rw [ite_eq_right (fun h => hb h.2)]
          exact iff_of_false (fun h => h) (fun h => hb (congrArg Prod.fst h.2))
      · simp only [hts, false_and, ite_false, Set.mem_empty_iff_false]
  | succ k ih =>
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      have hlt : ¬ t0.val + 1 + k < s.val := by omega
      change w.1 ∈ event bs clear s k (by omega) ∧ w.1 ∈ gate bs clear s k hk ↔
        (observe (k + 1) hk w).1 = s ∧ lastFlags (k + 1) hk w = (bs, clear)
      rw [calendarObservation_tag_succ, calendarLastFlags]
      by_cases heq : t0.val + 1 + k = s.val
      · have hqs : q = s := Fin.ext heq
        rw [calendarResidualEvent_before rate rewards C_star C_h control0 b0 u0 t0 bs clear s k
          (by omega) heq.le, calendarResidualGate, ite_eq_right hlt, ite_eq_left heq]
        cases hc : callFlag k hk w.1
        · have htag : (observe k (by omega) w.1).1 ≠ s := by
            intro he
            have hd := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0
              k (by omega) w.1).1
            change (observe k (by omega) w.1).1.val < t0.val + 1 + k at hd
            have := congrArg Fin.val he
            omega
          simp only [Set.mem_univ, Set.mem_ofPred_eq, hc, Bool.false_eq_true, false_and,
            true_and, ite_false, htag]
        · simp only [Set.mem_univ, Set.mem_ofPred_eq, hc, ite_true, true_and]
          change pending k hk w.1 = (bs, clear) ↔ q = s ∧ pending k hk w.1 = (bs, clear)
          exact ⟨fun h => ⟨hqs, h⟩, fun h => h.2⟩
      · have hprev : s.val < t0.val + 1 + k := by omega
        have hqne : q ≠ s := fun he => heq (congrArg Fin.val he)
        rw [calendarResidualGate, ite_eq_right hlt, ite_eq_right heq]
        cases hc : callFlag k hk w.1
        · simp only [Set.mem_ofPred_eq, hc, Bool.false_eq_true, ite_false, and_true]
          exact ih (by omega) hprev w.1
        · simp only [Set.mem_ofPred_eq, hc, ite_true]
          exact iff_of_false (fun h => Bool.noConfusion h.2) (fun h => hqne h.1)

theorem measurableSet_calendarLastCallEvent (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) : MeasurableSet (lastEvent bs clear s k hk) := by
  have ht : Measurable (fun w : Sample k => (observe k hk w).1) :=
    (measurable_sigma_elim (fun o : TaggedPrefix rate (calendarBoundary t0 k hk) => o.1)
      (fun _ => measurable_const)).comp
        (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)
  exact (measurableSet_eq_fun ht measurable_const).inter
    (measurableSet_eq_fun (measurable_calendarLastFlags rate rewards C_star C_h control0 b0 u0 t0 k hk)
      measurable_const)

/-- The last-call event itself is invariant under replacing the original
auxiliary tape, as derived from the literal physical selectors. -/
theorem calendarLastCallEvent_withAuxiliary (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : s.val < t0.val + 1 + k) (w : Sample k) (a : Auxiliary) :
    withAux k (w, a) ∈ lastEvent bs clear s k hk ↔ w ∈ lastEvent bs clear s k hk := by
  rw [← calendarResidualEvent_iff_lastCall rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs,
    ← calendarResidualEvent_iff_lastCall rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs]
  exact calendarResidualEvent_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w a

/-- An actual last-call event entails the native call and no later call
through the whole finite boundary, including its terminal value T. -/
theorem calendarLastCallEvent_origin (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) (hw : w ∈ lastEvent bs clear s k hk) :
    (callAt s (current k hk w)).isSome = true ∧
      NoCallBetween rate rewards C_star C_h s (calendarBoundary t0 k hk) (current k hk w) := by
  have ho := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk w).2
  simpa only [hw.1, calendarCurrentSource] using ho

/-- The requested produced-law block split, on a fixed actual last date and
its actual local orientation. `clear = true` retains PRE-clear calls;
`clear = false` includes the native stopped branch without changing its law. -/
theorem calendarLaw_lastCall_eraseBlock (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : s.val < t0.val + 1 + k) :
    ((law k hk).restrict (lastEvent bs clear s k hk)).map
        (fun w => (erase bs s k w, (refreshSplit bs s (original k w).1.2).2)) =
      (((law k hk).restrict (lastEvent bs clear s k hk)).map (erase bs s k)).prod
        (refreshAuxiliaryLaw bs s) := by
  have he : event bs clear s k hk = lastEvent bs clear s k hk :=
    Set.ext (calendarResidualEvent_iff_lastCall rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs)
  rw [← he]
  exact calendarLaw_restrict_eraseBlock rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk

/-- Refill recovers the entire restricted raw sample measure. In particular,
the theorem retains all original physical rows, arrays, J and full vectors;
it never divides by an event or endpoint mass. -/
theorem calendarLaw_lastCall_eq_restoreBlock (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : s.val < t0.val + 1 + k) :
    (law k hk).restrict (lastEvent bs clear s k hk) =
      ((((law k hk).restrict (lastEvent bs clear s k hk)).map (erase bs s k)).prod
        (refreshAuxiliaryLaw bs s)).map (fill bs s k) := by
  have h := congrArg (fun m => m.map (fill bs s k))
    (calendarLaw_lastCall_eraseBlock rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs)
  have hj : Measurable (fun w : Sample k =>
      (erase bs s k w, (refreshSplit bs s (original k w).1.2).2)) :=
    (measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k).prodMk
      ((refreshSplit bs s).measurable.snd.comp
        (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)
  rw [Measure.map_map (measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k) hj] at h
  have hid : (fill bs s k) ∘ (fun w : Sample k =>
      (erase bs s k w, (refreshSplit bs s (original k w).1.2).2)) = id :=
    funext (calendarFillBlock_erase rate rewards C_star C_h b0 u0 t0 bs s k)
  rwa [hid, Measure.map_id] at h

/-- The full current/archived observer is regenerated after refill and kept
jointly with the complete raw sample. Its own un-erased tape is not claimed
independent of the block it contains. -/
theorem calendarLaw_lastCall_joint_eq_restoreBlock (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hs : s.val < t0.val + 1 + k) :
    ((law k hk).restrict (lastEvent bs clear s k hk)).map (fun w => (w, observe k hk w)) =
      ((((law k hk).restrict (lastEvent bs clear s k hk)).map (erase bs s k)).prod
        (refreshAuxiliaryLaw bs s)).map
          (fun wx => (fill bs s k wx, observe k hk (fill bs s k wx))) := by
  have h := congrArg (fun m : Measure (Sample k) => m.map (fun w => (w, observe k hk w)))
    (calendarLaw_lastCall_eq_restoreBlock rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs)
  exact h.trans (Measure.map_map
    (measurable_id.prodMk
      (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk))
    (measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k))

end Bandits.Support.ReferenceGeneratedCalendarResidualBlock
