/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInstallationTransitionLaw

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Future auxiliary pairs in the original first-next assignment lifts

The two coordinates at a strictly later date are erased in the SAME full
auxiliary array. The laws below retain the entire original event source,
every remaining auxiliary coordinate, and the entire assignment vector.
All measures retain their original unnormalized event mass.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support

namespace Bandits.Support.ReferenceFirstNextLiftFutureAuxiliaryPairLaw

abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev AssignmentVector := AssignmentParameterFibreKernel.AssignmentVector

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤
local instance outcomeDiscrete :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⟨fun _ => trivial⟩

/-- Read both original scalar coordinates at the specified date. -/
def auxiliaryPair (q : Fin p.T) (a : AuxiliaryArray p) : Scalar × Scalar :=
  (a (q, 0), a (q, 1))

/-- Erase both labels by literal updates on the original full array. -/
def eraseAuxiliaryPair (q : Fin p.T) (a : AuxiliaryArray p) : AuxiliaryArray p :=
  Function.update (Function.update a (q, 0)
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero) (q, 1)
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero

/-- Reinsert a pair into that same array. -/
def fillAuxiliaryPair (q : Fin p.T) (a : AuxiliaryArray p)
    (x : Scalar × Scalar) : AuxiliaryArray p :=
  Function.update (Function.update a (q, 0) x.1) (q, 1) x.2

theorem measurable_auxiliaryPair (q : Fin p.T) :
    Measurable (auxiliaryPair q) :=
  (measurable_pi_apply (q, 0)).prodMk (measurable_pi_apply (q, 1))

theorem measurable_eraseAuxiliaryPair (q : Fin p.T) :
    Measurable (eraseAuxiliaryPair q) :=
  measurable_update_left.comp measurable_update_left

theorem measurable_fillAuxiliaryPair (q : Fin p.T) :
    Measurable (fun ax : AuxiliaryArray p × (Scalar × Scalar) =>
      fillAuxiliaryPair q ax.1 ax.2) := by
  exact measurable_update'.comp
    ((measurable_update'.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))

theorem eraseAuxiliaryPair_apply_other (q : Fin p.T) (a : AuxiliaryArray p)
    (i : Fin p.T × Fin 2) (h0 : i ≠ (q, 0)) (h1 : i ≠ (q, 1)) :
    eraseAuxiliaryPair q a i = a i := by
  simp only [eraseAuxiliaryPair, Function.update_of_ne h1, Function.update_of_ne h0]

theorem fillAuxiliaryPair_apply_other (q : Fin p.T) (a : AuxiliaryArray p)
    (x : Scalar × Scalar) (i : Fin p.T × Fin 2)
    (h0 : i ≠ (q, 0)) (h1 : i ≠ (q, 1)) :
    fillAuxiliaryPair q a x i = a i := by
  simp only [fillAuxiliaryPair, Function.update_of_ne h1, Function.update_of_ne h0]

theorem fillAuxiliaryPair_erase_pair (q : Fin p.T) (a : AuxiliaryArray p) :
    fillAuxiliaryPair q (eraseAuxiliaryPair q a) (auxiliaryPair q a) = a := by
  funext i
  by_cases h0 : i = (q, 0)
  · subst i
    simp [fillAuxiliaryPair, auxiliaryPair]
  by_cases h1 : i = (q, 1)
  · subst i
    simp [fillAuxiliaryPair, auxiliaryPair]
  rw [fillAuxiliaryPair_apply_other q _ _ i h0 h1,
    eraseAuxiliaryPair_apply_other q a i h0 h1]

/-- Retain the original source and whole vector while erasing the future pair. -/
def eraseLift {Z : Type*} (q : Fin p.T)
    (w : (Z × AuxiliaryArray p) × AssignmentVector p) :=
  ((w.1.1, eraseAuxiliaryPair q w.1.2), w.2)

/-- Restore the pair in the SAME full source/array/vector carrier. -/
def restoreLift {Z : Type*} (q : Fin p.T)
    (wx : ((Z × AuxiliaryArray p) × AssignmentVector p) × (Scalar × Scalar)) :=
  ((wx.1.1.1, fillAuxiliaryPair q wx.1.1.2 wx.2), wx.1.2)

theorem measurable_eraseLift {Z : Type*} [MeasurableSpace Z] (q : Fin p.T) :
    Measurable (eraseLift (Z := Z) q) :=
  ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_eraseAuxiliaryPair q).comp
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd

theorem measurable_restoreLift {Z : Type*} [MeasurableSpace Z] (q : Fin p.T) :
    Measurable (restoreLift (Z := Z) q) := by
  exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_fillAuxiliaryPair q).comp
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd))).prodMk (measurable_snd.comp measurable_fst)

theorem restoreLift_erase_pair {Z : Type*} (q : Fin p.T)
    (w : (Z × AuxiliaryArray p) × AssignmentVector p) :
    restoreLift q (eraseLift q w, auxiliaryPair q w.1.2) = w := by
  simp only [restoreLift, eraseLift, fillAuxiliaryPair_erase_pair]

theorem eraseLift_source {Z : Type*} (q : Fin p.T)
    (w : (Z × AuxiliaryArray p) × AssignmentVector p) :
    (eraseLift q w).1.1 = w.1.1 := rfl

theorem eraseLift_vector {Z : Type*} (q : Fin p.T)
    (w : (Z × AuxiliaryArray p) × AssignmentVector p) :
    (eraseLift q w).2 = w.2 := rfl

theorem restoreLift_source {Z : Type*} (q : Fin p.T)
    (wx : ((Z × AuxiliaryArray p) × AssignmentVector p) × (Scalar × Scalar)) :
    (restoreLift q wx).1.1 = wx.1.1.1 := rfl

theorem restoreLift_vector {Z : Type*} (q : Fin p.T)
    (wx : ((Z × AuxiliaryArray p) × AssignmentVector p) × (Scalar × Scalar)) :
    (restoreLift q wx).2 = wx.1.2 := rfl

section ActualKernels

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

private theorem collectionPath_auxiliary_ext
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (a b : AuxiliaryArray p)
    (hab : ∀ v : Fin p.T, v.val ≤ t.val → ∀ l : Fin 2, a (v, l) = b (v, l)) :
    ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z a =
      ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z b := by
  funext i
  have hdates := ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_dates
    rate rewards C_star C_h u t z.val z.property
  have hi := i.isLt
  have hstate :=
    ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h (u.val + i.val) (by omega) z.val a b
      (fun v hv l => hab v (by omega) l)
  have hl := ReferenceFirstNextInvocationJointLift.generatedIncoming_eq_path
    rate rewards C_star C_h u t z a i
  have hr := ReferenceFirstNextInvocationJointLift.generatedIncoming_eq_path
    rate rewards C_star C_h u t z b i
  exact Option.some.inj (hl.symm.trans ((congrArg Prod.fst hstate).trans hr))

/-- Actual nonrenewed fibre locality, including the original null-fibre rule. -/
theorem nonrenewedVectorKernel_auxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (a b : AuxiliaryArray p)
    (hab : ∀ v : Fin p.T, v.val ≤ t.val → ∀ l : Fin 2, a (v, l) = b (v, l)) :
    ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel
        rate rewards C_star C_h u t control0 (z, a) =
      ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel
        rate rewards C_star C_h u t control0 (z, b) := by
  have hp := collectionPath_auxiliary_ext rate rewards C_star C_h u t z a b hab
  change AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
      (ReferenceFirstNextInvocationJointLift.nextParameter
        rate rewards C_star C_h u t control0 z,
        some (ReferenceFirstLiveCollectionPathJoin.collectionPath
          rate rewards C_star C_h u t z a (Fin.last (t.val - u.val)))) =
    AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
      (ReferenceFirstNextInvocationJointLift.nextParameter
        rate rewards C_star C_h u t control0 z,
        some (ReferenceFirstLiveCollectionPathJoin.collectionPath
          rate rewards C_star C_h u t z b (Fin.last (t.val - u.val))))
  rw [hp]

/-- Actual renewal fibre locality: its analytical sample reads exactly `(t,1)`. -/
theorem renewalAssignmentFibreKernel_auxiliary_ext
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (a b : AuxiliaryArray p)
    (hab : ∀ v : Fin p.T, v.val ≤ t.val → ∀ l : Fin 2, a (v, l) = b (v, l)) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z, a) =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z, b) := by
  simp only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample, hab t le_rfl 1]

end ActualKernels

private theorem eraseAuxiliaryPair_past (t q : Fin p.T) (htq : t.val < q.val)
    (a : AuxiliaryArray p) (v : Fin p.T) (hvt : v.val ≤ t.val) (l : Fin 2) :
    a (v, l) = eraseAuxiliaryPair q a (v, l) := by
  symm
  apply eraseAuxiliaryPair_apply_other
  · intro h
    have he : v.val = q.val := congrArg (fun i : Fin p.T × Fin 2 => i.1.val) h
    omega
  · intro h
    have he : v.val = q.val := congrArg (fun i : Fin p.T × Fin 2 => i.1.val) h
    omega

/-- The real auxiliary Pi law, read as the zeroed full array and the two
original scalars. The finite subtype split is internal to this proof. -/
theorem auxiliaryUniformLaw_erase_pair (q : Fin p.T) :
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
        (fun a => (eraseAuxiliaryPair q a, auxiliaryPair q a)) =
      ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
        (eraseAuxiliaryPair q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  let S := {i : Fin p.T × Fin 2 // i.1 = q}
  let E := {i : Fin p.T × Fin 2 // ¬ i.1 = q}
  let μS : Measure (S → Scalar) := Measure.pi (fun _ => ContinuousControlSlice.scalarLaw)
  let μE : Measure (E → Scalar) := Measure.pi (fun _ => ContinuousControlSlice.scalarLaw)
  let split : AuxiliaryArray p ≃ᵐ (S → Scalar) × (E → Scalar) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ => Scalar)
      (fun i : Fin p.T × Fin 2 => i.1 = q)
  have hsplit : MeasurePreserving split
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) (μS.prod μE) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => ContinuousControlSlice.scalarLaw)
      (fun i : Fin p.T × Fin 2 => i.1 = q)
  let e : Fin 2 ≃ S :=
    { toFun := fun l => ⟨(q, l), rfl⟩
      invFun := fun i => i.val.2
      left_inv := fun _ => rfl
      right_inv := fun i => Subtype.ext (Prod.ext i.property.symm rfl) }
  let pick : (S → Scalar) → Scalar × Scalar :=
    fun s => (s ⟨(q, 0), rfl⟩, s ⟨(q, 1), rfl⟩)
  have hpick : MeasurePreserving pick μS
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
    exact (measurePreserving_piFinTwo (fun _ : Fin 2 => ContinuousControlSlice.scalarLaw)).comp
      (measurePreserving_piCongrLeft (fun _ : Fin 2 => ContinuousControlSlice.scalarLaw) e.symm)
  let put : (E → Scalar) → AuxiliaryArray p := fun a i =>
    if h : i.1 = q then ReferenceFirstLiveActualRefreshTestLaw.scalarZero else a ⟨i, h⟩
  have hput : Measurable put := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp only [put]
    split_ifs
    · exact measurable_const
    · exact measurable_pi_apply _
  have hput_eq (a : AuxiliaryArray p) : put (split a).2 = eraseAuxiliaryPair q a := by
    funext i
    rcases i with ⟨v, l⟩
    by_cases hv : v = q
    · subst v
      fin_cases l <;> simp [put, eraseAuxiliaryPair]
    · have h0 : (v, l) ≠ (q, 0) := fun h => hv (congrArg Prod.fst h)
      have h1 : (v, l) ≠ (q, 1) := fun h => hv (congrArg Prod.fst h)
      rw [eraseAuxiliaryPair_apply_other q a _ h0 h1]
      simp [put, hv, split, MeasurableEquiv.piEquivPiSubtypeProd]
  have hjoint :
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
          (fun a => (eraseAuxiliaryPair q a, auxiliaryPair q a)) =
        (μE.map put).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
    have hmaps := Measure.map_prod_map μE μS hput hpick.measurable
    rw [hpick.map_eq] at hmaps
    rw [hmaps, ← Measure.prod_swap (μ := μS) (ν := μE),
      ← hsplit.map_eq, Measure.map_map measurable_swap split.measurable,
      Measure.map_map (hput.prodMap hpick.measurable) (measurable_swap.comp split.measurable)]
    congr 1
    funext a
    exact Prod.ext (hput_eq a).symm rfl
  have hmarg := congrArg (fun μ => μ.map Prod.fst) hjoint
  rw [Measure.map_map measurable_fst
    ((measurable_eraseAuxiliaryPair q).prodMk (measurable_auxiliaryPair q)),
    (measurePreserving_fst (μ := μE.map put)
      (ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map_eq] at hmarg
  change (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
    (eraseAuxiliaryPair q) = μE.map put at hmarg
  rw [hmarg]
  exact hjoint

private theorem source_auxiliary_pair {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (q : Fin p.T) :
    (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (fun za => ((za.1, eraseAuxiliaryPair q za.2), auxiliaryPair q za.2)) =
      ((μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (fun za => (za.1, eraseAuxiliaryPair q za.2))).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  let α := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw
  have hα := auxiliaryUniformLaw_erase_pair (p := p) q
  have hmap := Measure.map_prod_map μ α measurable_id
    ((measurable_eraseAuxiliaryPair q).prodMk (measurable_auxiliaryPair q))
  rw [Measure.map_id, hα] at hmap
  have he := Measure.map_prod_map μ α measurable_id (measurable_eraseAuxiliaryPair q)
  rw [Measure.map_id] at he
  change μ.prod (α.map (eraseAuxiliaryPair q)) =
    (μ.prod α).map (fun za => (za.1, eraseAuxiliaryPair q za.2)) at he
  rw [← he]
  have hassoc := (measurePreserving_prodAssoc μ (α.map (eraseAuxiliaryPair q)) ν).symm.map_eq
  rw [hmap, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap
      ((measurable_eraseAuxiliaryPair q).prodMk (measurable_auxiliaryPair q)))] at hassoc
  exact hassoc

/- The following finite-measure calculation transports a proved base split
through a kernel which literally ignores the erased coordinates. It is used
below only after proving nonuse for each actual assignment fibre kernel. -/
private theorem compProd_pair_factorization
    {B X V : Type*} [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (μ : Measure B) [IsFiniteMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : ProbabilityTheory.Kernel B V) [ProbabilityTheory.IsMarkovKernel κ]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : μ.map (fun b => (e b, x b)) = (μ.map e).prod ν)
    (hκ : ∀ b, κ b = κ (e b)) :
    (μ.compProd κ).map (fun w => ((e w.1, w.2), x w.1)) =
      ((μ.compProd κ).map (fun w => (e w.1, w.2))).prod ν := by
  have hE : Measurable (fun w : B × V => (e w.1, w.2)) :=
    (he.comp measurable_fst).prodMk measurable_snd
  have hJ : Measurable (fun w : B × V => ((e w.1, w.2), x w.1)) :=
    hE.prodMk (hx.comp measurable_fst)
  have hpush : (μ.compProd κ).map (fun w => (e w.1, w.2)) =
      (μ.map e).compProd κ := by
    ext s hs
    rw [Measure.map_apply hE hs, Measure.compProd_apply (hs.preimage hE),
      Measure.compProd_apply hs,
      lintegral_map (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs) he]
    apply lintegral_congr
    intro b
    change κ b (Prod.mk (e b) ⁻¹' s) = κ (e b) (Prod.mk (e b) ⁻¹' s)
    rw [hκ b]
  rw [hpush]
  apply Measure.ext_prod
  intro s r hs hr
  let F : B → ℝ≥0∞ := fun b => κ b (Prod.mk b ⁻¹' s)
  have hF : Measurable F := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs
  let f : B × X → ℝ≥0∞ := fun bx => F bx.1 * r.indicator (fun _ => 1) bx.2
  have hf : Measurable f :=
    (hF.comp measurable_fst).mul ((measurable_const.indicator hr).comp measurable_snd)
  rw [Measure.map_apply hJ (hs.prod hr),
    Measure.compProd_apply ((hs.prod hr).preimage hJ),
    Measure.prod_prod, Measure.compProd_apply hs]
  calc
    (∫⁻ b, κ b (Prod.mk b ⁻¹' ((fun w : B × V =>
        ((e w.1, w.2), x w.1)) ⁻¹' (s ×ˢ r))) ∂μ) =
        ∫⁻ b, f (e b, x b) ∂μ := by
      apply lintegral_congr
      intro b
      change κ b {v | (e b, v) ∈ s ∧ x b ∈ r} =
        F (e b) * r.indicator (fun _ => 1) (x b)
      by_cases hb : x b ∈ r
      · simp only [hb, and_true, Set.indicator_of_mem, mul_one]
        exact congrArg (fun m : Measure V => m (Prod.mk (e b) ⁻¹' s)) (hκ b)
      · simp only [hb, and_false, Set.ofPred_false, measure_empty,
          Set.indicator_of_notMem hb, mul_zero]
    _ = ∫⁻ bx, f bx ∂μ.map (fun b => (e b, x b)) :=
      (lintegral_map hf (he.prodMk hx)).symm
    _ = ∫⁻ bx, f bx ∂(μ.map e).prod ν := by rw [hbase]
    _ = (∫⁻ b, F b ∂μ.map e) * ν r := by
      rw [lintegral_prod_mul hF.aemeasurable (measurable_const.indicator hr).aemeasurable,
        lintegral_indicator_const hr, one_mul]

private theorem lift_pair_factorization {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (κ : ProbabilityTheory.Kernel (Z × AuxiliaryArray p) (AssignmentVector p))
    [ProbabilityTheory.IsMarkovKernel κ] (q : Fin p.T)
    (hκ : ∀ za, κ za = κ (za.1, eraseAuxiliaryPair q za.2)) :
    ((μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd κ).map
        (fun w => (eraseLift q w, auxiliaryPair q w.1.2)) =
      (((μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd κ).map
        (eraseLift q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  exact compProd_pair_factorization _ _ κ
    (fun za => (za.1, eraseAuxiliaryPair q za.2))
    (measurable_fst.prodMk ((measurable_eraseAuxiliaryPair q).comp measurable_snd))
    (fun za => auxiliaryPair q za.2) ((measurable_auxiliaryPair q).comp measurable_snd)
    (source_auxiliary_pair μ q) hκ

private theorem measure_restore_pair {Z : Type*} [MeasurableSpace Z]
    (Λ : Measure ((Z × AuxiliaryArray p) × AssignmentVector p)) (q : Fin p.T)
    (hjoint : Λ.map (fun w => (eraseLift q w, auxiliaryPair q w.1.2)) =
      (Λ.map (eraseLift q)).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) :
    Λ = ((Λ.map (eraseLift q)).prod
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
        (restoreLift q) := by
  have h := congrArg (fun μ => μ.map (restoreLift (Z := Z) q)) hjoint
  have hj : Measurable (fun w : (Z × AuxiliaryArray p) × AssignmentVector p =>
      (eraseLift q w, auxiliaryPair q w.1.2)) :=
    (measurable_eraseLift q).prodMk
      ((measurable_auxiliaryPair q).comp (measurable_snd.comp measurable_fst))
  rw [Measure.map_map (measurable_restoreLift q) hj] at h
  have hid : restoreLift q ∘ (fun w : (Z × AuxiliaryArray p) × AssignmentVector p =>
      (eraseLift q w, auxiliaryPair q w.1.2)) = id :=
    funext (restoreLift_erase_pair q)
  rw [hid, Measure.map_id] at h
  exact h

section OriginalLifts

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t q : Fin p.T)

/-- Joint independence of BOTH future scalars from the entire zeroed
nonrenewed lift, under its actual fibre-weighted unnormalized law. -/
theorem nonrenewedLiftLaw_erase_pair
    (htq : t.val < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    (ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
        rate rewards C_star C_h u t control0).map
        (fun w => (eraseLift q w, auxiliaryPair q w.1.2)) =
      ((ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
        rate rewards C_star C_h u t control0).map (eraseLift q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  apply lift_pair_factorization
    (ReferenceFirstLiveCollectionPathJoin.eventSourceLaw rate rewards C_star C_h u t)
    (ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel
      rate rewards C_star C_h u t control0) q
  intro za
  exact nonrenewedVectorKernel_auxiliary_ext rate rewards C_star C_h u t control0
    za.1 za.2 (eraseAuxiliaryPair q za.2) (eraseAuxiliaryPair_past t q htq za.2)

/-- Restore the SAME two scalars to recover the original nonrenewed lift. -/
theorem nonrenewedLiftLaw_eq_restore_pair
    (htq : t.val < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
        rate rewards C_star C_h u t control0 =
      (((ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
        rate rewards C_star C_h u t control0).map (eraseLift q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
            (restoreLift q) :=
  measure_restore_pair _ q
    (nonrenewedLiftLaw_erase_pair rate rewards C_star C_h u t q htq control0)

/-- Joint independence of BOTH future scalars under the ORIGINAL renewal
lift, retaining its whole source, other auxiliary entries, and full vector. -/
theorem renewalLiftLaw_erase_pair (htq : t.val < q.val) :
    (ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map
        (fun w => (eraseLift q w, auxiliaryPair q w.1.2)) =
      ((ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map (eraseLift q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  apply lift_pair_factorization
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
      rate rewards C_star C_h u t) q
  intro za
  exact renewalAssignmentFibreKernel_auxiliary_ext rate rewards C_star C_h u t
    za.1 za.2 (eraseAuxiliaryPair q za.2) (eraseAuxiliaryPair_past t q htq za.2)

/-- Restoration gives the ORIGINAL renewal lift, with its original mass. -/
theorem renewalLiftLaw_eq_restore_pair (htq : t.val < q.val) :
    ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t =
      (((ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map (eraseLift q)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
            (restoreLift q) :=
  measure_restore_pair _ q
    (renewalLiftLaw_erase_pair rate rewards C_star C_h u t q htq)

end OriginalLifts

end Bandits.Support.ReferenceFirstNextLiftFutureAuxiliaryPairLaw

end
