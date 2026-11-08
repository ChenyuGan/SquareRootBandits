/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport

import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The current COLLECTION proposal in the original killed prefix law

Sources: ZIP4 `04_slow_fast_learner.tex:329-367` and
`06_interruptions.tex:391-426`.

Erase only the current label-zero scalar in the existing observer. Its physical
source prefix, every other label-zero entry, and complete logical past remain
literal. The original auxiliary Pi law then factors this scalar jointly from
that erased observer, both raw and after original fixed-ID localization.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell)
open ReferenceFirstLiveCalendarMarkedTransition
  (Observation Source AuxiliaryArray labelZero measurable_labelZero enlargedSourceLaw)
open ReferenceFirstCollectionLogicalPrefixExtension
  (extendedPast extendedObservation measurable_extendedObservation
    extendedPrefixStateAux extendedPrefixStateAux_auxiliary_ext
    NoCallBefore betaPre betaPre_mass_le_one
    extendedObservation_map_restrict_eq_betaPre)
open ReferenceFirstLiveActualRefreshTestLaw (scalarZero)
open ReferenceGeneratedCalendarEpisodePrefixRecombination (fixedIDBetaPre)
open ContinuousControlSlice (Scalar scalarLaw)

namespace Bandits.Support.ReferenceGeneratedCalendarPrefixProposalErasure

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Replace exactly the current label-zero entry by the existing zero scalar. -/
def eraseProposal (q : Fin p.T) (o : Observation p rate) : Observation p rate :=
  (o.1, (Function.update o.2.1 q scalarZero, o.2.2))

/-- The actual current COLLECTION proposal scalar in the existing observer. -/
def currentProposal (q : Fin p.T) (o : Observation p rate) : Scalar := o.2.1 q

/-- Reinsert a scalar into that same observer, preserving its other entries. -/
def refillProposal (q : Fin p.T) (v : Observation p rate × Scalar) : Observation p rate :=
  (v.1.1, (Function.update v.1.2.1 q v.2, v.1.2.2))

theorem measurable_eraseProposal (q : Fin p.T) :
    Measurable (eraseProposal (rate := rate) q) :=
  measurable_fst.prodMk
    ((measurable_update_left.comp measurable_snd.fst).prodMk measurable_snd.snd)

theorem measurable_currentProposal (q : Fin p.T) :
    Measurable (currentProposal (rate := rate) q) :=
  (measurable_pi_apply q).comp measurable_snd.fst

theorem measurable_refillProposal (q : Fin p.T) :
    Measurable (refillProposal (rate := rate) q) :=
  measurable_fst.fst.prodMk
    ((measurable_update'.comp (measurable_fst.snd.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd.snd)

theorem eraseProposal_source (q : Fin p.T) (o : Observation p rate) :
    (eraseProposal q o).1 = o.1 := rfl

theorem eraseProposal_past (q : Fin p.T) (o : Observation p rate) :
    (eraseProposal q o).2.2 = o.2.2 := rfl

theorem eraseProposal_other (q v : Fin p.T) (hv : v ≠ q) (o : Observation p rate) :
    (eraseProposal q o).2.1 v = o.2.1 v := by
  simp only [eraseProposal, Function.update_of_ne hv]

theorem currentProposal_eraseProposal (q : Fin p.T) (o : Observation p rate) :
    currentProposal q (eraseProposal q o) = scalarZero := by
  simp only [currentProposal, eraseProposal, Function.update_self]

theorem refillProposal_source (q : Fin p.T) (v : Observation p rate × Scalar) :
    (refillProposal q v).1 = v.1.1 := rfl

theorem refillProposal_past (q : Fin p.T) (v : Observation p rate × Scalar) :
    (refillProposal q v).2.2 = v.1.2.2 := rfl

theorem refillProposal_other (q v : Fin p.T) (hv : v ≠ q)
    (w : Observation p rate × Scalar) :
    (refillProposal q w).2.1 v = w.1.2.1 v := by
  simp only [refillProposal, Function.update_of_ne hv]

theorem currentProposal_refillProposal (q : Fin p.T) (v : Observation p rate × Scalar) :
    currentProposal q (refillProposal q v) = v.2 := by
  simp only [currentProposal, refillProposal, Function.update_self]

/-- Pointwise reconstruction of the entire original observer. -/
theorem refillProposal_erase_current (q : Fin p.T) (o : Observation p rate) :
    refillProposal q (eraseProposal q o, currentProposal q o) = o := by
  change (o.1, (Function.update (Function.update o.2.1 q scalarZero) q (o.2.1 q), o.2.2)) = o
  rw [Function.update_idem, Function.update_eq_self]

variable (rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- Every operation strictly before `q` ignores the current proposal coordinate. -/
theorem extendedPast_update_currentProposal (q : Fin p.T) (z : Source p)
    (a : AuxiliaryArray p) (x : Scalar) :
    extendedPast rate rewards C_star C_h q.castSucc (z, Function.update a (q, 0) x) =
      extendedPast rate rewards C_star C_h q.castSucc (z, a) := by
  apply congrArg Prod.snd
  apply extendedPrefixStateAux_auxiliary_ext
  intro t ht l
  apply Function.update_of_ne
  intro h
  have htq : t = q := congrArg Prod.fst h
  subst t
  exact Nat.lt_irrefl q.val ht

private theorem labelZero_update (q : Fin p.T) (a : AuxiliaryArray p) (x : Scalar) :
    labelZero (Function.update a (q, 0) x) = Function.update (labelZero a) q x := by
  funext t
  by_cases ht : t = q
  · subst t
    simp only [labelZero, Function.update_self]
  · have hpair : (t, (0 : Fin 2)) ≠ (q, 0) := fun h => ht (congrArg Prod.fst h)
    simp only [labelZero, Function.update_of_ne ht, Function.update_of_ne hpair]

/-- Erasure is exactly evaluation of the original observer after zeroing `(q,0)`. -/
theorem extendedObservation_eraseProposal (q : Fin p.T) (za : Source p × AuxiliaryArray p) :
    eraseProposal q (extendedObservation rate rewards C_star C_h control0 q.castSucc za) =
      extendedObservation rate rewards C_star C_h control0 q.castSucc
        (za.1, Function.update za.2 (q, 0) scalarZero) := by
  unfold eraseProposal extendedObservation
  rw [labelZero_update, extendedPast_update_currentProposal rate rewards C_star C_h]

/-- Arbitrary refill also gives the literal original observer with that one coordinate updated. -/
theorem extendedObservation_refillProposal (q : Fin p.T) (za : Source p × AuxiliaryArray p)
    (x : Scalar) :
    refillProposal q (extendedObservation rate rewards C_star C_h control0 q.castSucc za, x) =
      extendedObservation rate rewards C_star C_h control0 q.castSucc
        (za.1, Function.update za.2 (q, 0) x) := by
  unfold refillProposal extendedObservation
  rw [labelZero_update, extendedPast_update_currentProposal rate rewards C_star C_h]

omit rate rewards C_star C_h control0 in
private theorem auxiliary_currentProposal_product (q : Fin p.T) :
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
        (fun a => (Function.update a (q, 0) scalarZero, a (q, 0))) =
      ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
        (fun a => Function.update a (q, 0) scalarZero)).prod scalarLaw := by
  let k : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p := (q, 0)
  let S := {i : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // i = k}
  let E := {i : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // i ≠ k}
  let : Unique S := ⟨⟨⟨k, rfl⟩⟩, fun i => Subtype.ext i.property⟩
  let : Fintype S := Subtype.fintype (fun i => i = k)
  let μe : Measure (E → Scalar) := Measure.pi (fun _ => scalarLaw)
  let e : AuxiliaryArray p ≃ᵐ ((E → Scalar) × Scalar) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => Scalar) (fun i => i = k)).trans
      (((MeasurableEquiv.piUnique (fun _ : S => Scalar)).prodCongr
        (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodComm)
  have he (a : AuxiliaryArray p) : e a = ((fun i : E => a i.val), a k) := rfl
  have hsplit : MeasurePreserving e
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) (μe.prod scalarLaw) := by
    have hpi := measurePreserving_piEquivPiSubtypeProd
      (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => scalarLaw) (fun i => i = k)
    have hsingle := measurePreserving_piUnique (fun _ : S => scalarLaw)
    exact (Measure.measurePreserving_swap (μ := scalarLaw) (ν := μe)).comp
      ((hsingle.prod (MeasurePreserving.id μe)).comp hpi)
  let g : (E → Scalar) → AuxiliaryArray p :=
    fun a i => if h : i = k then scalarZero else a ⟨i, h⟩
  have hg : Measurable g := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = k
    · simpa only [g, hi, dite_true] using
        (measurable_const : Measurable (fun _ : E → Scalar => scalarZero))
    · simpa only [g, hi, dite_false] using (measurable_pi_apply (⟨i, hi⟩ : E))
  have hga (a : AuxiliaryArray p) : g (e a).1 = Function.update a k scalarZero := by
    funext i
    rw [he]
    by_cases hi : i = k
    · subst i
      simp only [g, dite_true, Function.update_self]
    · simp only [g, hi, dite_false, Function.update_of_ne hi]
  have hfull := ((show MeasurePreserving g μe (μe.map g) from ⟨hg, rfl⟩).prod
    (MeasurePreserving.id scalarLaw)).comp hsplit
  have hjoint : (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (fun a => (Function.update a k scalarZero, a k)) = (μe.map g).prod scalarLaw := by
    have h := hfull.map_eq
    change (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map
      (fun a => (g (e a).1, (e a).2)) = _ at h
    have heq : (fun a : AuxiliaryArray p => (g (e a).1, (e a).2)) =
        (fun a => (Function.update a k scalarZero, a k)) := by
      funext a
      apply Prod.ext
      · exact hga a
      · change (e a).2 = a k
        rw [he]
    rw [heq] at h
    exact h
  have hmarg := congrArg Measure.fst hjoint
  rw [Measure.fst_map_prodMk measurable_update_left (measurable_pi_apply k),
    Measure.fst_prod] at hmarg
  rw [hmarg]
  exact hjoint

private theorem extendedObservation_source_product (q : Fin p.T) (μ : Measure (Source p)) [SFinite μ] :
    (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (fun za => (eraseProposal q (extendedObservation rate rewards C_star C_h control0 q.castSucc za),
          currentProposal q (extendedObservation rate rewards C_star C_h control0 q.castSucc za))) =
      ((μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (fun za => eraseProposal q
          (extendedObservation rate rewards C_star C_h control0 q.castSucc za))).prod scalarLaw := by
  let α := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let u : AuxiliaryArray p → AuxiliaryArray p := fun a => Function.update a (q, 0) scalarZero
  have hu : Measurable u := measurable_update_left
  have hsplit : MeasurePreserving (fun a : AuxiliaryArray p => (u a, a (q, 0))) α
      ((α.map u).prod scalarLaw) :=
    ⟨hu.prodMk (measurable_pi_apply (q, 0)), auxiliary_currentProposal_product q⟩
  let O := extendedObservation rate rewards C_star C_h control0 q.castSucc
  have hO : Measurable O := measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc
  have hobs : MeasurePreserving O (μ.prod (α.map u)) ((μ.prod (α.map u)).map O) := ⟨hO, rfl⟩
  have hfull := (hobs.prod (MeasurePreserving.id scalarLaw)).comp
    ((measurePreserving_prodAssoc μ (α.map u) scalarLaw).symm.comp
      ((MeasurePreserving.id μ).prod hsplit))
  have hjoint : (μ.prod α).map (fun za => (eraseProposal q (O za), currentProposal q (O za))) =
      ((μ.prod (α.map u)).map O).prod scalarLaw := by
    have h := hfull.map_eq
    change (μ.prod α).map (fun za => (O (za.1, u za.2), za.2 (q, 0))) = _ at h
    have heq : (fun za : Source p × AuxiliaryArray p =>
        (O (za.1, u za.2), za.2 (q, 0))) =
        (fun za => (eraseProposal q (O za), currentProposal q (O za))) := by
      funext za
      exact Prod.ext (extendedObservation_eraseProposal rate rewards C_star C_h control0 q za).symm rfl
    rw [heq] at h
    exact h
  have hmarg := congrArg Measure.fst hjoint
  rw [Measure.fst_map_prodMk
    (X := fun za => eraseProposal q (O za)) (Y := fun za => currentProposal q (O za))
    ((measurable_eraseProposal q).comp hO)
    ((measurable_currentProposal q).comp hO), Measure.fst_prod] at hmarg
  rw [hmarg]
  exact hjoint

/-- The joint product law for the raw killed observer, including null no-call mass. -/
theorem betaPre_currentProposal_product (q : Fin p.T) :
    (betaPre rate rewards C_star C_h control0 q.castSucc).map
        (fun o => (eraseProposal q o, currentProposal q o)) =
      ((betaPre rate rewards C_star C_h control0 q.castSucc).map (eraseProposal q)).prod scalarLaw := by
  let A : Set (Source p) := {z | NoCallBefore rate rewards C_star C_h q.castSucc z}
  have hrect : {za : Source p × AuxiliaryArray p | NoCallBefore rate rewards C_star C_h q.castSucc za.1} =
      A ×ˢ Set.univ := by
    ext za
    change NoCallBefore rate rewards C_star C_h q.castSucc za.1 ↔
      NoCallBefore rate rewards C_star C_h q.castSucc za.1 ∧ True
    exact ⟨fun h => ⟨h, trivial⟩, And.left⟩
  rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 q.castSucc,
    Measure.map_map ((measurable_eraseProposal q).prodMk (measurable_currentProposal q))
      (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc),
    Measure.map_map (measurable_eraseProposal q)
      (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc)]
  change ((enlargedSourceLaw p).restrict _).map _ = (((enlargedSourceLaw p).restrict _).map _).prod scalarLaw
  rw [hrect]
  change (((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).restrict (A ×ˢ Set.univ)).map _ =
    ((((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).restrict (A ×ˢ Set.univ)).map _).prod scalarLaw
  rw [← Measure.restrict_prod_eq_prod_univ]
  exact extendedObservation_source_product rate rewards C_star C_h control0 q
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict A)

/-- Localization uses only the original ID atom; no calendar component is normalized. -/
theorem fixedIDBetaPre_currentProposal_product (ids : CompletePublicTable.IDArray p) (q : Fin p.T) :
    (fixedIDBetaPre rate rewards C_star C_h control0 ids q.castSucc).map
        (fun o => (eraseProposal q o, currentProposal q o)) =
      ((fixedIDBetaPre rate rewards C_star C_h control0 ids q.castSucc).map (eraseProposal q)).prod scalarLaw := by
  let : IsFiniteMeasure (betaPre rate rewards C_star C_h control0 q.castSucc) :=
    ⟨(betaPre_mass_le_one rate rewards C_star C_h control0 q.castSucc).trans_lt ENNReal.one_lt_top⟩
  let D : Set (Observation p rate) :=
    {o | o.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  have hD : MeasurableSet D :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst
  let j := fun o : Observation p rate => (eraseProposal q o, currentProposal q o)
  have hj : Measurable j := (measurable_eraseProposal q).prodMk (measurable_currentProposal q)
  have hpre : j ⁻¹' (D ×ˢ Set.univ) = D := by
    ext o
    change (o ∈ D ∧ True) ↔ o ∈ D
    exact ⟨And.left, fun h => ⟨h, trivial⟩⟩
  have herase : eraseProposal q ⁻¹' D = D := rfl
  unfold fixedIDBetaPre
  rw [Measure.map_smul _ hj.aemeasurable,
    Measure.map_smul _ (measurable_eraseProposal q).aemeasurable]
  change (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
      (((betaPre rate rewards C_star C_h control0 q.castSucc).restrict D).map j) =
    ((CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
      (((betaPre rate rewards C_star C_h control0 q.castSucc).restrict D).map (eraseProposal q))).prod scalarLaw
  conv_lhs => rw [← hpre, ← Measure.restrict_map hj (hD.prod MeasurableSet.univ)]
  change (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
      (((betaPre rate rewards C_star C_h control0 q.castSucc).map j).restrict (D ×ˢ Set.univ)) = _
  rw [betaPre_currentProposal_product rate rewards C_star C_h control0 q,
    ← Measure.restrict_prod_eq_prod_univ, ← Measure.prod_smul_left,
    Measure.restrict_map (measurable_eraseProposal q) hD, herase]

/-- Exact chronological joint law, raw or in any original fixed-ID experiment. -/
theorem betaPre_currentProposal_erasure_product (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) :
    (ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (fun o => (eraseProposal q o, currentProposal q o)) =
      ((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
          (eraseProposal q)).prod scalarLaw := by
  cases ids with
  | none => exact betaPre_currentProposal_product rate rewards C_star C_h control0 q
  | some id => exact fixedIDBetaPre_currentProposal_product rate rewards C_star C_h control0 id q

/-- Arbitrary measurable nonnegative joint tests; no integrability premise is needed. -/
theorem betaPre_currentProposal_erasure_test (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (Phi : Observation p rate × Scalar → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ o, Phi (eraseProposal q o, currentProposal q o)
      ∂ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)) =
      ∫⁻ v, Phi v ∂((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
          (eraseProposal q)).prod scalarLaw := by
  rw [← lintegral_map hPhi ((measurable_eraseProposal q).prodMk (measurable_currentProposal q)),
    betaPre_currentProposal_erasure_product rate rewards C_star C_h control0 ids q]

end Bandits.Support.ReferenceGeneratedCalendarPrefixProposalErasure
