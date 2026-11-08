/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateRoundStreams
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Adaptive private round draws

For one calendar round, this module splits the existing player-round scalar
array into strict past, current, and future coordinates.  The past view also
contains the already existing base private coordinates and separate target
stream.  It is not the physical history: no observations, feedback, or
causality are asserted here.

The resulting product law supports a measurable decision from that past view
which selects, separately for each player, either the existing full-arm draw
or the existing draw avoiding one arm.  The theorem gives the complete joint
action-vector atom kernel on every measurable past event.  It does not prove
that a physical protocol's decisions factor through this view, supply current
feedback, identify physical history, or construct the block-start held-arm
choice.

Sources: `sources/zip4/manuscript/07_public_setup.tex:52-95` and
`sources/zip4/manuscript/appendix_b_communication.tex:302-314,377-445`.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.FiniteBanditModel

namespace Bandits.Support.PrivateRoundFreshness

/-- The literal scalar carrier used by the already integrated private streams. -/
abbrev Scalar := BootstrapPrivateRoundStreams.Scalar

/-- The decision alphabet is given its canonical finite discrete measurable
space. -/
instance optionArmMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Fin p.K)) := ⊤

/-- Player-round labels strictly before the selected calendar round. -/
abbrev PastRoundLabel (p : Parameters) (t : Fin p.T) :=
  {label : {entry : PlayerRoundLabel p // entry.2 ≤ t} // label.1.2 < t}

/-- Labels at or before the selected round, used for the first coordinate
partition. -/
abbrev PastOrCurrentRoundLabel (p : Parameters) (t : Fin p.T) :=
  {label : PlayerRoundLabel p // label.2 ≤ t}

/-- The time-`t` labels inside the at-or-before partition that are not strict
past labels. -/
abbrev CurrentPastRoundLabel (p : Parameters) (t : Fin p.T) :=
  {label : PastOrCurrentRoundLabel p t // ¬ label.1.2 < t}

/-- Player-round labels strictly after the selected calendar round. -/
abbrev FutureRoundLabel (p : Parameters) (t : Fin p.T) :=
  {label : PlayerRoundLabel p // ¬ label.2 ≤ t}

theorem futureRoundLabel_time_gt (p : Parameters) (t : Fin p.T)
    (label : FutureRoundLabel p t) : t < label.1.2 :=
  lt_of_not_ge label.2

/-- Strict-past scalar coordinates for one calendar round. -/
abbrev PastRoundScalars (p : Parameters) (t : Fin p.T) :=
  PastRoundLabel p t → Scalar

/-- Forget the redundant at-or-before proof and recover the original
player-round label represented by a strict-past coordinate. -/
@[expose] def pastRoundLabelUnderlying (p : Parameters) (t : Fin p.T)
    (label : PastRoundLabel p t) : PlayerRoundLabel p := label.1.1

theorem pastRoundLabel_time_lt (p : Parameters) (t : Fin p.T)
    (label : PastRoundLabel p t) : (pastRoundLabelUnderlying p t label).2 < t :=
  label.2

/-- The one current scalar coordinate for each player. -/
abbrev CurrentRoundScalars (p : Parameters) := Fin p.m → Scalar

/-- Strict-future scalar coordinates for one calendar round. -/
abbrev FutureRoundScalars (p : Parameters) (t : Fin p.T) :=
  FutureRoundLabel p t → Scalar

/-- Information permitted to select the current draw branches.  The accepted
base private coordinates and target stream are separate independent factors;
the only player-round scalars present are those with time strictly less than
`t`.  This is not a physical-history type. -/
abbrev PastView (p : Parameters) (t : Fin p.T) :=
  PrivateCoordinates p × (PastRoundScalars p t × CoordinatorTargetScalars p)

/-- Literal product law of the strict-past scalar coordinates. -/
@[expose] noncomputable def pastRoundScalarLaw (p : Parameters) (t : Fin p.T) :
    Measure (PastRoundScalars p t) :=
  Measure.pi (fun _ : PastRoundLabel p t => ContinuousCategorical.uniform)

instance pastRoundScalarLaw_probability (p : Parameters) (t : Fin p.T) :
    IsProbabilityMeasure (pastRoundScalarLaw p t) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : PastRoundLabel p t => ContinuousCategorical.uniform))
  infer_instance

/-- Literal product law of the current player-indexed scalar coordinates. -/
@[expose] noncomputable def currentRoundScalarLaw (p : Parameters) :
    Measure (CurrentRoundScalars p) :=
  Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform)

instance currentRoundScalarLaw_probability (p : Parameters) :
    IsProbabilityMeasure (currentRoundScalarLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform))
  infer_instance

/-- Literal product law of the strict-future scalar coordinates. -/
@[expose] noncomputable def futureRoundScalarLaw (p : Parameters) (t : Fin p.T) :
    Measure (FutureRoundScalars p t) :=
  Measure.pi (fun _ : FutureRoundLabel p t => ContinuousCategorical.uniform)

instance futureRoundScalarLaw_probability (p : Parameters) (t : Fin p.T) :
    IsProbabilityMeasure (futureRoundScalarLaw p t) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : FutureRoundLabel p t => ContinuousCategorical.uniform))
  infer_instance

/-- Product law for the permitted past view, retaining its two independent
external private factors explicitly. -/
@[expose] noncomputable def pastViewLaw (p : Parameters) (t : Fin p.T) :
    Measure (PastView p t) :=
  (PrivateSourceStreams.privateCoordinatesLaw p).prod
    ((pastRoundScalarLaw p t).prod (coordinatorTargetScalarLaw p))

instance pastViewLaw_probability (p : Parameters) (t : Fin p.T) :
    IsProbabilityMeasure (pastViewLaw p t) := by
  dsimp [pastViewLaw]
  infer_instance

/-- Reindex the current-time scalar labels by player.  The proof records the
time equality and uses the finite-coordinate equivalence explicitly. -/
@[expose] def currentPastRoundLabelEquiv (p : Parameters) (t : Fin p.T) :
    Fin p.m ≃ CurrentPastRoundLabel p t where
  toFun i := ⟨⟨(i, t), by simp⟩, by simp⟩
  invFun label := label.val.val.1
  left_inv _ := rfl
  right_inv label := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact le_antisymm (le_of_not_gt label.property) label.val.property

/-- Explicit measurable equivalence splitting the player-round array into
strict past, one current scalar per player, and strict future. -/
@[expose] noncomputable def playerRoundScalarSplitEquiv (p : Parameters)
    (t : Fin p.T) : MeasurableEquiv (PlayerRoundScalars p)
      (PastRoundScalars p t ×
        (CurrentRoundScalars p × FutureRoundScalars p t)) := by
  let ePastCurrent : MeasurableEquiv
      (PastOrCurrentRoundLabel p t → Scalar)
      (PastRoundScalars p t × (CurrentPastRoundLabel p t → Scalar)) :=
    MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PastOrCurrentRoundLabel p t => Scalar)
    (fun label => label.1.2 < t)
  let eRound : MeasurableEquiv (PlayerRoundScalars p)
      ((PastOrCurrentRoundLabel p t → Scalar) × FutureRoundScalars p t) :=
    MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => Scalar)
    (fun label => label.2 ≤ t)
  let eCurrent : MeasurableEquiv (CurrentPastRoundLabel p t → Scalar)
      (CurrentRoundScalars p) :=
    MeasurableEquiv.piCongrLeft
    (fun _ : Fin p.m => Scalar) (currentPastRoundLabelEquiv p t).symm
  exact eRound.trans <|
    (MeasurableEquiv.prodCongr ePastCurrent (MeasurableEquiv.refl _)).trans <|
      MeasurableEquiv.prodAssoc.trans <|
        MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (PastRoundScalars p t)) <|
          MeasurableEquiv.prodCongr eCurrent
            (MeasurableEquiv.refl (FutureRoundScalars p t))

/-- The strict-past/current/future split preserves the exact product scalar
law.  The two subtype splits and the player reindex are measure preserving by
the corresponding Mathlib product-coordinate theorems. -/
theorem playerRoundScalarSplit_measurePreserving (p : Parameters) (t : Fin p.T) :
    MeasurePreserving (playerRoundScalarSplitEquiv p t) (playerRoundScalarLaw p)
      ((pastRoundScalarLaw p t).prod
        ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))) := by
  let ePastCurrent : MeasurableEquiv
      (PastOrCurrentRoundLabel p t → Scalar)
      (PastRoundScalars p t × (CurrentPastRoundLabel p t → Scalar)) :=
    MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PastOrCurrentRoundLabel p t => Scalar)
    (fun label => label.1.2 < t)
  let eRound : MeasurableEquiv (PlayerRoundScalars p)
      ((PastOrCurrentRoundLabel p t → Scalar) × FutureRoundScalars p t) :=
    MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => Scalar)
    (fun label => label.2 ≤ t)
  let eCurrent : MeasurableEquiv (CurrentPastRoundLabel p t → Scalar)
      (CurrentRoundScalars p) :=
    MeasurableEquiv.piCongrLeft
    (fun _ : Fin p.m => Scalar) (currentPastRoundLabelEquiv p t).symm
  have hRound : MeasurePreserving eRound (playerRoundScalarLaw p)
      ((Measure.pi (fun _ : PastOrCurrentRoundLabel p t => ContinuousCategorical.uniform)).prod
        (futureRoundScalarLaw p t)) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : PlayerRoundLabel p => ContinuousCategorical.uniform)
      (fun label => label.2 ≤ t)
  have hPastCurrent : MeasurePreserving ePastCurrent
      (Measure.pi (fun _ : PastOrCurrentRoundLabel p t => ContinuousCategorical.uniform))
      ((pastRoundScalarLaw p t).prod
        (Measure.pi (fun _ : CurrentPastRoundLabel p t => ContinuousCategorical.uniform))) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : PastOrCurrentRoundLabel p t => ContinuousCategorical.uniform)
      (fun label => label.1.2 < t)
  have hCurrent : MeasurePreserving eCurrent
      (Measure.pi (fun _ : CurrentPastRoundLabel p t => ContinuousCategorical.uniform))
      (currentRoundScalarLaw p) := by
    exact measurePreserving_piCongrLeft
      (fun _ : Fin p.m => ContinuousCategorical.uniform)
      (currentPastRoundLabelEquiv p t).symm
  have hFuture : MeasurePreserving id (futureRoundScalarLaw p t)
      (futureRoundScalarLaw p t) := MeasurePreserving.id _
  have hPastCurrentFuture := hPastCurrent.prod hFuture
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (PastRoundScalars p t × (CurrentPastRoundLabel p t → Scalar)) ×
          FutureRoundScalars p t ≃ᵐ
            PastRoundScalars p t × ((CurrentPastRoundLabel p t → Scalar) ×
              FutureRoundScalars p t))
      (((pastRoundScalarLaw p t).prod
        (Measure.pi (fun _ : CurrentPastRoundLabel p t => ContinuousCategorical.uniform))).prod
          (futureRoundScalarLaw p t))
      ((pastRoundScalarLaw p t).prod
        ((Measure.pi (fun _ : CurrentPastRoundLabel p t => ContinuousCategorical.uniform)).prod
          (futureRoundScalarLaw p t))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hReindex : MeasurePreserving
      (Prod.map id (Prod.map eCurrent id))
      ((pastRoundScalarLaw p t).prod
        ((Measure.pi (fun _ : CurrentPastRoundLabel p t => ContinuousCategorical.uniform)).prod
          (futureRoundScalarLaw p t)))
      ((pastRoundScalarLaw p t).prod
        ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))) := by
    exact (MeasurePreserving.id (pastRoundScalarLaw p t)).prod (hCurrent.prod hFuture)
  have hInitial := hPastCurrentFuture.comp hRound
  have hAssociated := hAssoc.comp hInitial
  have hFinal := hReindex.comp hAssociated
  change MeasurePreserving
    (eRound.trans <| (MeasurableEquiv.prodCongr ePastCurrent
      (MeasurableEquiv.refl _)).trans <| MeasurableEquiv.prodAssoc.trans <|
        MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) <|
          MeasurableEquiv.prodCongr eCurrent (MeasurableEquiv.refl _))
    (playerRoundScalarLaw p)
    ((pastRoundScalarLaw p t).prod
      ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t)))
  exact hFinal

/-- Split all extended private coordinates without changing the accepted
base law, target-stream law, or round scalar law. -/
@[expose] noncomputable def extendedPrivateRoundSplitEquiv (p : Parameters)
    (t : Fin p.T) : MeasurableEquiv (ExtendedPrivateCoordinates p)
      (PastView p t × (CurrentRoundScalars p × FutureRoundScalars p t)) := by
  let eRoundTarget : MeasurableEquiv
      (PlayerRoundScalars p × CoordinatorTargetScalars p)
      ((PastRoundScalars p t × CoordinatorTargetScalars p) ×
        (CurrentRoundScalars p × FutureRoundScalars p t)) := by
    exact ((MeasurableEquiv.prodCongr (playerRoundScalarSplitEquiv p t)
      (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc).trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm).trans
          MeasurableEquiv.prodAssoc.symm
  exact (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eRoundTarget).trans
    MeasurableEquiv.prodAssoc.symm

/-- Exact pushforward law of the split coordinates under the already
integrated `extendedPrivateLaw`.  In particular, the current scalar vector is
independent of the strict-past view, accepted base private coordinates,
coordinator targets, and strict-future scalars. -/
theorem extendedPrivateRoundSplit_measurePreserving (p : Parameters) (t : Fin p.T) :
    MeasurePreserving (extendedPrivateRoundSplitEquiv p t) (extendedPrivateLaw p)
      ((pastViewLaw p t).prod
        ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))) := by
  let hRound := playerRoundScalarSplit_measurePreserving p t
  have hTarget : MeasurePreserving id (coordinatorTargetScalarLaw p)
      (coordinatorTargetScalarLaw p) := MeasurePreserving.id _
  have hRoundTarget := hRound.prod hTarget
  let μCurrentFuture :=
    (currentRoundScalarLaw p).prod (futureRoundScalarLaw p t)
  have hAssoc := measurePreserving_prodAssoc (pastRoundScalarLaw p t)
    μCurrentFuture (coordinatorTargetScalarLaw p)
  have hSwap : MeasurePreserving Prod.swap
      (μCurrentFuture.prod (coordinatorTargetScalarLaw p))
      ((coordinatorTargetScalarLaw p).prod μCurrentFuture) := by
    exact Measure.measurePreserving_swap
  have hAssocBack := (measurePreserving_prodAssoc
    (pastRoundScalarLaw p t) (coordinatorTargetScalarLaw p)
    μCurrentFuture).symm
  have hReorder := hAssocBack.comp <|
    ((MeasurePreserving.id (pastRoundScalarLaw p t)).prod hSwap).comp <|
      hAssoc.comp hRoundTarget
  have hPrivate := (MeasurePreserving.id (PrivateSourceStreams.privateCoordinatesLaw p)).prod
    hReorder
  have hOuter := (measurePreserving_prodAssoc
    (PrivateSourceStreams.privateCoordinatesLaw p)
    ((pastRoundScalarLaw p t).prod (coordinatorTargetScalarLaw p))
    μCurrentFuture).symm.comp hPrivate
  change MeasurePreserving
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) <|
       ((MeasurableEquiv.prodCongr (playerRoundScalarSplitEquiv p t)
         (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc).trans <|
         (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm).trans
           MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodAssoc.symm)
    (extendedPrivateLaw p)
    ((pastViewLaw p t).prod
      ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t)))
  exact hOuter

/-- The literal per-player probability of a fixed requested arm under one
current decision branch. -/
@[expose] def privateRoundAtomProbability (p : Parameters)
    (choice : Option (Fin p.K)) (arm : Fin p.K) : ℝ≥0∞ :=
  match choice with
  | none => ENNReal.ofReal (1 / (p.K : ℝ))
  | some forbidden =>
      if arm = forbidden then 0
      else ENNReal.ofReal (1 / ((p.K - 1 : ℕ) : ℝ))

/-- Apply the existing source draw map to one scalar, choosing either its full
uniform output or its forbidden-arm complement output. -/
@[expose] def privateRoundScalarAction (p : Parameters)
    (choice : Option (Fin p.K)) (v : Scalar) : Fin p.K :=
  match choice with
  | none => fullArmScalarDraw p v
  | some forbidden => (forbiddenArmScalarDraw p forbidden v).val

/-- Measurability of the parameterized full-or-avoid draw.  The finite
decision coordinate is split into its measurable singleton fibers. -/
theorem measurable_privateRoundScalarAction (p : Parameters) :
    Measurable (fun z : Option (Fin p.K) × Scalar =>
      privateRoundScalarAction p z.1 z.2) := by
  classical
  intro s hs
  rw [show (fun z : Option (Fin p.K) × Scalar =>
      privateRoundScalarAction p z.1 z.2) ⁻¹' s =
      ⋃ arm : Fin p.K, if arm ∈ s then
        {z | privateRoundScalarAction p z.1 z.2 = arm} else ∅ by
          ext z
          simp]
  refine MeasurableSet.iUnion fun arm => ?_
  by_cases ha : arm ∈ s
  · simp only [ha]
    change MeasurableSet {z : Option (Fin p.K) × Scalar |
      privateRoundScalarAction p z.1 z.2 = arm}
    rw [show {z : Option (Fin p.K) × Scalar |
        privateRoundScalarAction p z.1 z.2 = arm} =
      ({z | z.1 = none} ∩ {z | fullArmScalarDraw p z.2 = arm}) ∪
        ⋃ forbidden : Fin p.K,
          ({z | z.1 = some forbidden} ∩
            {z | (forbiddenArmScalarDraw p forbidden z.2).val = arm}) by
              ext z
              cases hchoice : z.1 <;> simp [privateRoundScalarAction, hchoice]]
    refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun forbidden => ?_)
    · exact (measurable_fst (measurableSet_singleton none)).inter
        ((measurable_fullArmScalarDraw p (measurableSet_singleton arm)).preimage
          measurable_snd)
    · exact (measurable_fst (measurableSet_singleton (some forbidden))).inter
        ((measurable_subtype_coe.comp (measurable_forbiddenArmScalarDraw p forbidden)
          (measurableSet_singleton arm)).preimage measurable_snd)
  · simp [ha]

/-- The all-player action map for a fixed vector of branch decisions. -/
@[expose] def privateRoundActionMap (p : Parameters)
    (choice : Fin p.m → Option (Fin p.K)) (x : CurrentRoundScalars p) :
    Fin p.m → Fin p.K :=
  fun i => privateRoundScalarAction p (choice i) (x i)

theorem measurable_privateRoundActionMap (p : Parameters)
    (choice : Fin p.m → Option (Fin p.K)) :
    Measurable (privateRoundActionMap p choice) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_privateRoundScalarAction p).comp
    (measurable_const.prodMk (measurable_pi_apply i))

/-- For a fixed current decision vector, the complete arm-vector atom is the
product of the literal per-player probabilities. -/
theorem privateRoundActionMap_atom (p : Parameters)
    (choice : Fin p.m → Option (Fin p.K)) (arms : Fin p.m → Fin p.K) :
    (currentRoundScalarLaw p).map (privateRoundActionMap p choice) {arms} =
      ∏ i, privateRoundAtomProbability p (choice i) (arms i) := by
  rw [show privateRoundActionMap p choice = fun x : CurrentRoundScalars p =>
      fun i => privateRoundScalarAction p (choice i) (x i) by rfl]
  have hscalar (i : Fin p.m) : Measurable
      (fun v : Scalar => privateRoundScalarAction p (choice i) v) :=
    (measurable_privateRoundScalarAction p).comp
      (measurable_const.prodMk measurable_id)
  have hmap :
      (Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform)).map
        (fun x i => privateRoundScalarAction p (choice i) (x i)) =
      Measure.pi (fun i => ContinuousCategorical.uniform.map
        (fun v => privateRoundScalarAction p (choice i) v)) := by
    exact Measure.pi_map_pi (fun i => (hscalar i).aemeasurable)
  change (Measure.pi (fun _ : Fin p.m => ContinuousCategorical.uniform)).map
      (fun x i => privateRoundScalarAction p (choice i) (x i)) {arms} = _
  rw [hmap, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i hi
  cases hc : choice i with
  | none =>
      simp only [privateRoundScalarAction, privateRoundAtomProbability]
      exact fullArmScalarDraw_map_atom p (arms i)
  | some forbidden =>
      simp only [privateRoundScalarAction, privateRoundAtomProbability]
      by_cases hEq : arms i = forbidden
      · have hzero : (ContinuousCategorical.uniform.map
            (fun v => (forbiddenArmScalarDraw p forbidden v).val)) {arms i} = 0 := by
          change (ContinuousCategorical.uniform.map
            (Subtype.val ∘ forbiddenArmScalarDraw p forbidden)) {arms i} = 0
          rw [Measure.map_apply
            ((measurable_subtype_coe.comp
              (measurable_forbiddenArmScalarDraw p forbidden)))
            (measurableSet_singleton (arms i))]
          have hpre : (Subtype.val ∘ forbiddenArmScalarDraw p forbidden) ⁻¹'
              {arms i} = ∅ := by
            ext v
            change (forbiddenArmScalarDraw p forbidden v).val = arms i ↔ False
            constructor
            · intro hv
              have hne := (forbiddenArmScalarDraw p forbidden v).property
              exact hne (hv.trans hEq)
            · intro hv
              exact False.elim hv
          rw [hpre, measure_empty]
        simpa [hEq] using hzero
      · have hpre : (Subtype.val ∘ forbiddenArmScalarDraw p forbidden) ⁻¹'
            {arms i} = forbiddenArmScalarDraw p forbidden ⁻¹'
              {⟨arms i, hEq⟩} := by
          ext v
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · intro hv
            apply Subtype.ext
            exact hv
          · intro hv
            exact congrArg Subtype.val hv
        change (ContinuousCategorical.uniform.map
          (Subtype.val ∘ forbiddenArmScalarDraw p forbidden)) {arms i} = _
        rw [Measure.map_apply
          ((measurable_subtype_coe.comp
            (measurable_forbiddenArmScalarDraw p forbidden)))
              (measurableSet_singleton (arms i)), hpre]
        simpa [hEq] using forbiddenArmScalarDraw_uniform_atom p forbidden ⟨arms i, hEq⟩

/-- Apply the fixed per-player decisions selected by a past view to the whole
current scalar vector. -/
@[expose] def adaptivePrivateRoundActions (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (view : PastView p t) (current : CurrentRoundScalars p) :
    Fin p.m → Fin p.K :=
  privateRoundActionMap p (decision view) current

/-- Joint measurability of the action-vector map from the past view and the
current scalar vector. -/
theorem measurable_adaptivePrivateRoundActions (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) :
    Measurable (fun z : PastView p t × CurrentRoundScalars p =>
      adaptivePrivateRoundActions p t decision z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_privateRoundScalarAction p).comp <|
    ((measurable_pi_apply i).comp (hdecision.comp measurable_fst)).prodMk
      (measurable_pi_apply i |>.comp measurable_snd)

/-- Joint event for a measurable past set and the entire current arm vector. -/
@[expose] def adaptivePrivateRoundEvent (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (pastEvent : Set (PastView p t)) (arms : Fin p.m → Fin p.K) :
    Set (PastView p t ×
      (CurrentRoundScalars p × FutureRoundScalars p t)) :=
  {z | z.1 ∈ pastEvent ∧
    adaptivePrivateRoundActions p t decision z.1 z.2.1 = arms}

theorem measurableSet_adaptivePrivateRoundEvent (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    MeasurableSet (adaptivePrivateRoundEvent p t decision pastEvent arms) := by
  have hactions : Measurable (fun z : PastView p t ×
      (CurrentRoundScalars p × FutureRoundScalars p t) =>
        adaptivePrivateRoundActions p t decision z.1 z.2.1) := by
    exact (measurable_adaptivePrivateRoundActions p t decision hdecision).comp <|
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact (hpast.preimage measurable_fst).inter (hactions (measurableSet_singleton arms))

/-- The complete adapted action-vector kernel on every measurable past event.
The integral is over the full split product law; its right side is the
past-view integral of the product of the literal full/avoid atom masses. -/
theorem adaptivePrivateRoundEvent_kernel (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    (pastViewLaw p t).prod
      ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))
      (adaptivePrivateRoundEvent p t decision pastEvent arms) =
      ∫⁻ view in pastEvent,
        ∏ i, privateRoundAtomProbability p (decision view i) (arms i)
        ∂pastViewLaw p t := by
  classical
  have hevent := measurableSet_adaptivePrivateRoundEvent p t decision hdecision
    pastEvent hpast arms
  change (pastViewLaw p t).prod
      ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))
      (adaptivePrivateRoundEvent p t decision pastEvent arms) = _
  rw [Measure.prod_apply hevent]
  calc
    _ = ∫⁻ view,
          pastEvent.indicator (fun v =>
            ∏ i, privateRoundAtomProbability p (decision v i) (arms i)) view
          ∂pastViewLaw p t := by
            apply lintegral_congr
            intro view
            by_cases hv : view ∈ pastEvent
            · simp [Set.indicator, hv]
              have hfiber : (Prod.mk view :
                  (CurrentRoundScalars p × FutureRoundScalars p t) →
                    PastView p t × (CurrentRoundScalars p × FutureRoundScalars p t)) ⁻¹'
                    adaptivePrivateRoundEvent p t decision pastEvent arms =
                  (adaptivePrivateRoundActions p t decision view ⁻¹' {arms}) ×ˢ Set.univ := by
                ext q
                simp [adaptivePrivateRoundEvent, hv]
              rw [hfiber, Measure.prod_prod, measure_univ, mul_one]
              have hkernel := privateRoundActionMap_atom p (decision view) arms
              rw [Measure.map_apply
                (measurable_privateRoundActionMap p (decision view))
                (measurableSet_singleton arms)] at hkernel
              have hactions : adaptivePrivateRoundActions p t decision view =
                  privateRoundActionMap p (decision view) := rfl
              rw [hactions]
              exact hkernel
            · simp [Set.indicator, hv]
              have hfiber : (Prod.mk view :
                  (CurrentRoundScalars p × FutureRoundScalars p t) →
                    PastView p t × (CurrentRoundScalars p × FutureRoundScalars p t)) ⁻¹'
                    adaptivePrivateRoundEvent p t decision pastEvent arms = ∅ := by
                ext q
                simp [adaptivePrivateRoundEvent, hv]
              rw [hfiber, measure_empty]
    _ = _ := by rw [lintegral_indicator hpast]

/-- The exact adapted joint event kernel pulled back to the existing integrated
`extendedPrivateLaw`; no new private carrier or source law is introduced. -/
theorem extendedPrivate_adaptiveRoundEvent_kernel (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    extendedPrivateLaw p
      ((extendedPrivateRoundSplitEquiv p t) ⁻¹'
        adaptivePrivateRoundEvent p t decision pastEvent arms) =
      ∫⁻ view in pastEvent,
        ∏ i, privateRoundAtomProbability p (decision view i) (arms i)
        ∂pastViewLaw p t := by
  have hsplit := extendedPrivateRoundSplit_measurePreserving p t
  have hevent := measurableSet_adaptivePrivateRoundEvent p t decision hdecision
    pastEvent hpast arms
  calc
    _ = (extendedPrivateLaw p).map (extendedPrivateRoundSplitEquiv p t)
          (adaptivePrivateRoundEvent p t decision pastEvent arms) := by
            symm
            exact Measure.map_apply (hsplit.measurable) hevent
    _ = (pastViewLaw p t).prod
          ((currentRoundScalarLaw p).prod (futureRoundScalarLaw p t))
          (adaptivePrivateRoundEvent p t decision pastEvent arms) := by
            rw [hsplit.map_eq]
    _ = _ := adaptivePrivateRoundEvent_kernel p t decision hdecision pastEvent hpast arms

/-- Indicator-integral form of the complete adapted kernel under the existing
extended private law. -/
theorem extendedPrivate_adaptiveRoundIndicator_kernel (p : Parameters) (t : Fin p.T)
    (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    ∫⁻ x, (extendedPrivateRoundSplitEquiv p t ⁻¹'
      adaptivePrivateRoundEvent p t decision pastEvent arms).indicator
        (fun _ => (1 : ℝ≥0∞)) x ∂extendedPrivateLaw p =
      ∫⁻ view in pastEvent,
        ∏ i, privateRoundAtomProbability p (decision view i) (arms i)
        ∂pastViewLaw p t := by
  let event := (extendedPrivateRoundSplitEquiv p t) ⁻¹'
    adaptivePrivateRoundEvent p t decision pastEvent arms
  have hevent : MeasurableSet event := by
    exact (measurableSet_adaptivePrivateRoundEvent p t decision hdecision
      pastEvent hpast arms).preimage (extendedPrivateRoundSplitEquiv p t).measurable
  calc
    _ = extendedPrivateLaw p event := by
      exact lintegral_indicator_one hevent
    _ = _ := extendedPrivate_adaptiveRoundEvent_kernel p t decision hdecision
      pastEvent hpast arms

/-- Specialization at any fixed complete public output and reward matrix,
using the integrated law's existing fixed-public equality. -/
theorem fixedPublic_adaptiveRoundEvent_kernel (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K)
    (t : Fin p.T) (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    fixedPublicPrivateLaw p published rewards
      ((extendedPrivateRoundSplitEquiv p t) ⁻¹'
        adaptivePrivateRoundEvent p t decision pastEvent arms) =
      ∫⁻ view in pastEvent,
        ∏ i, privateRoundAtomProbability p (decision view i) (arms i)
        ∂pastViewLaw p t := by
  rw [BootstrapPrivateRoundStreams.fixedPublicPrivateLaw_eq_product]
  exact extendedPrivate_adaptiveRoundEvent_kernel p t decision hdecision
    pastEvent hpast arms

/-- Fixed-public indicator-integral specialization, for the arbitrary complete
public output and reward matrix passed to the existing private-law equality. -/
theorem fixedPublic_adaptiveRoundIndicator_kernel (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K)
    (t : Fin p.T) (decision : PastView p t → Fin p.m → Option (Fin p.K))
    (hdecision : Measurable decision) (pastEvent : Set (PastView p t))
    (hpast : MeasurableSet pastEvent) (arms : Fin p.m → Fin p.K) :
    ∫⁻ x, ((extendedPrivateRoundSplitEquiv p t) ⁻¹'
      adaptivePrivateRoundEvent p t decision pastEvent arms).indicator
        (fun _ => (1 : ℝ≥0∞)) x
        ∂BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards =
      ∫⁻ view in pastEvent,
        ∏ i, privateRoundAtomProbability p (decision view i) (arms i)
        ∂pastViewLaw p t := by
  let event := (extendedPrivateRoundSplitEquiv p t) ⁻¹'
    adaptivePrivateRoundEvent p t decision pastEvent arms
  have hevent : MeasurableSet event := by
    exact (measurableSet_adaptivePrivateRoundEvent p t decision hdecision
      pastEvent hpast arms).preimage (extendedPrivateRoundSplitEquiv p t).measurable
  calc
    _ = BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards event := by
      exact lintegral_indicator_one hevent
    _ = _ := fixedPublic_adaptiveRoundEvent_kernel p published rewards t decision
      hdecision pastEvent hpast arms

end Bandits.Support.PrivateRoundFreshness

end
