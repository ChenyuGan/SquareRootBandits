/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.BootstrapOriginalScalarLaw
public import Bandits.Support.BootstrapDownCountMean
public import Bandits.Support.GeneratedBootstrapMonitor
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapModeService

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generated coordinator DOWN-positive current-round conditional mean

The current-round test uses the existing generated descriptor and the whole
original current vector.  A stopped descriptor contributes analytic zero.
The conditional kernel integrates only the public round coordinates and the
original labelled player scalars; block activity is fixed by the descriptor.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:638-682`,
`sources/zip4/manuscript/07_public_setup.tex:40-55,75-113`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedDownConditionalMean

open MeasureTheory ProbabilityTheory FiniteBanditModel
open PrivateRoundFreshness
open ConstructorDimensions BootstrapDimensions
open CompletePublicTable BootstrapPrivateRoundStreams
open BootstrapPhysicalBlock BootstrapPhysicalInput
open BootstrapModeService BootstrapOriginalScalarLaw
open ActiveRoundActions
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open ReferenceInitializationRun GeneratedBootstrapMonitor
open PublicDiscreteDraws OrderedTupleSampler ContinuousControlSlice
open ReferencePrelaunchPhysicalReplay
open scoped Classical BigOperators

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

abbrev Descriptor (p : Parameters) := GeneratedBootstrapRoundLaw.Descriptor p
abbrev Current (p : Parameters) := GeneratedBootstrapRoundLaw.Current p

/-- A fixed harmless complete-row extension for the snapshot evaluator.  The
evaluator overwrites the selected calendar entry before it reads any action;
the other entries are never interpreted as a physical history or continuation. -/
def zeroControl (p : Parameters) : ContinuousLearningRows.TimeControl p :=
  ((fun _ => (⟨0, by norm_num, by norm_num⟩ : ContinuousControlSlice.Scalar)),
    fun _ => ((fun _ => (0 : AffineChannelLaw.Bit)), (0 : AffineChannelLaw.Bit)))

def snapshotRow (p : Parameters) : CompleteRow p :=
  ((fun _ _ => false), fun _ => zeroControl p)

/-- The static fields fixed by an existing generated descriptor.  This is an
adapter to the accepted one-round physical action function, not a run: it has
no recursion, history, or postlaunch physical branch. -/
def descriptorBaseInput (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (d : Descriptor p) : BootstrapPhysicalBlock.Input p s := by
  let b := d.1
  let profile := d.2.1
  let target := d.2.2.1
  let incoming := ReferenceInitializationRun.uninformed b
  let hK : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
  refine {
    uninformed := incoming
    active := fun j => (profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).1
    held := fun j => ((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).1
    privateId := fun j => ((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).2
    ids := ids
    row := snapshotRow p
    target := target
    uniform := fun _ _ => ⟨0, by exact Nat.zero_lt_of_lt (K_pos p)⟩
    coordinatorAvoid := fun _ => Classical.choice (BootstrapModeService.avoidArm_nonempty hK target)
    followerAvoid := fun j _ => Classical.choice
      (BootstrapModeService.avoidArm_nonempty hK
        ((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).1)
    rewards := rewards }

/-- The exact current-row physical test for a fixed processed descriptor.
Every randomized alternative is evaluated from that player's one original
current scalar by `roundPrivateValuesOfOriginalScalars`. -/
def snapshotDownPositive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapOriginalScalarStep.OriginalScalarVector p) (a : Fin p.K) : ℝ := by
  let x := descriptorBaseInput ids rewards s d
  let y := BootstrapModeService.currentInputOf x t r
    (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x v)
  exact if BootstrapPhysicalBlock.slot y t = downSlot ∧
      BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
      0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
    then 1 else 0

/-- The stopped branch has no physical action and contributes zero. -/
def downPositiveCurrentTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (a : Fin p.K) :
    Option (Descriptor p) × Current p → ℝ := fun z =>
  match z.1 with
  | none => 0
  | some d => snapshotDownPositive ids rewards s t d z.2.1 z.2.2 a

/-- The source's support indicator for the fixed rounded reward coordinate. -/
def rewardSupport (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : ℝ :=
  BootstrapDownCountMean.rewardSupport p rewards t a

private theorem rewardSupport_zero_or_one (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : rewardSupport rewards t a = 0 ∨
      rewardSupport rewards t a = 1 := by
  by_cases h : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) <;>
    simp [rewardSupport, BootstrapDownCountMean.rewardSupport, h]

private theorem rewardSupport_eq_one_iff (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) :
    rewardSupport rewards t a = 1 ↔
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) := by
  by_cases h : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) <;>
    simp [rewardSupport, BootstrapDownCountMean.rewardSupport, h]

private theorem measurable_snapshotDownPositive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p) (a : Fin p.K) :
    Measurable (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
        snapshotDownPositive ids rewards s t d z.1 z.2 a) := by
  let x := descriptorBaseInput ids rewards s d
  let acts := fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
    BootstrapPhysicalBlock.actions
      (BootstrapModeService.currentInputOf x t z.1
        (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2))
      d.2.2.2 t
  have hacts : Measurable acts := BootstrapOriginalScalarLaw.measurable_originalScalarActions
    x d.2.2.2 t
  have hslotEq : (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
        BootstrapPhysicalBlock.slot
          (BootstrapModeService.currentInputOf x t z.1
            (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)) t) =
      fun z => BootstrapModeService.roundSlot z.1 := by
    funext z
    simp [BootstrapPhysicalBlock.slot, BootstrapModeService.currentInputOf,
      BootstrapModeService.currentInput, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice]
  have hslot : Measurable (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
        BootstrapPhysicalBlock.slot
          (BootstrapModeService.currentInputOf x t z.1
            (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)) t) := by
    rw [hslotEq]
    exact (BootstrapModeService.measurePreserving_roundSlot p).measurable.comp measurable_fst
  have hcoord : Measurable (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p => acts z (coordinator p.two_le_m)) :=
    (measurable_pi_apply (coordinator p.two_le_m)).comp hacts
  have hfeedback : Measurable (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
        FiniteBanditModel.playerFeedback (acts z)
          (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t arm)) (coordinator p.two_le_m)) :=
    (Measurable.of_discrete (f := fun ac : FiniteBanditModel.ActionProfile p.m p.K =>
      FiniteBanditModel.playerFeedback ac
        (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t arm)) (coordinator p.two_le_m))).comp hacts
  have hslotSet : MeasurableSet {z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p | BootstrapPhysicalBlock.slot
      (BootstrapModeService.currentInputOf x t z.1
        (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)) t = downSlot} :=
    (measurableSet_singleton downSlot).preimage hslot
  have hcoordSet : MeasurableSet {z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p | acts z (coordinator p.two_le_m) = a} :=
    (measurableSet_singleton a).preimage hcoord
  have hfeedbackSet : MeasurableSet {z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p | 0 < FiniteBanditModel.playerFeedback (acts z)
      (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t arm)) (coordinator p.two_le_m)} :=
    (measurableSet_Ioi (a := (0 : ℝ))).preimage hfeedback
  have htest : MeasurableSet {z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p | BootstrapPhysicalBlock.slot
      (BootstrapModeService.currentInputOf x t z.1
        (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)) t = downSlot ∧
      acts z (coordinator p.two_le_m) = a ∧
      0 < FiniteBanditModel.playerFeedback (acts z)
        (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t arm)) (coordinator p.two_le_m)} :=
    hslotSet.inter (hcoordSet.inter hfeedbackSet)
  change Measurable (fun z : BootstrapModeService.RoundCoordinates p ×
      BootstrapOriginalScalarStep.OriginalScalarVector p =>
    if BootstrapPhysicalBlock.slot
        (BootstrapModeService.currentInputOf x t z.1
          (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)) t = downSlot ∧
      acts z (coordinator p.two_le_m) = a ∧
      0 < FiniteBanditModel.playerFeedback (acts z)
        (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t arm)) (coordinator p.two_le_m)
    then (1 : ℝ) else 0)
  exact Measurable.ite htest measurable_const measurable_const

theorem measurable_downPositiveCurrentTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (a : Fin p.K) :
    Measurable (downPositiveCurrentTest ids rewards s t a) := by
  apply measurable_from_prod_countable_right
  intro d
  cases d with
  | none => exact measurable_const
  | some d => exact measurable_snapshotDownPositive ids rewards s t d a

theorem downPositiveCurrentTest_unit_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (a : Fin p.K)
    (z : Option (Descriptor p) × Current p) :
    0 ≤ downPositiveCurrentTest ids rewards s t a z ∧
      downPositiveCurrentTest ids rewards s t a z ≤ 1 := by
  rcases z with ⟨od, c⟩
  cases od with
  | none => simp [downPositiveCurrentTest]
  | some d =>
      let x := descriptorBaseInput ids rewards s d
      let y := BootstrapModeService.currentInputOf x t c.1
        (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x c.2)
      change 0 ≤ (if BootstrapPhysicalBlock.slot y t = downSlot ∧
          BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
          0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
        then (1 : ℝ) else 0) ∧
        (if BootstrapPhysicalBlock.slot y t = downSlot ∧
          BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
          0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
        then (1 : ℝ) else 0) ≤ 1
      split_ifs <;> norm_num

theorem integrable_downPositiveCurrentTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (a : Fin p.K) :
    Integrable (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
      (downPositiveCurrentTest ids rewards s t a)) (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply GeneratedBootstrapFiltration.integrable_testValue p ids rewards C_star C_h eta s t ht
    (downPositiveCurrentTest ids rewards s t a)
    (measurable_downPositiveCurrentTest ids rewards s t a) 1 (by norm_num)
  intro z
  have hz := downPositiveCurrentTest_unit_bounds ids rewards s t a z
  exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩

theorem adapted_downPositiveCurrentTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (a : Fin p.K) :
    Measurable[GeneratedBootstrapFiltration.analysisFiltration p (t.val + 1)]
      (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
        (downPositiveCurrentTest ids rewards s t a)) := by
  have hd := GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta s t ht
  have hle : GeneratedBootstrapFiltration.analysisFiltration p t.val ≤
      GeneratedBootstrapFiltration.analysisFiltration p (t.val + 1) :=
    (GeneratedBootstrapFiltration.analysisFiltration p).mono (Nat.le_succ _)
  have hd' : Measurable[GeneratedBootstrapFiltration.analysisFiltration p (t.val + 1)]
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t) :=
    hd.mono hle le_rfl
  have hc := GeneratedBootstrapFiltration.measurable_current_succ p t
  change Measurable[GeneratedBootstrapFiltration.analysisFiltration p (t.val + 1)]
    (fun e => downPositiveCurrentTest ids rewards s t a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e,
        GeneratedBootstrapRoundLaw.current p t e))
  exact (measurable_downPositiveCurrentTest ids rewards s t a).comp (hd'.prodMk hc)

/-- The DOWN slot and coordinator tuple coordinate in the actual current
continuous slice. -/
private def tupleDownSet (a : Fin p.K) : Set (ContinuousControlSlice.Slice p.m p.K) :=
  {u | PublicDiscreteDraws.slotDraw u = downSlot ∧
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val (coordinator p.two_le_m) = a}

private def roundTupleDownSet (a : Fin p.K) : Set (BootstrapModeService.RoundCoordinates p) :=
  {r | BootstrapModeService.roundSlot r = downSlot ∧
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (BootstrapModeService.roundSlice r)).val (coordinator p.two_le_m) = a}

private def tupleFirstScalar (v : ContinuousControlSlice.Scalar) : Fin p.K :=
  PublicDiscreteDraws.equalArmSample p.K (K_pos p) v

private theorem tuple_coordinator_eq_firstScalar
    (u : ContinuousControlSlice.Slice p.m p.K) :
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val (coordinator p.two_le_m) =
      tupleFirstScalar (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
  have hsource := OrderedTupleSampler.sample_source_equation p.two_le_m p.m_lt_K u
    (coordinator p.two_le_m)
  have hrem : OrderedTupleSampler.remainder
      (OrderedTupleSampler.restrict
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u) 0 (Nat.zero_le p.m)) =
      (Finset.univ : Finset (Fin p.K)) := by
    simp [OrderedTupleSampler.remainder, OrderedTupleSampler.restrict]
  have hfirst : OrderedTupleSampler.rank p.K (K_pos p)
      (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) =
      tupleFirstScalar (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
    have hrank : OrderedTupleSampler.rank p.K (K_pos p)
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) =
        PublicDiscreteDraws.pilotFromScalar p.K (K_pos p)
          (ContinuousControlSlice.coordinate
            (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
      apply Fin.ext
      rfl
    exact hrank.trans (PublicDiscreteDraws.pilot_eq_equalArmSample (K_pos p) _)
  calc
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u).val (coordinator p.two_le_m) =
      (OrderedTupleSampler.remainder
        (OrderedTupleSampler.restrict
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u) 0 (Nat.zero_le p.m))).orderEmbOfFin
        (OrderedTupleSampler.card_remainder _)
        (OrderedTupleSampler.rank p.K (K_pos p)
          (u (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)))) := hsource
    _ = tupleFirstScalar (ContinuousControlSlice.coordinate
        (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
      simpa [hrem, univ_orderEmbOfFin_eq_id,
        ContinuousControlSlice.coordinate] using hfirst
where
  univ_orderEmbOfFin_eq_id (K : ℕ) :
      (Finset.univ : Finset (Fin K)).orderEmbOfFin (by simp) =
        OrderEmbedding.id (Fin K) := by
    have h := Finset.orderEmbOfFin_unique'
      (s := (Finset.univ : Finset (Fin K))) (h := by simp)
      (f := OrderEmbedding.id (Fin K)) (fun _ => Finset.mem_univ _)
    exact h.symm

private theorem tupleDownSet_measurable (a : Fin p.K) : MeasurableSet (tupleDownSet a) := by
  apply (measurableSet_eq_fun
    (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)) measurable_const).inter
  exact measurableSet_eq_fun
    (measurable_pi_apply (coordinator p.two_le_m) |>.comp
      (measurable_subtype_coe.comp
        (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))) measurable_const

private theorem slice_tupleDownSet_mass (a : Fin p.K) :
    (ContinuousControlSlice.sliceLaw p.m p.K).real (tupleDownSet a) =
      (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by
  classical
  let labels : Fin 2 → ContinuousControlSlice.Label p.m p.K := fun i =>
    if i.val = 0 then ContinuousControlSlice.Label.slot
    else ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)
  have hlabels : Function.Injective labels := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · cases hij
    · fin_cases j
      · cases hij
      · rfl
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate p.m p.K).precomp
    (g := labels) hlabels
  have hscalarIndep : IndepFun
      (ContinuousControlSlice.coordinate (labels 0))
      (ContinuousControlSlice.coordinate (labels 1))
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
    exact hcoords.indepFun (by decide)
  have hslotMap : Measurable (ContinuousCategorical.sample (by decide)
      PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum) :=
    ContinuousCategorical.measurable_sample (by decide)
      PublicDiscreteDraws.slotMass_nonneg PublicDiscreteDraws.slotMass_sum
  have htupleMap : Measurable (tupleFirstScalar (p := p)) := by
    change Measurable (PublicDiscreteDraws.equalArmSample p.K (K_pos p))
    exact ContinuousCategorical.measurable_sample (K_pos p)
      (PublicDiscreteDraws.equalMass_nonneg p.K)
      (PublicDiscreteDraws.equalMass_sum p.K (K_pos p))
  have hdrawIndep := hscalarIndep.comp hslotMap htupleMap
  have hslotMarg : (ContinuousControlSlice.sliceLaw p.m p.K)
      ((fun u => ContinuousCategorical.sample (by decide)
        PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum
        (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot}) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
    have hfun : (fun u : ContinuousControlSlice.Slice p.m p.K =>
        ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
          PublicDiscreteDraws.slotMass_sum (ContinuousControlSlice.coordinate (labels 0) u)) =
        PublicDiscreteDraws.slotDraw := by
      funext u
      simp [labels, PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate]
    rw [hfun, PublicDiscreteDraws.slotDraw_atom]
    norm_num [PublicDiscreteDraws.slotPMF, PublicDiscreteDraws.slotMass_down,
      ContinuousCategorical.massPMF_apply]
  have htupleMarg : (ContinuousControlSlice.sliceLaw p.m p.K)
      ((tupleFirstScalar ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a}) =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
    have hpre : (tupleFirstScalar ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a} =
        ContinuousControlSlice.coordinate (labels 1) ⁻¹'
          (tupleFirstScalar ⁻¹' {a}) := rfl
    rw [hpre, ← Measure.map_apply
      (ContinuousControlSlice.measurable_coordinate (labels 1))
      ((measurableSet_singleton a).preimage htupleMap),
      ContinuousControlSlice.map_coordinate]
    change ContinuousControlSlice.scalarLaw (tupleFirstScalar ⁻¹' {a}) = _
    rw [ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
    change ContinuousCategorical.uniform
      ((PublicDiscreteDraws.equalArmSample p.K (K_pos p)) ⁻¹' {a}) = _
    exact ContinuousCategorical.uniform_sample_singleton (K_pos p)
      (PublicDiscreteDraws.equalMass_nonneg p.K)
      (PublicDiscreteDraws.equalMass_sum p.K (K_pos p)) a
  have hsets : tupleDownSet a =
      (fun u => ContinuousCategorical.sample (by decide)
        PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum
        (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot} ∩
      (tupleFirstScalar ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a} := by
    ext u
    simp only [tupleDownSet, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [show labels 0 = ContinuousControlSlice.Label.slot by rfl,
      show labels 1 = ContinuousControlSlice.Label.tuple (coordinator p.two_le_m) by
        simp [labels]]
    rw [tuple_coordinator_eq_firstScalar]
    simp [PublicDiscreteDraws.slotDraw]
  rw [hsets, Measure.real]
  have hind := hdrawIndep.measure_inter_preimage_eq_mul {downSlot} {a}
    (measurableSet_singleton downSlot) (measurableSet_singleton a)
  have hslotMarg' : (ContinuousControlSlice.sliceLaw p.m p.K)
      ((ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
        {downSlot}) = ENNReal.ofReal (1 / 4 : ℝ) := by
    have hset : (ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
        {downSlot} = (fun u => ContinuousCategorical.sample (by decide)
          PublicDiscreteDraws.slotMass PublicDiscreteDraws.slotMass_sum
          (ContinuousControlSlice.coordinate (labels 0) u)) ⁻¹' {downSlot} := by
      ext u
      rfl
    rw [hset]
    exact hslotMarg
  have htupleId : ((tupleFirstScalar (p := p)) ∘ ContinuousControlSlice.coordinate (labels 1)) =
      fun u => tupleFirstScalar (p := p)
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u) := by
    funext u
    simp [labels]
  have htupleMarg' : (ContinuousControlSlice.sliceLaw p.m p.K)
      ((fun u => tupleFirstScalar (p := p)
        (ContinuousControlSlice.coordinate
          (ContinuousControlSlice.Label.tuple (coordinator p.two_le_m)) u)) ⁻¹' {a}) =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
    rw [← htupleId]
    exact htupleMarg
  change ((ContinuousControlSlice.sliceLaw p.m p.K)
      ((ContinuousCategorical.sample (by decide) PublicDiscreteDraws.slotMass
        PublicDiscreteDraws.slotMass_sum ∘ ContinuousControlSlice.coordinate (labels 0)) ⁻¹'
        {downSlot} ∩
        (tupleFirstScalar ∘ ContinuousControlSlice.coordinate (labels 1)) ⁻¹' {a})).toReal = _
  rw [hind, hslotMarg', htupleMarg]
  rw [ENNReal.toReal_mul]
  norm_num

private theorem roundTupleDownSet_measurable (a : Fin p.K) :
    MeasurableSet (roundTupleDownSet a) := by
  have heq : roundTupleDownSet a =
      (BootstrapModeService.roundSlice (p := p)) ⁻¹' tupleDownSet a := by
    ext r
    simp [roundTupleDownSet, tupleDownSet, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice]
  rw [heq]
  exact (tupleDownSet_measurable a).preimage
    (BootstrapModeService.measurePreserving_roundSlice p).measurable
private theorem roundTupleDownSet_real (a : Fin p.K) :
    (BootstrapModeService.roundCoordinatesMeasure p).real (roundTupleDownSet a) =
      (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by
  have hmp := BootstrapModeService.measurePreserving_roundSlice p
  have hset : roundTupleDownSet a =
      (BootstrapModeService.roundSlice (p := p)) ⁻¹' tupleDownSet a := by
    ext r
    simp [roundTupleDownSet, tupleDownSet, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice]
  rw [hset]
  change ((BootstrapModeService.roundCoordinatesMeasure p)
    ((BootstrapModeService.roundSlice (p := p)) ⁻¹' tupleDownSet a)).toReal = _
  have hmeasure : (BootstrapModeService.roundCoordinatesMeasure p)
      ((BootstrapModeService.roundSlice (p := p)) ⁻¹' tupleDownSet a) =
      (ContinuousControlSlice.sliceLaw p.m p.K) (tupleDownSet a) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable (tupleDownSet_measurable a)]
  rw [hmeasure]
  exact slice_tupleDownSet_mass a
private def originalFullArmVector
    (v : BootstrapOriginalScalarStep.OriginalScalarVector p) : Player p.m → Fin p.K :=
  fun i => BootstrapPrivateRoundStreams.fullArmScalarDraw p (v i)

private def incomingAvoidSet (incoming : Finset (Follower p.m)) (a : Fin p.K) :
    Set (BootstrapOriginalScalarStep.OriginalScalarVector p) :=
  {v | ∀ j ∈ incoming,
    originalFullArmVector v (followerPlayer p.two_le_m j) ≠ a}

private theorem originalFullArmVector_measurePreserving :
    MeasurePreserving originalFullArmVector
      (BootstrapOriginalScalarStep.originalScalarVectorMeasure p)
      (BootstrapModeService.privateArmVectorMeasure p) := by
  have hmap :
      (Measure.pi (fun _ : Player p.m => ContinuousCategorical.uniform)).map
        originalFullArmVector =
      Measure.pi (fun _ : Player p.m =>
        ContinuousCategorical.uniform.map (BootstrapPrivateRoundStreams.fullArmScalarDraw p)) := by
    exact Measure.pi_map_pi (fun _ =>
      (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).aemeasurable)
  refine ⟨measurable_pi_iff.mpr (fun i =>
    (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
      (measurable_pi_apply i)), ?_⟩
  change (Measure.pi (fun _ : Player p.m => ContinuousCategorical.uniform)).map
    originalFullArmVector = _
  rw [hmap]
  congr 1
  funext i
  exact BootstrapOriginalScalarLaw.map_fullArmScalarDraw p
private theorem incomingAvoidSet_eq (incoming : Finset (Follower p.m)) (a : Fin p.K) :
    incomingAvoidSet incoming a =
      originalFullArmVector ⁻¹' BootstrapModeService.privateArmAvoidanceSet p
        (incoming.image (followerPlayer p.two_le_m)) a := by
  ext v
  simp [incomingAvoidSet, BootstrapModeService.privateArmAvoidanceSet,
    originalFullArmVector]
private theorem incomingAvoidSet_measurable (incoming : Finset (Follower p.m))
    (a : Fin p.K) : MeasurableSet (incomingAvoidSet incoming a) := by
  rw [incomingAvoidSet_eq]
  exact (MeasurableSet.of_discrete).preimage
    (originalFullArmVector_measurePreserving.measurable)
private theorem incomingAvoidSet_real (incoming : Finset (Follower p.m)) (a : Fin p.K) :
    (PrivateRoundFreshness.currentRoundScalarLaw p).real
      (incomingAvoidSet incoming a) = (1 - 1 / (p.K : ℝ)) ^ incoming.card := by
  have hmp := originalFullArmVector_measurePreserving (p := p)
  change ((BootstrapOriginalScalarStep.originalScalarVectorMeasure p)
      (incomingAvoidSet incoming a)).toReal = _
  rw [incomingAvoidSet_eq]
  have hmeasure : (BootstrapOriginalScalarStep.originalScalarVectorMeasure p)
      (originalFullArmVector ⁻¹' BootstrapModeService.privateArmAvoidanceSet p
        (incoming.image (followerPlayer p.two_le_m)) a) =
      (BootstrapModeService.privateArmVectorMeasure p)
        (BootstrapModeService.privateArmAvoidanceSet p
          (incoming.image (followerPlayer p.two_le_m)) a) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable MeasurableSet.of_discrete]
  rw [hmeasure]
  change ((BootstrapModeService.privateArmVectorMeasure p)
      (BootstrapModeService.privateArmAvoidanceSet p
        (incoming.image (followerPlayer p.two_le_m)) a)).toReal = _
  have hAvoid := BootstrapModeService.privateArmVectorAvoidance_mass p
    (incoming.image (followerPlayer p.two_le_m)) a
  change (BootstrapModeService.privateArmVectorMeasure p).real
      (BootstrapModeService.privateArmAvoidanceSet p
        (incoming.image (followerPlayer p.two_le_m)) a) = _
  rw [hAvoid]
  rw [Finset.card_image_of_injective _ (followerPlayer_injective p.two_le_m)]
private theorem incomingAvoidSet_ge_quarter (incoming : Finset (Follower p.m))
    (a : Fin p.K) : (1 / 4 : ℝ) ≤
      (PrivateRoundFreshness.currentRoundScalarLaw p).real
        (incomingAvoidSet incoming a) := by
  rw [incomingAvoidSet_real]
  have hinc : incoming.card ≤ p.m - 1 := by
    have hcard := Finset.card_le_univ incoming
    change incoming.card ≤ Fintype.card (Fin (p.m - 1)) at hcard
    rw [Fintype.card_fin] at hcard
    exact hcard
  have hcard : incoming.card ≤ p.K - 1 := by
    have hmk : p.m ≤ p.K := Nat.le_of_lt p.m_lt_K
    omega
  have hKpos : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
  have hKoneNat : 1 ≤ p.K := le_trans (by decide : 1 ≤ 2)
    (p.two_le_m.trans (Nat.le_of_lt p.m_lt_K))
  have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKoneNat
  have hbase_nonneg : 0 ≤ 1 - 1 / (p.K : ℝ) := by
    have hinv : 1 / (p.K : ℝ) ≤ 1 := (div_le_one hKpos).2 hKone
    linarith
  have hbase_le : 1 - 1 / (p.K : ℝ) ≤ 1 := by
    have hinv : 0 ≤ 1 / (p.K : ℝ) := by positivity
    linarith
  let q : ℝ := 1 + ((p.K - 1 : ℕ) : ℝ)⁻¹
  have hsubcast : ((p.K - 1 : ℕ) : ℝ) = (p.K : ℝ) - 1 := by
    rw [Nat.cast_sub hKoneNat]
    norm_num
  have hsubpos : (0 : ℝ) < (p.K : ℝ) - 1 := by
    have hKgt : 1 < p.K := lt_of_lt_of_le (by decide : 1 < 2)
      (p.two_le_m.trans (Nat.le_of_lt p.m_lt_K))
    exact sub_pos.mpr (by exact_mod_cast hKgt)
  have hq : 1 - 1 / (p.K : ℝ) = q⁻¹ := by
    dsimp [q]
    rw [hsubcast]
    field_simp [hKpos.ne', hsubpos.ne']
    ring
  have hqbase : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hpow : q ^ (p.K - 1) ≤ Real.exp 1 := by
    dsimp [q]
    exact Real.one_add_inv_pow_le_exp
  have hpowlt : q ^ incoming.card < 3 := by
    have hpowle : q ^ incoming.card ≤ q ^ (p.K - 1) :=
      pow_le_pow_right₀ hqbase hcard
    exact (hpowle.trans hpow).trans_lt Real.exp_one_lt_three
  have hinv : (1 / 3 : ℝ) < (q ^ incoming.card)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt
      (pow_pos (by linarith [hqbase]) _) hpowlt
  rw [hq, inv_pow]
  exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3).trans hinv.le

private def currentLowerRectangle (incoming : Finset (Follower p.m)) (a : Fin p.K) :
    Set (Current p) := roundTupleDownSet a ×ˢ incomingAvoidSet incoming a
private def currentUpperRectangle (a : Fin p.K) : Set (Current p) :=
  roundTupleDownSet a ×ˢ Set.univ

private theorem currentLowerRectangle_measurable (incoming : Finset (Follower p.m))
    (a : Fin p.K) : MeasurableSet (currentLowerRectangle incoming a) :=
  (roundTupleDownSet_measurable a).prod (incomingAvoidSet_measurable incoming a)
private theorem currentUpperRectangle_measurable (a : Fin p.K) :
    MeasurableSet (currentUpperRectangle a) :=
  (roundTupleDownSet_measurable a).prod MeasurableSet.univ
private theorem real_prod_rectangle {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (B : Set β) : (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  simp [Measure.real, Measure.prod_prod]
private theorem currentLowerRectangle_real (incoming : Finset (Follower p.m))
    (a : Fin p.K) :
    (GeneratedBootstrapRoundLaw.currentLaw p).real (currentLowerRectangle incoming a) =
      ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) *
        ((1 - 1 / (p.K : ℝ)) ^ incoming.card) := by
  change ((BootstrapModeService.roundCoordinatesMeasure p).prod
    (PrivateRoundFreshness.currentRoundScalarLaw p)).real
      (roundTupleDownSet a ×ˢ incomingAvoidSet incoming a) = _
  rw [real_prod_rectangle, roundTupleDownSet_real, incomingAvoidSet_real]
private theorem currentUpperRectangle_real (a : Fin p.K) :
    (GeneratedBootstrapRoundLaw.currentLaw p).real (currentUpperRectangle a) =
      (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by
  change ((BootstrapModeService.roundCoordinatesMeasure p).prod
    (PrivateRoundFreshness.currentRoundScalarLaw p)).real
      (roundTupleDownSet a ×ˢ Set.univ) = _
  rw [real_prod_rectangle, roundTupleDownSet_real, probReal_univ]
  ring

/-- The conditional lower-bound guard is the actual incoming activity profile
stored by a processed descriptor. -/
def descriptorAllInactive (d : Descriptor p) : Prop :=
  ∀ j : {j // j ∈ ReferenceInitializationRun.uninformed d.1},
    (d.2.1 (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).1 = false

/-- Boolean form used to show that the source branch guard is measurable in
the enlarged past. The stopped descriptor has no active physical branch. -/
def processedAllInactive (d : Option (Descriptor p)) : Bool :=
  match d with
  | none => false
  | some q => decide (descriptorAllInactive q)

theorem measurable_processedAllInactive :
    Measurable (processedAllInactive (p := p)) :=
  measurable_of_countable (processedAllInactive (p := p))

theorem actual_allInactiveGuard_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    Measurable[GeneratedBootstrapFiltration.analysisFiltration p t.val]
      (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
        processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards
          C_star C_h eta s t e)) := by
  exact (measurable_processedAllInactive (p := p)).comp
    (GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta s t ht)
private theorem snapshot_slot_eq_roundSlot
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapOriginalScalarStep.OriginalScalarVector p) :
    let x := descriptorBaseInput ids rewards s d
    let y := BootstrapModeService.currentInputOf x t r
      (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x v)
    BootstrapPhysicalBlock.slot y t = BootstrapModeService.roundSlot r := by
  simp [BootstrapPhysicalBlock.slot, BootstrapModeService.currentInputOf,
    BootstrapModeService.currentInput, BootstrapModeService.roundSlot,
    BootstrapModeService.roundSlice]

private theorem snapshot_tuple_eq_roundTuple
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapOriginalScalarStep.OriginalScalarVector p) :
    let x := descriptorBaseInput ids rewards s d
    let y := BootstrapModeService.currentInputOf x t r
      (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x v)
    BootstrapPhysicalBlock.tuple y t =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (BootstrapModeService.roundSlice r) := by
  simp [BootstrapPhysicalBlock.tuple, BootstrapModeService.currentInputOf,
    BootstrapModeService.currentInput, BootstrapModeService.roundSlice]

private theorem snapshot_eq_one_implies_rewardSupport
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapOriginalScalarStep.OriginalScalarVector p) (a : Fin p.K)
    (h : snapshotDownPositive ids rewards s t d r v a = 1) :
    rewardSupport rewards t a = 1 := by
  let x := descriptorBaseInput ids rewards s d
  let y := BootstrapModeService.currentInputOf x t r
    (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x v)
  have hevent : BootstrapPhysicalBlock.slot y t = downSlot ∧
      BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
      0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m) := by
    have h' : (if BootstrapPhysicalBlock.slot y t = downSlot ∧
        BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
        0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
      then (1 : ℝ) else 0) = 1 := by
        simpa [snapshotDownPositive, x, y] using h
    split_ifs at h' with hevent
    · exact hevent
    · norm_num at h'
  rcases hevent with ⟨_, haction, hfeedback⟩
  have hfeedback' : 0 < FiniteBanditModel.playerFeedback
      (BootstrapPhysicalBlock.actions y d.2.2.2 t)
      (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (y.rewards t arm)) (coordinator p.two_le_m) := by
    simpa [BootstrapPhysicalBlock.feedback] using hfeedback
  have hfree := FiniteBanditModel.collisionFreeFor_of_playerFeedback_pos
    (BootstrapPhysicalBlock.actions y d.2.2.2 t)
    (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (y.rewards t arm)) (coordinator p.two_le_m) hfeedback'
  have hrew : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t a) := by
    unfold FiniteBanditModel.playerFeedback at hfeedback'
    rw [ite_eq_left hfree, haction] at hfeedback'
    simpa [y, x, BootstrapModeService.currentInputOf,
      BootstrapModeService.currentInput, descriptorBaseInput] using hfeedback'
  exact (rewardSupport_eq_one_iff rewards t a).2 hrew

private theorem snapshot_test_le_upperRectangle
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (a : Fin p.K) (z : Current p) :
    snapshotDownPositive ids rewards s t d z.1 z.2 a ≤
      Set.indicator (currentUpperRectangle a) (fun _ => (1 : ℝ)) z := by
  by_cases htest : snapshotDownPositive ids rewards s t d z.1 z.2 a = 1
  · have hsupport := snapshot_eq_one_implies_rewardSupport ids rewards s t d z.1 z.2 a htest
    let x := descriptorBaseInput ids rewards s d
    let y := BootstrapModeService.currentInputOf x t z.1
      (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)
    have hevent : BootstrapPhysicalBlock.slot y t = downSlot ∧
        BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
        0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m) := by
      have h' : (if BootstrapPhysicalBlock.slot y t = downSlot ∧
          BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
          0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
        then (1 : ℝ) else 0) = 1 := by
          simpa [snapshotDownPositive, x, y] using htest
      split_ifs at h' with hevent
      · exact hevent
      · norm_num at h'
    rcases hevent with ⟨hslot, hcoord, _⟩
    have htupleArm : (BootstrapPhysicalBlock.tuple y t).val (coordinator p.two_le_m) = a := by
      have hcoord' : BootstrapPhysicalBlock.coordinatorAction y d.2.2.2 t = a := by
        simpa only [BootstrapPhysicalBlock.actions_coordinator] using hcoord
      rw [BootstrapPhysicalBlock.coordinatorAction_down y d.2.2.2 t hslot] at hcoord'
      exact hcoord'
    have hr : z.1 ∈ roundTupleDownSet a := by
      change BootstrapModeService.roundSlot z.1 = downSlot ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (BootstrapModeService.roundSlice z.1)).val (coordinator p.two_le_m) = a
      constructor
      · exact (snapshot_slot_eq_roundSlot ids rewards s t d z.1 z.2).symm.trans hslot
      · rw [snapshot_tuple_eq_roundTuple ids rewards s t d z.1 z.2] at htupleArm
        exact htupleArm
    have hz : z ∈ currentUpperRectangle a := ⟨hr, Set.mem_univ _⟩
    simp [Set.indicator, hz, htest]
  · have hzero : snapshotDownPositive ids rewards s t d z.1 z.2 a = 0 := by
      have h01 : snapshotDownPositive ids rewards s t d z.1 z.2 a = 0 ∨
          snapshotDownPositive ids rewards s t d z.1 z.2 a = 1 := by
        let x := descriptorBaseInput ids rewards s d
        let y := BootstrapModeService.currentInputOf x t z.1
          (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)
        change (if BootstrapPhysicalBlock.slot y t = downSlot ∧
            BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
            0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
          then (1 : ℝ) else 0) = 0 ∨ _ = 1
        by_cases hevent : BootstrapPhysicalBlock.slot y t = downSlot ∧
            BootstrapPhysicalBlock.actions y d.2.2.2 t (coordinator p.two_le_m) = a ∧
            0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t (coordinator p.two_le_m)
        · simp [snapshotDownPositive, x, y, hevent]
        · simp [snapshotDownPositive, x, y, hevent]
      rcases h01 with hzero | hone
      · exact hzero
      · exact (htest hone).elim
    simp [Set.indicator, hzero]
    split_ifs <;> norm_num

private theorem snapshot_test_ge_lowerRectangle
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (a : Fin p.K) (hinactive : descriptorAllInactive d)
    (hchi : rewardSupport rewards t a = 1) (z : Current p) :
    Set.indicator (currentLowerRectangle (ReferenceInitializationRun.uninformed d.1) a)
      (fun _ => (1 : ℝ)) z ≤
        snapshotDownPositive ids rewards s t d z.1 z.2 a := by
  by_cases hz : z ∈ currentLowerRectangle (ReferenceInitializationRun.uninformed d.1) a
  · have ⟨hr, hv⟩ := hz
    let x := descriptorBaseInput ids rewards s d
    let y := BootstrapModeService.currentInputOf x t z.1
      (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)
    have hslot : BootstrapPhysicalBlock.slot y t = downSlot := by
      calc
        BootstrapPhysicalBlock.slot y t = BootstrapModeService.roundSlot z.1 :=
          snapshot_slot_eq_roundSlot ids rewards s t d z.1 z.2
        _ = downSlot := hr.1
    have htuple : BootstrapPhysicalBlock.tuple y t =
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (BootstrapModeService.roundSlice z.1) :=
      snapshot_tuple_eq_roundTuple ids rewards s t d z.1 z.2
    have hcoord : BootstrapPhysicalBlock.actions y d.2.2.2 t
        (coordinator p.two_le_m) = a := by
      rw [BootstrapPhysicalBlock.actions_coordinator,
        BootstrapPhysicalBlock.coordinatorAction_down y d.2.2.2 t hslot]
      rw [htuple]
      exact hr.2
    have hfree : FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y d.2.2.2 t) (coordinator p.two_le_m) := by
      intro i hne
      rcases ActiveRoundActions.player_cases p.two_le_m i with hcoord | ⟨j, rfl⟩
      · exact (hne hcoord).elim
      · by_cases hj : j ∈ ReferenceInitializationRun.uninformed d.1
        · let j' : {j // j ∈ x.uninformed} := ⟨j, by simpa [x, descriptorBaseInput] using hj⟩
          have hact : x.active j' = false := by
            change (d.2.1 (BootstrapPhysicalInput.sourceFollowerIndex p j)).1 = false
            exact hinactive j'
          have haction : BootstrapPhysicalBlock.actions y d.2.2.2 t
              (followerPlayer p.two_le_m j) =
              BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.2 (followerPlayer p.two_le_m j)) := by
            rw [BootstrapPhysicalBlock.actions_follower,
              BootstrapPhysicalBlock.followerAction]
            have hmem : j ∈ y.uninformed := by simpa [y, x,
              BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
              descriptorBaseInput] using hj
            rw [dite_eq_left hmem]
            have hact' : y.active ⟨j, hmem⟩ = false := by
              simpa [y, x, BootstrapModeService.currentInputOf,
                BootstrapModeService.currentInput, descriptorBaseInput] using hact
            rw [BootstrapPhysicalBlock.uninformedAction_inactive y t ⟨j, hmem⟩ hact']
            simp [y, x, BootstrapModeService.currentInputOf,
              BootstrapModeService.currentInput,
              BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars]
          have havoid : BootstrapPrivateRoundStreams.fullArmScalarDraw p
              (z.2 (followerPlayer p.two_le_m j)) ≠ a := by
            exact hv j hj
          rw [haction, hcoord]
          exact havoid
        · have haction : BootstrapPhysicalBlock.actions y d.2.2.2 t
              (followerPlayer p.two_le_m j) =
              (BootstrapPhysicalBlock.tuple y t).val (followerPlayer p.two_le_m j) := by
            rw [BootstrapPhysicalBlock.actions_follower,
              BootstrapPhysicalBlock.followerAction]
            have hmem : j ∉ y.uninformed := by
              simpa [y, x, BootstrapModeService.currentInputOf,
                BootstrapModeService.currentInput, descriptorBaseInput] using hj
            rw [dite_eq_right hmem]
            exact BootstrapPhysicalBlock.unoccupiedAction_down y t j hslot
          intro heq
          have htupleCoord : (BootstrapPhysicalBlock.tuple y t).val
              (coordinator p.two_le_m) = a := by
            rw [htuple]
            exact hr.2
          have harmcoord : BootstrapPhysicalBlock.actions y d.2.2.2 t
              (coordinator p.two_le_m) =
              (BootstrapPhysicalBlock.tuple y t).val (coordinator p.two_le_m) :=
            hcoord.trans htupleCoord.symm
          have harms : (BootstrapPhysicalBlock.tuple y t).val
              (followerPlayer p.two_le_m j) =
              (BootstrapPhysicalBlock.tuple y t).val (coordinator p.two_le_m) := by
            calc
              _ = BootstrapPhysicalBlock.actions y d.2.2.2 t
                  (followerPlayer p.two_le_m j) := haction.symm
              _ = BootstrapPhysicalBlock.actions y d.2.2.2 t
                  (coordinator p.two_le_m) := heq
              _ = (BootstrapPhysicalBlock.tuple y t).val
                  (coordinator p.two_le_m) := harmcoord
          have harmaction : (BootstrapPhysicalBlock.tuple y t).val
              (followerPlayer p.two_le_m j) =
              BootstrapPhysicalBlock.actions y d.2.2.2 t
                (followerPlayer p.two_le_m j) := haction.symm
          have htupleCoord : (BootstrapPhysicalBlock.tuple y t).val
              (coordinator p.two_le_m) = a := by
            rw [htuple]
            exact hr.2
          have harmcoord : BootstrapPhysicalBlock.actions y d.2.2.2 t
              (coordinator p.two_le_m) =
              (BootstrapPhysicalBlock.tuple y t).val (coordinator p.two_le_m) :=
            hcoord.trans htupleCoord.symm
          have harmtuple : (BootstrapPhysicalBlock.tuple y t).val
              (followerPlayer p.two_le_m j) =
              (BootstrapPhysicalBlock.tuple y t).val (coordinator p.two_le_m) :=
            harmaction.trans (heq.trans harmcoord)
          exact followerPlayer_ne_coordinator p.two_le_m j
            ((BootstrapPhysicalBlock.tuple y t).property harmtuple)
    have hrew : 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t a) := (rewardSupport_eq_one_iff rewards t a).mp hchi
    have hfeedback : 0 < BootstrapPhysicalBlock.feedback y d.2.2.2 t
        (coordinator p.two_le_m) := by
      rw [BootstrapPhysicalBlock.feedback]
      unfold FiniteBanditModel.playerFeedback
      rw [ite_eq_left hfree, hcoord]
      simpa [y, x, BootstrapModeService.currentInputOf,
        BootstrapModeService.currentInput, descriptorBaseInput] using hrew
    have htest : snapshotDownPositive ids rewards s t d z.1 z.2 a = 1 := by
      simp [snapshotDownPositive, x, y, hslot, hcoord, hfeedback]
    simp [Set.indicator, hz, htest]
  · have hnonneg := (downPositiveCurrentTest_unit_bounds ids rewards s t a
      (some d, z)).1
    simp [Set.indicator, hz]
    exact hnonneg

theorem conditionalKernel_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (t : Fin p.T) (a : Fin p.K)
    (d : Option (Descriptor p)) :
    0 ≤ GeneratedBootstrapFiltration.conditionalKernel p
      (downPositiveCurrentTest ids rewards s t a) d ∧
    GeneratedBootstrapFiltration.conditionalKernel p
      (downPositiveCurrentTest ids rewards s t a) d ≤
      rewardSupport rewards t a / (p.K : ℝ) ∧
    (∀ q, d = some q → descriptorAllInactive q →
      rewardSupport rewards t a / (16 * (p.K : ℝ)) ≤
        GeneratedBootstrapFiltration.conditionalKernel p
          (downPositiveCurrentTest ids rewards s t a) d) := by
  have hH := measurable_downPositiveCurrentTest ids rewards s t a
  have hunit := downPositiveCurrentTest_unit_bounds ids rewards s t a
  have hKpos : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
  cases d with
  | none =>
      constructor
      · simp [GeneratedBootstrapFiltration.conditionalKernel,
          downPositiveCurrentTest]
      · constructor
        · have hchi : 0 ≤ rewardSupport rewards t a := by
            unfold rewardSupport BootstrapDownCountMean.rewardSupport
            split_ifs <;> norm_num
          simpa [GeneratedBootstrapFiltration.conditionalKernel,
            downPositiveCurrentTest] using div_nonneg hchi (le_of_lt hKpos)
        · intro q hd
          cases hd
  | some q =>
      have hsection : Integrable
          (fun z : Current p => snapshotDownPositive ids rewards s t q z.1 z.2 a)
          (GeneratedBootstrapRoundLaw.currentLaw p) := by
        apply GeneratedBootstrapFiltration.integrable_conditionalKernelSection p
          (downPositiveCurrentTest ids rewards s t a) hH 1 (by norm_num)
          (fun w => by
            have hw := downPositiveCurrentTest_unit_bounds ids rewards s t a w
            exact abs_le.mpr ⟨by linarith [hw.1], hw.2⟩) (some q)
      have hunitSection (z : Current p) :
          0 ≤ snapshotDownPositive ids rewards s t q z.1 z.2 a ∧
            snapshotDownPositive ids rewards s t q z.1 z.2 a ≤ 1 := by
        simpa [downPositiveCurrentTest] using hunit (some q, z)
      have hchi01 := rewardSupport_zero_or_one rewards t a
      have hkernelEq :
          GeneratedBootstrapFiltration.conditionalKernel p
            (downPositiveCurrentTest ids rewards s t a) (some q) =
          ∫ z : Current p, snapshotDownPositive ids rewards s t q z.1 z.2 a
            ∂GeneratedBootstrapRoundLaw.currentLaw p := by
        rfl
      rcases hchi01 with hchi0 | hchi1
      · have hzero (z : Current p) :
            snapshotDownPositive ids rewards s t q z.1 z.2 a = 0 := by
          have h01 : snapshotDownPositive ids rewards s t q z.1 z.2 a = 0 ∨
              snapshotDownPositive ids rewards s t q z.1 z.2 a = 1 := by
            let x := descriptorBaseInput ids rewards s q
            let y := BootstrapModeService.currentInputOf x t z.1
              (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars x z.2)
            change (if BootstrapPhysicalBlock.slot y t = downSlot ∧
                BootstrapPhysicalBlock.actions y q.2.2.2 t (coordinator p.two_le_m) = a ∧
                0 < BootstrapPhysicalBlock.feedback y q.2.2.2 t (coordinator p.two_le_m)
              then (1 : ℝ) else 0) = 0 ∨ _ = 1
            by_cases hevent : BootstrapPhysicalBlock.slot y t = downSlot ∧
                BootstrapPhysicalBlock.actions y q.2.2.2 t (coordinator p.two_le_m) = a ∧
                0 < BootstrapPhysicalBlock.feedback y q.2.2.2 t (coordinator p.two_le_m)
            · simp [snapshotDownPositive, x, y, hevent]
            · simp [snapshotDownPositive, x, y, hevent]
          rcases h01 with hzero | hone
          · exact hzero
          · have hsupport := snapshot_eq_one_implies_rewardSupport
              ids rewards s t q z.1 z.2 a hone
            rw [hchi0] at hsupport
            norm_num at hsupport
        refine ⟨?_, ?_, ?_⟩
        · rw [hkernelEq]
          simp [hzero]
        · rw [hkernelEq, hchi0]
          simp [hzero]
        · intro q' hd _
          cases hd
          rw [hkernelEq, hchi0]
          simp [hzero]
      · have hUpperPoint (z : Current p) :
            snapshotDownPositive ids rewards s t q z.1 z.2 a ≤
              Set.indicator (currentUpperRectangle a) (fun _ => (1 : ℝ)) z :=
          snapshot_test_le_upperRectangle ids rewards s t q a z
        have hUpperInt : Integrable
            (Set.indicator (currentUpperRectangle a) (fun _ : Current p => (1 : ℝ)))
            (GeneratedBootstrapRoundLaw.currentLaw p) :=
          (integrable_const (1 : ℝ)).indicator (currentUpperRectangle_measurable a)
        have hUpper := integral_mono hsection hUpperInt hUpperPoint
        have hMass := currentUpperRectangle_real (p := p) a
        have hfraction : (1 / (4 * (p.K : ℝ)) : ℝ) ≤ 1 / (p.K : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hKpos]
          nlinarith
        have hAvoid0 := incomingAvoidSet_ge_quarter
            (p := p) (ReferenceInitializationRun.uninformed q.1) a
        rw [incomingAvoidSet_real] at hAvoid0
        have hAvoid : (1 / 4 : ℝ) ≤
            (1 - 1 / (p.K : ℝ)) ^ (ReferenceInitializationRun.uninformed q.1).card := hAvoid0
        have hmassLower : (1 / (16 * (p.K : ℝ)) : ℝ) ≤
            ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) *
              ((1 - 1 / (p.K : ℝ)) ^
                (ReferenceInitializationRun.uninformed q.1).card) := by
          have hleft : 0 ≤ (1 / 4 : ℝ) * (1 / (p.K : ℝ)) := by positivity
          calc
            (1 / (16 * (p.K : ℝ)) : ℝ) =
                ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) * (1 / 4) := by
                  field_simp [hKpos.ne']
                  ring
            _ ≤ ((1 / 4 : ℝ) * (1 / (p.K : ℝ))) *
                ((1 - 1 / (p.K : ℝ)) ^
                  (ReferenceInitializationRun.uninformed q.1).card) :=
              mul_le_mul_of_nonneg_left hAvoid hleft
        refine ⟨?_, ?_, ?_⟩
        · rw [hkernelEq]
          exact integral_nonneg (fun z => (hunitSection z).1)
        · rw [hkernelEq]
          calc
            (∫ z : Current p, snapshotDownPositive ids rewards s t q z.1 z.2 a
                ∂GeneratedBootstrapRoundLaw.currentLaw p) ≤
              ∫ z, Set.indicator (currentUpperRectangle a) (fun _ => (1 : ℝ)) z
                ∂GeneratedBootstrapRoundLaw.currentLaw p := hUpper
            _ = (1 / (4 * (p.K : ℝ)) : ℝ) := by
              calc
                _ = (GeneratedBootstrapRoundLaw.currentLaw p).real
                    (currentUpperRectangle a) :=
                  integral_indicator_one (μ := GeneratedBootstrapRoundLaw.currentLaw p)
                    (currentUpperRectangle_measurable a)
                _ = _ := by simpa [one_div, mul_comm] using hMass
            _ ≤ rewardSupport rewards t a / (p.K : ℝ) := by
              rw [hchi1]
              simpa [one_div] using hfraction
        · intro q' hd hinactive
          cases hd
          have hLowerPoint (z : Current p) :
              Set.indicator (currentLowerRectangle (ReferenceInitializationRun.uninformed q.1) a)
                (fun _ : Current p => (1 : ℝ)) z ≤
                  snapshotDownPositive ids rewards s t q z.1 z.2 a :=
            snapshot_test_ge_lowerRectangle ids rewards s t q a hinactive hchi1 z
          have hLowerInt : Integrable
              (Set.indicator (currentLowerRectangle (ReferenceInitializationRun.uninformed q.1) a)
                (fun _ : Current p => (1 : ℝ)))
              (GeneratedBootstrapRoundLaw.currentLaw p) :=
            (integrable_const (1 : ℝ)).indicator
              (currentLowerRectangle_measurable
                (ReferenceInitializationRun.uninformed q.1) a)
          have hLower := integral_mono hLowerInt hsection hLowerPoint
          have hMass := currentLowerRectangle_real
            (p := p) (ReferenceInitializationRun.uninformed q.1) a
          rw [hkernelEq, hchi1]
          calc
            (1 / (16 * (p.K : ℝ)) : ℝ) ≤
                (∫ z : Current p,
                  Set.indicator (currentLowerRectangle (ReferenceInitializationRun.uninformed q.1) a)
                    (fun _ => (1 : ℝ)) z
                  ∂GeneratedBootstrapRoundLaw.currentLaw p) := by
                    calc
                      (1 / (16 * (p.K : ℝ)) : ℝ) ≤
                          (GeneratedBootstrapRoundLaw.currentLaw p).real
                            (currentLowerRectangle (ReferenceInitializationRun.uninformed q.1) a) := by
                        rw [hMass]
                        exact hmassLower
                      _ = _ := (integral_indicator_one
                        (μ := GeneratedBootstrapRoundLaw.currentLaw p)
                        (currentLowerRectangle_measurable
                          (ReferenceInitializationRun.uninformed q.1) a)).symm
            _ ≤ ∫ z : Current p, snapshotDownPositive ids rewards s t q z.1 z.2 a
                ∂GeneratedBootstrapRoundLaw.currentLaw p := hLower

/-! ## Actual filtration identity and monitor block accounting -/

theorem actual_downPositive_condExp_identity (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (a : Fin p.K) :
    condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p)
        (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a)) =ᵐ[GeneratedBootstrapRoundLaw.originalLaw p]
      GeneratedBootstrapFiltration.conditionalKernelValue p ids rewards C_star C_h eta s t
        (downPositiveCurrentTest ids rewards s t a) := by
  have hbound : ∀ z, |downPositiveCurrentTest ids rewards s t a z| ≤ 1 := by
    intro z
    have hz := downPositiveCurrentTest_unit_bounds ids rewards s t a z
    exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  exact GeneratedBootstrapFiltration.actual_condExp_identity p ids rewards C_star C_h eta s t ht
    (downPositiveCurrentTest ids rewards s t a)
    (measurable_downPositiveCurrentTest ids rewards s t a) 1 (by norm_num) hbound

theorem actual_downPositive_condExp_upper (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (a : Fin p.K) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p)
        (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a)) e ≤
        rewardSupport rewards t a / (p.K : ℝ) := by
  have hce := actual_downPositive_condExp_identity ids rewards C_star C_h eta s t ht a
  filter_upwards [hce] with e he
  rw [he]
  change GeneratedBootstrapFiltration.conditionalKernel p
      (downPositiveCurrentTest ids rewards s t a)
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) ≤ _
  exact (conditionalKernel_bounds ids rewards s t a
    (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e)).2.1

theorem actual_downPositive_condExp_lower_on_allInactive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (a : Fin p.K) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      processedAllInactive (GeneratedBootstrapRoundLaw.descriptor p ids rewards
        C_star C_h eta s t e) = true →
      rewardSupport rewards t a / (16 * (p.K : ℝ)) ≤
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p)
          (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
            (downPositiveCurrentTest ids rewards s t a)) e := by
  have hce := actual_downPositive_condExp_identity ids rewards C_star C_h eta s t ht a
  filter_upwards [hce] with e he hguard
  rw [he]
  cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e with
  | none => simp [processedAllInactive, hd] at hguard
  | some q =>
      have hinactive : descriptorAllInactive q := by
        exact of_decide_eq_true (by simpa [processedAllInactive, hd] using hguard)
      simpa [GeneratedBootstrapFiltration.conditionalKernelValue, hd] using
        (conditionalKernel_bounds ids rewards s t a (some q)).2.2 q rfl hinactive

private theorem snapshotDownPositive_eq_downArm_of_reconstruction
    (s : Fin (n_boot p)) (t : Fin p.T)
    (source : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (profile : PrivateSourceStreams.BlockDrawProfile p)
    (target : Fin p.K) (st : BootstrapPhysicalBlock.State p)
    (hprofile : profile = BootstrapPhysicalInput.currentBlockDrawProfile p
      (ReferenceInitializationRun.nextBlock b h) b.numerators b.weight_ge_one
      source.coordinates)
    (htarget : target = (ReferenceInitializationRun.physical source b h).target)
    (hstate : st = BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical source b h) t.val)
    (a : Fin p.K) :
    snapshotDownPositive source.ids source.rewards s t
      (b, (profile, (target, st)))
      (BootstrapModeService.roundCoordinates p t source.row)
      (fun i => BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates i t) a =
      if ReferenceInitializationRun.downArm source b h t = some a then 1 else 0 := by
  subst st
  subst target
  rw [hprofile]
  let profileActual := BootstrapPhysicalInput.currentBlockDrawProfile p
    (ReferenceInitializationRun.nextBlock b h) b.numerators b.weight_ge_one source.coordinates
  let base := descriptorBaseInput source.ids source.rewards s
    (b, (profileActual, ((ReferenceInitializationRun.physical source b h).target,
      BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source b h) t.val)))
  let actual := ReferenceInitializationRun.physical source b h
  let hr := BootstrapModeService.roundCoordinates p t source.row
  let v : BootstrapOriginalScalarStep.OriginalScalarVector p :=
    fun i => BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates i t
  let y := BootstrapModeService.currentInputOf base t hr
    (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars base v)
  have hslot : BootstrapPhysicalBlock.slot y t =
      BootstrapPhysicalBlock.slot actual t := by
    simp [y, base, actual, BootstrapPhysicalBlock.slot,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapModeService.roundCoordinates,
      hr, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput]
  have htuple : BootstrapPhysicalBlock.tuple y t =
      BootstrapPhysicalBlock.tuple actual t := by
    simp [y, base, actual, BootstrapPhysicalBlock.tuple,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapModeService.roundCoordinates, hr, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput]
  have htarget' : base.target = actual.target := by
    simp [base, actual, descriptorBaseInput]
  have hforward : BootstrapPhysicalBlock.forwardProduct y
      (BootstrapPhysicalBlock.run actual t.val) t =
      BootstrapPhysicalBlock.forwardProduct actual
        (BootstrapPhysicalBlock.run actual t.val) t := by
    simp [BootstrapPhysicalBlock.forwardProduct, y, base, actual,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapModeService.roundCoordinates, hr, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput]
  have huniform : y.uniform (coordinator p.two_le_m) t =
      actual.uniform (coordinator p.two_le_m) t := by
    simp [y, base, actual, descriptorBaseInput,
      BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.uniformArmMap,
      BootstrapPhysicalInput.playerRoundScalarAt, v, ReferenceInitializationRun.physical]
  have hcoordAvoid : y.coordinatorAvoid t = actual.coordinatorAvoid t := by
    simp [y, base, actual, descriptorBaseInput,
      BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.targetArmMap,
      BootstrapPhysicalInput.playerRoundScalarAt, v, ReferenceInitializationRun.physical]
  have hrewards : y.rewards = actual.rewards := by
    simp [y, base, actual, descriptorBaseInput,
      BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
      BootstrapPhysicalInput.blockInput, ReferenceInitializationRun.physical]
  have htargetY : y.target = actual.target := by
    simpa [y, BootstrapModeService.currentInputOf, BootstrapModeService.currentInput] using htarget'
  have hactions : BootstrapPhysicalBlock.actions y
      (BootstrapPhysicalBlock.run actual t.val) t =
      BootstrapPhysicalBlock.actions actual (BootstrapPhysicalBlock.run actual t.val) t := by
    funext i
    by_cases hc : i = coordinator p.two_le_m
    · subst i
      rw [BootstrapPhysicalBlock.actions_coordinator, BootstrapPhysicalBlock.actions_coordinator]
      unfold BootstrapPhysicalBlock.coordinatorAction
      rw [hslot]
      by_cases hs : BootstrapPhysicalBlock.slot actual t = dataSlot
      · simp only [hs, ↓reduceIte]
        by_cases hmY : (BootstrapPhysicalBlock.run actual t.val).mode = .multicast ∧
            BootstrapPhysicalBlock.forwardProduct y
              (BootstrapPhysicalBlock.run actual t.val) t = 1
        · have hmA : (BootstrapPhysicalBlock.run actual t.val).mode = .multicast ∧
              BootstrapPhysicalBlock.forwardProduct actual
                (BootstrapPhysicalBlock.run actual t.val) t = 1 := by
            simpa [hforward] using hmY
          simp [hmY, hmA, hcoordAvoid]
        · have hmA : ¬ ((BootstrapPhysicalBlock.run actual t.val).mode = .multicast ∧
              BootstrapPhysicalBlock.forwardProduct actual
                (BootstrapPhysicalBlock.run actual t.val) t = 1) := by
            simpa [hforward] using hmY
          simp [hmY, hmA, htargetY]
      · simp only [hs, ↓reduceIte]
        by_cases hd : BootstrapPhysicalBlock.slot actual t = downSlot
        · simp [hd, htuple]
        · simp [hd, huniform]
    · have hneq : ¬ i = coordinator p.two_le_m := hc
      rw [← ActiveRoundActions.followerPlayer_followerIndex p.two_le_m i hneq]
      rw [BootstrapPhysicalBlock.actions_follower, BootstrapPhysicalBlock.actions_follower]
      simp [BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.uninformedAction,
        BootstrapPhysicalBlock.unoccupiedAction, BootstrapPhysicalBlock.slot,
        BootstrapPhysicalBlock.pilot, BootstrapPhysicalBlock.tuple,
        BootstrapPhysicalBlock.selected, BootstrapPhysicalBlock.initialUpBit,
        y, base, actual, profileActual, descriptorBaseInput,
        BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
        BootstrapModeService.roundCoordinates,
        BootstrapPhysicalInput.blockInput,
        BootstrapPhysicalInput.activityMap, BootstrapPhysicalInput.heldMap,
        BootstrapPhysicalInput.privateIDMap, BootstrapPhysicalInput.uniformArmMap,
        BootstrapPhysicalInput.currentBlockDrawProfileMap,
        BootstrapPhysicalInput.currentBlockDrawProfile,
        BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars,
        BootstrapPhysicalInput.playerRoundScalarAt, v, hr,
        ReferenceInitializationRun.physical]
  have hfeedback : BootstrapPhysicalBlock.feedback y
      (BootstrapPhysicalBlock.run actual t.val) t (coordinator p.two_le_m) =
      BootstrapPhysicalBlock.feedback actual
        (BootstrapPhysicalBlock.run actual t.val) t (coordinator p.two_le_m) := by
    simp [BootstrapPhysicalBlock.feedback, hactions, hrewards]
  change (if BootstrapPhysicalBlock.slot y t = downSlot ∧
      BootstrapPhysicalBlock.actions y (BootstrapPhysicalBlock.run actual t.val) t
        (coordinator p.two_le_m) = a ∧
      0 < BootstrapPhysicalBlock.feedback y (BootstrapPhysicalBlock.run actual t.val)
        t (coordinator p.two_le_m) then (1 : ℝ) else 0) =
    if ReferenceInitializationRun.downArm source b h t = some a then 1 else 0
  by_cases hd : BootstrapPhysicalBlock.slot actual t = downSlot
  · rw [hslot, hactions, BootstrapPhysicalBlock.actions_coordinator, hfeedback]
    rw [BootstrapPhysicalBlock.coordinatorAction_down actual
      (BootstrapPhysicalBlock.run actual t.val) t hd]
    simp [ReferenceInitializationRun.downArm, actual, hd, and_comm]
  · rw [hslot]
    simp [ReferenceInitializationRun.downArm, actual, hd]

private theorem downArm_indicator_eq_actualPhysical
    (source : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (t : Fin p.T) (a : Fin p.K) :
    (if ReferenceInitializationRun.downArm source b h t = some a then (1 : ℝ) else 0) =
      (if BootstrapPhysicalBlock.slot (ReferenceInitializationRun.physical source b h) t = downSlot ∧
          BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical source b h)
            (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source b h) t.val)
            t (coordinator p.two_le_m) = a ∧
          0 < BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical source b h)
            (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source b h) t.val)
            t (coordinator p.two_le_m)
        then (1 : ℝ) else 0) := by
  by_cases hd : BootstrapPhysicalBlock.slot
      (ReferenceInitializationRun.physical source b h) t = downSlot
  · have hcoord := BootstrapPhysicalBlock.coordinatorAction_down
      (ReferenceInitializationRun.physical source b h)
      (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source b h) t.val)
      t hd
    simp [ReferenceInitializationRun.downArm, hd,
      BootstrapPhysicalBlock.actions_coordinator, hcoord, and_comm]
  · simp [ReferenceInitializationRun.downArm, hd]

/-- Pointwise reconstruction of the actual generated current-round test.
The source boundary/profile/target/pre-choice state are recovered from the
accepted descriptor theorem. The two returned indicators are respectively
the physical DOWN-positive event and the credited counter event read by the
bootstrap monitor. -/
theorem actual_downPositive_descriptor_bridge
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (a : Fin p.K)
    (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p)
    (target : Fin p.K) (st : BootstrapPhysicalBlock.State p)
    (hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
      some (b, (profile, (target, st)))) :
    ∃ h : b.completed < n_boot p,
      ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b ∧
      b.crossing = none ∧
      profile = BootstrapPhysicalInput.currentBlockDrawProfile p
        (ReferenceInitializationRun.nextBlock b h) b.numerators b.weight_ge_one
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates ∧
      target = (ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h).target ∧
      st = BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h) t.val ∧
      GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a) e =
        (if BootstrapPhysicalBlock.slot (ReferenceInitializationRun.physical
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h) t = downSlot ∧
          BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h)
            (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h) t.val)
            t (coordinator p.two_le_m) = a ∧
          0 < BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h)
            (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h) t.val)
            t (coordinator p.two_le_m)
        then 1 else 0) ∧
      GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a) e =
        (if ReferenceInitializationRun.downArm
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h t = some a
        then 1 else 0) := by
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  have hrec := (GeneratedBootstrapRoundLaw.descriptor_eq_some_iff
    (p := p) ids rewards C_star C_h eta s t e b profile target st).mp hd
  change boundary = b ∧ boundary.crossing = none ∧
    ∃ h : boundary.completed < n_boot p,
      BootstrapPhysicalInput.currentBlockDrawProfile p
        (ReferenceInitializationRun.nextBlock boundary h) boundary.numerators
        boundary.weight_ge_one source.coordinates = profile ∧
      (ReferenceInitializationRun.physical source boundary h).target = target ∧
      BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source boundary h)
        t.val = st at hrec
  rcases hrec with ⟨hb, hcross, h, hprofile, htarget, hstate⟩
  subst b
  refine ⟨h, rfl, hcross, hprofile.symm, htarget.symm, hstate.symm, ?_, ?_⟩
  · have htest :
        GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a) e =
        snapshotDownPositive ids rewards s t (boundary, (profile, (target, st)))
          (BootstrapModeService.roundCoordinates p t source.row)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates i t) a := by
      simp [source, GeneratedBootstrapFiltration.testValue, hd,
        GeneratedBootstrapRoundLaw.current, downPositiveCurrentTest,
        GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]
    rw [htest]
    calc
      snapshotDownPositive ids rewards s t (boundary, (profile, (target, st)))
          (BootstrapModeService.roundCoordinates p t source.row)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates i t) a =
        (if ReferenceInitializationRun.downArm source boundary h t = some a then
          (1 : ℝ) else 0) := by
            simpa [source, GeneratedBootstrapRoundLaw.input,
              ReferenceInitializationMeasurability.inputOfCoordinates] using
              snapshotDownPositive_eq_downArm_of_reconstruction s t source boundary h
                profile target st hprofile.symm htarget.symm hstate.symm a
      _ = (if BootstrapPhysicalBlock.slot
            (ReferenceInitializationRun.physical source boundary h) t = downSlot ∧
              BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical source boundary h)
                (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source boundary h)
                  t.val) t (coordinator p.two_le_m) = a ∧
              0 < BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical source boundary h)
                (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source boundary h)
                  t.val) t (coordinator p.two_le_m)
          then 1 else 0) := by
            exact downArm_indicator_eq_actualPhysical source boundary h t a
  · have htest :
        GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (downPositiveCurrentTest ids rewards s t a) e =
        snapshotDownPositive ids rewards s t (boundary, (profile, (target, st)))
          (BootstrapModeService.roundCoordinates p t source.row)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates i t) a := by
      simp [source, GeneratedBootstrapFiltration.testValue, hd,
        GeneratedBootstrapRoundLaw.current, downPositiveCurrentTest,
        GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]
    rw [htest]
    exact snapshotDownPositive_eq_downArm_of_reconstruction s t source boundary h
      profile target st hprofile.symm htarget.symm hstate.symm a

private theorem calendar_sum_eq_blockRound (s : Fin (n_boot p))
    (f : Fin p.T → ℕ) :
    (∑ t ∈ calendarBlock p s, f t) =
      ∑ u : Fin (blockLength p s), f (blockRound p s u) := by
  classical
  symm
  apply Finset.sum_bij (fun u _ => blockRound p s u)
  · intro u hu
    exact blockRound_mem p s u
  · intro u hu v hv huv
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val huv)
  · intro t ht
    obtain ⟨u, hu⟩ := exists_blockRound p s t ht
    exact ⟨u, Finset.mem_univ _, hu⟩
  · intro u hu
    rfl

/-- The whole just-finished physical block, including a block whose final
update triggers launch, is exactly the count consumed by the accepted monitor. -/
theorem downArm_calendar_sum_eq_historyBlockCount
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (a : Fin p.K) :
    (∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
      if ReferenceInitializationRun.downArm x b h t = some a then 1 else 0) =
      GeneratedBootstrapMonitor.historyBlockCount x
        (ReferenceInitializationRun.elapsed p (b.completed + 1))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        (ReferenceInitializationRun.extendedHistory x b h (coordinator p.two_le_m))
        (ReferenceInitializationRun.nextBlock b h)
        (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b h]) a := by
  rw [calendar_sum_eq_blockRound (p := p) (ReferenceInitializationRun.nextBlock b h)]
  unfold GeneratedBootstrapMonitor.historyBlockCount
  apply Finset.sum_congr rfl
  intro u hu
  have hEnd : blockEnd p (ReferenceInitializationRun.nextBlock b h) ≤
      ReferenceInitializationRun.elapsed p (b.completed + 1) := by
    rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b h]
  have hidx : (⟨(blockEmbed u).val,
      Nat.lt_of_lt_of_le (blockEmbed u).isLt hEnd⟩ :
        Fin (ReferenceInitializationRun.elapsed p (b.completed + 1))) = blockEmbed u := by
    apply Fin.ext
    rfl
  rw [hidx, ReferenceInitializationRun.downArm_eq_generatedDownArm x b h u]

theorem downArm_calendar_sum_bounds
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (a : Fin p.K) :
    0 ≤ (∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
      if ReferenceInitializationRun.downArm x b h t = some a then 1 else 0) ∧
    (∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
      if ReferenceInitializationRun.downArm x b h t = some a then 1 else 0) ≤ B_boot p := by
  rw [downArm_calendar_sum_eq_historyBlockCount]
  have hcount := GeneratedBootstrapMonitor.historyBlockCount_bounds x
    (ReferenceInitializationRun.elapsed p (b.completed + 1))
    (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
    (ReferenceInitializationRun.extendedHistory x b h (coordinator p.two_le_m))
    (ReferenceInitializationRun.nextBlock b h)
    (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b h]) a
  have hlen : blockLength p (ReferenceInitializationRun.nextBlock b h) ≤ B_boot p := by
    rw [blockLength_eq_calendarBlock_card]
    exact BootstrapDimensions.calendarBlock_card_le_B_boot p
      (ReferenceInitializationRun.nextBlock b h)
  exact ⟨hcount.1, hcount.2.trans hlen⟩

end Bandits.Support.GeneratedDownConditionalMean

end
