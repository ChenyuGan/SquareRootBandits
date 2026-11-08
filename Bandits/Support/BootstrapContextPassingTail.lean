/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapBlockCausality
public import Bandits.Support.BootstrapContextPrefixOperation
public import Bandits.Support.BootstrapPrivateIDFibers
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.FalseForwardBaseTail
public import Bandits.Support.FalseForwardContextBound
public import Bandits.Support.FalseRowSliceFactorization
public import Bandits.Support.ForwardPrefixRareTail
public import Bandits.Support.ForwardPrefixSlice
public import Bandits.Support.OrderedTupleSampler
public import Bandits.Support.PublicDiscreteDraws

/-!
# Actual context passing probabilities and false-row publication tails

The eligible family is the actual two-player context projection of
`BootstrapContextPrefixOperation`. Its joint measurability is proved from the
finite state recursion and the literal ID, learning-slot, true-forward, and
local-round coordinates. False-row passing probabilities integrate the
original coordinator/focal scalar pair, and the public statistic uses the
accepted false-factor split of the unchanged complete published output.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-357` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,75-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators Classical

namespace Bandits.Support.BootstrapContextPassingTail

variable {p : ConstructorDimensions.Parameters}

abbrev Context (p : ConstructorDimensions.Parameters) :=
  FalseForwardContextBound.Context p

abbrev LocalRoundPair (c : Context p) :=
  BootstrapContextPrefixOperation.LocalRoundPair c

abbrev ContextTime (c : Context p) :=
  BootstrapContextPrefixOperation.ContextTime c

private def contextModeEquiv : Bool ≃ BootstrapPhysicalBlock.Mode :=
  { toFun := fun b => if b then .multicast else .discover
    invFun := fun mode => if mode = .multicast then true else false
    left_inv := by intro b; cases b <;> rfl
    right_inv := by intro mode; cases mode <;> rfl }

private instance contextModeFintype : Fintype BootstrapPhysicalBlock.Mode :=
  Fintype.ofEquiv Bool contextModeEquiv

private theorem contextStateCoordinates_injective :
    Function.Injective (BootstrapBlockCausality.stateCoordinates (p := p)) := by
  intro x y h
  cases x
  cases y
  simp only [BootstrapBlockCausality.stateCoordinates, Prod.mk.injEq] at h
  rcases h with ⟨hlist, hmode, hpositive⟩
  cases hlist
  cases hmode
  cases hpositive
  rfl

private theorem contextState_finite : Finite (BootstrapPhysicalBlock.State p) := by
  exact Finite.of_injective
    (fun st : BootstrapPhysicalBlock.State p =>
      (st.list, st.mode, st.positives))
    (by
      intro x y h
      cases x
      cases y
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨hlist, hmode, hpositive⟩
      cases hlist
      cases hmode
      cases hpositive
      rfl)

private instance contextStateFiniteInstance : Finite (BootstrapPhysicalBlock.State p) :=
  contextState_finite

private instance contextStateFintype : Fintype (BootstrapPhysicalBlock.State p) :=
  Fintype.ofFinite _

private instance contextStateMeasurableSingleton :
    MeasurableSingletonClass (BootstrapPhysicalBlock.State p) where
  measurableSet_singleton st := by
    change ∃ q, MeasurableSet q ∧
      BootstrapBlockCausality.stateCoordinates (p := p) ⁻¹' q = {st}
    refine ⟨{BootstrapBlockCausality.stateCoordinates st},
      measurableSet_singleton _, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact contextStateCoordinates_injective h
    · intro h
      exact congrArg (BootstrapBlockCausality.stateCoordinates (p := p)) h

private theorem measurable_decide_ne {α : Type*} [MeasurableSpace α]
    (f : α → Fin p.K) (hf : Measurable f) (a : Fin p.K) :
    Measurable (fun x => decide (f x ≠ a)) :=
  (measurable_of_finite (fun b : Fin p.K => decide (b ≠ a))).comp hf

private theorem measurable_forbiddenArmValue (a : Fin p.K) :
    Measurable (fun x : BootstrapPrivateRoundStreams.Scalar =>
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p a x).val) := by
  exact (Measurable.of_discrete :
    Measurable (fun b : BootstrapPrivateRoundStreams.ArmAvoiding p a => b.val)).comp
      (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p a)

private theorem measurable_idBit (c : Context p) (u : Fin (A_id p))
    (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c => z.1.1 u t.1) := by
  exact (measurable_pi_apply t.1).comp
    ((measurable_pi_apply u).comp (measurable_fst.comp measurable_fst))

private theorem measurable_learningSlice (c : Context p) (v : Fin (M p))
    (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      ((z.1.2.1 v) t.1).1) := by
  exact (measurable_fst.comp (ContinuousLearningRows.measurable_controlAt t.1)).comp
    ((measurable_pi_apply v).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))

private theorem measurable_learningSlot (c : Context p) (v : Fin (M p))
    (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      PublicDiscreteDraws.slotDraw (((z.1.2.1 v) t.1).1)) :=
  (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp
    (measurable_learningSlice c v t)

private theorem measurable_trueForwardBit (c : Context p) (u : Fin (A_id p))
    (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      z.1.2.2 u t.1) := by
  exact (measurable_pi_apply t.1).comp
    ((measurable_pi_apply u).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))

private theorem measurable_focalAction_joint (c : Context p)
    (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.focalAction c z.1 u z.2 t) := by
  have hid := measurable_idBit c u t
  have hdraw : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (BootstrapContextPrefixOperation.heldArm c) (z.2.2 t)).val) :=
    measurable_forbiddenArmValue (p := p) _ |>.comp
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hset : MeasurableSet {z : FalseFactorBase p × LocalRoundPair c |
      z.1.1 u t.1} := hid (measurableSet_singleton true)
  have hzero : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      if z.1.1 u t.1 then (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (BootstrapContextPrefixOperation.heldArm c) (z.2.2 t)).val
      else BootstrapContextPrefixOperation.heldArm c) :=
    Measurable.ite hset hdraw measurable_const
  simpa [BootstrapContextPrefixOperation.focalAction] using hzero

private theorem measurable_trueForwardProduct_joint (c : Context p)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.trueForwardProduct c z.1 st t) := by
  classical
  unfold BootstrapContextPrefixOperation.trueForwardProduct
  apply Finset.measurable_fun_prod
  intro u hu
  exact (measurable_of_finite fun b : Bool => if b then 1 else 0).comp
    (measurable_trueForwardBit c u t)

private theorem measurable_coordinatorAction_at_state_joint (c : Context p)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.coordinatorAction c z.1 z.2 st t) := by
  let slot : FalseFactorBase p × LocalRoundPair c → PublicDiscreteDraws.Slot :=
    fun z => PublicDiscreteDraws.slotDraw (((z.1.2.1
      (BootstrapContextPrefixOperation.trueRowIndex c)) t.1).1)
  have hslot : Measurable slot := measurable_learningSlot c _ t
  let data : Set (FalseFactorBase p × LocalRoundPair c) := {z | slot z = dataSlot}
  let down : Set (FalseFactorBase p × LocalRoundPair c) := {z | slot z = downSlot}
  have hdata : MeasurableSet data := hslot (measurableSet_singleton dataSlot)
  have hdown : MeasurableSet down := hslot (measurableSet_singleton downSlot)
  let forward : FalseFactorBase p × LocalRoundPair c → ℕ :=
    fun z => BootstrapContextPrefixOperation.trueForwardProduct c z.1 st t
  have hforward : Measurable forward := measurable_trueForwardProduct_joint c st t
  let multicast : Set (FalseFactorBase p × LocalRoundPair c) :=
    if st.mode = .multicast then {z | forward z = 1} else ∅
  have hmulticast : MeasurableSet multicast := by
    by_cases hm : st.mode = .multicast
    · simp only [multicast, hm, ↓reduceIte]
      change MeasurableSet (forward ⁻¹' ({1} : Set ℕ))
      exact hforward (measurableSet_singleton 1)
    · simp [multicast, hm]
  let coordDraw : FalseFactorBase p × LocalRoundPair c → Fin p.K :=
    fun z => (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
      (BootstrapContextPrefixOperation.targetArm c) (z.2.1 t)).val
  have hcoordDraw : Measurable coordDraw :=
    measurable_forbiddenArmValue (p := p) _ |>.comp
      ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))
  let tupleDraw : FalseFactorBase p × LocalRoundPair c → Fin p.K := fun z =>
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (((z.1.2.1 (BootstrapContextPrefixOperation.trueRowIndex c)) t.1).1)).val
      (ActiveRoundActions.coordinator p.two_le_m)
  have htupleInput : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      (((z.1.2.1 (BootstrapContextPrefixOperation.trueRowIndex c)) t.1).1)) :=
    measurable_learningSlice c _ t
  have htupleDraw : Measurable tupleDraw :=
    ((measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp
        (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))).comp htupleInput
  let dataAction : FalseFactorBase p × LocalRoundPair c → Fin p.K := fun z =>
    if z ∈ multicast then coordDraw z else BootstrapContextPrefixOperation.targetArm c
  have hdataAction : Measurable dataAction := Measurable.ite hmulticast hcoordDraw measurable_const
  let nondataAction : FalseFactorBase p × LocalRoundPair c → Fin p.K := fun z =>
    if z ∈ down then tupleDraw z else
      BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.2.1 t)
  have hfull : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapPrivateRoundStreams.fullArmScalarDraw p (z.2.1 t)) :=
    (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
      ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))
  have hnondata : Measurable nondataAction := Measurable.ite hdown htupleDraw hfull
  have hresult : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      if z ∈ data then dataAction z else nondataAction z) :=
    Measurable.ite hdata hdataAction hnondata
  simpa [BootstrapContextPrefixOperation.coordinatorAction, slot, forward,
    multicast, data, down, coordDraw, tupleDraw, dataAction, nondataAction,
    Set.mem_setOf_eq] using hresult

private theorem measurable_coordinatorAction_joint (c : Context p)
    (t : ContextTime c) :
    Measurable (fun z : BootstrapPhysicalBlock.State p ×
        (FalseFactorBase p × LocalRoundPair c) =>
      BootstrapContextPrefixOperation.coordinatorAction c z.2.1 z.2.2 z.1 t) := by
  exact measurable_from_prod_countable_right
    (fun st => measurable_coordinatorAction_at_state_joint c st t)

private theorem measurable_stateCoordinates {α : Type*} [MeasurableSpace α]
    (f : α → BootstrapPhysicalBlock.State p) (hf : Measurable f) :
    Measurable (BootstrapBlockCausality.stateCoordinates (p := p) ∘ f) :=
  (measurable_comap_iff).mp hf

private theorem measurable_stateStep_joint (c : Context p) (u : Fin (A_id p))
    (t : ContextTime c) :
    Measurable (fun z : (FalseFactorBase p × LocalRoundPair c) ×
        BootstrapPhysicalBlock.State p =>
      BootstrapContextPrefixOperation.stateStep c z.1.1 u z.1.2 z.2 t) := by
  classical
  let source := (FalseFactorBase p × LocalRoundPair c) × BootstrapPhysicalBlock.State p
  let idColumn : source → Fin (A_id p) → Bool := fun z u' => z.1.1.1 u' t.1
  have hidColumn : Measurable idColumn := by
    apply measurable_pi_iff.mpr
    intro u'
    exact (measurable_pi_apply t.1).comp
      ((measurable_pi_apply u').comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  let coords : source →
      Finset (Fin (A_id p)) × (BootstrapPhysicalBlock.Mode × Finset (Fin p.T)) :=
    fun z => BootstrapBlockCausality.stateCoordinates z.2
  have hcoords : Measurable coords :=
    measurable_stateCoordinates (fun z : source => z.2) (measurable_snd)
  let slot : source → PublicDiscreteDraws.Slot := fun z =>
    PublicDiscreteDraws.slotDraw (((z.1.1.2.1
      (BootstrapContextPrefixOperation.trueRowIndex c)) t.1).1)
  have hslot : Measurable slot := by
    exact (measurable_learningSlot c _ t).comp measurable_fst
  let avoid : source → Bool := fun z =>
    decide (BootstrapContextPrefixOperation.focalAction c z.1.1 u z.1.2 t ≠
      BootstrapContextPrefixOperation.targetArm c)
  have havoid : Measurable avoid :=
    measurable_decide_ne (fun z : source =>
      BootstrapContextPrefixOperation.focalAction c z.1.1 u z.1.2 t)
      ((measurable_focalAction_joint c u t).comp measurable_fst)
      (BootstrapContextPrefixOperation.targetArm c)
  let input : source →
      (Fin (A_id p) → Bool) ×
        (Finset (Fin (A_id p)) × (BootstrapPhysicalBlock.Mode × Finset (Fin p.T))) ×
        (PublicDiscreteDraws.Slot × Bool) :=
    fun z => (idColumn z, coords z, (slot z, avoid z))
  have hinput : Measurable input := by
    exact hidColumn.prodMk (hcoords.prodMk (hslot.prodMk havoid))
  let update : (Fin (A_id p) → Bool) ×
        (Finset (Fin (A_id p)) × (BootstrapPhysicalBlock.Mode × Finset (Fin p.T))) ×
        (PublicDiscreteDraws.Slot × Bool) → BootstrapPhysicalBlock.State p :=
    fun q =>
      let st : BootstrapPhysicalBlock.State p :=
        ⟨q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩
      if st.mode = .discover ∧ q.2.2.1 = dataSlot ∧
          BootstrapContextPrefixOperation.targetSupport c t = true ∧ q.2.2.2 = true then
        let kept := st.list.filter fun v => q.1 v = true
        ⟨kept, if kept.card ≤ L0 p then .multicast else .discover,
          insert t.1 st.positives⟩
      else st
  have hupdate : Measurable update := by
    apply (measurable_comap_iff).2
    exact measurable_of_finite _
  have hrepr : ∀ z : source,
      BootstrapContextPrefixOperation.stateStep c z.1.1 u z.1.2 z.2 t = update (input z) := by
    intro z
    rfl
  have hfun : (fun z : source =>
      BootstrapContextPrefixOperation.stateStep c z.1.1 u z.1.2 z.2 t) =
      update ∘ input := funext hrepr
  rw [hfun]
  exact hupdate.comp hinput

theorem measurable_stateTrace_joint (c : Context p) (u : Fin (A_id p)) :
    ∀ n, Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      by_cases hn : n < p.T
      · let t : Fin p.T := ⟨n, hn⟩
        by_cases hblock : t ∈ calendarBlock p c.1
        · let bt : ContextTime c := ⟨t, hblock⟩
          have hstep : Measurable (fun z : (FalseFactorBase p × LocalRoundPair c) ×
              BootstrapPhysicalBlock.State p =>
              BootstrapContextPrefixOperation.stateStep c z.1.1 u z.1.2 z.2 bt) :=
            measurable_stateStep_joint c u bt
          have hinput : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
              (z, BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 n)) :=
            measurable_id.prodMk ih
          have htrace : ∀ z : FalseFactorBase p × LocalRoundPair c,
              BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 (n + 1) =
                BootstrapContextPrefixOperation.stateStep c z.1 u z.2
                  (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 n) bt := by
            intro z
            simp [BootstrapContextPrefixOperation.stateTrace, hn, t, hblock, bt]
          rw [show (fun z : FalseFactorBase p × LocalRoundPair c =>
              BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 (n + 1)) =
                (fun z => BootstrapContextPrefixOperation.stateStep c z.1 u z.2
                  (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 n) bt)
                from funext htrace]
          exact hstep.comp hinput
        · simpa [BootstrapContextPrefixOperation.stateTrace, hn, t, hblock] using ih
      · simpa [BootstrapContextPrefixOperation.stateTrace, hn] using ih

private theorem measurable_coordinatorAction_onTrace_joint (c : Context p)
    (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.coordinatorAction c z.1 z.2
        (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 t.1) t) := by
  have htrace := measurable_stateTrace_joint c u t.1
  exact (measurable_coordinatorAction_joint c t).comp
    (htrace.prodMk measurable_id)

private theorem measurable_focalPositive_joint (c : Context p)
    (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.focalPositive c z.1 z.2
        (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 t.1) t) := by
  have hcoord := measurable_coordinatorAction_onTrace_joint c u t
  have htest := measurable_decide_ne
    (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.coordinatorAction c z.1 z.2
        (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 t.1) t)
    hcoord (BootstrapContextPrefixOperation.heldArm c)
  cases hs : BootstrapContextPrefixOperation.heldSupport c t with
  | false =>
      simpa [BootstrapContextPrefixOperation.focalPositive, hs] using
        (measurable_const : Measurable (fun _ : FalseFactorBase p × LocalRoundPair c => false))
  | true =>
      simpa [BootstrapContextPrefixOperation.focalPositive, hs] using htest

theorem measurable_candidateEligibleSet_joint (c : Context p)
    (u : Fin (A_id p)) (v : Fin (M p)) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      BootstrapContextPrefixOperation.candidateEligibleSet c z.1 u z.2 v) := by
  classical
  apply (measurable_finset_iff).2
  intro t
  by_cases hblock : t ∈ calendarBlock p c.1
  · apply measurableSet_setOfPred.mp
    let bt : ContextTime c := ⟨t, hblock⟩
    have hid : Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
        z.1.1 u t) := (measurable_pi_apply t).comp
          ((measurable_pi_apply u).comp (measurable_fst.comp measurable_fst))
    have hslot := measurable_learningSlot c v bt
    have htest := measurable_focalPositive_joint c u bt
    have hIdMeas : MeasurableSet {z : FalseFactorBase p × LocalRoundPair c |
        z.1.1 u t = false} := hid (measurableSet_singleton false)
    have hslotMeas : MeasurableSet {z : FalseFactorBase p × LocalRoundPair c |
        PublicDiscreteDraws.slotDraw (((z.1.2.1 v) t).1) = dataSlot} :=
      hslot (measurableSet_singleton dataSlot)
    have htestSet : MeasurableSet {z : FalseFactorBase p × LocalRoundPair c |
        BootstrapContextPrefixOperation.focalPositive c z.1 z.2
          (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 t) bt = true} :=
      htest (measurableSet_singleton true)
    have heq : {z : FalseFactorBase p × LocalRoundPair c |
        t ∈ BootstrapContextPrefixOperation.candidateEligibleSet c z.1 u z.2 v} =
        ({z | z.1.1 u t = false} ∩
          {z | PublicDiscreteDraws.slotDraw (((z.1.2.1 v) t).1) = dataSlot}) ∩
          {z | BootstrapContextPrefixOperation.focalPositive c z.1 z.2
            (BootstrapContextPrefixOperation.stateTrace c z.1 u z.2 t) bt = true} := by
      ext z
      simp [BootstrapContextPrefixOperation.candidateEligibleSet, hblock, bt,
        and_assoc]
    rw [heq]
    exact (hIdMeas.inter hslotMeas).inter htestSet
  · have heq : {z : FalseFactorBase p × LocalRoundPair c |
        t ∈ BootstrapContextPrefixOperation.candidateEligibleSet c z.1 u z.2 v} = ∅ := by
      ext z
      simp [BootstrapContextPrefixOperation.candidateEligibleSet, hblock]
    apply measurableSet_setOfPred.mp
    rw [heq]
    exact MeasurableSet.empty

theorem measurable_candidateEligibleListFunction_choose_joint
    (c : Context p) (u : Fin (A_id p)) (v : Fin (M p)) :
    Measurable (fun z : FalseFactorBase p × LocalRoundPair c =>
      (BootstrapContextPrefixOperation.candidateEligibleListFunction
        c z.1 u v).choose z.2) := by
  simpa [BootstrapContextPrefixOperation.candidateEligibleListFunction] using
    measurable_candidateEligibleSet_joint c u v

@[expose] def localRoundPairLaw (c : Context p) : Measure (LocalRoundPair c) :=
  BootstrapPrivateIDFibers.roundPairLaw p c.1

instance localRoundPairLaw_probability (c : Context p) :
    IsProbabilityMeasure (localRoundPairLaw c) := by
  dsimp [localRoundPairLaw, LocalRoundPair,
    BootstrapContextPrefixOperation.LocalRoundPair,
    BootstrapContextPrefixOperation.RoundPair]
  infer_instance

@[expose] def actualEligibleFamily (c : Context p) :
    FalseForwardBaseTail.BaseMeasurableEligibleFamily p c.1 (LocalRoundPair c) :=
  fun label =>
    { choose := fun z =>
        (BootstrapContextPrefixOperation.candidateEligibleListFunction
          c z.1 label.2 label.1).choose z.2
      choose_subset := fun z =>
        (BootstrapContextPrefixOperation.candidateEligibleListFunction
          c z.1 label.2 label.1).choose_subset z.2
      measurable_choose := measurable_candidateEligibleListFunction_choose_joint
        c label.2 label.1 }

theorem candidateEligibleTimes_nodup (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (v : Fin (M p)) (rounds : LocalRoundPair c) :
    (BootstrapContextPrefixOperation.candidateEligibleTimes c base u v rounds).Nodup :=
  ForwardPrefixSlice.chronologicalEligibleTimes_nodup
    (BootstrapContextPrefixOperation.candidateEligibleListFunction c base u v) rounds

theorem candidatePasses_iff_firstQuota (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c)
    (v : FalseRow p (BootstrapContextPrefixOperation.trueRowIndex c))
    (falseRows : FalseForwardRows p (BootstrapContextPrefixOperation.trueRowIndex c)) :
    BootstrapContextPrefixOperation.candidatePasses c base u rounds v falseRows ↔
      q_dec p ≤ (BootstrapContextPrefixOperation.candidateEligibleTimes
        c base u v.1 rounds).length ∧
        ∀ t ∈ (BootstrapContextPrefixOperation.candidateEligibleTimes
          c base u v.1 rounds).take (q_dec p), falseRows v u t = true := by
  rw [BootstrapContextPrefixOperation.candidatePasses,
    ForwardPrefixSlice.privatePrefixPasses_iff_first_q]
  rfl

@[expose] def singletonFalseForwardRows (c : Context p)
    (label : SliceLabel p) (hfalse : label.1 ≠
      BootstrapContextPrefixOperation.trueRowIndex c) (slice : ForwardSlice p) :
    FalseForwardRows p (BootstrapContextPrefixOperation.trueRowIndex c) :=
  fun v u t => if v.1 = label.1 ∧ u = label.2 then slice t else false

@[expose] def contextPassSet (c : Context p) (base : FalseFactorBase p)
    (label : SliceLabel p) (hfalse : label.1 ≠
      BootstrapContextPrefixOperation.trueRowIndex c) (slice : ForwardSlice p) :
    Set (LocalRoundPair c) :=
  {rounds | BootstrapContextPrefixOperation.candidatePasses c base label.2 rounds
    ⟨label.1, hfalse⟩ (singletonFalseForwardRows c label hfalse slice)}

theorem contextPassSet_eq_privatePrefixPassSet (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c)
    (slice : ForwardSlice p) :
    contextPassSet c base label hfalse slice =
      ForwardPrefixSlice.privatePrefixPassSet
        (BootstrapContextPrefixOperation.candidateEligibleListFunction
          c base label.2 label.1) slice := by
  ext rounds
  simp [contextPassSet, BootstrapContextPrefixOperation.candidatePasses,
    singletonFalseForwardRows, ForwardPrefixSlice.privatePrefixPassSet]

theorem measurableSet_contextPassSet (c : Context p) (base : FalseFactorBase p)
    (label : SliceLabel p) (hfalse : label.1 ≠
      BootstrapContextPrefixOperation.trueRowIndex c) (slice : ForwardSlice p) :
    MeasurableSet (contextPassSet c base label hfalse slice) := by
  rw [contextPassSet_eq_privatePrefixPassSet]
  exact ForwardPrefixSlice.measurableSet_privatePrefixPassSet _ _

@[expose] noncomputable def contextPassingProbability (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c)
    (slice : ForwardSlice p) : ℝ :=
  ∫ rounds, (contextPassSet c base label hfalse slice).indicator
    (fun _ => (1 : ℝ)) rounds ∂localRoundPairLaw c

theorem contextPassingProbability_eq_integratedPrivatePassing (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c)
    (slice : ForwardSlice p) :
    contextPassingProbability c base label hfalse slice =
      ForwardPrefixSlice.integratedPrivatePassing (localRoundPairLaw c)
        (BootstrapContextPrefixOperation.candidateEligibleListFunction
          c base label.2 label.1) slice := by
  rw [contextPassingProbability, ForwardPrefixSlice.integratedPrivatePassing,
    contextPassSet_eq_privatePrefixPassSet]

theorem contextPassingProbability_mem_unitInterval (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c)
    (slice : ForwardSlice p) :
    contextPassingProbability c base label hfalse slice ∈ Set.Icc (0 : ℝ) 1 := by
  rw [contextPassingProbability_eq_integratedPrivatePassing]
  exact ⟨ForwardPrefixSlice.integratedPrivatePassing_nonneg _ _ _,
    ForwardPrefixSlice.integratedPrivatePassing_le_one _ _ _⟩

private def contextPassSetJoint (c : Context p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    Set ((FalseFactorBase p × ForwardSlice p) × LocalRoundPair c) :=
  {z | BootstrapContextPrefixOperation.candidatePasses c z.1.1 label.2 z.2
    ⟨label.1, hfalse⟩ (singletonFalseForwardRows c label hfalse z.1.2)}

private def contextJointEligibleListFunction (c : Context p) (label : SliceLabel p) :
    ForwardPrefixSlice.EligibleListFunction p c.1
      (FalseFactorBase p × LocalRoundPair c) where
  choose := fun z => BootstrapContextPrefixOperation.candidateEligibleSet c
    z.1 label.2 z.2 label.1
  choose_subset := fun z =>
    (BootstrapContextPrefixOperation.candidateEligibleListFunction
      c z.1 label.2 label.1).choose_subset z.2
  measurable_choose := measurable_candidateEligibleSet_joint c label.2 label.1

private def contextPassCoordinates (c : Context p) :
    ((FalseFactorBase p × ForwardSlice p) × LocalRoundPair c) →
      ((FalseFactorBase p × LocalRoundPair c) × CompletePublicTable.ForwardRow p) :=
  fun z => ((z.1.1, z.2), fun (_ : Fin (A_id p)) (t : Fin p.T) => z.1.2 t)

private theorem measurable_contextPassCoordinates (c : Context p) :
    Measurable (contextPassCoordinates c) := by
  have hprivate : Measurable
      (fun z : (FalseFactorBase p × ForwardSlice p) × LocalRoundPair c =>
        (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hrow : Measurable
      (fun z : (FalseFactorBase p × ForwardSlice p) × LocalRoundPair c =>
        fun (_ : Fin (A_id p)) (t : Fin p.T) => z.1.2 t) := by
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply t).comp (measurable_snd.comp measurable_fst)
  change Measurable (fun z : (FalseFactorBase p × ForwardSlice p) × LocalRoundPair c =>
    ((z.1.1, z.2), fun (_ : Fin (A_id p)) (t : Fin p.T) => z.1.2 t))
  exact hprivate.prodMk hrow

private theorem measurableSet_contextPassSetJoint (c : Context p)
    (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    MeasurableSet (contextPassSetJoint c label hfalse) := by
  classical
  have hset : contextPassSetJoint c label hfalse =
      contextPassCoordinates c ⁻¹'
        ForwardPrefixSlice.jointPrivatePrefixPassSet
          (contextJointEligibleListFunction c label) label.2 := by
    ext z
    simp [contextPassSetJoint, contextPassCoordinates,
      ForwardPrefixSlice.jointPrivatePrefixPassSet,
      contextJointEligibleListFunction,
      BootstrapContextPrefixOperation.candidatePasses,
      BootstrapContextPrefixOperation.candidateEligibleListFunction,
      ForwardPrefixSlice.privatePrefixPasses,
      ForwardPrefixSlice.chronologicalEligibleTimes,
      singletonFalseForwardRows]
  rw [hset]
  exact measurable_contextPassCoordinates c
    (ForwardPrefixSlice.measurableSet_jointPrivatePrefixPassSet
      (contextJointEligibleListFunction c label) label.2)

@[expose] noncomputable def contextPassingProbabilityJoint (c : Context p)
    (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    FalseFactorBase p × ForwardSlice p → ℝ :=
  fun z => contextPassingProbability c z.1 label hfalse z.2

theorem measurable_contextPassingProbabilityJoint (c : Context p)
    (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    Measurable (contextPassingProbabilityJoint c label hfalse) := by
  have hindicator : Measurable
      ((contextPassSetJoint c label hfalse).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_contextPassSetJoint c label hfalse)
  change Measurable (fun z : FalseFactorBase p × ForwardSlice p =>
    ∫ rounds, (contextPassSetJoint c label hfalse).indicator
      (fun _ => (1 : ℝ)) (z, rounds) ∂localRoundPairLaw c)
  exact hindicator.stronglyMeasurable.integral_prod_right'.measurable

theorem contextPassingProbability_eq_factorFalseForwardPassingProbability
    (c : Context p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c)
    (z : FalseFactorOutput p (BootstrapContextPrefixOperation.trueRowIndex c)) :
    contextPassingProbability c z.1 label hfalse
        (FalseForwardBaseTail.factorFalseForwardSlice p
          (BootstrapContextPrefixOperation.trueRowIndex c) label hfalse z) =
      FalseForwardBaseTail.factorFalseForwardPassingProbability
        (localRoundPairLaw c) (actualEligibleFamily c)
        (BootstrapContextPrefixOperation.trueRowIndex c) label hfalse z := by
  rw [contextPassingProbability_eq_integratedPrivatePassing,
    FalseForwardBaseTail.factorFalseForwardPassingProbability_eq_integratedPrivatePassing]
  rfl

private theorem forwardRowSlice_map (u : Fin (A_id p)) :
    (CompletePublicTable.forwardRowMeasure p).map
        (fun row : CompletePublicTable.ForwardRow p => fun t => row u t) =
      ForwardPrefixSlice.forwardSliceMeasure p := by
  have houter := measurePreserving_eval
    (fun _ : Fin (A_id p) =>
      Measure.pi (fun _ : Fin p.T => CompletePublicTable.forwardBitLaw p)) u
  simpa [CompletePublicTable.forwardRowMeasure,
    ForwardPrefixSlice.forwardSliceMeasure] using houter.map_eq

theorem contextPassingProbability_mean_eq_quotaExpectation (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    (∫ slice : ForwardSlice p,
      contextPassingProbability c base label hfalse slice
        ∂ForwardPrefixSlice.forwardSliceMeasure p) =
      ∫ rounds : LocalRoundPair c,
        ({rounds | q_dec p ≤
          (BootstrapContextPrefixOperation.candidateEligibleTimes c base
            label.2 label.1 rounds).length} : Set (LocalRoundPair c)).indicator
            (fun _ => (1 : ℝ)) rounds *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p
          ∂localRoundPairLaw c := by
  let toSlice : CompletePublicTable.ForwardRow p → ForwardSlice p :=
    fun row t => row label.2 t
  have htoSlice : Measurable toSlice :=
    measurable_pi_iff.mpr fun t => CompletePublicTable.measurable_forwardRowCoordinate p label.2 t
  have hmap := forwardRowSlice_map (p := p) label.2
  have hG : Measurable (contextPassingProbability c base label hfalse) :=
    by
      have heq : (fun slice => contextPassingProbability c base label hfalse slice) =
          ForwardPrefixSlice.integratedPrivatePassing (localRoundPairLaw c)
            (BootstrapContextPrefixOperation.candidateEligibleListFunction
              c base label.2 label.1) := by
        funext slice
        exact contextPassingProbability_eq_integratedPrivatePassing c base label hfalse slice
      change Measurable (fun slice => contextPassingProbability c base label hfalse slice)
      rw [heq]
      exact ForwardPrefixSlice.measurable_integratedPrivatePassing _ _
  have hGmap : AEStronglyMeasurable (contextPassingProbability c base label hfalse)
      ((CompletePublicTable.forwardRowMeasure p).map toSlice) := by
    rw [hmap]
    exact hG.aestronglyMeasurable
  calc
    (∫ slice : ForwardSlice p,
        contextPassingProbability c base label hfalse slice
          ∂ForwardPrefixSlice.forwardSliceMeasure p) =
        ∫ row : CompletePublicTable.ForwardRow p,
          contextPassingProbability c base label hfalse (toSlice row)
          ∂CompletePublicTable.forwardRowMeasure p := by
            rw [← hmap]
            exact integral_map htoSlice.aemeasurable hGmap
    _ = ∫ row : CompletePublicTable.ForwardRow p,
          ForwardPrefixSlice.integratedPrivatePassing (localRoundPairLaw c)
            (BootstrapContextPrefixOperation.candidateEligibleListFunction
              c base label.2 label.1) (fun t => row label.2 t)
          ∂CompletePublicTable.forwardRowMeasure p := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun row => by
              exact contextPassingProbability_eq_integratedPrivatePassing c base label hfalse
                (toSlice row)
    _ = ∫ rounds : LocalRoundPair c,
          ForwardPrefixSlice.privateQuotaSuccessWeight
            (BootstrapContextPrefixOperation.candidateEligibleListFunction
              c base label.2 label.1) rounds ∂localRoundPairLaw c :=
          ForwardPrefixSlice.integratedPrivatePassing_mean_eq_privateExpectation
            (localRoundPairLaw c)
            (BootstrapContextPrefixOperation.candidateEligibleListFunction
              c base label.2 label.1) label.2
    _ = ∫ rounds : LocalRoundPair c,
          ({rounds | q_dec p ≤
            (BootstrapContextPrefixOperation.candidateEligibleTimes c base
              label.2 label.1 rounds).length} : Set (LocalRoundPair c)).indicator
              (fun _ => (1 : ℝ)) rounds *
            ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p
            ∂localRoundPairLaw c := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun rounds => by
            simpa [BootstrapContextPrefixOperation.candidateEligibleTimes,
              ForwardPrefixSlice.forwardTrueProbability] using
              (ForwardPrefixSlice.privateQuotaSuccessWeight_eq_indicator
                (BootstrapContextPrefixOperation.candidateEligibleListFunction
                  c base label.2 label.1) rounds)

theorem contextPassingProbability_mean_le_firstQuotaPower (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    (∫ slice : ForwardSlice p,
      contextPassingProbability c base label hfalse slice
        ∂ForwardPrefixSlice.forwardSliceMeasure p) ≤
      ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
  rw [contextPassingProbability_mean_eq_quotaExpectation c base label hfalse]
  let E := BootstrapContextPrefixOperation.candidateEligibleListFunction
    c base label.2 label.1
  let Q : Set (LocalRoundPair c) := {rounds |
    q_dec p ≤ (BootstrapContextPrefixOperation.candidateEligibleTimes
      c base label.2 label.1 rounds).length}
  have hQ : MeasurableSet Q := by
    change MeasurableSet {rounds : LocalRoundPair c | q_dec p ≤
      (ForwardPrefixSlice.chronologicalEligibleTimes E rounds).length}
    exact ForwardPrefixSlice.measurableSet_privateQuotaEvent E
  calc
    (∫ rounds : LocalRoundPair c,
        ({rounds | q_dec p ≤
          (BootstrapContextPrefixOperation.candidateEligibleTimes c base
            label.2 label.1 rounds).length} : Set (LocalRoundPair c)).indicator
            (fun _ => (1 : ℝ)) rounds *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p
          ∂localRoundPairLaw c) =
        (∫ rounds : LocalRoundPair c,
          Q.indicator (fun _ => (1 : ℝ)) rounds ∂localRoundPairLaw c) *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
            rw [integral_mul_const]
    _ = (localRoundPairLaw c).real Q *
          ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by
            rw [integral_indicator_const 1 hQ]
            simp only [smul_eq_mul, mul_one]
  have hpow : 0 ≤ ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p :=
    pow_nonneg (ForwardPrefixSlice.forwardTrueProbability_nonneg p) _
  calc
    (localRoundPairLaw c).real Q *
        ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p ≤
      1 * ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p :=
        mul_le_mul_of_nonneg_right measureReal_le_one hpow
    _ = ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p := by ring

theorem contextPassingProbability_mean_le_exp_bound (c : Context p)
    (base : FalseFactorBase p) (label : SliceLabel p)
    (hfalse : label.1 ≠ BootstrapContextPrefixOperation.trueRowIndex c) :
    (∫ slice : ForwardSlice p,
      contextPassingProbability c base label hfalse slice
        ∂ForwardPrefixSlice.forwardSliceMeasure p) ≤
      Real.exp (-8 * (b_N p : ℝ)) := by
  calc
    _ ≤ ForwardPrefixSlice.forwardTrueProbability p ^ q_dec p :=
      contextPassingProbability_mean_le_firstQuotaPower c base label hfalse
    _ ≤ Real.exp (-8 * (b_N p : ℝ)) :=
      ForwardPrefixSlice.forwardTrueProbability_le_exp_bound p

@[expose] def localEpsilon (p : ConstructorDimensions.Parameters) : ℝ :=
  1 / ((B_boot p : ℝ) * (n_boot p : ℝ))

@[expose] noncomputable def actualContextPublishedFalseForwardStatistic
    (c : Context p) (x : CompletePublicTable.PublishedOutput p) : ℝ :=
  let J := BootstrapContextPrefixOperation.trueRowIndex c
  let z := FalseRowSliceFactorization.falseRowFactorEquiv p J x
  (1 / (A_id p : ℝ)) *
    ∑ v : Fin (M p), ∑ u : Fin (A_id p),
      if hfalse : v ≠ J then
        contextPassingProbability c z.1 (v, u) hfalse
          (FalseForwardBaseTail.factorFalseForwardSlice p J (v, u) hfalse z)
      else 0

theorem actualContextPublishedFalseForwardStatistic_eq_factor
    (c : Context p) (x : CompletePublicTable.PublishedOutput p) :
    actualContextPublishedFalseForwardStatistic c x =
      FalseForwardBaseTail.factorFalseForwardStatistic (localRoundPairLaw c)
        (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c)
        (FalseRowSliceFactorization.falseRowFactorEquiv p
          (BootstrapContextPrefixOperation.trueRowIndex c) x) := by
  let J := BootstrapContextPrefixOperation.trueRowIndex c
  let z := FalseRowSliceFactorization.falseRowFactorEquiv p J x
  unfold actualContextPublishedFalseForwardStatistic
    FalseForwardBaseTail.factorFalseForwardStatistic
  apply congrArg (fun r : ℝ => (1 / (A_id p : ℝ)) * r)
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hfalse : v ≠ J
  · simpa [J, z, hfalse] using
      (contextPassingProbability_eq_factorFalseForwardPassingProbability c
        (v, u) hfalse z)
  · have hv : v = J := by
      by_contra hne
      exact hfalse hne
    simp [J, hv]

theorem actualContextPublishedFalseForwardStatistic_eq_published
    (c : Context p) (x : CompletePublicTable.PublishedOutput p) :
    actualContextPublishedFalseForwardStatistic c x =
      FalseForwardBaseTail.publishedFalseForwardStatistic (localRoundPairLaw c)
        (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c) x := by
  calc
    actualContextPublishedFalseForwardStatistic c x =
        FalseForwardBaseTail.factorFalseForwardStatistic (localRoundPairLaw c)
          (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c)
          (FalseRowSliceFactorization.falseRowFactorEquiv p
            (BootstrapContextPrefixOperation.trueRowIndex c) x) :=
      actualContextPublishedFalseForwardStatistic_eq_factor c x
    _ = FalseForwardBaseTail.publishedFalseForwardStatistic (localRoundPairLaw c)
          (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c) x :=
      (FalseForwardBaseTail.publishedFalseForwardStatistic_eq_factor
        (localRoundPairLaw c) (actualEligibleFamily c)
        (BootstrapContextPrefixOperation.trueRowIndex c) x).symm

@[expose] def actualContextPublishedFalseForwardBadSet (c : Context p) :
    Set (CompletePublicTable.PublishedOutput p) :=
  {x | actualContextPublishedFalseForwardStatistic c x > localEpsilon p}

theorem actualContextPublishedFalseForwardBadSet_eq_published
    (c : Context p) :
    actualContextPublishedFalseForwardBadSet c =
      FalseForwardBaseTail.publishedFalseForwardBadSet (localRoundPairLaw c)
        (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c) := by
  ext x
  change actualContextPublishedFalseForwardStatistic c x > localEpsilon p ↔
    FalseForwardBaseTail.publishedFalseForwardStatistic (localRoundPairLaw c)
      (actualEligibleFamily c) (BootstrapContextPrefixOperation.trueRowIndex c) x >
        1 / ((B_boot p : ℝ) * (n_boot p : ℝ))
  rw [actualContextPublishedFalseForwardStatistic_eq_published]
  rfl

theorem measurableSet_actualContextPublishedFalseForwardBadSet (c : Context p) :
    MeasurableSet (actualContextPublishedFalseForwardBadSet c) := by
  rw [actualContextPublishedFalseForwardBadSet_eq_published]
  exact FalseForwardBaseTail.measurableSet_publishedFalseForwardBadSet
    (localRoundPairLaw c) (actualEligibleFamily c)
    (BootstrapContextPrefixOperation.trueRowIndex c)

theorem exists_universal_N0_actualContextPublishedFalseForwardBadSet_probability_le :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      ∀ c : Context p,
        MeasurableSet (actualContextPublishedFalseForwardBadSet c) ∧
        (CompletePublicTable.publishedOutputMeasure p).real
          (actualContextPublishedFalseForwardBadSet c) ≤
          Real.exp (-((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) := by
  obtain ⟨N₀, hN₀⟩ :=
    FalseForwardBaseTail.exists_universal_N0_publishedFalseForwardBadSet_probability_le
  refine ⟨N₀, ?_⟩
  intro p hN₀p c
  have h := hN₀ p hN₀p c.1
    (BootstrapContextPrefixOperation.trueRowIndex c)
    (localRoundPairLaw c) (actualEligibleFamily c)
  rw [actualContextPublishedFalseForwardBadSet_eq_published]
  exact h

@[expose] def actualContextFalseForwardBadUnion (p : ConstructorDimensions.Parameters) :
    Set (CompletePublicTable.PublishedOutput p) :=
  FalseForwardContextBound.suppliedContextBadUnion p
    (fun c => actualContextPublishedFalseForwardBadSet c)

@[expose] def commonNumericPublicGoodSet (p : ConstructorDimensions.Parameters) :
    Set (CompletePublicTable.PublishedOutput p) :=
  (actualContextFalseForwardBadUnion p)ᶜ

theorem commonNumericPublicGoodSet_eq_forall (p : ConstructorDimensions.Parameters) :
    commonNumericPublicGoodSet p =
      {x | ∀ c : Context p,
        actualContextPublishedFalseForwardStatistic c x ≤ localEpsilon p} := by
  ext x
  simp [commonNumericPublicGoodSet, actualContextFalseForwardBadUnion,
    FalseForwardContextBound.suppliedContextBadUnion,
    actualContextPublishedFalseForwardBadSet, not_lt]

theorem measurableSet_commonNumericPublicGoodSet (p : ConstructorDimensions.Parameters) :
    MeasurableSet (commonNumericPublicGoodSet p) := by
  rw [commonNumericPublicGoodSet]
  exact (FalseForwardContextBound.measurableSet_suppliedContextBadUnion p
    (fun c => actualContextPublishedFalseForwardBadSet c)
    (fun c => measurableSet_actualContextPublishedFalseForwardBadSet c)).compl

theorem commonNumericPublicGoodSet_failure_probability_le_of_construction_branch
    : ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
        (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
      MeasurableSet (commonNumericPublicGoodSet p) ∧
      (CompletePublicTable.publishedOutputMeasure p).real
        (commonNumericPublicGoodSet p)ᶜ ≤ 1 / (N p : ℝ) := by
  obtain ⟨N₀, hN₀tail⟩ :=
    exists_universal_N0_actualContextPublishedFalseForwardBadSet_probability_le
  refine ⟨N₀, ?_⟩
  intro p hN₀p hbranch
  have hcontext (c : Context p) :
      (CompletePublicTable.publishedOutputMeasure p).real
        (actualContextPublishedFalseForwardBadSet c) ≤
          Real.exp (-((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) :=
    (hN₀tail p hN₀p c).2
  have hunion := FalseForwardContextBound.suppliedContextBadUnion_probability_le_inv_N
    p hbranch (CompletePublicTable.publishedOutputMeasure p)
    (fun c => actualContextPublishedFalseForwardBadSet c)
    (fun c => measurableSet_actualContextPublishedFalseForwardBadSet c)
    (fun c => by
      apply (ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top (CompletePublicTable.publishedOutputMeasure p)
          (actualContextPublishedFalseForwardBadSet c)) (Real.exp_nonneg _)).2
      simpa [Measure.real] using hcontext c)
  refine ⟨measurableSet_commonNumericPublicGoodSet p, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion.2
  simpa [commonNumericPublicGoodSet, actualContextFalseForwardBadUnion,
    FalseForwardContextBound.suppliedContextBadUnion, Measure.real,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (N p : ℝ))] using hreal

end Bandits.Support.BootstrapContextPassingTail

end
