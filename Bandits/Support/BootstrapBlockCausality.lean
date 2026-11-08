/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.CompletePublicTable

/-!
# Causality and measurability of the physical bootstrap block

Sources: `sources/zip4/manuscript/07_public_setup.tex:74-118`,
`sources/zip4/manuscript/appendix_b_communication.tex:398-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:40-42`.  These results concern
only the already defined deterministic `BootstrapPhysicalBlock.run`.  They
record prefix dependence and Borel measurability for the literal complete-row
and supplied private-draw inputs; they make no probability, independence,
freshness, or execution-coupling claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapBlockCausality

open MeasureTheory ConstructorDimensions BootstrapDimensions FiniteBanditModel
open PublicDiscreteDraws ActiveRoundActions RealRewardGridCount
open BootstrapPhysicalBlock CompletePublicTable ContinuousLearningRows
open scoped Classical BigOperators

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The naturally varying local coordinates: one existing complete continuous
row, followed by the supplied uniform, coordinator-complement, and follower-
complement draw arrays.  The block-start fields and reward row are parameters
of `inputOf`, not random coordinates in this product. -/
abbrev LocalCoordinates (p : ConstructorDimensions.Parameters)
    (uninformed : Finset (Follower p.m))
    (held : {j // j ∈ uninformed} → Arm p.K) (target : Arm p.K) :=
  CompletePublicTable.CompleteRow p ×
    ((Player p.m → Fin p.T → Arm p.K) ×
      ((Fin p.T → BootstrapPhysicalBlock.AvoidArm p target) ×
        ((j : {j // j ∈ uninformed}) → Fin p.T →
          BootstrapPhysicalBlock.AvoidArm p (held j))))

/-- Assemble the existing physical input from fixed block-start data and the
literal product of a complete row with the supplied finite draw arrays. -/
def inputOf (uninformed : Finset (Follower p.m))
    (active : {j // j ∈ uninformed} → Bool)
    (held : {j // j ∈ uninformed} → Arm p.K)
    (privateId : {j // j ∈ uninformed} → Fin (A_id p))
    (ids : CompletePublicTable.IDArray p) (target : Arm p.K)
    (rewards : Fin p.T → Arm p.K → Fin (D p + 1))
    (v : LocalCoordinates p uninformed held target) : BootstrapPhysicalBlock.Input p s :=
  { uninformed := uninformed
    active := active
    held := held
    privateId := privateId
    ids := ids
    row := v.1
    target := target
    uniform := v.2.1
    coordinatorAvoid := v.2.2.1
    followerAvoid := v.2.2.2
    rewards := rewards }

/-- Equality of precisely the complete-row and supplied private coordinates
read on one calendar round. -/
def roundCoordinatesEq (uninformed : Finset (Follower p.m))
    (held : {j // j ∈ uninformed} → Arm p.K) (target : Arm p.K)
    (v w : LocalCoordinates p uninformed held target)
    (t : Fin p.T) : Prop :=
  (∀ u, v.1.1 u t = w.1.1 u t) ∧
    v.1.2 t = w.1.2 t ∧
    (∀ i, v.2.1 i t = w.2.1 i t) ∧
    v.2.2.1 t = w.2.2.1 t ∧
    (∀ j, v.2.2.2 j t = w.2.2.2 j t)

variable (uninformed : Finset (Follower p.m))
variable (active : {j // j ∈ uninformed} → Bool)
variable (held : {j // j ∈ uninformed} → Arm p.K)
variable (privateId : {j // j ∈ uninformed} → Fin (A_id p))
variable (ids : CompletePublicTable.IDArray p) (target : Arm p.K)
variable (rewards : Fin p.T → Arm p.K → Fin (D p + 1))

def blockInput (v : LocalCoordinates p uninformed held target) :=
  inputOf (s := s) uninformed active held privateId ids target rewards v

/-- The existing physical recursion on the literal product input. -/
def blockRun (v : LocalCoordinates p uninformed held target) (n : ℕ) :=
  BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids
    target rewards v) n

/-- The finite recursion mode carries its ordinary discrete measurable
structure. -/
instance modeMeasurableSpace : MeasurableSpace BootstrapPhysicalBlock.Mode := ⊤

instance modeMeasurableEq : MeasurableEq BootstrapPhysicalBlock.Mode := by
  constructor
  change MeasurableSet {z : BootstrapPhysicalBlock.Mode × BootstrapPhysicalBlock.Mode |
    z.1 = z.2}
  have hdiag :
      {z : BootstrapPhysicalBlock.Mode × BootstrapPhysicalBlock.Mode | z.1 = z.2} =
        {(.discover, .discover)} ∪ {(.multicast, .multicast)} := by
    ext z
    rcases z with ⟨a, b⟩
    cases a <;> cases b <;> simp
  rw [hdiag]
  exact (measurableSet_singleton _).union (measurableSet_singleton _)

/-- The state measurable structure is induced by its existing list, mode, and
positive-log fields. -/
def stateCoordinates (st : BootstrapPhysicalBlock.State p) :
    Finset (Fin (A_id p)) ×
      (BootstrapPhysicalBlock.Mode × Finset (Fin p.T)) :=
  (st.list, (st.mode, st.positives))

instance stateMeasurableSpace : MeasurableSpace (BootstrapPhysicalBlock.State p) :=
  MeasurableSpace.comap stateCoordinates inferInstance

/-- Evaluation of the existing forward-row bit at a specified round. -/
theorem measurable_localForward (u : Fin (A_id p)) (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target => v.1.1 u t) := by
  exact (measurable_pi_apply t).comp
    ((measurable_pi_apply u).comp (measurable_fst.comp measurable_fst))

private theorem measurable_stateList {α : Type*} [MeasurableSpace α]
    (f : α → BootstrapPhysicalBlock.State p) (hf : Measurable f) :
    Measurable (fun x => (f x).list) := by
  have hcoords : Measurable (stateCoordinates ∘ f) := (measurable_comap_iff).mp hf
  exact measurable_fst.comp hcoords

private theorem measurable_stateMode {α : Type*} [MeasurableSpace α]
    (f : α → BootstrapPhysicalBlock.State p) (hf : Measurable f) :
    Measurable (fun x => (f x).mode) := by
  have hcoords : Measurable (stateCoordinates ∘ f) := (measurable_comap_iff).mp hf
  exact measurable_fst.comp (measurable_snd.comp hcoords)

private theorem measurable_statePositives {α : Type*} [MeasurableSpace α]
    (f : α → BootstrapPhysicalBlock.State p) (hf : Measurable f) :
    Measurable (fun x => (f x).positives) := by
  have hcoords : Measurable (stateCoordinates ∘ f) := (measurable_comap_iff).mp hf
  exact measurable_snd.comp (measurable_snd.comp hcoords)

/-- Product-one for the physical forward-bit row is exactly the all-one test
on the retained list. -/
private theorem forwardProduct_eq_one_iff
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) :
    BootstrapPhysicalBlock.forwardProduct x st t = 1 ↔
      ∀ u ∈ st.list, x.row.1 u t = true := by
  classical
  unfold BootstrapPhysicalBlock.forwardProduct
  have hle : ∀ u ∈ st.list, (if x.row.1 u t then 1 else 0 : ℕ) ≤ 1 := by
    intro u hu
    split <;> simp
  rw [Finset.prod_eq_one_iff_of_le_one hle]
  constructor
  · intro h u hu
    by_cases hb : x.row.1 u t
    · exact hb
    · have hh := h u hu
      simp [hb] at hh
  · intro h u hu
    simp [h u hu]

/-- Measurability of the current retained-list all-forward test, using the
finite list field and the genuine current complete-row bit projections. -/
private theorem measurable_forwardProduct_one
    (t : Fin p.T) :
    MeasurableSet {z : LocalCoordinates p uninformed held target × BootstrapPhysicalBlock.State p |
      BootstrapPhysicalBlock.forwardProduct
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t = 1} := by
  classical
  have hlist : Measurable (fun z : LocalCoordinates p uninformed held target ×
      BootstrapPhysicalBlock.State p => z.2.list) :=
    measurable_stateList (fun z : _ × BootstrapPhysicalBlock.State p => z.2) measurable_snd
  have hset : MeasurableSet {z : LocalCoordinates p uninformed held target ×
      BootstrapPhysicalBlock.State p | ∀ u ∈ z.2.list,
        (z.1.1.1 u t : Bool) = true} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => by
      have hmem : Measurable (fun z : LocalCoordinates p uninformed held target ×
          BootstrapPhysicalBlock.State p => u ∈ z.2.list) :=
        (measurable_finset_iff.mp hlist) u
      have hmemSet : MeasurableSet {z : LocalCoordinates p uninformed held target ×
          BootstrapPhysicalBlock.State p | u ∈ z.2.list} :=
        measurableSet_setOfPred.mpr hmem
      have hbit : Measurable (fun z : LocalCoordinates p uninformed held target ×
          BootstrapPhysicalBlock.State p => z.1.1.1 u t) :=
        (measurable_localForward uninformed held target u t).comp measurable_fst
      have hbitSet : MeasurableSet {z : LocalCoordinates p uninformed held target ×
          BootstrapPhysicalBlock.State p | z.1.1.1 u t = true} :=
        measurableSet_eq_fun hbit measurable_const
      have heq : {z : LocalCoordinates p uninformed held target ×
          BootstrapPhysicalBlock.State p | u ∈ z.2.list → z.1.1.1 u t = true} =
          {z | z ∉ {z : LocalCoordinates p uninformed held target ×
            BootstrapPhysicalBlock.State p | u ∈ z.2.list} ∨ z.1.1.1 u t = true} := by
        ext z
        constructor
        · intro hz
          by_cases hm : u ∈ z.2.list
          · exact Or.inr (hz hm)
          · exact Or.inl hm
        · rintro (hn | hb) hm
          · exact (hn hm).elim
          · exact hb
      rw [heq]
      exact hmemSet.compl.union hbitSet
  have hsetEq :
      {z : LocalCoordinates p uninformed held target × BootstrapPhysicalBlock.State p |
        BootstrapPhysicalBlock.forwardProduct
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t = 1} =
      {z | ∀ u ∈ z.2.list, z.1.1.1 u t = true} := by
    ext z
    exact forwardProduct_eq_one_iff
      (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
  rw [hsetEq]
  exact hset

private theorem measurable_localLearningRow :
    Measurable (fun v : LocalCoordinates p uninformed held target => v.1.2) :=
  measurable_snd.comp measurable_fst

/-- The accepted continuous slice coordinate at the current round. -/
theorem measurable_localSlice (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target => (v.1.2 t).1) :=
  (ContinuousLearningRows.measurable_sliceAt t).comp
    (measurable_localLearningRow uninformed held target)

/-- The accepted affine sample for the specified current follower channel. -/
theorem measurable_localAffine (t : Fin p.T) (j : Follower p.m) :
    Measurable (fun v : LocalCoordinates p uninformed held target => (v.1.2 t).2 (1, j)) :=
  (ContinuousLearningRows.measurable_affineAt t (1, j)).comp
    (measurable_localLearningRow uninformed held target)

private theorem measurable_uniformCoordinate (i : Player p.m) (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target => v.2.1 i t) :=
  (measurable_pi_apply t).comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))

private theorem measurable_coordinatorAvoidCoordinate (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target => v.2.2.1 t) :=
  (measurable_pi_apply t).comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd))

private theorem measurable_followerAvoidCoordinate (j : {j // j ∈ uninformed})
    (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target => v.2.2.2 j t) :=
  (measurable_pi_apply t).comp
    ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

/-- Slot sampling on the current slice is the accepted continuous categorical
map. -/
@[fun_prop] theorem measurable_slotInput (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.slot (blockInput (s := s) uninformed active held privateId ids target rewards v) t) := by
  simp only [BootstrapPhysicalBlock.slot, blockInput, inputOf]
  exact (PublicDiscreteDraws.measurable_slotDraw).comp (measurable_localSlice uninformed held target t)

/-- Selected-follower sampling on the current slice is the accepted
discrete-control map. -/
@[fun_prop] theorem measurable_selectedInput (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.selected (blockInput (s := s) uninformed active held privateId ids target rewards v) t) := by
  simp only [BootstrapPhysicalBlock.selected, blockInput, inputOf]
  exact (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
    (measurable_localSlice uninformed held target t)

/-- Ordered tuple sampling on the current slice is the accepted tuple map. -/
@[fun_prop] theorem measurable_tupleInput (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.tuple (blockInput (s := s) uninformed active held privateId ids target rewards v) t) := by
  simp only [BootstrapPhysicalBlock.tuple, blockInput, inputOf]
  exact (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp
    (measurable_localSlice uninformed held target t)

/-- Pilot sampling on the current slice is the accepted pilot map. -/
@[fun_prop] theorem measurable_pilotInput (t : Fin p.T) (i : Player p.m) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.pilot (blockInput (s := s) uninformed active held privateId ids target rewards v) t i) := by
  simp only [BootstrapPhysicalBlock.pilot, blockInput, inputOf]
  exact (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) i).comp
    (measurable_localSlice uninformed held target t)

/-- The current UP affine bit is measurable through the accepted complete-row
affine coordinate and affine hash. -/
@[fun_prop] theorem measurable_initialUpBitInput (t : Fin p.T) (j : Follower p.m) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.initialUpBit
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t j) := by
  simp only [BootstrapPhysicalBlock.initialUpBit, blockInput, inputOf]
  exact (Measurable.of_discrete (f := fun sample : AffineChannelLaw.Sample
      (ContinuousLearningRows.B p) =>
        AffineChannelLaw.affineHash sample (BootstrapPhysicalBlock.initialUpWord p))).comp
    (measurable_localAffine uninformed held target t j)

/-- A one-round view consists of the supplied local coordinates and the
existing pre-choice state. -/
abbrev RoundView :=
  LocalCoordinates p uninformed held target × BootstrapPhysicalBlock.State p

private theorem measurable_viewSlot (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.slot (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t) :=
  (measurable_slotInput (s := s) uninformed active held privateId ids target rewards t).comp
    measurable_fst

private theorem measurable_viewSelected (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.selected (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t) :=
  (measurable_selectedInput (s := s) uninformed active held privateId ids target rewards t).comp
    measurable_fst

private theorem measurable_viewTuple (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.tuple (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t) :=
  (measurable_tupleInput (s := s) uninformed active held privateId ids target rewards t).comp
    measurable_fst

private theorem measurable_viewPilot (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.pilot (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t i) :=
  (measurable_pilotInput (s := s) uninformed active held privateId ids target rewards t i).comp
    measurable_fst

private theorem measurable_viewInitialUpBit (t : Fin p.T) (j : Follower p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.initialUpBit (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t j) :=
  (measurable_initialUpBitInput (s := s) uninformed active held privateId ids target rewards t j).comp
    measurable_fst

private theorem measurable_viewUniform (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target => z.1.2.1 i t) :=
  (measurable_uniformCoordinate uninformed held target i t).comp measurable_fst

private theorem measurable_viewCoordinatorAvoid (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target => z.1.2.2.1 t) :=
  (measurable_coordinatorAvoidCoordinate uninformed held target t).comp measurable_fst

private theorem measurable_viewFollowerAvoid (t : Fin p.T)
    (j : {j // j ∈ uninformed}) :
    Measurable (fun z : RoundView (p := p) uninformed held target => z.1.2.2.2 j t) :=
  (measurable_followerAvoidCoordinate uninformed held target j t).comp measurable_fst

private theorem measurable_viewForward (t : Fin p.T) (u : Fin (A_id p)) :
    Measurable (fun z : RoundView (p := p) uninformed held target => z.1.1.1 u t) :=
  (measurable_localForward uninformed held target u t).comp measurable_fst

private theorem measurable_viewSlotEq (t : Fin p.T) (q : PublicDiscreteDraws.Slot) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      BootstrapPhysicalBlock.slot (blockInput (s := s) uninformed active held
        privateId ids target rewards z.1) t = q} := by
  exact measurableSet_eq_fun (measurable_viewSlot (s := s) uninformed active held
    privateId ids target rewards t) measurable_const

private theorem measurable_viewModeEq (q : BootstrapPhysicalBlock.Mode) :
    MeasurableSet {z : RoundView (p := p) uninformed held target | z.2.mode = q} := by
  have hmode : Measurable (fun z : RoundView (p := p) uninformed held target => z.2.mode) :=
    measurable_stateMode (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  exact (measurableSet_singleton q).preimage hmode

private theorem measurable_viewForwardProductOne (t : Fin p.T) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      BootstrapPhysicalBlock.forwardProduct
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t = 1} :=
  measurable_forwardProduct_one (s := s) uninformed active held privateId ids target rewards t

private theorem measurable_viewAllDataEvent (t : Fin p.T) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      z.2.mode = .multicast ∧
        BootstrapPhysicalBlock.forwardProduct
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t = 1} := by
  exact (measurable_viewModeEq (p := p) (uninformed := uninformed) (held := held)
    (target := target) BootstrapPhysicalBlock.Mode.multicast).inter
      (measurable_viewForwardProductOne (s := s) uninformed active held privateId ids target
        rewards t)

private theorem measurable_viewTupleArm (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.tuple
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t).val i) := by
  have htup := measurable_subtype_coe.comp
    (measurable_viewTuple (s := s) uninformed active held privateId ids target rewards t)
  exact (measurable_pi_apply i).comp htup

private theorem measurable_viewCoordinatorAction (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.coordinatorAction
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t) := by
  classical
  have hdata := measurable_viewSlotEq (s := s) uninformed active held privateId ids target
    rewards t PublicDiscreteDraws.dataSlot
  have hdown := measurable_viewSlotEq (s := s) uninformed active held privateId ids target
    rewards t PublicDiscreteDraws.downSlot
  have hrelease := measurable_viewAllDataEvent (s := s) uninformed active held privateId ids
    target rewards t
  have htuple := measurable_viewTupleArm (s := s) uninformed active held privateId ids target
    rewards t (coordinator p.two_le_m)
  have huniform := measurable_viewUniform (uninformed := uninformed) (held := held)
    (target := target) t (coordinator p.two_le_m)
  have havoid := measurable_subtype_coe.comp
    (measurable_viewCoordinatorAvoid (uninformed := uninformed) (held := held)
      (target := target) t)
  unfold BootstrapPhysicalBlock.coordinatorAction
  exact Measurable.ite hdata
    (Measurable.ite hrelease havoid measurable_const)
    (Measurable.ite hdown htuple huniform)

private theorem measurable_uninformedActionInput (t : Fin p.T)
    (j : {j // j ∈ uninformed}) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.uninformedAction
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t j) := by
  classical
  by_cases hactive : active j = true
  · by_cases hid : ids (privateId j) t = true
    · have hv : Measurable (fun v : LocalCoordinates p uninformed held target =>
          (v.2.2.2 j t).val) :=
        (measurable_subtype_coe.comp
          (measurable_followerAvoidCoordinate uninformed held target j t))
      simpa [BootstrapPhysicalBlock.uninformedAction, blockInput, inputOf, hactive, hid] using hv
    · simpa [BootstrapPhysicalBlock.uninformedAction, blockInput, inputOf, hactive, hid] using
        (measurable_const : Measurable fun _ : LocalCoordinates p uninformed held target => held j)
  · simpa [BootstrapPhysicalBlock.uninformedAction, blockInput, inputOf, hactive] using
      measurable_uniformCoordinate uninformed held target (followerPlayer p.two_le_m j.val) t

private theorem measurable_unoccupiedActionInput (t : Fin p.T) (j : Follower p.m) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.unoccupiedAction
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t j) := by
  classical
  have hdata : MeasurableSet {v : LocalCoordinates p uninformed held target |
      BootstrapPhysicalBlock.slot
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t =
        PublicDiscreteDraws.dataSlot} :=
    measurableSet_eq_fun (measurable_slotInput (s := s) uninformed active held privateId ids
      target rewards t) measurable_const
  have hup : MeasurableSet {v : LocalCoordinates p uninformed held target |
      BootstrapPhysicalBlock.slot
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t =
        PublicDiscreteDraws.upSlot} :=
    measurableSet_eq_fun (measurable_slotInput (s := s) uninformed active held privateId ids
      target rewards t) measurable_const
  have hselected : MeasurableSet {v : LocalCoordinates p uninformed held target |
      BootstrapPhysicalBlock.selected
        (blockInput (s := s) uninformed active held privateId ids target rewards v) t = j} :=
    measurableSet_eq_fun (measurable_selectedInput (s := s) uninformed active held privateId ids
      target rewards t) measurable_const
  have hsend : Measurable (fun v : LocalCoordinates p uninformed held target =>
      ActiveRoundActions.sendArm
        (BootstrapPhysicalBlock.initialUpBit
          (blockInput (s := s) uninformed active held privateId ids target rewards v) t j)
        ((BootstrapPhysicalBlock.tuple
          (blockInput (s := s) uninformed active held privateId ids target rewards v) t).val
            (followerPlayer p.two_le_m j))
        ((BootstrapPhysicalBlock.tuple
          (blockInput (s := s) uninformed active held privateId ids target rewards v) t).val
            (coordinator p.two_le_m))) := by
    have hargs : Measurable (fun v : LocalCoordinates p uninformed held target =>
        (BootstrapPhysicalBlock.initialUpBit
            (blockInput (s := s) uninformed active held privateId ids target rewards v) t j,
          ((BootstrapPhysicalBlock.tuple
            (blockInput (s := s) uninformed active held privateId ids target rewards v) t).val
              (followerPlayer p.two_le_m j),
           (BootstrapPhysicalBlock.tuple
            (blockInput (s := s) uninformed active held privateId ids target rewards v) t).val
              (coordinator p.two_le_m)))) := by
      have htup := measurable_subtype_coe.comp
        (measurable_tupleInput (s := s) uninformed active held privateId ids target rewards t)
      exact (measurable_initialUpBitInput (s := s) uninformed active held privateId ids target
        rewards t j).prodMk
          (((measurable_pi_apply (followerPlayer p.two_le_m j)).comp htup).prodMk
            ((measurable_pi_apply (coordinator p.two_le_m)).comp htup))
    exact (Measurable.of_discrete (f := fun q : AffineChannelLaw.Bit × (Arm p.K × Arm p.K) =>
      ActiveRoundActions.sendArm q.1 q.2.1 q.2.2)).comp hargs
  have htupleVal := measurable_subtype_coe.comp
    (measurable_tupleInput (s := s) uninformed active held privateId ids target rewards t)
  have htuple := (measurable_pi_apply (followerPlayer p.two_le_m j)).comp htupleVal
  have hpilot := measurable_pilotInput (s := s) uninformed active held privateId ids target
    rewards t (followerPlayer p.two_le_m j)
  have hupsel := hup.inter hselected
  unfold BootstrapPhysicalBlock.unoccupiedAction
  exact Measurable.ite hdata hpilot (Measurable.ite hupsel hsend htuple)

private theorem measurable_viewFollowerAction (t : Fin p.T) (j : Follower p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.followerAction
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t j) := by
  by_cases hj : j ∈ uninformed
  · let j' : {j // j ∈ uninformed} := ⟨j, hj⟩
    have h : Measurable (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.uninformedAction
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t j') :=
      (measurable_uninformedActionInput (s := s) uninformed active held privateId ids
        target rewards t j').comp measurable_fst
    simpa [BootstrapPhysicalBlock.followerAction, blockInput, inputOf, hj, j'] using h
  · have h : Measurable (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.unoccupiedAction
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t j) :=
      (measurable_unoccupiedActionInput (s := s) uninformed active held privateId ids
        target rewards t j).comp measurable_fst
    simpa [BootstrapPhysicalBlock.followerAction, blockInput, inputOf, hj] using h

/-- The simultaneous physical action profile is measurable on the actual
complete-row/private-coordinate product and pre-choice state. -/
theorem measurable_actionsView (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.actions
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t) := by
  apply measurable_pi_iff.mpr
  intro i
  rcases ActiveRoundActions.player_cases p.two_le_m i with hcoord | ⟨j, hj⟩
  · subst i
    simpa only [BootstrapPhysicalBlock.actions_coordinator] using
      measurable_viewCoordinatorAction (s := s) uninformed active held privateId ids target
        rewards t
  · have hfun : (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.actions
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t i) =
      (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.followerAction
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t j) := by
      funext z
      rw [hj, BootstrapPhysicalBlock.actions_follower]
    rw [hfun]
    exact measurable_viewFollowerAction (s := s) uninformed active held privateId ids target
      rewards t j

private theorem measurable_viewCollisionFree (t : Fin p.T) (i : Player p.m) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t) i} := by
  classical
  have hactions := measurable_actionsView (s := s) uninformed active held privateId ids target
    rewards t
  have hcoordinate (j : Player p.m) :
      Measurable (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.actions
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t j) := (measurable_pi_apply j).comp hactions
  have hcondition (j : Player p.m) : MeasurableSet {z : RoundView
      (p := p) uninformed held target |
        j = i ∨
          BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t j ≠
            BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t i} := by
    by_cases hji : j = i
    · simp [hji]
    · have heq := measurableSet_eq_fun (hcoordinate j) (hcoordinate i)
      have hneq : MeasurableSet {z : RoundView (p := p) uninformed held target |
          BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t j ≠
            BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t i} := by
        rw [show {z : RoundView (p := p) uninformed held target |
              BootstrapPhysicalBlock.actions
                  (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
                  z.2 t j ≠
                BootstrapPhysicalBlock.actions
                  (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
                  z.2 t i} =
              {z | BootstrapPhysicalBlock.actions
                    (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
                    z.2 t j =
                  BootstrapPhysicalBlock.actions
                    (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
                    z.2 t i}ᶜ by
          ext z
          simp [ne_eq]]
        exact heq.compl
      simpa [hji] using hneq
  have hset : {z : RoundView (p := p) uninformed held target |
      FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t) i} =
      Set.iInter (fun j : Player p.m => {z : RoundView (p := p) uninformed held target |
        j = i ∨
          BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t j ≠
            BootstrapPhysicalBlock.actions
              (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
              z.2 t i}) := by
    ext z
    simp only [FiniteBanditModel.collisionFreeFor, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h j
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (h j hji)
    · intro h j hji
      rcases h j with hji' | hne
      · exact (hji hji').elim
      · exact hne
  rw [hset]
  exact MeasurableSet.iInter hcondition

/-- The exact finite collision test and integer reward lookup are measurable
once the simultaneously chosen actions are measurable. -/
theorem measurable_observationIndexView (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.observationIndex
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t i) := by
  have hactions := measurable_actionsView (s := s) uninformed active held privateId ids target
    rewards t
  have hactioni := (measurable_pi_apply i).comp hactions
  have hreward : Measurable (fun z : RoundView (p := p) uninformed held target =>
      rewards t (BootstrapPhysicalBlock.actions
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t i)) :=
    (Measurable.of_discrete (f := fun a : Arm p.K => rewards t a)).comp hactioni
  unfold BootstrapPhysicalBlock.observationIndex
  exact Measurable.ite
    (measurable_viewCollisionFree (s := s) uninformed active held privateId ids target rewards t i)
    hreward measurable_const

/-- Real feedback is the accepted grid image of the measured integer
observation, with collision-zero behavior inherited from the physical block. -/
theorem measurable_feedbackView (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.feedback
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t i) := by
  have hindex := measurable_observationIndexView (s := s) uninformed active held privateId ids
    target rewards t i
  have hgrid : Measurable (fun q : Fin (D p + 1) =>
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p) q) := Measurable.of_discrete
  have hvalue : Measurable (fun z : RoundView (p := p) uninformed held target =>
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (BootstrapPhysicalBlock.observationIndex
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t i)) := hgrid.comp hindex
  have heq : (fun z : RoundView (p := p) uninformed held target =>
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (BootstrapPhysicalBlock.observationIndex
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t i)) =
      (fun z => BootstrapPhysicalBlock.feedback
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t i) := by
    funext z
    exact BootstrapPhysicalBlock.observationIndex_value
      (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
      z.2 t i
  rw [← heq]
  exact hvalue

private theorem measurable_viewDiscoveryPositive (t : Fin p.T) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t} := by
  classical
  have hmode := measurable_viewModeEq (p := p) (uninformed := uninformed)
    (held := held) (target := target) BootstrapPhysicalBlock.Mode.discover
  have hslot := measurable_viewSlotEq (s := s) uninformed active held privateId ids target
    rewards t PublicDiscreteDraws.dataSlot
  have hfeedback := measurable_feedbackView (s := s) uninformed active held privateId ids
    target rewards t (coordinator p.two_le_m)
  have hpositive : MeasurableSet {z : RoundView (p := p) uninformed held target |
      0 < BootstrapPhysicalBlock.feedback
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t (coordinator p.two_le_m)} := by
    exact (measurableSet_Ioi (a := (0 : ℝ))).preimage hfeedback
  have hblock : MeasurableSet {z : RoundView (p := p) uninformed held target |
      t ∈ BootstrapDimensions.calendarBlock p s} := by
    by_cases ht : t ∈ BootstrapDimensions.calendarBlock p s <;> simp [ht]
  have hset : {z : RoundView (p := p) uninformed held target |
      BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t} =
      {z | t ∈ BootstrapDimensions.calendarBlock p s} ∩
        {z | z.2.mode = .discover} ∩
        {z | BootstrapPhysicalBlock.slot
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) t =
            PublicDiscreteDraws.dataSlot} ∩
        {z | 0 < BootstrapPhysicalBlock.feedback
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t (coordinator p.two_le_m)} := by
    ext z
    simp [BootstrapPhysicalBlock.discoveryPositive, and_assoc]
  rw [hset]
  exact (((hblock.inter hmode).inter hslot).inter hpositive)

private theorem measurable_card_of_measurable_finset {α β : Type*} [MeasurableSpace α]
    [Fintype β] (f : α → Finset β) (hf : Measurable f) :
    Measurable (fun x => (f x).card) := by
  classical
  have hsum : Measurable (fun x =>
      ∑ b ∈ Finset.univ, if b ∈ f x then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum Finset.univ
    intro b hb
    have hmem : Measurable (fun x => b ∈ f x) := (measurable_finset_iff.mp hf) b
    exact Measurable.ite (measurableSet_setOfPred.mpr hmem) measurable_const measurable_const
  have hcard (x : α) : (f x).card =
      ∑ b ∈ Finset.univ, if b ∈ f x then (1 : ℕ) else 0 := by
    simpa using (Finset.card_filter (p := fun b : β => b ∈ f x) Finset.univ)
  have heq : (fun x => (f x).card) =
      (fun x => ∑ b ∈ Finset.univ, if b ∈ f x then (1 : ℕ) else 0) := by
    funext x
    exact hcard x
  rw [heq]
  exact hsum

private theorem measurable_viewKeptList (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      z.2.list.filter (fun u => ids u t = true)) := by
  apply measurable_finset_iff.mpr
  intro u
  have hlist := measurable_stateList
    (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  have hmem : Measurable (fun z : RoundView (p := p) uninformed held target =>
      u ∈ z.2.list) := (measurable_finset_iff.mp hlist) u
  by_cases hid : ids u t = true
  · simpa [Finset.mem_filter, hid] using hmem
  · simp [Finset.mem_filter, hid]

private theorem measurable_viewInsertedPositives (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      insert t z.2.positives) := by
  apply measurable_finset_iff.mpr
  intro u
  have hpos := measurable_statePositives
    (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  have hmem : Measurable (fun z : RoundView (p := p) uninformed held target =>
      u ∈ z.2.positives) := (measurable_finset_iff.mp hpos) u
  by_cases hut : u = t
  · simp [hut]
  · simpa [Finset.mem_insert, hut] using hmem

private theorem measurable_viewStepList (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).list) := by
  have hlist := measurable_stateList
    (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  have hkept := measurable_viewKeptList (uninformed := uninformed) (held := held)
    (target := target) (ids := ids) t
  have hpositive := measurable_viewDiscoveryPositive (s := s) uninformed active held privateId
    ids target rewards t
  have hfun : (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).list) =
      (fun z => if BootstrapPhysicalBlock.discoveryPositive
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
        then z.2.list.filter (fun u => ids u t = true) else z.2.list) := by
    funext z
    by_cases hp : BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
  rw [hfun]
  exact Measurable.ite hpositive hkept hlist

private theorem measurable_viewQuotaEvent (t : Fin p.T) :
    MeasurableSet {z : RoundView (p := p) uninformed held target |
      (z.2.list.filter (fun u => ids u t = true)).card ≤ BootstrapDimensions.L0 p} := by
  have hkept := measurable_viewKeptList (uninformed := uninformed) (held := held)
    (target := target) (ids := ids) t
  have hcard : Measurable (fun z : RoundView (p := p) uninformed held target =>
      (z.2.list.filter (fun u => ids u t = true)).card) := by
    exact measurable_card_of_measurable_finset _ hkept
  exact (measurableSet_Iic (a := BootstrapDimensions.L0 p)).preimage hcard

private theorem measurable_viewStepMode (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).mode) := by
  have hmode := measurable_stateMode
    (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  have hpositive := measurable_viewDiscoveryPositive (s := s) uninformed active held privateId
    ids target rewards t
  have hquota := measurable_viewQuotaEvent (uninformed := uninformed) (held := held)
    (target := target) (ids := ids) t
  have hfun : (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).mode) =
      (fun z => if BootstrapPhysicalBlock.discoveryPositive
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
        then if (z.2.list.filter (fun u => ids u t = true)).card ≤ BootstrapDimensions.L0 p
          then BootstrapPhysicalBlock.Mode.multicast else BootstrapPhysicalBlock.Mode.discover
        else z.2.mode) := by
    funext z
    by_cases hp : BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
  rw [hfun]
  exact Measurable.ite hpositive (Measurable.ite hquota measurable_const measurable_const) hmode

private theorem measurable_viewStepPositives (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).positives) := by
  have hpos := measurable_statePositives
    (fun z : RoundView (p := p) uninformed held target => z.2) measurable_snd
  have hinserted := measurable_viewInsertedPositives (uninformed := uninformed) (held := held)
    (target := target) t
  have hpositive := measurable_viewDiscoveryPositive (s := s) uninformed active held privateId
    ids target rewards t
  have hfun : (fun z : RoundView (p := p) uninformed held target =>
      (BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t).positives) =
      (fun z => if BootstrapPhysicalBlock.discoveryPositive
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
        then insert t z.2.positives else z.2.positives) := by
    funext z
    by_cases hp : BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1) z.2 t
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
    · simp only [BootstrapPhysicalBlock.step, hp]
      rfl
  rw [hfun]
  exact Measurable.ite hpositive hinserted hpos

/-- The existing one-round state update is measurable in its true row/private
coordinates and pre-choice state, including post-observation list filtering
and the next-round multicast switch. -/
theorem measurable_stepView (t : Fin p.T) :
    Measurable (fun z : RoundView (p := p) uninformed held target =>
      BootstrapPhysicalBlock.step
        (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
        z.2 t) := by
  apply measurable_comap_iff.mpr
  exact (measurable_viewStepList (s := s) uninformed active held privateId ids target rewards t).prodMk
    ((measurable_viewStepMode (s := s) uninformed active held privateId ids target rewards t).prodMk
      (measurable_viewStepPositives (s := s) uninformed active held privateId ids target rewards t))

/-- Every finite pre-choice state of the literal recursion is measurable in
the complete-row and supplied finite private-coordinate product. -/
theorem measurable_runInput (n : ℕ) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      blockRun (s := s) uninformed active held privateId ids target rewards v n) := by
  induction n with
  | zero =>
      change Measurable (fun _ : LocalCoordinates p uninformed held target =>
        BootstrapPhysicalBlock.initialState p)
      exact measurable_const
  | succ n ih =>
      by_cases hn : n < p.T
      · simp only [blockRun, BootstrapPhysicalBlock.run, hn, ↓reduceDIte]
        have hpair : Measurable (fun v : LocalCoordinates p uninformed held target =>
            (v, blockRun (s := s) uninformed active held privateId ids target rewards v n)) :=
          measurable_id.prodMk ih
        exact (measurable_stepView (s := s) uninformed active held privateId ids target rewards
          ⟨n, hn⟩).comp hpair
      · simpa [blockRun, BootstrapPhysicalBlock.run, hn] using ih

/-- Physical feedback at a calendar round, with the existing recursion state. -/
def runFeedback (t : Fin p.T) (i : Player p.m)
    (v : LocalCoordinates p uninformed held target) : ℝ :=
  BootstrapPhysicalBlock.feedback (blockInput (s := s) uninformed active held privateId ids
    target rewards v) (blockRun (s := s) uninformed active held privateId ids target rewards v t.val) t i

/-- Integer observation at a calendar round, with the existing recursion state. -/
def runObservationIndex (t : Fin p.T) (i : Player p.m)
    (v : LocalCoordinates p uninformed held target) : Fin (D p + 1) :=
  BootstrapPhysicalBlock.observationIndex (blockInput (s := s) uninformed active held privateId ids
    target rewards v) (blockRun (s := s) uninformed active held privateId ids target rewards v t.val) t i

/-- The input and actual pre-choice recursion state packaged for one round. -/
def blockRunView (t : Fin p.T) (v : LocalCoordinates p uninformed held target) :
    RoundView (p := p) uninformed held target :=
  (v, blockRun (s := s) uninformed active held privateId ids target rewards v t.val)

private theorem measurable_blockRunView (t : Fin p.T) :
    Measurable (blockRunView (s := s) uninformed active held privateId ids target rewards t) :=
  measurable_id.prodMk
    (measurable_runInput (s := s) uninformed active held privateId ids target rewards t.val)

/-- The current physical actions are measurable after composing the one-round
map with the actual run state at that calendar time. -/
theorem measurable_actions_run (t : Fin p.T) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.actions
        (blockInput (s := s) uninformed active held privateId ids target rewards v)
        (blockRun (s := s) uninformed active held privateId ids target rewards v t.val) t) := by
  exact (measurable_actionsView (s := s) uninformed active held privateId ids target rewards t).comp
    (measurable_blockRunView (s := s) uninformed active held privateId ids target rewards t)

/-- The actual run feedback is measurable after the same finite recursion. -/
theorem measurable_feedback_run (t : Fin p.T) (i : Player p.m) :
    Measurable (runFeedback (s := s) uninformed active held privateId ids target rewards t i) := by
  have hfun : runFeedback (s := s) uninformed active held privateId ids target rewards t i =
      (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.feedback
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t i) ∘
        blockRunView (s := s) uninformed active held privateId ids target rewards t := by
    funext v
    rfl
  rw [hfun]
  exact (measurable_feedbackView (s := s) uninformed active held privateId ids target rewards t i).comp
    (measurable_blockRunView (s := s) uninformed active held privateId ids target rewards t)

/-- The actual integer observation trace on this block is measurable. -/
theorem measurable_observationIndex_run (t : Fin p.T) (i : Player p.m) :
    Measurable (runObservationIndex (s := s) uninformed active held privateId ids target rewards
      t i) := by
  have hfun : runObservationIndex (s := s) uninformed active held privateId ids target rewards
      t i =
      (fun z : RoundView (p := p) uninformed held target =>
        BootstrapPhysicalBlock.observationIndex
          (blockInput (s := s) uninformed active held privateId ids target rewards z.1)
          z.2 t i) ∘
        blockRunView (s := s) uninformed active held privateId ids target rewards t := by
    funext v
    rfl
  rw [hfun]
  exact (measurable_observationIndexView (s := s) uninformed active held privateId ids target
    rewards t i).comp
      (measurable_blockRunView (s := s) uninformed active held privateId ids target rewards t)

private theorem measurable_physicalStayRoundsInput (j : {j // j ∈ uninformed}) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.physicalStayRounds
        (blockInput (s := s) uninformed active held privateId ids target rewards v) j) := by
  apply measurable_finset_iff.mpr
  intro t
  have hfeedback := measurable_feedback_run (s := s) uninformed active held privateId ids target
    rewards t (followerPlayer p.two_le_m j.val)
  have hpositive : MeasurableSet {v : LocalCoordinates p uninformed held target |
      0 < runFeedback (s := s) uninformed active held privateId ids target rewards t
        (followerPlayer p.two_le_m j.val) v} :=
    (measurableSet_Ioi (a := (0 : ℝ))).preimage hfeedback
  simp only [BootstrapPhysicalBlock.physicalStayRounds, Finset.mem_filter]
  by_cases ht : t ∈ BootstrapDimensions.calendarBlock p s
  · by_cases hid : ids (privateId j) t = false
    · simpa [blockInput, inputOf, blockRun, runFeedback, ht, hid] using
        (measurableSet_setOfPred.mp hpositive)
    · simpa [blockInput, inputOf, ht, hid] using
        (measurable_const : Measurable fun _ : LocalCoordinates p uninformed held target => False)
  · simpa [blockInput, inputOf, ht] using
      (measurable_const : Measurable fun _ : LocalCoordinates p uninformed held target => False)

/-- The exact physical stay gain is measurable on the actual product input;
its bound is the calendar block length. -/
theorem measurable_physicalStayGainInput (j : {j // j ∈ uninformed}) :
    Measurable (fun v : LocalCoordinates p uninformed held target =>
      BootstrapPhysicalBlock.physicalStayGain
        (blockInput (s := s) uninformed active held privateId ids target rewards v) j) := by
  have hrounds := measurable_physicalStayRoundsInput (s := s) uninformed active held privateId
    ids target rewards j
  have hcard : Measurable (fun v : LocalCoordinates p uninformed held target =>
      (BootstrapPhysicalBlock.physicalStayRounds
        (blockInput (s := s) uninformed active held privateId ids target rewards v) j).card) :=
    measurable_card_of_measurable_finset _ hrounds
  by_cases ha : active j = true
  · simpa [BootstrapPhysicalBlock.physicalStayGain, blockInput, inputOf, ha] using hcard
  · simpa [BootstrapPhysicalBlock.physicalStayGain, blockInput, inputOf, ha] using
      (measurable_const : Measurable fun _ : LocalCoordinates p uninformed held target => 0)

theorem physicalStayGainInput_le_blockLength (j : {j // j ∈ uninformed})
    (v : LocalCoordinates p uninformed held target) :
    BootstrapPhysicalBlock.physicalStayGain
      (blockInput (s := s) uninformed active held privateId ids target rewards v) j ≤
        BootstrapDimensions.B_boot p := by
  classical
  by_cases ha : active j = true
  · simp only [BootstrapPhysicalBlock.physicalStayGain, blockInput, inputOf, ha]
    have hsubset :
        BootstrapPhysicalBlock.physicalStayRounds
            (blockInput (s := s) uninformed active held privateId ids target rewards v) j ⊆
          BootstrapDimensions.calendarBlock p s := by
      intro t ht
      exact (Finset.mem_filter.mp ht).1
    exact (Finset.card_le_card hsubset).trans (BootstrapDimensions.calendarBlock_card_le_B_boot p s)
  · simp [BootstrapPhysicalBlock.physicalStayGain, blockInput, inputOf, ha]

/-- Equal local coordinates give the same simultaneous physical actions at the
current round.  In particular the forward product reads only the current
complete-row coordinate. -/
theorem actions_eq_of_roundCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (h : roundCoordinatesEq uninformed held target v w t) :
    BootstrapPhysicalBlock.actions (blockInput (s := s) uninformed active held privateId ids target rewards v)
      st t =
    BootstrapPhysicalBlock.actions (blockInput (s := s) uninformed active held privateId ids target rewards w)
      st t := by
  classical
  rcases h with ⟨hforward, hlearning, huniform, hcoord, hfollower⟩
  have hproduct :
      BootstrapPhysicalBlock.forwardProduct
        (blockInput (s := s) uninformed active held privateId ids target rewards v) st t =
      BootstrapPhysicalBlock.forwardProduct
        (blockInput (s := s) uninformed active held privateId ids target rewards w) st t := by
    simp only [BootstrapPhysicalBlock.forwardProduct, blockInput, inputOf]
    apply Finset.prod_congr rfl
    intro u hu
    simp [hforward u]
    rfl
  funext i
  by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
  · subst i
    rw [BootstrapPhysicalBlock.actions_coordinator, BootstrapPhysicalBlock.actions_coordinator]
    unfold BootstrapPhysicalBlock.coordinatorAction
    rw [hproduct]
    simp [BootstrapPhysicalBlock.slot, BootstrapPhysicalBlock.tuple, blockInput, inputOf,
      hlearning, huniform, hcoord]
    rfl
  · simp [BootstrapPhysicalBlock.actions, ActiveRoundActions.followerIndex,
      BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.uninformedAction,
      BootstrapPhysicalBlock.unoccupiedAction, BootstrapPhysicalBlock.slot,
      BootstrapPhysicalBlock.selected, BootstrapPhysicalBlock.tuple,
      BootstrapPhysicalBlock.pilot, BootstrapPhysicalBlock.initialUpBit,
      blockInput, inputOf, hi, hlearning, huniform, hfollower]
    rfl

/-- Feedback agrees once the current actions agree; the reward row is the same
fixed source input on both sides. -/
theorem feedback_eq_of_roundCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (i : Player p.m)
    (h : roundCoordinatesEq uninformed held target v w t) :
    BootstrapPhysicalBlock.feedback
      (blockInput (s := s) uninformed active held privateId ids target rewards v) st t i =
    BootstrapPhysicalBlock.feedback
      (blockInput (s := s) uninformed active held privateId ids target rewards w) st t i := by
  unfold BootstrapPhysicalBlock.feedback
  rw [actions_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids target rewards v w st t h]
  simp [blockInput, inputOf]

/-- The integer observation index uses the same current action and the fixed
current reward row, including collision-zero observations. -/
theorem observationIndex_eq_of_roundCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (i : Player p.m)
    (h : roundCoordinatesEq uninformed held target v w t) :
    BootstrapPhysicalBlock.observationIndex
      (blockInput (s := s) uninformed active held privateId ids target rewards v) st t i =
    BootstrapPhysicalBlock.observationIndex
      (blockInput (s := s) uninformed active held privateId ids target rewards w) st t i := by
  unfold BootstrapPhysicalBlock.observationIndex
  rw [actions_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids target rewards v w st t h]
  simp [blockInput, inputOf]

/-- The physical one-round state transition agrees under equal current local
coordinates and equal pre-choice states. -/
theorem step_eq_of_roundCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (h : roundCoordinatesEq uninformed held target v w t) :
    BootstrapPhysicalBlock.step
      (blockInput (s := s) uninformed active held privateId ids target rewards v) st t =
    BootstrapPhysicalBlock.step
      (blockInput (s := s) uninformed active held privateId ids target rewards w) st t := by
  have hpos :
      BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards v) st t ↔
      BootstrapPhysicalBlock.discoveryPositive
        (blockInput (s := s) uninformed active held privateId ids target rewards w) st t := by
    have hfeedback := feedback_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids
      target rewards v w st t (ActiveRoundActions.coordinator p.two_le_m) h
    rcases h with ⟨hforward, hlearning, huniform, hcoord, hfollower⟩
    have hslot :
        BootstrapPhysicalBlock.slot
            (blockInput (s := s) uninformed active held privateId ids target rewards v) t =
          BootstrapPhysicalBlock.slot
            (blockInput (s := s) uninformed active held privateId ids target rewards w) t := by
      simp [BootstrapPhysicalBlock.slot, blockInput, inputOf, hlearning]
    unfold BootstrapPhysicalBlock.discoveryPositive
    rw [hslot, hfeedback]
  unfold BootstrapPhysicalBlock.step
  rw [propext hpos]
  simp [blockInput, inputOf]
  rfl

/-- The run after `n` updates depends on the supplied local coordinates only at
calendar rounds strictly before `n`. -/
theorem run_eq_of_prefixCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (n : ℕ)
    (h : ∀ r : Fin p.T, r.val < n → roundCoordinatesEq uninformed held target v w r) :
    BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards v) n =
    BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards w) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < p.T
      · rw [BootstrapPhysicalBlock.run_succ _ ⟨n, hn⟩,
          BootstrapPhysicalBlock.run_succ _ ⟨n, hn⟩]
        have hprev : ∀ r : Fin p.T, r.val < n →
            roundCoordinatesEq uninformed held target v w r :=
          fun r hr => h r (Nat.lt_trans hr (Nat.lt_succ_self n))
        rw [ih hprev]
        exact step_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids target rewards
          v w _ ⟨n, hn⟩ (h ⟨n, hn⟩ (Nat.lt_succ_self n))
      · simp only [BootstrapPhysicalBlock.run, hn, ↓reduceDIte]
        exact ih (fun r hr => h r (Nat.lt_trans hr (Nat.lt_succ_self n)))

/-- The pre-choice state at round `t` depends only on strict past coordinates;
no current or future row or private draw appears. -/
theorem run_at_current_eq_of_strictPast
    (v w : LocalCoordinates p uninformed held target) (t : Fin p.T)
    (h : ∀ r : Fin p.T, r.val < t.val → roundCoordinatesEq uninformed held target v w r) :
    BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards v) t.val =
    BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards w) t.val :=
  run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards v w t.val h

/-- The actual discovery-positive list and mode after a prefix agree whenever
the underlying local inputs agree on that prefix. -/
theorem positives_and_mode_eq_of_prefixCoordinatesEq
    (v w : LocalCoordinates p uninformed held target) (n : ℕ)
    (h : ∀ r : Fin p.T, r.val < n → roundCoordinatesEq uninformed held target v w r) :
    (BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards v) n).positives =
      (BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards w) n).positives ∧
    (BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards v) n).mode =
      (BootstrapPhysicalBlock.run (blockInput (s := s) uninformed active held privateId ids target rewards w) n).mode := by
  have hr := run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards v w n h
  exact ⟨congrArg BootstrapPhysicalBlock.State.positives hr,
    congrArg BootstrapPhysicalBlock.State.mode hr⟩

/-- The physically generated discovery-positive round set, truncated to a
calendar prefix, is determined by the same strict-prefix data as `run`. -/
theorem discoveryPositiveRounds_prefix_eq
    (v w : LocalCoordinates p uninformed held target) (n : ℕ)
    (h : ∀ r : Fin p.T, r.val < n → roundCoordinatesEq uninformed held target v w r) :
    (BootstrapPhysicalBlock.discoveryPositiveRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards v)).filter
        (fun r => r.val < n) =
    (BootstrapPhysicalBlock.discoveryPositiveRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards w)).filter
        (fun r => r.val < n) := by
  calc
    (BootstrapPhysicalBlock.discoveryPositiveRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards v)).filter
        (fun r => r.val < n) =
      (BootstrapPhysicalBlock.run
        (blockInput (s := s) uninformed active held privateId ids target rewards v) n).positives :=
        (BootstrapPhysicalBlock.run_positives_eq_physical_prefix _ n).symm
    _ = (BootstrapPhysicalBlock.run
        (blockInput (s := s) uninformed active held privateId ids target rewards w) n).positives :=
      congrArg BootstrapPhysicalBlock.State.positives
        (run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards v w n h)
    _ = (BootstrapPhysicalBlock.discoveryPositiveRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards w)).filter
        (fun r => r.val < n) :=
        BootstrapPhysicalBlock.run_positives_eq_physical_prefix _ n

/-- Equality of physical stay rounds strictly before a cutoff. The cutoff may
be inside the block; later current-row and private values are unrestricted. -/
theorem physicalStayRounds_prefix_eq
    (v w : LocalCoordinates p uninformed held target)
    (j : {j // j ∈ uninformed}) (cutoff : Fin p.T)
    (h : ∀ r : Fin p.T, r.val < cutoff.val → roundCoordinatesEq uninformed held target v w r) :
    ((BootstrapPhysicalBlock.physicalStayRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards v) j).filter
        (fun r => r.val < cutoff.val)) =
    ((BootstrapPhysicalBlock.physicalStayRounds
      (blockInput (s := s) uninformed active held privateId ids target rewards w) j).filter
        (fun r => r.val < cutoff.val)) := by
  classical
  simp only [blockInput, inputOf]
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter, BootstrapPhysicalBlock.physicalStayRounds,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hblock, hid, hpos⟩, hcut⟩
    refine ⟨⟨hblock, hid, ?_⟩, hcut⟩
    have hr := run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards
      v w r.val (fun q hq => h q (by omega))
    simp only [blockInput, inputOf] at hr
    rw [hr] at hpos
    have hfeedback := feedback_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids
      target rewards v w (BootstrapPhysicalBlock.run
        (blockInput (s := s) uninformed active held privateId ids target rewards w) r.val) r
      (followerPlayer p.two_le_m j.val) (h r hcut)
    simp only [blockInput, inputOf] at hfeedback
    rw [hfeedback] at hpos
    exact hpos
  · rintro ⟨⟨hblock, hid, hpos⟩, hcut⟩
    refine ⟨⟨hblock, hid, ?_⟩, hcut⟩
    have hr := run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards
      v w r.val (fun q hq => h q (by omega))
    simp only [blockInput, inputOf] at hr
    rw [hr.symm] at hpos
    have hfeedback := feedback_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids
      target rewards v w (BootstrapPhysicalBlock.run
        (blockInput (s := s) uninformed active held privateId ids target rewards v) r.val) r
      (followerPlayer p.two_le_m j.val) (h r hcut)
    simp only [blockInput, inputOf] at hfeedback
    rw [hfeedback.symm] at hpos
    exact hpos

/-- The active-gated physical stay gain accumulated strictly before a cutoff
agrees; no declaration-save or launch flag is an input to this count. -/
theorem physicalStayGain_prefix_eq
    (v w : LocalCoordinates p uninformed held target)
    (j : {j // j ∈ uninformed}) (cutoff : Fin p.T)
    (h : ∀ r : Fin p.T, r.val < cutoff.val → roundCoordinatesEq uninformed held target v w r) :
    (if active j = true then
      ((BootstrapPhysicalBlock.physicalStayRounds
        (blockInput (s := s) uninformed active held privateId ids target rewards v) j).filter
          (fun r => r.val < cutoff.val)).card else 0) =
    (if active j = true then
      ((BootstrapPhysicalBlock.physicalStayRounds
        (blockInput (s := s) uninformed active held privateId ids target rewards w) j).filter
          (fun r => r.val < cutoff.val)).card else 0) := by
  by_cases ha : active j = true
  · simp only [ha]
    rw [physicalStayRounds_prefix_eq (s := s) uninformed active held privateId ids target rewards
      v w j cutoff h]
  · simp [ha]

/-- The observations in the physical `observationTrace` agree at all block
rounds strictly before a cutoff. Externally supplied save and launch flags are
deliberately unrestricted and are not asserted to be measurable or causal. -/
theorem observationTrace_observations_eq_before_cutoff
    (v w : LocalCoordinates p uninformed held target)
    (j : {j // j ∈ uninformed}) (savedV savedW : Fin p.T → Bool)
    (launchV launchW : Bool) (cutoff : Fin p.T)
    (h : ∀ r : Fin p.T, r.val < cutoff.val → roundCoordinatesEq uninformed held target v w r) :
    ∀ t : Fin p.T, t.val < cutoff.val →
      (BootstrapPhysicalBlock.observationTrace
        (blockInput (s := s) uninformed active held privateId ids target rewards v) j savedV launchV).observation t =
      (BootstrapPhysicalBlock.observationTrace
        (blockInput (s := s) uninformed active held privateId ids target rewards w) j savedW launchW).observation t := by
  intro t ht
  by_cases hblock : t ∈ BootstrapDimensions.calendarBlock p s
  · simp only [BootstrapPhysicalBlock.observationTrace, hblock, ↓reduceIte]
    rw [run_eq_of_prefixCoordinatesEq (s := s) uninformed active held privateId ids target rewards
      v w t.val (fun r hr => h r (by omega))]
    exact observationIndex_eq_of_roundCoordinatesEq (s := s) uninformed active held privateId ids
      target rewards v w _ t (followerPlayer p.two_le_m j.val) (h t ht)
  · simp [BootstrapPhysicalBlock.observationTrace, hblock]
