/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.BootstrapOriginalScalarLaw
public import Bandits.Support.BootstrapStayGainMean
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.ReferenceInitializationRun

/-!
# Generated DATA stay-positive conditional mean

The stay test below is evaluated from the actual generated descriptor and
the existing current row and original player-round scalar vector. A missing
descriptor is the stopped branch and contributes zero. A present descriptor
uses its actual incoming set, block draw profile, target, and pre-choice
physical state.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-407,485-505`
and `sources/zip4/manuscript/07_public_setup.tex:27-38,87-109`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedStayConditionalMean

abbrev Parameters := ConstructorDimensions.Parameters

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open BootstrapPrivateRoundStreams PrivateRoundFreshness
open BootstrapOriginalScalarStep
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open BootstrapPhysicalBlock BootstrapModeService BootstrapOriginalScalarLaw
open BootstrapStayAvoidance ReferenceInitializationRun BootstrapPhysicalInput
open ActiveRoundActions
open scoped Classical

variable (p : Parameters)

/-- A fixed complete row used only to fill coordinates outside the current
round in the existing physical input adapter. The test below overwrites the
round `t` row and every current private action value before evaluating actions. -/
def baseRow : CompleteRow p :=
  Classical.choice (nonempty_of_isProbabilityMeasure (completeRowMeasure p))

/-- The existing descriptor data repackaged as the accepted physical-block
input. Its incoming followers and all three draw fields come from the
descriptor's actual generated block profile. -/
def inputOfDescriptor (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (d : Descriptor p) : BootstrapPhysicalBlock.Input p s :=
  let b := d.1
  let draws := d.2.1
  let z := d.2.2.1
  {
    uninformed := ReferenceInitializationRun.uninformed b
    active := fun j => (draws (sourceFollowerIndex p j.1)).1
    held := fun j => (draws (sourceFollowerIndex p j.1)).2.1
    privateId := fun j => (draws (sourceFollowerIndex p j.1)).2.2
    ids := ids
    row := baseRow p
    target := z
    uniform := fun i _ => fullArmScalarDraw p ⟨0, by norm_num⟩
    coordinatorAvoid := fun _ => forbiddenArmScalarDraw p z ⟨0, by norm_num⟩
    followerAvoid := fun j _ =>
      forbiddenArmScalarDraw p ((draws (sourceFollowerIndex p j.1)).2.1)
        ⟨0, by norm_num⟩
    rewards := rewards
  }

/-- The literal guarded stay test on an optional generated descriptor and the
existing original current vector. Descriptor absence and a nonincoming focal
follower have zero analytic count. -/
def dataStayTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (d : Option (Descriptor p) × Current p) : ℝ :=
  match d.1 with
  | none => 0
  | some desc =>
    let x := inputOfDescriptor p ids rewards (s := s) desc
    if hi : i ∈ x.uninformed then
      dataStayPositive x desc.2.2.2 t ⟨i, hi⟩ d.2.1
        (roundPrivateValuesOfOriginalScalars x d.2.2)
    else 0

/-- The actual generated test, with the unchanged descriptor and current
projections of the original source coordinates. -/
def actualDataStayTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (e : Coordinates p) : ℝ :=
  testValue p ids rewards C_star C_h eta s t (dataStayTest p ids rewards (s := s) t i) e

/-- A processed actual descriptor reconstructs the run's own boundary, draw
profile, target, pre-choice state, and source block index. These fields come
from `descriptor_eq_some_iff` and `processed_nextBlock`; none is supplied as
an independent physical premise. -/
theorem actualDescriptor_reconstructs_source_block (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (e : Coordinates p)
    (d : Descriptor p)
    (hdesc : descriptor p ids rewards C_star C_h eta s t e = some d) :
    let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
    let b := ReferenceInitializationRun.run x s.val
    b = d.1 ∧ ∃ h : b.completed < n_boot p,
      BootstrapPhysicalInput.currentBlockDrawProfile p
        (ReferenceInitializationRun.nextBlock b h) b.numerators b.weight_ge_one
          x.coordinates = d.2.1 ∧
      (ReferenceInitializationRun.physical x b h).target = d.2.2.1 ∧
      BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val =
        d.2.2.2 ∧
      ReferenceInitializationRun.nextBlock b h = s := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  have hrec := (descriptor_eq_some_iff ids rewards C_star C_h eta s t e
    d.1 d.2.1 d.2.2.1 d.2.2.2).mp hdesc
  dsimp only at hrec
  rcases hrec with ⟨hb, hcross, hremaining, hprofile, htarget, hstate⟩
  refine ⟨hb, hremaining, ?_, ?_, ?_, ?_⟩
  · simpa [x, b] using hprofile
  · simpa [x, b] using htarget
  · simpa [x, b] using hstate
  · exact processed_nextBlock ids rewards C_star C_h eta s e hcross hremaining

/-- On every processed original input, the bounded current-vector test is the
source block's literal DATA stay event. The descriptor equality supplies the
block profile, target, and exact pre-choice state; the current row and labelled
scalar vector are the original projections at `e`. -/
theorem actualDataStayTest_eq_sourceStayPositive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (e : Coordinates p) (b : Boundary p) (draws : PrivateSourceStreams.BlockDrawProfile p)
    (z : Fin p.K) (st : BootstrapPhysicalBlock.State p)
    (hdesc : descriptor p ids rewards C_star C_h eta s t e = some (b, (draws, (z, st))))
    (hi : i ∈ ReferenceInitializationRun.uninformed b) :
    ∃ h : b.completed < n_boot p,
      let y := ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b h
      let j : {j // j ∈ y.uninformed} :=
        ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩
      actualDataStayTest p ids rewards C_star C_h eta (s := s) t i e =
        BootstrapStayAvoidance.dataStayPositive y st t j (roundCoordinates p t y.row)
          (roundPrivateValuesOfOriginalScalars y
            (fun q => BootstrapPhysicalInput.playerRoundScalarAt p
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates q t)) ∧
      (BootstrapOriginalScalarLaw.physicalOutputOfObservable y st t
        (BootstrapOriginalScalarStep.originalScalarObservable y st t
          (roundCoordinates p t y.row)
          (fun q => BootstrapPhysicalInput.playerRoundScalarAt p
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates q t)) =
        ((roundCoordinates p t y.row, BootstrapPhysicalBlock.actions y st t),
          ((fun q => BootstrapPhysicalBlock.feedback y st t q),
            ((fun q => BootstrapPhysicalBlock.observationIndex y st t q),
              BootstrapPhysicalBlock.step y st t)))) ∧
      (BootstrapStayAvoidance.dataStayPositive y st t j (roundCoordinates p t y.row)
          (roundPrivateValuesOfOriginalScalars y
            (fun q => BootstrapPhysicalInput.playerRoundScalarAt p
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates q t)) =
        if y.active j = true ∧ y.ids (y.privateId j) t = false ∧
            BootstrapPhysicalBlock.slot y t = PublicDiscreteDraws.dataSlot ∧
            0 < BootstrapPhysicalBlock.feedback y st t
              (PublicDiscreteDraws.followerPlayer p.two_le_m j.1)
        then 1 else 0) ∧
      BootstrapPhysicalBlock.run y t.val = st ∧
      ReferenceInitializationRun.nextBlock b h = s := by
  have hrec := actualDescriptor_reconstructs_source_block p ids rewards C_star C_h eta
    (s := s) t e (b, (draws, (z, st))) hdesc
  dsimp only at hrec
  rcases hrec with ⟨hb, hrem, hprofile, htarget, hstate, hindex⟩
  subst b
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let actualBoundary := ReferenceInitializationRun.run source s.val
  have hblock : actualBoundary.completed < n_boot p := by simpa [source] using hrem
  have hprofileB : BootstrapPhysicalInput.currentBlockDrawProfile p
      (ReferenceInitializationRun.nextBlock actualBoundary hblock) actualBoundary.numerators
        actualBoundary.weight_ge_one source.coordinates = draws := by
    simpa [source] using hprofile
  have htargetB : (ReferenceInitializationRun.physical source actualBoundary hblock).target = z := by
    simpa [source, actualBoundary] using htarget
  have hstateB : BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical source actualBoundary hblock) t.val = st := by
    simpa [source, actualBoundary] using hstate
  have hindexB : ReferenceInitializationRun.nextBlock actualBoundary hblock = s := by
    simpa [source, actualBoundary] using hindex
  let y := ReferenceInitializationRun.physical source actualBoundary hblock
  have hz : z = y.target := htargetB.symm
  subst z
  let x := inputOfDescriptor p ids rewards (s := s) (actualBoundary, (draws, (y.target, st)))
  have hmem : i ∈ x.uninformed := by
    simpa [x, inputOfDescriptor] using hi
  have hmemY : i ∈ y.uninformed := by
    change i ∈ ReferenceInitializationRun.uninformed actualBoundary
    exact hi
  let jx : {j // j ∈ x.uninformed} := ⟨i, hmem⟩
  let jy : {j // j ∈ y.uninformed} := ⟨i, hmemY⟩
  have hincoming : x.uninformed = y.uninformed := rfl
  have hactive : ∀ q : {q // q ∈ x.uninformed}, x.active q = y.active q := by
    intro q
    dsimp [x, inputOfDescriptor, y, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput]
    exact congrArg (fun f : PrivateSourceStreams.BlockDrawProfile p =>
      (f (BootstrapPhysicalInput.sourceFollowerIndex p q.1)).1) hprofileB.symm
  have hheld : ∀ q : {q // q ∈ x.uninformed}, x.held q = y.held q := by
    intro q
    dsimp [x, inputOfDescriptor, y, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput]
    exact congrArg (fun f : PrivateSourceStreams.BlockDrawProfile p =>
      ((f (BootstrapPhysicalInput.sourceFollowerIndex p q.1)).2).1) hprofileB.symm
  have hprivateId : ∀ q : {q // q ∈ x.uninformed}, x.privateId q = y.privateId q := by
    intro q
    dsimp [x, inputOfDescriptor, y, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput]
    exact congrArg (fun f : PrivateSourceStreams.BlockDrawProfile p =>
      ((f (BootstrapPhysicalInput.sourceFollowerIndex p q.1)).2).2) hprofileB.symm
  have hids : x.ids = y.ids := rfl
  let r := roundCoordinates p t y.row
  let v : OriginalScalarVector p := fun q =>
    BootstrapPhysicalInput.playerRoundScalarAt p source.coordinates q t
  let cx := BootstrapModeService.currentInputOf x t r (roundPrivateValuesOfOriginalScalars x v)
  let cy := BootstrapModeService.currentInputOf y t r (roundPrivateValuesOfOriginalScalars y v)
  have hslot : BootstrapPhysicalBlock.slot cx t = BootstrapPhysicalBlock.slot cy t := by
    simp [cx, cy, BootstrapModeService.currentInputOf,
      BootstrapModeService.currentInput, BootstrapPhysicalBlock.slot]
  have havoidVal (q : {j // j ∈ x.uninformed}) :
      ((roundPrivateValuesOfOriginalScalars x v).2.2 q).val =
        ((roundPrivateValuesOfOriginalScalars y v).2.2 q).val := by
    change (forbiddenArmScalarDraw p (x.held q)
        (v (PublicDiscreteDraws.followerPlayer p.two_le_m q.1))).val =
      (forbiddenArmScalarDraw p (y.held q)
        (v (PublicDiscreteDraws.followerPlayer p.two_le_m q.1))).val
    rw [hheld q]
  have hfollower (j : Follower p.m) :
      BootstrapPhysicalBlock.followerAction cx t j =
        BootstrapPhysicalBlock.followerAction cy t j := by
    by_cases hj : j ∈ x.uninformed
    · have hjY : j ∈ y.uninformed := by simpa [hincoming] using hj
      let qx : {q // q ∈ x.uninformed} := ⟨j, hj⟩
      let qy : {q // q ∈ y.uninformed} := ⟨j, hjY⟩
      have hqEq : qx = qy := Subtype.ext rfl
      have hactiveAt : x.active qx = y.active qy := by
        calc
          x.active qx = y.active qx := hactive qx
          _ = y.active qy := congrArg y.active hqEq
      have hheldAt : x.held qx = y.held qy := by
        calc
          x.held qx = y.held qx := hheld qx
          _ = y.held qy := congrArg y.held hqEq
      have hprivateIdAt : x.privateId qx = y.privateId qy := by
        calc
          x.privateId qx = y.privateId qx := hprivateId qx
          _ = y.privateId qy := congrArg y.privateId hqEq
      have hcx : j ∈ cx.uninformed := by change j ∈ x.uninformed; exact hj
      have hcy : j ∈ cy.uninformed := by change j ∈ y.uninformed; exact hjY
      have hactiveCurrent : cx.active qx = cy.active qy := hactiveAt
      have hheldCurrent : cx.held qx = cy.held qy := hheldAt
      have hprivateIdCurrent : cx.privateId qx = cy.privateId qy := hprivateIdAt
      have hidCurrent : cx.ids (cx.privateId qx) t = cy.ids (cy.privateId qy) t := by
        change x.ids (x.privateId qx) t = y.ids (y.privateId qy) t
        rw [hids, hprivateIdAt]
      have havoidRound :
          ((roundPrivateValuesOfOriginalScalars x v).2.2 qx).val =
            ((roundPrivateValuesOfOriginalScalars y v).2.2 qy).val := by
        calc
          ((roundPrivateValuesOfOriginalScalars x v).2.2 qx).val =
              ((roundPrivateValuesOfOriginalScalars y v).2.2 qx).val := havoidVal qx
          _ = ((roundPrivateValuesOfOriginalScalars y v).2.2 qy).val :=
            congrArg (fun q : {q // q ∈ y.uninformed} =>
              ((roundPrivateValuesOfOriginalScalars y v).2.2 q).val) hqEq
      have havoidCurrent : (cx.followerAvoid qx t).val = (cy.followerAvoid qy t).val := by
        simpa [cx, cy, BootstrapModeService.currentInputOf,
          BootstrapModeService.currentInput] using havoidRound
      have huniformCurrent :
          cx.uniform (PublicDiscreteDraws.followerPlayer p.two_le_m j) t =
            cy.uniform (PublicDiscreteDraws.followerPlayer p.two_le_m j) t := by
        simp [cx, cy, BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
          roundPrivateValuesOfOriginalScalars]
      simp only [BootstrapPhysicalBlock.followerAction, hcx, hcy]
      change BootstrapPhysicalBlock.uninformedAction cx t qx =
        BootstrapPhysicalBlock.uninformedAction cy t qy
      unfold BootstrapPhysicalBlock.uninformedAction
      rw [← hactiveCurrent]
      by_cases ha : cx.active qx = true
      · simp only [ha]
        rw [← hidCurrent]
        by_cases hid : cx.ids (cx.privateId qx) t = true
        · simp only [hid]
          exact havoidCurrent
        · simp only [hid]
          exact hheldCurrent
      · simp only [ha]
        exact huniformCurrent
    · have hjY : j ∉ y.uninformed := by simpa [hincoming] using hj
      simp [BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.unoccupiedAction,
        cx, cy, BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
        BootstrapPhysicalBlock.slot, BootstrapPhysicalBlock.tuple, BootstrapPhysicalBlock.pilot,
        BootstrapPhysicalBlock.selected, BootstrapPhysicalBlock.initialUpBit, hj, hjY]
  have hactions : BootstrapPhysicalBlock.actions cx st t =
      BootstrapPhysicalBlock.actions cy st t := by
    funext q
    by_cases hq : q = ActiveRoundActions.coordinator p.two_le_m
    · subst q
      simp [BootstrapPhysicalBlock.actions, BootstrapPhysicalBlock.coordinatorAction,
        cx, cy,
        BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
        roundPrivateValuesOfOriginalScalars, BootstrapPhysicalBlock.slot,
        BootstrapPhysicalBlock.forwardProduct, BootstrapPhysicalBlock.tuple,
        x, y, inputOfDescriptor, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput]
    · simpa [BootstrapPhysicalBlock.actions, hq, cx, cy] using
        hfollower (ActiveRoundActions.followerIndex p.two_le_m q hq)
  have hfeedback : BootstrapPhysicalBlock.feedback cx st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      BootstrapPhysicalBlock.feedback cy st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    have hrewardsCurrent : cx.rewards = cy.rewards := rfl
    simp only [BootstrapPhysicalBlock.feedback, hactions]
    rw [hrewardsCurrent]
  have hstay : BootstrapStayAvoidance.dataStayPositive x st t jx r
        (roundPrivateValuesOfOriginalScalars x v) =
      BootstrapStayAvoidance.dataStayPositive y st t jy r
        (roundPrivateValuesOfOriginalScalars y v) := by
    unfold BootstrapStayAvoidance.dataStayPositive
    rw [hactive jx, hids, hprivateId jx, hslot, hfeedback]
    rfl
  have htest : actualDataStayTest p ids rewards C_star C_h eta (s := s) t i e =
      BootstrapStayAvoidance.dataStayPositive x st t jx r
        (roundPrivateValuesOfOriginalScalars x v) := by
    simp only [actualDataStayTest, testValue, hdesc, dataStayTest, current]
    change (if hm : i ∈ x.uninformed then
        BootstrapStayAvoidance.dataStayPositive x st t ⟨i, hm⟩ r
          (roundPrivateValuesOfOriginalScalars x v) else 0) =
      BootstrapStayAvoidance.dataStayPositive x st t jx r
        (roundPrivateValuesOfOriginalScalars x v)
    by_cases hm : i ∈ x.uninformed
    · simp [hm, jx]
    · simp only [hm]
      exact (hm hmem).elim
  have houtputs := originalScalar_source_outputs_blockInput
    (ReferenceInitializationRun.nextBlock actualBoundary hblock)
    (ReferenceInitializationRun.uninformed actualBoundary) actualBoundary.numerators
    actualBoundary.weight_ge_one ids e.1 rewards source.coordinates t st jy
  have hsourceEvent := houtputs.2
  refine ⟨hblock, ?_⟩
  constructor
  · rw [htest, hstay]
  · constructor
    · exact houtputs.1
    · constructor
      · exact hsourceEvent
      · exact ⟨hstateB, hindexB⟩

/-- Structural conditioning event for the fixed-snapshot input: the generated
descriptor is present, contains the focal follower, that follower is active
with held arm `a`, the target is `z ≠ a`, and every other incoming follower
is inactive. -/
def isolationGuard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K) :
    Option (Descriptor p) → Prop
  | none => False
  | some d =>
    ∃ hi : i ∈ ReferenceInitializationRun.uninformed d.1,
      let x := inputOfDescriptor p ids rewards (s := s) d
      let j : {j // j ∈ x.uninformed} := ⟨i, hi⟩
      x.active j = true ∧ x.held j = a ∧ x.target = z ∧ z ≠ a ∧
        ∀ k : {j // j ∈ x.uninformed}, k ≠ j → x.active k = false

/-- The source support and actual generated ID-zero factor attached to the
focal follower in a descriptor. It vanishes when the descriptor is stopped or
the focal follower is not incoming. -/
def dataStayLowerBound (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m) (a : Fin p.K)
    (d : Option (Descriptor p)) : ℝ :=
  match d with
  | none => 0
  | some desc =>
    let x := inputOfDescriptor p ids rewards (s := s) desc
    if hi : i ∈ x.uninformed then
      let j : {j // j ∈ x.uninformed} := ⟨i, hi⟩
      chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0) / 16
    else 0

/-- The test is jointly Borel measurable on the actual descriptor and the
entire current original public/private vector. -/
theorem measurable_dataStayTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m) :
    Measurable (dataStayTest p ids rewards (s := s) t i) := by
  apply measurable_from_prod_countable_right
  intro d
  cases d with
  | none => exact measurable_const
  | some desc =>
    let x := inputOfDescriptor p ids rewards (s := s) desc
    by_cases hi : i ∈ x.uninformed
    · have hmeas := measurable_originalScalar_dataStayPositive x desc.2.2.2 t ⟨i, hi⟩
      convert hmeas using 1
      funext c
      simp [dataStayTest, x, hi]
    · have hmeas : Measurable (fun _ : Current p => (0 : ℝ)) := measurable_const
      convert hmeas using 1
      funext c
      simp [dataStayTest, x, hi]

/-- The literal test is a zero-or-one indicator, including the stopped branch. -/
theorem dataStayTest_unit_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (d : Option (Descriptor p) × Current p) :
    0 ≤ dataStayTest p ids rewards (s := s) t i d ∧
      dataStayTest p ids rewards (s := s) t i d ≤ 1 := by
  cases hd : d.1 with
  | none => simp [dataStayTest, hd]
  | some desc =>
    let x := inputOfDescriptor p ids rewards (s := s) desc
    by_cases hi : i ∈ x.uninformed
    · simp only [dataStayTest, hd]
      unfold dataStayPositive
      split_ifs <;> norm_num
    · simp only [dataStayTest, hd]
      split_ifs with h
      · exact (hi h).elim
      · norm_num

/-- The source-clock process associated with one fixed round. All other clock
indices are zero; at `t.val + 1` the value is exactly the generated stay test. -/
def sourceClockTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m) :
    ℕ → Coordinates p → ℝ := fun n e =>
  if n = t.val + 1 then actualDataStayTest p ids rewards C_star C_h eta (s := s) t i e
  else 0

theorem sourceClockTest_at_round (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (e : Coordinates p) :
    sourceClockTest p ids rewards C_star C_h eta (s := s) t i (t.val + 1) e =
      actualDataStayTest p ids rewards C_star C_h eta (s := s) t i e := by
  simp [sourceClockTest]

/-- Adaptation of the actual stay test to the next source-clock sigma algebra. -/
theorem measurable_actualDataStayTest_succ (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (ht : t ∈ calendarBlock p s) :
    Measurable[analysisFiltration p (t.val + 1)]
      (actualDataStayTest p ids rewards C_star C_h eta (s := s) t i) := by
  have hd := (measurable_descriptor p ids rewards C_star C_h eta s t ht).mono
    ((analysisFiltration p).mono (Nat.le_succ t.val)) le_rfl
  have hc := measurable_current_succ p t
  exact (measurable_dataStayTest p ids rewards (s := s) t i).comp (hd.prodMk hc)

/-- The generated conditional-expectation identity for the specific actual
stay test. It uses the accepted product-law identity, with no descriptor-atom
mass premise. -/
theorem actualDataStayTest_condExp_identity (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (ht : t ∈ calendarBlock p s) :
    condExp (analysisFiltration p t.val) (originalLaw p)
      (actualDataStayTest p ids rewards C_star C_h eta (s := s) t i) =ᵐ[originalLaw p]
        conditionalKernelValue p ids rewards C_star C_h eta s t
          (dataStayTest p ids rewards (s := s) t i) := by
  exact actual_condExp_identity p ids rewards C_star C_h eta s t ht
    (dataStayTest p ids rewards (s := s) t i)
    (measurable_dataStayTest p ids rewards (s := s) t i) 1 (by norm_num)
    (fun z => by
      have h := dataStayTest_unit_bounds p ids rewards (s := s) t i z
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩)

/-- Integrability of this concrete stopped/guarded test follows from its joint
Borel measurability and unit bound through the accepted filtration API. -/
theorem integrable_actualDataStayTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (ht : t ∈ calendarBlock p s) :
    Integrable (actualDataStayTest p ids rewards C_star C_h eta (s := s) t i)
      (originalLaw p) := by
  exact integrable_testValue p ids rewards C_star C_h eta s t ht
    (dataStayTest p ids rewards (s := s) t i) (measurable_dataStayTest p ids rewards (s := s) t i)
    1 (by norm_num) (fun z => by
      have h := dataStayTest_unit_bounds p ids rewards (s := s) t i z
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩)

/-- The source-clock form used by `BootstrapIntervalBounds.conditionalMean` is
the same conditional expectation at `F(t.val)`. -/
theorem sourceClockConditionalMean_eq_kernel (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (ht : t ∈ calendarBlock p s) :
    BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
      (sourceClockTest p ids rewards C_star C_h eta (s := s) t i) (t.val + 1) =ᵐ[originalLaw p]
        conditionalKernelValue p ids rewards C_star C_h eta s t
          (dataStayTest p ids rewards (s := s) t i) := by
  rw [BootstrapIntervalBounds.conditionalMean]
  have htest : sourceClockTest p ids rewards C_star C_h eta (s := s) t i
      (t.val + 1) = actualDataStayTest p ids rewards C_star C_h eta
        (s := s) t i := by
    funext e
    exact sourceClockTest_at_round p ids rewards C_star C_h eta (s := s) t i e
  rw [htest, Nat.add_sub_cancel]
  exact actualDataStayTest_condExp_identity p ids rewards C_star C_h eta t i ht

/-- Pointwise structural lower bound for the conditional kernel. The guard is
formed from the actual descriptor's incoming set and recorded block draws. -/
theorem conditionalKernel_ge_of_isolation (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m) (a z : Fin p.K)
    (ht : t ∈ calendarBlock p s) (d : Option (Descriptor p))
    (hg : isolationGuard p ids rewards (s := s) i a z d) :
    conditionalKernel p (dataStayTest p ids rewards (s := s) t i) d ≥
      dataStayLowerBound p ids rewards (s := s) t i a d := by
  cases d with
  | none => exact (False.elim hg)
  | some desc =>
    rcases hg with ⟨hi, hactive, hheld, htarget, hza, hinactive⟩
    let x := inputOfDescriptor p ids rewards (s := s) desc
    let j : {j // j ∈ x.uninformed} := ⟨i, hi⟩
    have hmem : i ∈ x.uninformed := by
      simpa [x, inputOfDescriptor] using hi
    have hmode : desc.2.2.2.mode = .discover ∨ desc.2.2.2.mode = .multicast := by
      cases desc.2.2.2.mode <;> simp
    have hmean := originalScalar_dataStayPositive_mean_ge x desc.2.2.2 t j a z ht
      hactive hheld htarget hza hinactive hmode
    have hkernel : conditionalKernel p (dataStayTest p ids rewards (s := s) t i)
        (some desc) =
        ∫ c : Current p, dataStayPositive x desc.2.2.2 t j c.1
          (roundPrivateValuesOfOriginalScalars x c.2) ∂currentLaw p := by
      dsimp [conditionalKernel, dataStayTest]
      have hmem' : i ∈ (inputOfDescriptor p ids rewards (s := s) desc).uninformed := by
        simpa [x] using hmem
      congr 1
      funext c
      split_ifs
      · apply congrArg (fun q : {j // j ∈ x.uninformed} =>
          dataStayPositive x desc.2.2.2 t q c.1
            (roundPrivateValuesOfOriginalScalars x c.2))
        apply Subtype.ext
        rfl
    have hlower : dataStayLowerBound p ids rewards (s := s) t i a (some desc) =
        chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0) / 16 := by
      simp [dataStayLowerBound, x, hmem, j]
    rw [hkernel, hlower]
    simpa [Current, currentLaw, originalScalarSnapshotMeasure,
      originalScalarVectorMeasure, currentRoundScalarLaw] using hmean

/-- The actual conditional mean obeys the specific stay lower bound almost
everywhere on the structural isolation event. The implication is pointwise in
the original generated input and does not condition on an atom of positive
mass. -/
theorem sourceClockConditionalMean_ge_of_isolation (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m) (a z : Fin p.K)
    (ht : t ∈ calendarBlock p s) :
    ∀ᵐ e ∂originalLaw p,
      isolationGuard p ids rewards (s := s) i a z
        (descriptor p ids rewards C_star C_h eta s t e) →
      BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
        (sourceClockTest p ids rewards C_star C_h eta (s := s) t i) (t.val + 1) e ≥
        dataStayLowerBound p ids rewards (s := s) t i a
          (descriptor p ids rewards C_star C_h eta s t e) := by
  filter_upwards [sourceClockConditionalMean_eq_kernel p ids rewards C_star C_h eta
    t i ht] with e hmean
  intro hg
  rw [hmean]
  exact conditionalKernel_ge_of_isolation p ids rewards t i a z ht
    (descriptor p ids rewards C_star C_h eta s t e) hg

end Bandits.Support.GeneratedStayConditionalMean

end
