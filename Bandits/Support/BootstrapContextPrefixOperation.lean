/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPrivateIDFibers
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.FalseForwardContextBound
public import Bandits.Support.FalseRowSliceFactorization
public import Bandits.Support.ForwardPrefixSlice
public import Bandits.Support.GeneratedBootstrapSupportContext
public import Bandits.Support.GeneratedEligibleFamily
public import Bandits.Support.GeneratedForwardPrefixTests

/-!
# Explicit two-player context prefix tests

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-338,350-365`
and `sources/zip4/manuscript/07_public_setup.tex:27-38,75-113,123-140`.

The operation below is an analysis projection on the existing finite source
context, the fixed numerical base, a private ID, and the original coordinator
and focal-player round scalars. It creates no physical input or peer action
profile. Its eligibility reads no false forward coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPrivateIDFibers
open Bandits.Support.FalseForwardContextBound
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.GeneratedBootstrapSupportContext
open Bandits.Support.GeneratedEligibleFamily
open Bandits.Support.GeneratedForwardPrefixTests
open scoped Classical

namespace Bandits.Support.BootstrapContextPrefixOperation

variable {p : ConstructorDimensions.Parameters}

/-- The accepted context's original, shortened block-time subtype. -/
abbrev ContextTime (c : Context p) := FalseRowSliceFactorization.BlockTime p c.1

/-- The pair of original round-scalar streams extracted by the accepted
private-ID fiber split: coordinator first, tested follower second. -/
abbrev RoundPair (s : Fin (n_boot p)) :=
  (BootstrapPrivateIDFibers.BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
    (BootstrapPrivateIDFibers.BlockTime p s → BootstrapPrivateIDFibers.Scalar)

abbrev LocalRoundPair (c : Context p) := RoundPair c.1

/-- The source row label fixed by the context. -/
def trueRowIndex (c : Context p) : Fin (M p) := c.2.1

/-- The source follower label fixed by the context. -/
def followerIndex (c : Context p) : Fin (p.m - 1) := c.2.2.1

/-- The held arm fixed by the context. -/
def heldArm (c : Context p) : Fin p.K := c.2.2.2.1

/-- The coordinator target fixed by the context. -/
def targetArm (c : Context p) : Fin p.K := c.2.2.2.2.1

/-- The focal-arm support and peer-avoidance vector from the context. -/
def heldSupport (c : Context p) : ContextTime c → Bool := c.2.2.2.2.2.1

/-- The target-arm support and peer-avoidance vector from the context. -/
def targetSupport (c : Context p) : ContextTime c → Bool := c.2.2.2.2.2.2

/-- The original local coordinates from the accepted fiber split. -/
def localCoordinates (s : Fin (n_boot p)) (i : Fin (p.m - 1))
    (hi : i.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p) :
    BootstrapPrivateIDFibers.LocalCoordinates p s :=
  (BootstrapPrivateIDFibers.splitEquiv p s i hi rho).2

/-- Restrict the original local coordinates to their coordinator/follower
round-scalar pair. -/
def originalRoundPair (s : Fin (n_boot p)) (i : Fin (p.m - 1))
    (hi : i.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p) :
    RoundPair s :=
  (localCoordinates s i hi rho).2

/-- The extracted pair is exactly the two original scalar sequences on this
same possibly shortened block. -/
theorem originalRoundPair_eq_source (s : Fin (n_boot p))
    (i : Fin (p.m - 1)) (hi : i.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    originalRoundPair s i hi rho =
      (fun t : BootstrapPrivateIDFibers.BlockTime p s =>
        BootstrapPhysicalInput.playerRoundScalarAt p rho
          (ActiveRoundActions.coordinator p.two_le_m) t.1,
       fun t : BootstrapPrivateIDFibers.BlockTime p s =>
        BootstrapPhysicalInput.playerRoundScalarAt p rho
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (BootstrapPrivateIDFibers.sourceFollower p i)) t.1) := by
  change ((BootstrapPrivateIDFibers.splitEquiv p s i hi rho).2.2) = _
  apply Prod.ext
  · funext t
    exact BootstrapPrivateIDFibers.split_coordinatorRound_scalar p s i hi rho t
  · funext t
    have h := BootstrapPrivateIDFibers.split_followerRound_scalar p s i hi rho t
    simpa [BootstrapPhysicalInput.playerRoundScalarAt,
      BootstrapPrivateIDFibers.sourceFollower, PublicDiscreteDraws.followerPlayer] using h

private def modeEquiv : Bool ≃ BootstrapPhysicalBlock.Mode :=
  { toFun := fun b => if b then .multicast else .discover
    invFun := fun mode => if mode = .multicast then true else false
    left_inv := by intro b; cases b <;> rfl
    right_inv := by intro mode; cases mode <;> rfl }

private instance modeFintype : Fintype BootstrapPhysicalBlock.Mode :=
  Fintype.ofEquiv Bool modeEquiv

private theorem finite_physicalState (p : ConstructorDimensions.Parameters) :
    Finite (BootstrapPhysicalBlock.State p) := by
  classical
  exact Finite.of_injective
    (fun st : BootstrapPhysicalBlock.State p => (st.list, st.mode, st.positives))
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

private instance physicalStateFinite (p : ConstructorDimensions.Parameters) :
    Finite (BootstrapPhysicalBlock.State p) := finite_physicalState p

private theorem physicalStateCoordinates_injective :
    Function.Injective (Bandits.Support.BootstrapBlockCausality.stateCoordinates
      (p := p)) := by
  intro x y h
  cases x
  cases y
  simp only [Bandits.Support.BootstrapBlockCausality.stateCoordinates,
    Prod.mk.injEq] at h
  rcases h with ⟨hlist, hmode, hpositive⟩
  cases hlist
  cases hmode
  cases hpositive
  rfl

private instance physicalStateMeasurableSingleton :
    MeasurableSingletonClass (BootstrapPhysicalBlock.State p) where
  measurableSet_singleton st := by
    change ∃ q, MeasurableSet q ∧
      Bandits.Support.BootstrapBlockCausality.stateCoordinates
        (p := p) ⁻¹' q = {st}
    refine ⟨{Bandits.Support.BootstrapBlockCausality.stateCoordinates st},
      measurableSet_singleton _, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact physicalStateCoordinates_injective h
    · intro h
      exact congrArg
        (Bandits.Support.BootstrapBlockCausality.stateCoordinates (p := p)) h

/-- The active focal action on a context slot. The action is held on an ID
zero and is the exact inverse-categorical avoid-arm draw on an ID one. -/
def focalAction (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c) (t : ContextTime c) : Fin p.K :=
  if base.1 u t.1 then
    (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (heldArm c) (rounds.2 t)).val
  else heldArm c

/-- The original true-row forward product, retained only for MULTICAST. -/
def trueForwardProduct (c : Context p) (base : FalseFactorBase p)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) : ℕ :=
  ∏ u ∈ st.list, if base.2.2 u t.1 then 1 else 0

/-- Coordinator action in the literal projected operation. DATA uses the
context target and the true-row forward product; DOWN uses the true-row tuple;
UP uses the coordinator's own original scalar. -/
def coordinatorAction (c : Context p) (base : FalseFactorBase p)
    (rounds : LocalRoundPair c) (st : BootstrapPhysicalBlock.State p)
    (t : ContextTime c) : Fin p.K :=
  if slotDraw ((base.2.1 (trueRowIndex c)) t.1).1 = dataSlot then
    if st.mode = .multicast ∧ trueForwardProduct c base st t = 1 then
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (targetArm c)
        (rounds.1 t)).val
    else targetArm c
  else if slotDraw ((base.2.1 (trueRowIndex c)) t.1).1 = downSlot then
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      ((base.2.1 (trueRowIndex c)) t.1).1).val
      (ActiveRoundActions.coordinator p.two_le_m)
  else BootstrapPrivateRoundStreams.fullArmScalarDraw p (rounds.1 t)

/-- One literal context-state step. Discovery positivity is the held-target
support bit conjoined with the focal action avoiding the target. The ID-column
filter and next-round MULTICAST switch match the accepted physical step. -/
def stateStepFromAvoidance (c : Context p) (base : FalseFactorBase p)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) (avoid : Bool) :
    BootstrapPhysicalBlock.State p :=
  if st.mode = .discover ∧
      slotDraw ((base.2.1 (trueRowIndex c)) t.1).1 = dataSlot ∧
      targetSupport c t = true ∧ avoid = true then
    let kept := st.list.filter fun v => base.1 v t.1 = true
    ⟨kept, if kept.card ≤ L0 p then .multicast else .discover,
      insert t.1 st.positives⟩
  else st

/-- One literal context-state step. Discovery positivity is the held-target
support bit conjoined with the focal action avoiding the target. The ID-column
filter and next-round MULTICAST switch match the accepted physical step. -/
def stateStep (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) :
    BootstrapPhysicalBlock.State p :=
  stateStepFromAvoidance c base st t
    (decide (focalAction c base u rounds t ≠ targetArm c))

/-- Coordinator state at every calendar prefix, initialized from the accepted
physical block initial state. Outside this context's block the trace is held
fixed, matching the accepted block operation. -/
def stateTrace (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c) : ℕ → BootstrapPhysicalBlock.State p
  | 0 => BootstrapPhysicalBlock.initialState p
  | n + 1 =>
      if hn : n < p.T then
        let t : Fin p.T := ⟨n, hn⟩
        if hblock : t ∈ calendarBlock p c.1 then
          stateStep c base u rounds (stateTrace c base u rounds n) ⟨t, hblock⟩
        else stateTrace c base u rounds n
      else stateTrace c base u rounds n

theorem stateTrace_succ (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c) (n : ℕ) :
    stateTrace c base u rounds (n + 1) =
      if hn : n < p.T then
        let t : Fin p.T := ⟨n, hn⟩
        if hblock : t ∈ calendarBlock p c.1 then
          stateStep c base u rounds (stateTrace c base u rounds n) ⟨t, hblock⟩
        else stateTrace c base u rounds n
      else stateTrace c base u rounds n := by
  rfl

@[simp] theorem stateTrace_zero (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c) :
    stateTrace c base u rounds 0 = BootstrapPhysicalBlock.initialState p := rfl

/-- The focal ID-zero positive test. False-forward coordinates do not occur. -/
def focalPositive (c : Context p) (base : FalseFactorBase p)
    (rounds : LocalRoundPair c)
    (st : BootstrapPhysicalBlock.State p) (t : ContextTime c) : Bool :=
  heldSupport c t && decide
    (coordinatorAction c base rounds st t ≠ heldArm c)

/-- Candidate eligibility intersects the actual context's ID-zero positive
test with this candidate's own continuous learning-row DATA slot. -/
def candidateEligibleSet (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c) (v : Fin (M p)) :
    Finset (Fin p.T) :=
  (calendarBlock p c.1).filter fun t =>
    base.1 u t = false ∧
      slotDraw ((base.2.1 v) t).1 = dataSlot ∧
      (if ht : t ∈ calendarBlock p c.1 then
        focalPositive c base rounds
          (stateTrace c base u rounds t.val) ⟨t, ht⟩ = true
      else False)

private theorem measurable_forbiddenArmValue (a : Fin p.K) :
    Measurable (fun x : BootstrapPrivateRoundStreams.Scalar =>
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p a x).val) := by
  exact (Measurable.of_discrete :
    Measurable (fun b : BootstrapPrivateRoundStreams.ArmAvoiding p a => b.val)).comp
      (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p a)

private theorem measurable_decide_ne {α : Type*} [MeasurableSpace α]
    (f : α → Fin p.K) (hf : Measurable f) (a : Fin p.K) :
    Measurable (fun x => decide (f x ≠ a)) := by
  exact (measurable_of_finite (fun b : Fin p.K => decide (b ≠ a))).comp hf

/-- The held-or-avoid action is measurable in the original focal scalar. -/
theorem measurable_focalAction (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun rounds : LocalRoundPair c => focalAction c base u rounds t) := by
  cases hid : base.1 u t.1 with
  | false =>
    simp only [focalAction, hid]
    exact measurable_const
  | true =>
    simp only [focalAction, hid, ↓reduceIte]
    exact measurable_forbiddenArmValue (p := p) (heldArm c) |>.comp
      ((measurable_pi_apply t).comp measurable_snd)

/-- Coordinator action measurability at a fixed source state. -/
private theorem measurable_coordinatorAction_at_state (c : Context p)
    (base : FalseFactorBase p) (st : BootstrapPhysicalBlock.State p)
    (t : ContextTime c) :
    Measurable (fun rounds : LocalRoundPair c =>
      coordinatorAction c base rounds st t) := by
  have hscalar : Measurable (fun rounds : LocalRoundPair c => rounds.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  by_cases hd : slotDraw ((base.2.1 (trueRowIndex c)) t.1).1 = dataSlot
  · by_cases hm : st.mode = .multicast
    · by_cases hp : trueForwardProduct c base st t = 1
      · simp only [coordinatorAction, ite_eq_left hd, hm, hp]
        change Measurable (fun rounds : LocalRoundPair c =>
          (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (targetArm c)
            (rounds.1 t)).val)
        simpa only [Function.comp_def] using
          (measurable_forbiddenArmValue (p := p) (targetArm c)).comp hscalar
      · simp only [coordinatorAction, ite_eq_left hd, hm, hp]
        exact measurable_const
    · simp only [coordinatorAction, ite_eq_left hd, hm]
      exact measurable_const
  · by_cases hdown : slotDraw ((base.2.1 (trueRowIndex c)) t.1).1 = downSlot
    · simp only [coordinatorAction, ite_eq_right hd, ite_eq_left hdown]
      exact measurable_const
    · simp only [coordinatorAction, ite_eq_right hd, ite_eq_right hdown]
      change Measurable (fun rounds : LocalRoundPair c =>
        BootstrapPrivateRoundStreams.fullArmScalarDraw p (rounds.1 t))
      simpa only [Function.comp_def] using
        (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp hscalar

/-- The projected state step is a measurable finite-state update once the
focal avoid bit is supplied. -/
private theorem measurable_stateStepFromAvoidance (c : Context p)
    (base : FalseFactorBase p) (t : ContextTime c) :
    Measurable (fun q : BootstrapPhysicalBlock.State p × Bool =>
      stateStepFromAvoidance c base q.1 t q.2) := by
  exact measurable_of_finite _

/-- Every finite prefix of the explicit state recursion is measurable in the
original local coordinator/follower scalar pair. -/
theorem measurable_stateTrace (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) :
    ∀ n, Measurable (fun rounds : LocalRoundPair c =>
      stateTrace c base u rounds n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      by_cases hn : n < p.T
      · let t : Fin p.T := ⟨n, hn⟩
        by_cases hblock : t ∈ calendarBlock p c.1
        · let bt : ContextTime c := ⟨t, hblock⟩
          let avoid (rounds : LocalRoundPair c) : Bool :=
            decide (focalAction c base u rounds bt ≠ targetArm c)
          have havoid : Measurable avoid :=
            measurable_decide_ne (fun rounds => focalAction c base u rounds bt)
              (measurable_focalAction c base u bt) (targetArm c)
          let update (q : BootstrapPhysicalBlock.State p × Bool) :=
            stateStepFromAvoidance c base q.1 bt q.2
          have hupdate : Measurable update := measurable_stateStepFromAvoidance c base bt
          have hpair : Measurable (fun rounds : LocalRoundPair c =>
              (stateTrace c base u rounds n, avoid rounds)) := ih.prodMk havoid
          have htrace : ∀ rounds : LocalRoundPair c,
              stateTrace c base u rounds (n + 1) =
                update (stateTrace c base u rounds n, avoid rounds) := by
            intro rounds
            simp [stateTrace, hn, t, hblock, bt, update, avoid, stateStep]
          have hfun : (fun rounds : LocalRoundPair c =>
              stateTrace c base u rounds (n + 1)) =
              (fun rounds => update (stateTrace c base u rounds n, avoid rounds)) :=
            funext htrace
          rw [hfun]
          exact hupdate.comp hpair
        · simpa [stateTrace, hn, t, hblock] using ih
      · simpa [stateTrace, hn] using ih

/-- Measurability of the projected coordinator action when its state is the
explicit state trace. -/
private theorem measurable_coordinatorAction_onTrace (c : Context p)
    (base : FalseFactorBase p) (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun rounds : LocalRoundPair c =>
      coordinatorAction c base rounds (stateTrace c base u rounds t.1) t) := by
  classical
  let branches : ∀ st : BootstrapPhysicalBlock.State p,
      Measurable (fun rounds : LocalRoundPair c => coordinatorAction c base rounds st t) :=
    fun st => measurable_coordinatorAction_at_state c base st t
  have hjoint : Measurable (fun q : BootstrapPhysicalBlock.State p × LocalRoundPair c =>
      coordinatorAction c base q.2 q.1 t) :=
    measurable_from_prod_countable_right branches
  exact hjoint.comp
    ((measurable_stateTrace c base u t.1).prodMk measurable_id)

/-- The context focal-positive test is measurable in the two original local
round-scalar sequences. -/
theorem measurable_focalPositive (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (t : ContextTime c) :
    Measurable (fun rounds : LocalRoundPair c =>
      focalPositive c base rounds (stateTrace c base u rounds t.1) t) := by
  have hcoord := measurable_coordinatorAction_onTrace c base u t
  have hne := measurable_decide_ne
    (fun rounds => coordinatorAction c base rounds
      (stateTrace c base u rounds t.1) t) hcoord (heldArm c)
  cases hs : heldSupport c t with
  | false =>
    simp only [focalPositive, hs, Bool.false_and]
    exact measurable_const
  | true =>
    simp only [focalPositive, hs, Bool.true_and]
    exact hne

/-- The fixed-context, fixed-base, fixed-ID eligible-family function is
measurable in `BootstrapPrivateIDFibers.roundPairLaw`'s local pair carrier. -/
theorem measurable_candidateEligibleSet (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (v : Fin (M p)) :
    Measurable (fun rounds : LocalRoundPair c =>
      candidateEligibleSet c base u rounds v) := by
  classical
  apply (measurable_finset_iff).2
  intro t
  by_cases hblock : t ∈ calendarBlock p c.1
  · by_cases hid : base.1 u t = false
    · by_cases hslot : slotDraw ((base.2.1 v) t).1 = dataSlot
      · apply measurableSet_setOfPred.mp
        have htest : Measurable (fun rounds : LocalRoundPair c =>
            focalPositive c base rounds
              (stateTrace c base u rounds t.val) ⟨t, hblock⟩) :=
          measurable_focalPositive c base u ⟨t, hblock⟩
        have hset : {rounds : LocalRoundPair c |
            t ∈ candidateEligibleSet c base u rounds v} =
            {rounds | focalPositive c base rounds
              (stateTrace c base u rounds t.val) ⟨t, hblock⟩ = true} := by
          ext rounds
          simp [candidateEligibleSet, hblock, hid, hslot]
        rw [hset]
        exact htest (measurableSet_singleton true)
      · simp [candidateEligibleSet, hblock, hid, hslot]
    · simp [candidateEligibleSet, hblock, hid]
  · simp [candidateEligibleSet, hblock]

/-- A projected candidate's chronological eligible list, built by the
accepted generic finite-set sort operation. -/
def candidateEligibleListFunction (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (v : Fin (M p)) :
    ForwardPrefixSlice.EligibleListFunction p c.1 (LocalRoundPair c) where
  choose := fun rounds => candidateEligibleSet c base u rounds v
  choose_subset := fun _ _ ht => (Finset.mem_filter.mp ht).1
  measurable_choose := measurable_candidateEligibleSet c base u v

/-- The candidate's full chronological eligible list; there is no truncation
when a decoder would save a declaration. -/
def candidateEligibleTimes (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (v : Fin (M p)) (rounds : LocalRoundPair c) :
    List (Fin p.T) :=
  ForwardPrefixSlice.chronologicalEligibleTimes
    (candidateEligibleListFunction c base u v) rounds

/-- Apply the accepted prefix-slice test to the projected eligible list and
the tested false candidate's own numerical forward row at this private ID. -/
def candidatePasses (c : Context p) (base : FalseFactorBase p)
    (u : Fin (A_id p)) (rounds : LocalRoundPair c)
    (v : FalseRowSliceFactorization.FalseRow p (trueRowIndex c))
    (falseRows : FalseRowSliceFactorization.FalseForwardRows p (trueRowIndex c)) :
    Prop :=
  ForwardPrefixSlice.privatePrefixPasses
    (candidateEligibleListFunction c base u v.1) rounds
    (fun t => falseRows v u t)

/-- Restrict an existing physical block time to its matching source context
time, without extending the source block past its shortened endpoint. -/
def actualContextTime
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (t : FalseRowSliceFactorization.BlockTime p s) :
    ContextTime (GeneratedBootstrapSupportContext.actualContextMap P J x s q) :=
  ⟨t.1, by
    change t.1 ∈ calendarBlock p s
    exact t.2⟩

private theorem blockInput_cast_eq
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (coordinates : ExtendedPrivateCoordinates p) :
    e ▸ BootstrapPhysicalInput.blockInput p s₁ incoming numerators hpos
        ids row rewards coordinates =
      BootstrapPhysicalInput.blockInput p s₂ incoming numerators hpos
        ids row rewards coordinates := by
  cases e
  rfl

private theorem candidateEligibleSetOnPhysical_input_congr
    (base : FalseFactorBase p) (s : Fin (n_boot p))
    {left right : BootstrapPhysicalBlock.Input p s} (e : left = right)
    (j : {i // i ∈ left.uninformed}) (v : Fin (M p)) :
    GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s left j v =
      GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s right (e ▸ j) v := by
  cases e
  rfl

theorem active_cast_eq
    {s : Fin (n_boot p)} {left right : BootstrapPhysicalBlock.Input p s}
    (e : left = right) (j : {i // i ∈ left.uninformed}) :
    right.active (e ▸ j) = left.active j := by
  cases e
  rfl

theorem privateId_cast_eq
    {s : Fin (n_boot p)} {left right : BootstrapPhysicalBlock.Input p s}
    (e : left = right) (j : {i // i ∈ left.uninformed}) :
    right.privateId (e ▸ j) = left.privateId j := by
  cases e
  rfl

theorem observationIndex_cast_eq
    {s : Fin (n_boot p)} {left right : BootstrapPhysicalBlock.Input p s}
    (e : left = right) (j : {i // i ∈ left.uninformed})
    (n : ℕ) (t : Fin p.T) :
    BootstrapPhysicalBlock.observationIndex right
        (BootstrapPhysicalBlock.run right n) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m (e ▸ j).1) =
      BootstrapPhysicalBlock.observationIndex left
        (BootstrapPhysicalBlock.run left n) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) := by
  cases e
  rfl

theorem followerValue_cast_eq
    {s : Fin (n_boot p)} {left right : BootstrapPhysicalBlock.Input p s}
    (e : left = right) (j : {i // i ∈ left.uninformed}) :
    (e ▸ j).1 = j.1 := by
  cases e
  rfl

/-- On a genuinely processed block, the accepted generated physical input is
the same existing block input as the one carried by the actual local context. -/
theorem actualPhysicalInput_eq_generatedPhysical
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s) :
    GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s =
      GeneratedForwardPrefixTests.actualPhysicalBlock x s h := by
  have hindex := GeneratedForwardPrefixTests.actualBlockIndex x s h
  have hphysicalDef :
      GeneratedForwardPrefixTests.actualPhysicalBlock x s h =
        hindex ▸ ReferenceInitializationRun.physical x
          (GeneratedForwardPrefixTests.actualBoundary x s)
          (GeneratedForwardPrefixTests.actualBlockRemaining x s h) := by
    unfold GeneratedForwardPrefixTests.actualPhysicalBlock
    rfl
  rw [hphysicalDef]
  unfold GeneratedBootstrapSupportContext.actualPhysicalInput
  change BootstrapPhysicalInput.blockInput p s
      (ReferenceInitializationRun.uninformed q.incoming) q.incoming.numerators
      q.incoming.weight_ge_one x.ids x.row x.rewards x.coordinates =
    hindex ▸ BootstrapPhysicalInput.blockInput p
      (ReferenceInitializationRun.nextBlock
        (ReferenceInitializationRun.run x s.val)
        (GeneratedForwardPrefixTests.actualBlockRemaining x s h))
      (ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val))
      (ReferenceInitializationRun.run x s.val).numerators
      (ReferenceInitializationRun.run x s.val).weight_ge_one
      x.ids x.row x.rewards x.coordinates
  rw [q.incoming_eq_run]
  exact (blockInput_cast_eq hindex
    (ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val))
    (ReferenceInitializationRun.run x s.val).numerators
    (ReferenceInitializationRun.run x s.val).weight_ge_one
    x.ids x.row x.rewards x.coordinates).symm

/-- The accepted generated active follower obtained by transporting the
actual local follower across the actual physical-input identity. -/
def actualGeneratedFollower
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s) :
    GeneratedForwardPrefixTests.ActiveIncomingFollower x s h := by
  let heq := actualPhysicalInput_eq_generatedPhysical q h
  refine ⟨heq ▸ q.follower, ?_⟩
  rw [active_cast_eq heq q.follower, q.active]

/-- Pointwise identification of the explicit context recursion with the
existing physical State trace for every actual processed, incoming-uninformed,
active local block. The only local random coordinates supplied are the
original coordinator/follower scalar restrictions. -/
theorem stateTrace_eq_actualPhysical
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s) :
    ∀ n : ℕ, n ≤ p.T →
      stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) n =
      BootstrapPhysicalBlock.run
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s) n := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have h := i.isLt
    omega
  have hcontextBlock : c.1 = s := by
    rfl
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let u := phys.privateId q.follower
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  have hbaseIDs : base.1 = phys.ids := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1 = x.ids
    rw [hcoords.1, q.ids_eq]
  have hbaseLearning : base.2.1 J = phys.row.2 := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.2.1 J = x.row.2
    rw [hcoords.2.1, q.row_eq]
    rfl
  have hbaseForward : base.2.2 = phys.row.1 := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.2.2 = x.row.1
    rw [hcoords.2.2.1, q.row_eq]
  have hcontextRow : trueRowIndex c = J := rfl
  have hcontextID : followerIndex c = i := rfl
  have hcontextHeld : heldArm c = phys.held q.follower := rfl
  have hcontextTarget : targetArm c = phys.target := rfl
  have hheldSupport : heldSupport c =
      GeneratedBootstrapSupportContext.supportAvoidanceVector phys q.follower
        (phys.held q.follower) := rfl
  have htargetSupport : targetSupport c =
      GeneratedBootstrapSupportContext.supportAvoidanceVector phys q.follower phys.target := rfl
  have hsourceFollower : BootstrapPrivateIDFibers.sourceFollower p i = q.follower.1 := by
    apply Fin.ext
    rfl
  have hroundPair := originalRoundPair_eq_source s i hi x.coordinates
  have hroundCoordinator (bt : ContextTime c) :
      rounds.1 bt = BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
        (ActiveRoundActions.coordinator p.two_le_m) bt.1 := by
    have h := congrFun (congrArg Prod.fst hroundPair) bt
    exact h
  have hroundFollower (bt : ContextTime c) :
      rounds.2 bt = BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
        (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1) bt.1 := by
    change (originalRoundPair s i hi x.coordinates).2 bt = _
    have h := congrFun (congrArg Prod.snd hroundPair) bt
    simpa [hsourceFollower] using h
  have hslot (bt : ContextTime c) :
      BootstrapPhysicalBlock.slot phys bt.1 =
        slotDraw ((base.2.1 J) bt.1).1 := by
    change slotDraw (phys.row.2 bt.1).1 = slotDraw ((base.2.1 J) bt.1).1
    rw [← hbaseLearning]
  have hforwardProduct (st : BootstrapPhysicalBlock.State p) (bt : ContextTime c) :
      BootstrapPhysicalBlock.forwardProduct phys st bt.1 =
        trueForwardProduct c base st bt := by
    simp [BootstrapPhysicalBlock.forwardProduct, trueForwardProduct,
      hbaseForward]
  have hcoordAvoid (bt : ContextTime c) :
      (phys.coordinatorAvoid bt.1).val =
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (targetArm c)
          (rounds.1 bt)).val := by
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p phys.target
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) bt.1)).val = _
    rw [hcontextTarget, hroundCoordinator bt]
  have hcoordUniform (bt : ContextTime c) :
      phys.uniform (ActiveRoundActions.coordinator p.two_le_m) bt.1 =
        BootstrapPrivateRoundStreams.fullArmScalarDraw p (rounds.1 bt) := by
    change BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) bt.1) = _
    rw [hroundCoordinator bt]
  have hcoordinatorAction (st : BootstrapPhysicalBlock.State p)
      (bt : ContextTime c) :
      coordinatorAction c base rounds st bt =
        BootstrapPhysicalBlock.coordinatorAction phys st bt.1 := by
    unfold coordinatorAction BootstrapPhysicalBlock.coordinatorAction
    rw [hcontextRow, hslot bt, hforwardProduct st bt, hcoordAvoid bt,
      hcontextTarget, hcoordUniform bt]
    simp only [BootstrapPhysicalBlock.tuple]
    rw [hbaseLearning]
  have hfocalAvoid (bt : ContextTime c) :
      (phys.followerAvoid q.follower bt.1).val =
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (heldArm c)
          (rounds.2 bt)).val := by
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (phys.held q.follower)
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1) bt.1)).val = _
    rw [hcontextHeld, hroundFollower bt]
  have hbaseIDbit (bt : ContextTime c) :
      base.1 u bt.1 = phys.ids (phys.privateId q.follower) bt.1 := by
    rw [hbaseIDs]
  have hactive : phys.active q.follower = true := by
    simpa [phys] using q.active
  have hfocalAction (bt : ContextTime c) (st : BootstrapPhysicalBlock.State p) :
      focalAction c base u rounds bt =
        BootstrapPhysicalBlock.actions phys st bt.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1) := by
    unfold focalAction
    rw [BootstrapPhysicalBlock.actions_follower,
      BootstrapPhysicalBlock.followerAction,
      dite_eq_left q.follower.property]
    simp only [BootstrapPhysicalBlock.uninformedAction]
    rw [hactive]
    by_cases hid : base.1 u bt.1
    · have hbit : phys.ids (phys.privateId q.follower) bt.1 = true := by
        rw [← hbaseIDbit bt]
        exact hid
      simp [hid, hbit, hfocalAvoid bt]
    · have hbit : ¬ phys.ids (phys.privateId q.follower) bt.1 = true := by
        intro h
        apply hid
        rw [hbaseIDbit bt]
        exact h
      simp [hid, hbit, hcontextHeld]
  have hdiscovery (st : BootstrapPhysicalBlock.State p) (bt : ContextTime c) :
      BootstrapPhysicalBlock.discoveryPositive phys st bt.1 ↔
        st.mode = BootstrapPhysicalBlock.Mode.discover ∧
          slotDraw ((base.2.1 J) bt.1).1 = dataSlot ∧
          targetSupport c bt = true ∧
          focalAction c base u rounds bt ≠ targetArm c := by
    have hblock : bt.1 ∈ calendarBlock p s := by
      rw [← hcontextBlock]
      exact bt.2
    change (bt.1 ∈ calendarBlock p s ∧
      st.mode = BootstrapPhysicalBlock.Mode.discover ∧
      BootstrapPhysicalBlock.slot phys bt.1 = dataSlot ∧
      0 < BootstrapPhysicalBlock.feedback phys st bt.1
        (ActiveRoundActions.coordinator p.two_le_m)) ↔ _
    simp only [hblock, true_and]
    have hslotData : BootstrapPhysicalBlock.slot phys bt.1 = dataSlot ↔
        slotDraw ((base.2.1 J) bt.1).1 = dataSlot := by
      rw [hslot bt]
    constructor
    · rintro ⟨hm, hd, hp⟩
      have hsupport :=
        (GeneratedBootstrapSupportContext.coordinator_feedback_pos_iff_support
          phys st q.follower bt hm hd).mp hp
      rcases hsupport with ⟨hs, havoid⟩
      refine ⟨hm, hslotData.mp hd, ?_, ?_⟩
      · simpa only [← htargetSupport] using hs
      · rw [hfocalAction bt st, hcontextTarget]
        exact havoid
    · rintro ⟨hm, hd, hs, havoid⟩
      have hd' : BootstrapPhysicalBlock.slot phys bt.1 = dataSlot :=
        hslotData.mpr hd
      have hs' : GeneratedBootstrapSupportContext.supportAvoidanceVector
          phys q.follower phys.target bt = true := by
        simpa only [htargetSupport] using hs
      have havoid' : BootstrapPhysicalBlock.actions phys st bt.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1) ≠ phys.target := by
        rw [← hfocalAction bt st, ← hcontextTarget]
        exact havoid
      refine ⟨hm, hd', ?_⟩
      exact (GeneratedBootstrapSupportContext.coordinator_feedback_pos_iff_support
        phys st q.follower bt hm hd').mpr ⟨hs', havoid'⟩
  have hstep (st : BootstrapPhysicalBlock.State p) (bt : ContextTime c) :
      stateStep c base u rounds st bt =
        BootstrapPhysicalBlock.step phys st bt.1 := by
    simp [stateStep, stateStepFromAvoidance, BootstrapPhysicalBlock.step,
      hdiscovery st bt, hbaseIDs, hcontextRow]
  change ∀ n : ℕ, n ≤ p.T → stateTrace c base u rounds n =
    BootstrapPhysicalBlock.run phys n
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < p.T := by omega
      let t : Fin p.T := ⟨n, hnlt⟩
      by_cases hblock : t ∈ calendarBlock p c.1
      · let bt : ContextTime c := ⟨t, hblock⟩
        rw [stateTrace_succ, dite_eq_left hnlt, dite_eq_left hblock]
        rw [BootstrapPhysicalBlock.run_succ phys t]
        rw [ih (by omega)]
        exact hstep (BootstrapPhysicalBlock.run phys n) bt
      · have hno : ¬ BootstrapPhysicalBlock.discoveryPositive phys
            (BootstrapPhysicalBlock.run phys n) t := by
          have hphysicalBlock : t ∉ calendarBlock p s := by
            intro ht
            apply hblock
            simpa only [hcontextBlock] using ht
          intro h
          exact hphysicalBlock h.1
        rw [stateTrace_succ, dite_eq_left hnlt, dite_eq_right hblock]
        have hrunsucc : BootstrapPhysicalBlock.run phys (n + 1) =
            BootstrapPhysicalBlock.step phys (BootstrapPhysicalBlock.run phys n) t := by
          simpa [t] using BootstrapPhysicalBlock.run_succ phys t
        rw [hrunsucc,
          BootstrapPhysicalBlock.step_of_no_positive phys
            (BootstrapPhysicalBlock.run phys n) t hno, ih (by omega)]

/-- On a processed block the projected state at every prefix is exactly the
existing generated physical State trace. -/
theorem stateTrace_eq_generatedPhysical
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s) :
    ∀ n : ℕ, n ≤ p.T →
      stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) n =
      BootstrapPhysicalBlock.run
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) n := by
  intro n hn
  rw [← actualPhysicalInput_eq_generatedPhysical q h]
  exact stateTrace_eq_actualPhysical q n hn

/-- The accepted actual-local-context reduction also identifies the explicit
projected context and every prefix when the two original local scalar pairs
agree. -/
theorem stateTrace_eq_of_actual_local_context_reduction
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x y : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (left : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (right : GeneratedBootstrapSupportContext.ActualLocalBlock P J y s)
    (hsource : left.follower.1 = right.follower.1)
    (hid : (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).privateId
        left.follower =
      (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).privateId
        right.follower)
    (hheld : (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).held
        left.follower =
      (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).held
        right.follower)
    (htarget : (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).target =
      (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).target)
    (hSupportHeld :
      GeneratedBootstrapSupportContext.supportAvoidanceVector
          (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s)
          left.follower
          ((GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).held
            left.follower) =
        GeneratedBootstrapSupportContext.supportAvoidanceVector
          (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s)
          right.follower
          ((GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).held
            right.follower))
    (hSupportTarget :
      GeneratedBootstrapSupportContext.supportAvoidanceVector
          (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s)
          left.follower
          (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).target =
        GeneratedBootstrapSupportContext.supportAvoidanceVector
          (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s)
          right.follower
          (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).target)
    (hcoordRound : ∀ t : FalseRowSliceFactorization.BlockTime p s,
      BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1 =
        BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1)
    (hfollowerRound : ∀ t : FalseRowSliceFactorization.BlockTime p s,
      BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1) t.1 =
        BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1) t.1)
    (n : ℕ) (hn : n ≤ p.T) :
    GeneratedBootstrapSupportContext.actualContextMap P J x s left =
        GeneratedBootstrapSupportContext.actualContextMap P J y s right ∧
      stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s left)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
          ((GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).privateId
            left.follower)
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p left.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p left.follower.1).isLt
              omega) x.coordinates) n =
        stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J y s right)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
          ((GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).privateId
            right.follower)
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p right.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p right.follower.1).isLt
              omega) y.coordinates) n := by
  have hreduce := GeneratedBootstrapSupportContext.actual_local_context_reduction
    left right hsource hid hheld htarget hSupportHeld hSupportTarget hcoordRound hfollowerRound
  rcases hreduce with ⟨hcontext, ⟨hrun, _⟩⟩
  refine ⟨hcontext, ?_⟩
  calc
    stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s left)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s).privateId
          left.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p left.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p left.follower.1).isLt
            omega) x.coordinates) n =
      BootstrapPhysicalBlock.run
        (GeneratedBootstrapSupportContext.actualPhysicalInput x left.incoming s) n :=
      stateTrace_eq_actualPhysical left n hn
    _ = BootstrapPhysicalBlock.run
        (GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s) n :=
      hrun n hn
    _ = stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J y s right)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
          ((GeneratedBootstrapSupportContext.actualPhysicalInput y right.incoming s).privateId
            right.follower)
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p right.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p right.follower.1).isLt
              omega) y.coordinates) n :=
      (stateTrace_eq_actualPhysical right n hn).symm

/-- The exact projected coordinator action agrees with the existing physical
action at every state and source block time of an actual local block. -/
theorem coordinatorAction_eq_actualPhysical
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (st : BootstrapPhysicalBlock.State p)
    (bt : ContextTime (GeneratedBootstrapSupportContext.actualContextMap P J x s q)) :
    coordinatorAction (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        st bt =
      BootstrapPhysicalBlock.coordinatorAction
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s)
        st bt.1 := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have h := i.isLt
    omega
  let rounds : LocalRoundPair c := by
    change RoundPair s
    exact originalRoundPair s i hi x.coordinates
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  have hbaseLearning : base.2.1 J = phys.row.2 := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.2.1 J = x.row.2
    rw [hcoords.2.1, q.row_eq]
    rfl
  have hbaseForward : base.2.2 = phys.row.1 := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.2.2 = x.row.1
    rw [hcoords.2.2.1, q.row_eq]
  have hcontextRow : trueRowIndex c = J := rfl
  have hcontextTarget : targetArm c = phys.target := rfl
  have hroundPair := originalRoundPair_eq_source s i hi x.coordinates
  have hroundCoordinator (bt : ContextTime c) :
      rounds.1 bt = BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
        (ActiveRoundActions.coordinator p.two_le_m) bt.1 := by
    exact congrFun (congrArg Prod.fst hroundPair) bt
  have hslot (bt : ContextTime c) :
      BootstrapPhysicalBlock.slot phys bt.1 =
        slotDraw ((base.2.1 J) bt.1).1 := by
    change slotDraw (phys.row.2 bt.1).1 = slotDraw ((base.2.1 J) bt.1).1
    rw [← hbaseLearning]
  have hforwardProduct (st : BootstrapPhysicalBlock.State p)
      (bt : ContextTime c) :
      BootstrapPhysicalBlock.forwardProduct phys st bt.1 =
        trueForwardProduct c base st bt := by
    simp [BootstrapPhysicalBlock.forwardProduct, trueForwardProduct,
      hbaseForward]
  have hcoordAvoid (bt : ContextTime c) :
      (phys.coordinatorAvoid bt.1).val =
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
          (targetArm c) (rounds.1 bt)).val := by
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p phys.target
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) bt.1)).val = _
    rw [hcontextTarget, hroundCoordinator bt]
  have hcoordUniform (bt : ContextTime c) :
      phys.uniform (ActiveRoundActions.coordinator p.two_le_m) bt.1 =
        BootstrapPrivateRoundStreams.fullArmScalarDraw p (rounds.1 bt) := by
    change BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) bt.1) = _
    rw [hroundCoordinator bt]
  change coordinatorAction c base rounds st bt =
    BootstrapPhysicalBlock.coordinatorAction phys st bt.1
  unfold coordinatorAction BootstrapPhysicalBlock.coordinatorAction
  rw [hcontextRow, hslot bt, hforwardProduct st bt, hcoordAvoid bt,
    hcontextTarget, hcoordUniform bt]
  simp only [BootstrapPhysicalBlock.tuple]
  rw [hbaseLearning]

/-- On ID zero, the projected focal test is exactly positivity of the actual
physical observation index. -/
theorem focalPositive_eq_actualObservation
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (bt : FalseRowSliceFactorization.BlockTime p s)
    (hid : ((FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1)
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower) bt.1 = false) :
    focalPositive (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        (stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
          ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
            q.follower)
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
              omega) x.coordinates) bt.1.val) (actualContextTime q bt) =
      decide (0 < (BootstrapPhysicalBlock.observationIndex
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s)
        (BootstrapPhysicalBlock.run
          (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s)
          bt.1.val) bt.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val) := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have h := i.isLt
    omega
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let u := phys.privateId q.follower
  let btContext := actualContextTime q bt
  have hcontextHeld : heldArm c = phys.held q.follower := rfl
  have hheldSupport : heldSupport c =
      GeneratedBootstrapSupportContext.supportAvoidanceVector phys q.follower
        (phys.held q.follower) := rfl
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  have hbaseId : base.1 = P.1 := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1 = P.1
    rw [hcoords.1]
  have hphysIds : phys.ids = x.ids := by
    change (BootstrapPhysicalInput.blockInput p s
      (ReferenceInitializationRun.uninformed q.incoming) q.incoming.numerators
      q.incoming.weight_ge_one x.ids x.row x.rewards x.coordinates).ids = x.ids
    exact BootstrapPhysicalInput.blockInput_ids p s
      (ReferenceInitializationRun.uninformed q.incoming)
      q.incoming.numerators q.incoming.weight_ge_one x.ids x.row x.rewards
      x.coordinates
  have hactive : phys.active q.follower = true := by
    simpa [phys] using q.active
  have hidPhysical : phys.ids (phys.privateId q.follower) bt.1 = false := by
    rw [hphysIds, q.ids_eq, ← hbaseId]
    exact hid
  have hheldSupportAt : heldSupport c btContext =
      GeneratedBootstrapSupportContext.supportAvoidanceVector phys q.follower
        (phys.held q.follower) bt := by
    rfl
  have htrace : stateTrace c base u rounds bt.1.val =
      BootstrapPhysicalBlock.run phys bt.1.val := by
    change stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) bt.1.val =
      BootstrapPhysicalBlock.run
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s) bt.1.val
    exact stateTrace_eq_actualPhysical q bt.1.val (Nat.le_of_lt bt.1.isLt)
  have hcoordLocal : coordinatorAction c base rounds
      (BootstrapPhysicalBlock.run phys bt.1.val) btContext =
        BootstrapPhysicalBlock.coordinatorAction phys
          (BootstrapPhysicalBlock.run phys bt.1.val) bt.1 := by
    change coordinatorAction (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        (originalRoundPair s (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        (BootstrapPhysicalBlock.run
          (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s) bt.1.val)
        (actualContextTime q bt) =
      BootstrapPhysicalBlock.coordinatorAction
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s)
        (BootstrapPhysicalBlock.run
          (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s) bt.1.val)
        bt.1
    exact coordinatorAction_eq_actualPhysical q
      (BootstrapPhysicalBlock.run phys bt.1.val) btContext
  change decide (heldSupport c btContext = true ∧
      coordinatorAction c base rounds
        (stateTrace c base u rounds bt.1.val) btContext ≠ heldArm c) =
    decide (0 < (BootstrapPhysicalBlock.observationIndex phys
      (BootstrapPhysicalBlock.run phys bt.1.val) bt.1
      (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val)
  rw [htrace, hheldSupportAt, hcontextHeld,
    hcoordLocal,
    ← BootstrapPhysicalBlock.actions_coordinator]
  apply Bool.decide_congr
  exact (GeneratedBootstrapSupportContext.follower_feedback_pos_iff_support
    phys (BootstrapPhysicalBlock.run phys bt.1.val) q.follower bt hactive
    hidPhysical).symm.trans
      (BootstrapPhysicalBlock.observationIndex_pos_iff phys
        (BootstrapPhysicalBlock.run phys bt.1.val) bt.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).symm

/-- The ID-zero focal test on a processed generated block is the actual
physical observation-index positivity test. -/
theorem focalPositive_eq_generatedObservation
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s)
    (bt : FalseRowSliceFactorization.BlockTime p s)
    (hid : ((FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1)
        ((GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId
          (actualGeneratedFollower q h).val) bt.1 = false) :
    focalPositive (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        (stateTrace (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
          ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
            q.follower)
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
              omega) x.coordinates) bt.1.val) (actualContextTime q bt) =
      decide (0 < (BootstrapPhysicalBlock.observationIndex
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h)
        (BootstrapPhysicalBlock.run
          (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) bt.1.val) bt.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (actualGeneratedFollower q h).val.1)).val) := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let gen := GeneratedForwardPrefixTests.actualPhysicalBlock x s h
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let u := phys.privateId q.follower
  let j := actualGeneratedFollower q h
  have heq := actualPhysicalInput_eq_generatedPhysical q h
  have hidValue : gen.privateId j.val = phys.privateId q.follower :=
    privateId_cast_eq heq q.follower
  have hidPhysical : base.1 (phys.privateId q.follower) bt.1 = false := by
    change base.1 (gen.privateId j.val) bt.1 = false at hid
    rw [hidValue] at hid
    exact hid
  have hlabel : j.val.1 = q.follower.1 := by
    change (heq ▸ q.follower).1 = q.follower.1
    exact followerValue_cast_eq heq q.follower
  have hobs := observationIndex_cast_eq heq q.follower bt.1.val bt.1
  rw [followerValue_cast_eq heq q.follower] at hobs
  have hactual := focalPositive_eq_actualObservation q bt hidPhysical
  calc
    focalPositive c base
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        (stateTrace c base u
          (originalRoundPair s
            (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
            (by
              have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
              omega) x.coordinates) bt.1.val) (actualContextTime q bt) =
        decide (0 < (BootstrapPhysicalBlock.observationIndex phys
          (BootstrapPhysicalBlock.run phys bt.1.val) bt.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val) := by
      simpa [base, phys, c, u] using hactual
    _ = decide (0 < (BootstrapPhysicalBlock.observationIndex gen
          (BootstrapPhysicalBlock.run gen bt.1.val) bt.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val.1)).val) := by
      rw [hlabel, hobs.symm]

/-- On every actual local block, the explicit context eligible set is the
existing physical eligible set. Candidate data slots are read from that
candidate's own continuous learning row. -/
theorem candidateEligibleSet_eq_actualPhysical
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (v : Fin (M p)) :
    candidateEligibleSet (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) v =
      GeneratedEligibleFamily.candidateEligibleSetOnPhysical
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 s
        (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s)
        q.follower v := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have h := i.isLt
    omega
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let u := phys.privateId q.follower
  have hcontextBlock : c.1 = s := by
    rfl
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  have hbaseIDs : base.1 = phys.ids := by
    change (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1 = x.ids
    rw [hcoords.1, q.ids_eq]
  have hactive : phys.active q.follower = true := by
    simpa [phys] using q.active
  classical
  apply Finset.ext
  intro t
  by_cases hblock : t ∈ calendarBlock p s
  · let sourceTime : FalseRowSliceFactorization.BlockTime p s := ⟨t, hblock⟩
    let contextTime : ContextTime c := actualContextTime q sourceTime
    have hidBase : base.1 u t = phys.ids (phys.privateId q.follower) t := by
      rw [hbaseIDs]
    have htest (hid : base.1 u t = false) :
        focalPositive c base rounds
          (stateTrace c base u rounds t.val) contextTime =
        decide (0 < (BootstrapPhysicalBlock.observationIndex phys
          (BootstrapPhysicalBlock.run phys t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val) := by
      have hid' :
          ((FalseRowSliceFactorization.falseRowFactorEquiv p J P).1.1)
            (phys.privateId q.follower) t = false := by
        simpa [base, phys, u] using hid
      have h := focalPositive_eq_actualObservation q sourceTime hid'
      simpa [base, phys, c, u, rounds, i, hi, sourceTime, contextTime] using h
    have hpositive (hid : base.1 u t = false) :
        focalPositive c base rounds
          (stateTrace c base u rounds t.val) contextTime = true ↔
        0 < (BootstrapPhysicalBlock.observationIndex phys
          (BootstrapPhysicalBlock.run phys t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val := by
      rw [htest hid]
      simp only [decide_eq_true_eq]
    have hidIff : base.1 u t = false ↔
        phys.ids (phys.privateId q.follower) t = false := by
      rw [hbaseIDs]
    have hcontextMem : t ∈ calendarBlock p c.1 := by
      simpa [hcontextBlock] using hblock
    have htime : (⟨t, hcontextMem⟩ : ContextTime c) = contextTime := by
      apply Subtype.ext
      rfl
    have htestIff :
        (if ht : t ∈ calendarBlock p c.1 then
          focalPositive c base rounds (stateTrace c base u rounds t.val)
            ⟨t, ht⟩ = true
        else False) ↔
          focalPositive c base rounds
            (stateTrace c base u rounds t.val) contextTime = true := by
      rw [dite_eq_left hcontextMem, htime]
    simp only [candidateEligibleSet,
      GeneratedEligibleFamily.candidateEligibleSetOnPhysical,
      GeneratedEligibleFamily.candidateEligibleOnPhysical, Finset.mem_filter]
    change
      (t ∈ calendarBlock p c.1 ∧
        (base.1 u t = false ∧
          slotDraw ((base.2.1 v) t).1 = dataSlot ∧
          (if ht : t ∈ calendarBlock p c.1 then
            focalPositive c base rounds (stateTrace c base u rounds t.val)
              ⟨t, ht⟩ = true
          else False))) ↔
      (t ∈ calendarBlock p s ∧
        (phys.active q.follower = true ∧
          phys.ids (phys.privateId q.follower) t = false ∧
          slotDraw ((base.2.1 v) t).1 = dataSlot ∧
          0 < (BootstrapPhysicalBlock.observationIndex phys
            (BootstrapPhysicalBlock.run phys t.val) t
            (PublicDiscreteDraws.followerPlayer p.two_le_m q.follower.1)).val))
    constructor
    · rintro ⟨hmem, ⟨hid, hslot, hpos⟩⟩
      have hpos' := htestIff.mp hpos
      exact ⟨by simpa [hcontextBlock] using hmem, hactive,
        hidIff.mp hid, hslot, (hpositive hid).mp hpos'⟩
    · rintro ⟨hmem, hact, hid, hslot, hpos⟩
      have hpos' : focalPositive c base rounds
          (stateTrace c base u rounds t.val) contextTime = true :=
        (hpositive (hidIff.mpr hid)).mpr hpos
      have hcontextMem' : t ∈ calendarBlock p c.1 := by
        simpa [hcontextBlock] using hmem
      have htest :
          (if ht : t ∈ calendarBlock p c.1 then
            focalPositive c base rounds (stateTrace c base u rounds t.val)
              ⟨t, ht⟩ = true
          else False) := htestIff.mpr hpos'
      exact ⟨hcontextMem', hidIff.mpr hid, hslot, htest⟩
  · have hcontextNot : t ∉ calendarBlock p c.1 := by
      simpa [hcontextBlock] using hblock
    simp only [candidateEligibleSet,
      GeneratedEligibleFamily.candidateEligibleSetOnPhysical,
      GeneratedEligibleFamily.candidateEligibleOnPhysical, Finset.mem_filter]
    constructor
    · rintro ⟨hmem, _⟩
      exact False.elim (hcontextNot hmem)
    · rintro ⟨hmem, _⟩
      exact False.elim (hblock hmem)

/-- The projected eligible set is the accepted generated candidate set on
every genuinely processed actual block. -/
theorem candidateEligibleSet_eq_generatedEligibleSet
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s)
    (v : Fin (M p)) :
    candidateEligibleSet (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) v =
      GeneratedForwardPrefixTests.eligibleSet x s h
        (actualGeneratedFollower q h) P.2 v := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let gen := GeneratedForwardPrefixTests.actualPhysicalBlock x s h
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let u := phys.privateId q.follower
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have hlt := i.isLt
    omega
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let j := actualGeneratedFollower q h
  have heq := actualPhysicalInput_eq_generatedPhysical q h
  have hfollower : heq ▸ q.follower = j.val := by
    rfl
  have hphysicalSet :
      GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s phys q.follower v =
        GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s gen j.val v := by
    rw [← hfollower]
    exact candidateEligibleSetOnPhysical_input_congr base s heq q.follower v
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  calc
    candidateEligibleSet c base u rounds v =
        GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s phys q.follower v :=
      candidateEligibleSet_eq_actualPhysical q v
    _ = GeneratedEligibleFamily.candidateEligibleSetOnPhysical base s gen j.val v :=
      hphysicalSet
    _ = GeneratedForwardPrefixTests.eligibleSet x s h j P.2 v :=
      GeneratedEligibleFamily.candidateEligibleSetOnActualPhysical_eq_eligibleSet
        base x s h j P.2 v hcoords.2.1

/-- Sorting the explicit set gives the accepted full chronological generated
eligible list, with no declaration-based truncation. -/
theorem candidateEligibleTimes_eq_generated
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s)
    (v : Fin (M p)) :
    candidateEligibleTimes
        (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower) v
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates) =
      GeneratedForwardPrefixTests.chronologicalEligibleTimes x s h
        (actualGeneratedFollower q h) P.2 v := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have hlt := i.isLt
    omega
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let u := phys.privateId q.follower
  change (candidateEligibleSet c base u rounds v).sort =
    (GeneratedForwardPrefixTests.eligibleSet x s h
      (actualGeneratedFollower q h) P.2 v).sort
  rw [candidateEligibleSet_eq_generatedEligibleSet q h v]

/-- The projected permanent-mismatch/first-quota pass is exactly the
existing generated false-candidate event for the selected published table. -/
theorem candidatePasses_iff_generatedFalseCandidatePasses
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)}
    (q : GeneratedBootstrapSupportContext.ActualLocalBlock P J x s)
    (h : GeneratedForwardPrefixTests.processesBlock x s)
    (v : FalseRowSliceFactorization.FalseRow p J) :
    candidatePasses
        (GeneratedBootstrapSupportContext.actualContextMap P J x s q)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
        ((GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
          q.follower)
        (originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1).isLt
            omega) x.coordinates)
        v (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 ↔
      GeneratedForwardPrefixTests.falseCandidatePasses x s h
        (actualGeneratedFollower q h) P.2 J v := by
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let falseRows := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
  let phys := GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s
  let gen := GeneratedForwardPrefixTests.actualPhysicalBlock x s h
  let c := GeneratedBootstrapSupportContext.actualContextMap P J x s q
  let u := phys.privateId q.follower
  let i := BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1
  have hi : i.val + 1 < p.m := by
    have hlt := i.isLt
    omega
  let rounds : LocalRoundPair c := originalRoundPair s i hi x.coordinates
  let j := actualGeneratedFollower q h
  have htimes : candidateEligibleTimes c base u v.1 rounds =
      GeneratedForwardPrefixTests.chronologicalEligibleTimes x s h j P.2 v.1 := by
    change (candidateEligibleSet c base u rounds v.1).sort =
      (GeneratedForwardPrefixTests.eligibleSet x s h j P.2 v.1).sort
    rw [candidateEligibleSet_eq_generatedEligibleSet q h v.1]
  have hid : phys.privateId q.follower = gen.privateId j.val := by
    change (GeneratedBootstrapSupportContext.actualPhysicalInput x q.incoming s).privateId
        q.follower =
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId
        ((actualPhysicalInput_eq_generatedPhysical q h) ▸ q.follower)
    exact (privateId_cast_eq (actualPhysicalInput_eq_generatedPhysical q h)
      q.follower).symm
  have hcoords := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J P
  have hnumeric (t : Fin p.T) : falseRows v u t =
      (P.2 v.1).1 (gen.privateId j.val) t := by
    change ((FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 v) u t =
      (P.2 v.1).1 (gen.privateId j.val) t
    rw [hcoords.2.2.2]
    change (P.2 v.1).1 (phys.privateId q.follower) t =
      (P.2 v.1).1 (gen.privateId j.val) t
    rw [hid]
  change ForwardPrefixSlice.privatePrefixPasses
      (candidateEligibleListFunction c base u v.1) rounds
      (fun t => falseRows v u t) ↔
    GeneratedForwardPrefixTests.falseCandidatePasses x s h j P.2 J v
  rw [ForwardPrefixSlice.privatePrefixPasses_iff_first_q,
    GeneratedForwardPrefixTests.falseCandidatePasses_iff_first_quota]
  have htimes' : ForwardPrefixSlice.chronologicalEligibleTimes
      (candidateEligibleListFunction c base u v.1) rounds =
        GeneratedForwardPrefixTests.chronologicalEligibleTimes x s h j P.2 v.1 := by
    simpa [candidateEligibleTimes] using htimes
  rw [htimes']
  constructor
  · rintro ⟨hquota, hpass⟩
    refine ⟨hquota, ?_⟩
    intro t ht
    have hpass' := hpass t ht
    rw [hnumeric t] at hpass'
    exact hpass'
  · rintro ⟨hquota, hpass⟩
    refine ⟨hquota, ?_⟩
    intro t ht
    rw [hnumeric t]
    exact hpass t ht

end Bandits.Support.BootstrapContextPrefixOperation

end
