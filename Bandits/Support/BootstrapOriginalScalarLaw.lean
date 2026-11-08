/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapOriginalScalarStep

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Observable laws of the existing original bootstrap scalars

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,61-109` and
`sources/zip4/manuscript/appendix_b_communication.tex:390-407,485-506`.
The fixed analytical input and pre-choice state remain explicit. Only the
selected branch at each distinct physical player label is sampled; the latent
full/complement alternatives are never asserted independent under the original
scalar adapter. These are internal fixed-snapshot results, not conditional
generated-history laws or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Bandits.Support.BootstrapOriginalScalarLaw

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPrivateRoundStreams BootstrapPhysicalBlock BootstrapModeService
open BootstrapOriginalScalarStep BootstrapStayAvoidance PublicDiscreteDraws
open ActiveRoundActions ContinuousCategorical

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The physical player owning a latent alternative. -/
def branchPlayer (x : BootstrapPhysicalBlock.Input p s) : PrivateBranchIndex x → Player p.m
  | none => coordinator p.two_le_m
  | some (.inl i) => i
  | some (.inr j) => followerPlayer p.two_le_m j.1

/-- Forget only the complement subtype proof, retaining the arm value. -/
def branchArm (x : BootstrapPhysicalBlock.Input p s) (k : PrivateBranchIndex x) :
    privateBranchValue x k → Fin p.K :=
  match k with
  | none => Subtype.val
  | some (.inl _) => id
  | some (.inr _) => Subtype.val

theorem measurable_branchArm (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) : Measurable (branchArm x k) := by
  cases k with
  | none => exact measurable_subtype_coe
  | some q => cases q with
    | inl i => exact measurable_id
    | inr j => exact measurable_subtype_coe

/-- The literal scalar draw associated with a latent alternative. -/
def branchScalarDraw (x : BootstrapPhysicalBlock.Input p s) (k : PrivateBranchIndex x) :
    ContinuousCategorical.Scalar → privateBranchValue x k :=
  match k with
  | none => forbiddenArmScalarDraw p x.target
  | some (.inl _) => fullArmScalarDraw p
  | some (.inr j) => forbiddenArmScalarDraw p (x.held j)

theorem measurable_branchScalarDraw (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) : Measurable (branchScalarDraw x k) := by
  cases k with
  | none => exact measurable_forbiddenArmScalarDraw p x.target
  | some q => cases q with
    | inl i => exact measurable_fullArmScalarDraw p
    | inr j => exact measurable_forbiddenArmScalarDraw p (x.held j)

theorem map_fullArmScalarDraw (p : ConstructorDimensions.Parameters) :
    ContinuousCategorical.uniform.map (fullArmScalarDraw p) = privateArmMeasure p := by
  exact ContinuousCategorical.uniform_map_sample (K_pos p)
    (equalArmMass_nonneg p.K) (equalArmMass_sum p.K (K_pos p))

theorem map_forbiddenArmScalarDraw (p : ConstructorDimensions.Parameters) (a : Fin p.K) :
    ContinuousCategorical.uniform.map (forbiddenArmScalarDraw p a) =
      privateAvoidMeasure p a := by
  apply Measure.ext_of_singleton
  intro b
  rw [forbiddenArmScalarDraw_map_atom, privateAvoidMeasure,
    ProbabilityTheory.uniformOn_univ]
  have hcard : Fintype.card (BootstrapPhysicalBlock.AvoidArm p a) = p.K - 1 := by
    rw [Fintype.card_subtype_compl (fun b : Fin p.K => b = a)]
    simp only [Fintype.card_fin, Fintype.card_unique]
  rw [Measure.count_singleton, hcard]
  have hK : 1 < p.K := lt_of_lt_of_le (by decide : 1 < 2)
    (p.two_le_m.trans (Nat.le_of_lt p.m_lt_K))
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hK))]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast]

theorem map_branchScalarDraw (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) :
    ContinuousCategorical.uniform.map (branchScalarDraw x k) = privateBranchMeasure x k := by
  cases k with
  | none => exact map_forbiddenArmScalarDraw p x.target
  | some q => cases q with
    | inl i => exact map_fullArmScalarDraw p
    | inr j => exact map_forbiddenArmScalarDraw p (x.held j)

/-- Select the only latent coordinate read by a randomized action. A
deterministic branch may select its unused full-arm coordinate. -/
def selectedBranch (x : BootstrapPhysicalBlock.Input p s) (st : State p)
    (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) (i : Player p.m) :
    PrivateBranchIndex x := by
  classical
  exact if hi : i = coordinator p.two_le_m then
    if roundSlot r = dataSlot ∧ st.mode = .multicast ∧
        r.1 ∈ forwardReleaseSet p st.list then none else some (.inl i)
  else
    let j := followerIndex p.two_le_m i hi
    if hj : j ∈ x.uninformed then
      if x.active ⟨j, hj⟩ = true ∧ x.ids (x.privateId ⟨j, hj⟩) t = true then
        some (.inr ⟨j, hj⟩) else some (.inl i)
    else some (.inl i)

theorem branchPlayer_selectedBranch (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (i : Player p.m) : branchPlayer x (selectedBranch x st t r i) = i := by
  classical
  by_cases hi : i = coordinator p.two_le_m
  · simp only [selectedBranch, dite_eq_left hi]
    split_ifs <;> simp only [branchPlayer, hi]
  · simp only [selectedBranch, dite_eq_right hi]
    split_ifs <;> simp only [branchPlayer, followerPlayer_followerIndex]

theorem selectedBranch_injective (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) :
    Function.Injective (selectedBranch x st t r) := by
  intro i j h
  simpa only [branchPlayer_selectedBranch] using congrArg (branchPlayer x) h

/-- Apply the actual branch conditions to its selected arm. Held, UP-row,
and ordered-tuple branches retain their literal deterministic actions. -/
def finishAction (x : BootstrapPhysicalBlock.Input p s) (st : State p)
    (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) (i : Player p.m)
    (a : Fin p.K) : Fin p.K := by
  classical
  exact if hi : i = coordinator p.two_le_m then
    if roundSlot r = dataSlot then
      if st.mode = .multicast ∧ r.1 ∈ forwardReleaseSet p st.list then a else x.target
    else if roundSlot r = downSlot then
      (BootstrapPhysicalBlock.tuple (currentInputOf x t r (storedRoundPrivateValues x t)) t).val i
    else a
  else
    let j := followerIndex p.two_le_m i hi
    if hj : j ∈ x.uninformed then
      if x.active ⟨j, hj⟩ = true then
        if x.ids (x.privateId ⟨j, hj⟩) t = true then a else x.held ⟨j, hj⟩
      else a
    else BootstrapPhysicalBlock.unoccupiedAction
      (currentInputOf x t r (storedRoundPrivateValues x t)) t j

theorem actionsOfPrivateBranches_selected (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (b : (k : PrivateBranchIndex x) → privateBranchValue x k) :
    actionsOfPrivateBranches x st t r b = fun i =>
      finishAction x st t r i
        (branchArm x (selectedBranch x st t r i) (b (selectedBranch x st t r i))) := by
  classical
  funext i
  by_cases hi : i = coordinator p.two_le_m
  · by_cases hd : roundSlot r = dataSlot
    · by_cases hm : st.mode = .multicast ∧ r.1 ∈ forwardReleaseSet p st.list
      · rw [show selectedBranch x st t r i = none by simp [selectedBranch, hi, hd, hm]]
        simp [actionsOfPrivateBranches, finishAction, hi, hd, hm, branchArm]
      · simp [actionsOfPrivateBranches, finishAction, hi, hd, hm]
    · rw [show selectedBranch x st t r i = some (.inl i) by
        simp [selectedBranch, hi, hd]]
      simp only [actionsOfPrivateBranches, finishAction, dite_eq_left hi, ite_eq_right hd, branchArm, id_eq]
  · let j := followerIndex p.two_le_m i hi
    by_cases hj : j ∈ x.uninformed
    · by_cases ha : x.active ⟨j, hj⟩ = true
      · by_cases hid : x.ids (x.privateId ⟨j, hj⟩) t = true
        · rw [show selectedBranch x st t r i = some (.inr ⟨j, hj⟩) by
            simp [selectedBranch, hi, hj, ha, hid, j]]
          simp [actionsOfPrivateBranches, finishAction, hi, hj, ha, hid, j, branchArm]
        · simp [actionsOfPrivateBranches, finishAction, hi, hj, ha, hid, j]
      · rw [show selectedBranch x st t r i = some (.inl i) by
          simp [selectedBranch, hi, hj, ha, j]]
        simp [actionsOfPrivateBranches, finishAction, hi, hj, ha, j, branchArm]
    · simp [actionsOfPrivateBranches, finishAction, hi, hj, j]

theorem privateBranchCoordinates_originalScalar (x : BootstrapPhysicalBlock.Input p s)
    (v : OriginalScalarVector p) (k : PrivateBranchIndex x) :
    privateBranchCoordinates x (roundPrivateValuesOfOriginalScalars x v) k =
      branchScalarDraw x k (v (branchPlayer x k)) := by
  cases k with
  | none => rfl
  | some q => cases q <;> rfl

/-- Fixed-public-coordinate equality of the entire simultaneous action law.
No equality of the latent alternatives' laws is asserted. -/
theorem map_originalScalarActions (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) :
    (originalScalarVectorMeasure p).map (originalScalarActions x st t r) =
      (roundPrivateMeasure x).map
        (fun d => BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) := by
  classical
  let k := selectedBranch x st t r
  let g : (i : Player p.m) → privateBranchValue x (k i) → Fin p.K :=
    fun i a => finishAction x st t r i (branchArm x (k i) a)
  have hg (i : Player p.m) : Measurable (g i) :=
    (Measurable.of_discrete (f := finishAction x st t r i)).comp
      (measurable_branchArm x (k i))
  have hscalar : originalScalarActions x st t r =
      fun v i => g i (branchScalarDraw x (k i) (v i)) := by
    funext v
    rw [← actionsOfPrivateBranches_originalScalars, actionsOfPrivateBranches_selected]
    funext i
    rw [privateBranchCoordinates_originalScalar, branchPlayer_selectedBranch]
  have hlatent : (fun d => BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      (fun (b : (q : PrivateBranchIndex x) → privateBranchValue x q) i =>
        g i (b (k i))) ∘ privateBranchCoordinates x := by
    funext d
    rw [← actionsOfPrivateBranches_eq_actions, actionsOfPrivateBranches_selected]
    rfl
  have hcoord : Measurable (privateBranchCoordinates x) := by
    apply measurable_pi_iff.mpr
    intro q
    cases q with
    | none => exact measurable_fst.comp measurable_snd
    | some q => cases q with
      | inl i => exact (measurable_pi_apply i).comp measurable_fst
      | inr j => exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hind : iIndepFun (fun i (b : (q : PrivateBranchIndex x) → privateBranchValue x q) =>
      g i (b (k i))) (privateBranchProductMeasure x) := by
    have heval := iIndepFun_pi (μ := privateBranchMeasure x)
      (X := fun _ a => a) (fun _ => measurable_id.aemeasurable)
    exact (heval.precomp (selectedBranch_injective x st t r)).comp g hg
  have hm (i : Player p.m) : Measurable
      (fun (b : (q : PrivateBranchIndex x) → privateBranchValue x q) => g i (b (k i))) :=
    (hg i).comp (measurable_pi_apply (k i))
  rw [hscalar, hlatent, ← Measure.map_map (measurable_pi_iff.mpr hm) hcoord,
    map_privateBranchCoordinates]
  change (Measure.pi (fun _ : Player p.m => ContinuousCategorical.uniform)).map
    (fun v i => g i (branchScalarDraw x (k i) (v i))) = _
  rw [Measure.pi_map_pi (μ := fun _ : Player p.m => ContinuousCategorical.uniform)
    (f := fun i a => g i (branchScalarDraw x (k i) a))
    (fun i => ((hg i).comp (measurable_branchScalarDraw x (k i))).aemeasurable),
    hind.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  change ContinuousCategorical.uniform.map (g i ∘ branchScalarDraw x (k i)) =
    (privateBranchProductMeasure x).map (g i ∘ Function.eval (k i))
  rw [← Measure.map_map (hg i) (measurable_branchScalarDraw x (k i)),
    ← Measure.map_map (hg i) (measurable_pi_apply (k i)), map_branchScalarDraw]
  exact congrArg (fun μ => μ.map (g i))
    (measurePreserving_eval (privateBranchMeasure x) (k i)).map_eq.symm

/-- The existing current input's literal complete row and private arrays,
viewed in the accepted causality module's measurable carrier. -/
def snapshotLocalCoordinates (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (w : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x) :
    BootstrapBlockCausality.LocalCoordinates p x.uninformed x.held x.target :=
  let y := currentInputOf x t w.1 w.2
  (y.row, (y.uniform, (y.coordinatorAvoid, y.followerAvoid)))

theorem measurable_snapshotLocalCoordinates (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) : Measurable (snapshotLocalCoordinates x t) := by
  classical
  change Measurable (fun w => snapshotLocalCoordinates x t w)
  dsimp only [snapshotLocalCoordinates, currentInputOf, currentInput]
  fun_prop

/-- Joint measurability in the entire public coordinate and all accepted
private values, using the existing physical actions' measurable API. -/
theorem measurable_currentActions (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) :
    Measurable (fun w : BootstrapModeService.RoundCoordinates p ×
      BootstrapModeService.RoundPrivateValues x =>
        BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t) := by
  exact (BootstrapBlockCausality.measurable_actionsView (s := s) x.uninformed x.active
    x.held x.privateId x.ids x.target x.rewards t).comp
      ((measurable_snapshotLocalCoordinates x t).prodMk measurable_const)

theorem measurable_roundPrivateValuesOfOriginalScalars
    (x : BootstrapPhysicalBlock.Input p s) :
    Measurable (roundPrivateValuesOfOriginalScalars x) := by
  exact (measurable_pi_iff.mpr (fun i =>
    (measurable_fullArmScalarDraw p).comp (measurable_pi_apply i))).prodMk
    (((measurable_forbiddenArmScalarDraw p x.target).comp
      (measurable_pi_apply (coordinator p.two_le_m))).prodMk
      (measurable_pi_iff.mpr (fun j =>
        (measurable_forbiddenArmScalarDraw p (x.held j)).comp
          (measurable_pi_apply (followerPlayer p.two_le_m j.1)))))

/-- Joint measurability of the original full simultaneous actions in `(r,v)`.
This includes all continuous controls used in row UP and tuple branches. -/
theorem measurable_originalScalarActions (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) :
    Measurable (fun w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p =>
      originalScalarActions x st t w.1 w.2) := by
  exact (measurable_currentActions x st t).comp
    (measurable_fst.prodMk
      ((measurable_roundPrivateValuesOfOriginalScalars x).comp measurable_snd))

theorem measurable_originalScalarObservable (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) :
    Measurable (fun w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p =>
      originalScalarObservable x st t w.1 w.2) :=
  measurable_fst.prodMk (measurable_originalScalarActions x st t)

theorem measurable_originalScalarActions_fixed (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) :
    Measurable (originalScalarActions x st t r) :=
  (measurable_originalScalarActions x st t).of_uncurry_left

theorem measurable_currentActions_fixed (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p) :
    Measurable (fun d : BootstrapModeService.RoundPrivateValues x =>
      BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) :=
  (measurable_currentActions x st t).comp (measurable_const.prodMk measurable_id)

/-- The entire current forward-ID vector and continuous time control are
retained jointly with the entire simultaneous action profile. -/
theorem map_originalScalarObservable (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) :
    (originalScalarSnapshotMeasure x).map
      (fun w => originalScalarObservable x st t w.1 w.2) =
    (currentSnapshotMeasure x t).map
      (fun w => (w.1, BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t)) := by
  have ho := measurable_originalScalarObservable x st t
  have hc := measurable_fst.prodMk (measurable_currentActions x st t)
  ext E hE
  rw [Measure.map_apply ho hE, Measure.map_apply hc hE]
  change ((roundCoordinatesMeasure p).prod (originalScalarVectorMeasure p)) _ =
    ((roundCoordinatesMeasure p).prod (roundPrivateMeasure x)) _
  rw [Measure.prod_apply (ho hE), Measure.prod_apply (hc hE)]
  apply lintegral_congr
  intro r
  have hslice := hE.preimage (measurable_const.prodMk measurable_id :
    Measurable (fun a : ActionProfile p.m p.K => (r, a)))
  have hfixed := congrArg (fun μ : Measure (ActionProfile p.m p.K) =>
    μ ((fun a => (r, a)) ⁻¹' E)) (map_originalScalarActions x st t r)
  have hom : Measurable (originalScalarActions x st t r) :=
    (measurable_originalScalarActions x st t).of_uncurry_left
  have hcm : Measurable (fun d : BootstrapModeService.RoundPrivateValues x =>
      BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) :=
    (measurable_currentActions x st t).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hom hslice, Measure.map_apply hcm hslice] at hfixed
  exact hfixed

/-- The observable carrier retains every public coordinate and every action. -/
abbrev Observable (p : ConstructorDimensions.Parameters) :=
  BootstrapModeService.RoundCoordinates p × ActionProfile p.m p.K

/-- Literal collision feedback from the full action profile and fixed rewards. -/
def feedbackOfObservable (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (i : Player p.m) (w : Observable p) : ℝ :=
  playerFeedback w.2
    (fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards t a)) i

/-- Literal typed grid observation, including collision zero. -/
def observationOfObservable (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (i : Player p.m) (w : Observable p) : Fin (D p + 1) :=
  if collisionFreeFor w.2 i then x.rewards t (w.2 i) else ⟨0, Nat.zero_lt_succ _⟩

/-- The existing step, expressed only through the observable public row,
physical feedback, fixed IDs, and supplied pre-choice state. -/
def stepOfObservable (x : BootstrapPhysicalBlock.Input p s) (st : State p)
    (t : Fin p.T) (w : Observable p) : State p :=
  if t ∈ calendarBlock p s ∧ st.mode = .discover ∧ roundSlot w.1 = dataSlot ∧
      0 < feedbackOfObservable x t (coordinator p.two_le_m) w then
    let kept := st.list.filter fun u => x.ids u t = true
    ⟨kept, if kept.card ≤ L0 p then .multicast else .discover, insert t st.positives⟩
  else st

/-- The actual DATA-stay-positive indicator expressed through the observable. -/
def dataStayPositiveOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (w : Observable p) : ℝ :=
  if x.active j = true ∧ x.ids (x.privateId j) t = false ∧
      roundSlot w.1 = dataSlot ∧
      0 < feedbackOfObservable x t (followerPlayer p.two_le_m j.1) w then 1 else 0

theorem measurable_feedbackOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (i : Player p.m) : Measurable (feedbackOfObservable x t i) :=
  (Measurable.of_discrete (f := fun a : ActionProfile p.m p.K =>
    playerFeedback a (fun a => RealRewardGridCount.realRewardGridValue
      (D p) (D_pos p) (x.rewards t a)) i)).comp measurable_snd

theorem measurable_observationOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (i : Player p.m) : Measurable (observationOfObservable x t i) :=
  (Measurable.of_discrete (f := fun a : ActionProfile p.m p.K =>
    if collisionFreeFor a i then x.rewards t (a i) else ⟨0, Nat.zero_lt_succ _⟩)).comp
      measurable_snd

theorem measurable_stepOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) : Measurable (stepOfObservable x st t) := by
  change Measurable (fun w => stepOfObservable x st t w)
  have hd : MeasurableSet {w : Observable p | roundSlot w.1 = dataSlot} :=
    (measurableSet_singleton dataSlot).preimage
      ((measurePreserving_roundSlot p).measurable.comp measurable_fst)
  have hp := (measurableSet_Ioi (a := (0 : ℝ))).preimage
    (measurable_feedbackOfObservable x t (coordinator p.two_le_m))
  by_cases hcal : t ∈ calendarBlock p s
  · by_cases hm : st.mode = .discover
    · simpa only [stepOfObservable, hcal, hm, true_and] using
        (Measurable.ite (hd.inter hp) measurable_const measurable_const :
          Measurable (fun w : Observable p =>
            if roundSlot w.1 = dataSlot ∧
                0 < feedbackOfObservable x t (coordinator p.two_le_m) w then
              (⟨st.list.filter (fun u => x.ids u t = true),
                if (st.list.filter (fun u => x.ids u t = true)).card ≤ L0 p then
                  .multicast else .discover, insert t st.positives⟩ : State p)
            else st))
    · simp only [stepOfObservable, hm, and_false, false_and, ite_false]
      exact measurable_const
  · simp only [stepOfObservable, hcal, false_and, ite_false]
    exact measurable_const

theorem measurable_dataStayPositiveOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    Measurable (dataStayPositiveOfObservable x t j) := by
  change Measurable (fun w => dataStayPositiveOfObservable x t j w)
  have hd : MeasurableSet {w : Observable p | roundSlot w.1 = dataSlot} :=
    (measurableSet_singleton dataSlot).preimage
      ((measurePreserving_roundSlot p).measurable.comp measurable_fst)
  have hp := (measurableSet_Ioi (a := (0 : ℝ))).preimage
    (measurable_feedbackOfObservable x t (followerPlayer p.two_le_m j.1))
  by_cases ha : x.active j = true
  · by_cases hid : x.ids (x.privateId j) t = false
    · simpa only [dataStayPositiveOfObservable, ha, hid, true_and] using
        (Measurable.ite (hd.inter hp) measurable_const measurable_const :
          Measurable (fun w : Observable p =>
            if roundSlot w.1 = dataSlot ∧
                0 < feedbackOfObservable x t (followerPlayer p.two_le_m j.1) w then
              (1 : ℝ) else 0))
    · simp only [dataStayPositiveOfObservable, hid, Bool.true_eq_false, false_and, and_false, ite_false]
      exact measurable_const
  · simp only [dataStayPositiveOfObservable, ha, Bool.false_eq_true, false_and, ite_false]
    exact measurable_const

theorem feedbackOfObservable_eq (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) (i : Player p.m) :
    feedbackOfObservable x t i
        (r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      BootstrapPhysicalBlock.feedback (currentInputOf x t r d) st t i := rfl

theorem observationOfObservable_eq (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) (i : Player p.m) :
    observationOfObservable x t i
        (r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      BootstrapPhysicalBlock.observationIndex (currentInputOf x t r d) st t i := rfl

theorem stepOfObservable_eq (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) :
    stepOfObservable x st t
        (r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      BootstrapPhysicalBlock.step (currentInputOf x t r d) st t := by
  have hs : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = roundSlot r := by
    simp only [currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
      roundSlot, roundSlice, ite_true]
  simp only [stepOfObservable, BootstrapPhysicalBlock.step,
    BootstrapPhysicalBlock.discoveryPositive, hs]
  rfl

theorem dataStayPositiveOfObservable_eq (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) (j : {j // j ∈ x.uninformed}) :
    dataStayPositiveOfObservable x t j
        (r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      dataStayPositive x st t j r d := by
  have hs : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = roundSlot r := by
    simp only [currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
      roundSlot, roundSlice, ite_true]
  simp only [dataStayPositiveOfObservable, dataStayPositive, hs]
  rfl

/-- A measurable consumer of the proved joint observable law. -/
theorem map_observable_consumer {α : Type*} [MeasurableSpace α]
    (x : BootstrapPhysicalBlock.Input p s) (st : State p) (t : Fin p.T)
    (f : Observable p → α) (hf : Measurable f) :
    (originalScalarSnapshotMeasure x).map
        (fun w => f (originalScalarObservable x st t w.1 w.2)) =
      (currentSnapshotMeasure x t).map
        (fun w => f (w.1, BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t)) := by
  change (originalScalarSnapshotMeasure x).map
    (f ∘ fun w => originalScalarObservable x st t w.1 w.2) =
    (currentSnapshotMeasure x t).map
      (f ∘ fun w => (w.1, BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t))
  rw [← Measure.map_map hf (measurable_originalScalarObservable x st t),
    ← Measure.map_map hf (measurable_fst.prodMk (measurable_currentActions x st t)),
    map_originalScalarObservable]

/-- Simultaneously retain the observable, every physical feedback, every typed
observation, and the existing state step. -/
def physicalOutputOfObservable (x : BootstrapPhysicalBlock.Input p s) (st : State p)
    (t : Fin p.T) (w : Observable p) :
    Observable p × ((Player p.m → ℝ) × ((Player p.m → Fin (D p + 1)) × State p)) :=
  (w, ((fun i => feedbackOfObservable x t i w),
    ((fun i => observationOfObservable x t i w), stepOfObservable x st t w)))

theorem measurable_physicalOutputOfObservable (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) : Measurable (physicalOutputOfObservable x st t) :=
  measurable_id.prodMk
    ((measurable_pi_iff.mpr (measurable_feedbackOfObservable x t)).prodMk
      ((measurable_pi_iff.mpr (measurable_observationOfObservable x t)).prodMk
        (measurable_stepOfObservable x st t)))

theorem physicalOutputOfObservable_eq (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (d : BootstrapModeService.RoundPrivateValues x) :
    physicalOutputOfObservable x st t
        (r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t) =
      ((r, BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t),
        ((fun i => BootstrapPhysicalBlock.feedback (currentInputOf x t r d) st t i),
          ((fun i => BootstrapPhysicalBlock.observationIndex (currentInputOf x t r d) st t i),
            BootstrapPhysicalBlock.step (currentInputOf x t r d) st t))) := by
  simp only [physicalOutputOfObservable, feedbackOfObservable_eq,
    observationOfObservable_eq, stepOfObservable_eq]

/-- The proved joint law is consumed by the literal existing physical
feedback, typed observations, and state update, jointly with the full original
observable. This theorem also covers an empty incoming follower set. -/
theorem map_originalScalar_physicalOutput (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) :
    (originalScalarSnapshotMeasure x).map (fun w =>
      let y := currentInputOf x t w.1 (roundPrivateValuesOfOriginalScalars x w.2)
      ((w.1, BootstrapPhysicalBlock.actions y st t),
        ((fun i => BootstrapPhysicalBlock.feedback y st t i),
          ((fun i => BootstrapPhysicalBlock.observationIndex y st t i),
            BootstrapPhysicalBlock.step y st t)))) =
    (currentSnapshotMeasure x t).map (fun w =>
      let y := currentInputOf x t w.1 w.2
      ((w.1, BootstrapPhysicalBlock.actions y st t),
        ((fun i => BootstrapPhysicalBlock.feedback y st t i),
          ((fun i => BootstrapPhysicalBlock.observationIndex y st t i),
            BootstrapPhysicalBlock.step y st t)))) := by
  have h := map_observable_consumer x st t (physicalOutputOfObservable x st t)
    (measurable_physicalOutputOfObservable x st t)
  simpa only [physicalOutputOfObservable, originalScalarObservable, originalScalarActions,
    feedbackOfObservable_eq, observationOfObservable_eq, stepOfObservable_eq] using h

/-- Integral identity for every measurable real observable consumer of the
proved joint law. Integrability of the concrete stay consumer is proved below. -/
theorem integral_observable_consumer (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (f : Observable p → ℝ) (hf : Measurable f) :
    (∫ w, f (originalScalarObservable x st t w.1 w.2) ∂originalScalarSnapshotMeasure x) =
      ∫ w, f (w.1, BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t)
        ∂currentSnapshotMeasure x t := by
  calc
    _ = ∫ w, f w ∂(originalScalarSnapshotMeasure x).map
        (fun w => originalScalarObservable x st t w.1 w.2) :=
      (integral_map (measurable_originalScalarObservable x st t).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = ∫ w, f w ∂(currentSnapshotMeasure x t).map
        (fun w => (w.1, BootstrapPhysicalBlock.actions (currentInputOf x t w.1 w.2) st t)) := by
      rw [map_originalScalarObservable]
    _ = _ := integral_map
      (measurable_fst.prodMk (measurable_currentActions x st t)).aemeasurable
        hf.aestronglyMeasurable

theorem measurable_originalScalar_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    Measurable (fun w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p =>
      dataStayPositive x st t j w.1 (roundPrivateValuesOfOriginalScalars x w.2)) := by
  have h := (measurable_dataStayPositiveOfObservable x t j).comp
    (measurable_originalScalarObservable x st t)
  simpa only [Function.comp_def, originalScalarObservable, originalScalarActions,
    dataStayPositiveOfObservable_eq] using h

theorem map_originalScalar_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    (originalScalarSnapshotMeasure x).map (fun w =>
      dataStayPositive x st t j w.1 (roundPrivateValuesOfOriginalScalars x w.2)) =
      (currentSnapshotMeasure x t).map (fun w => dataStayPositive x st t j w.1 w.2) := by
  have h := map_observable_consumer x st t (dataStayPositiveOfObservable x t j)
    (measurable_dataStayPositiveOfObservable x t j)
  simpa only [originalScalarObservable, originalScalarActions,
    dataStayPositiveOfObservable_eq] using h

theorem measurable_current_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    Measurable (fun w : BootstrapModeService.RoundCoordinates p ×
        BootstrapModeService.RoundPrivateValues x => dataStayPositive x st t j w.1 w.2) := by
  have h := (measurable_dataStayPositiveOfObservable x t j).comp
    (measurable_fst.prodMk (measurable_currentActions x st t))
  simpa only [Function.comp_def, dataStayPositiveOfObservable_eq] using h

/-- Integrability of the actual original-scalar stay indicator requires no
extra fixed-row law, expected-value equality, or isolation premise. -/
theorem integrable_originalScalar_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    Integrable (fun w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p =>
      dataStayPositive x st t j w.1 (roundPrivateValuesOfOriginalScalars x w.2))
      (originalScalarSnapshotMeasure x) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_originalScalar_dataStayPositive x st t j).aestronglyMeasurable
  filter_upwards [] with w
  unfold dataStayPositive
  split_ifs <;> norm_num

theorem integrable_current_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    Integrable (fun w : BootstrapModeService.RoundCoordinates p ×
        BootstrapModeService.RoundPrivateValues x => dataStayPositive x st t j w.1 w.2)
      (currentSnapshotMeasure x t) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_current_dataStayPositive x st t j).aestronglyMeasurable
  filter_upwards [] with w
  unfold dataStayPositive
  split_ifs <;> norm_num

/-- Usable unconditional integral identity for the actual indicator composed
with the predecessor's literal same-scalar adapter. -/
theorem integral_originalScalar_dataStayPositive (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    (∫ w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p,
      dataStayPositive x st t j w.1 (roundPrivateValuesOfOriginalScalars x w.2)
        ∂originalScalarSnapshotMeasure x) =
    ∫ w : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
      dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t := by
  have h := integral_observable_consumer x st t (dataStayPositiveOfObservable x t j)
    (measurable_dataStayPositiveOfObservable x t j)
  simpa only [originalScalarObservable, originalScalarActions,
    dataStayPositiveOfObservable_eq] using h

/-- Transfer of the accepted fixed-snapshot stay mean with exactly its visible
calendar, distinguished-follower, target, isolation, and mode inputs.
Source: `appendix_b_communication.tex:485-490`; no chronological conditioning
or whole-block averaging is claimed. -/
theorem originalScalar_dataStayPositive_mean_ge (x : BootstrapPhysicalBlock.Input p s)
    (st : State p) (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (hcal : t ∈ calendarBlock p s) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmode : st.mode = .discover ∨ st.mode = .multicast) :
    (∫ w : BootstrapModeService.RoundCoordinates p × OriginalScalarVector p,
      dataStayPositive x st t j w.1 (roundPrivateValuesOfOriginalScalars x w.2)
        ∂originalScalarSnapshotMeasure x) ≥
      chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0) / 16 := by
  rw [integral_originalScalar_dataStayPositive]
  exact BootstrapStayGainMean.dataStayPositive_mean_ge x st t j a z
    hcal hactive hheld htarget hza hinactive hmode

/-- At the existing source block input, the just-proved observable law's
outputs pull back pointwise to that input's actual physical outputs and DATA
stay indicator. The source fields are exactly `playerRoundScalarAt p rho i t`;
no new run or replacement private coordinates are constructed. -/
theorem originalScalar_source_outputs_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T)
    (st : State p) (j : {j // j ∈ incoming}) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    (physicalOutputOfObservable x st t
        (originalScalarObservable x st t (roundCoordinates p t x.row)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t)) =
      ((roundCoordinates p t x.row, BootstrapPhysicalBlock.actions x st t),
        ((fun i => BootstrapPhysicalBlock.feedback x st t i),
          ((fun i => BootstrapPhysicalBlock.observationIndex x st t i),
            BootstrapPhysicalBlock.step x st t)))) ∧
    (dataStayPositive x st t j (roundCoordinates p t x.row)
        (roundPrivateValuesOfOriginalScalars x
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t)) =
      if x.active j = true ∧ x.ids (x.privateId j) t = false ∧
          BootstrapPhysicalBlock.slot x t = dataSlot ∧
          0 < BootstrapPhysicalBlock.feedback x st t (followerPlayer p.two_le_m j.1)
      then 1 else 0) := by
  dsimp only
  constructor
  · simp only [originalScalarObservable, originalScalarActions]
    rw [physicalOutputOfObservable_eq, currentInputOf_originalScalar_blockInput]
  · unfold dataStayPositive
    rw [currentInputOf_originalScalar_blockInput]

end Bandits.Support.BootstrapOriginalScalarLaw

end
