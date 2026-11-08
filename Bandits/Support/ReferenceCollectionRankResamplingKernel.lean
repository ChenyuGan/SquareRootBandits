/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionRankCellPhysicalTransport
public import Bandits.Support.ReferenceCollectionEarlierMarkedPrefix

/-!
# Actual rank-adapted collection resampling

The kernel reads the actual kth collection invocation on its input source.
Absence returns that source and an absent mark. A present invocation sums all
checked outcomes, retaining the entire assignment vector and the original
strict-past source mark. Its consumer is
`ReferenceChronologicalCollectionPhysicalMarginalInduction`.

Sources: `06_interruptions.tex:391-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceCollectionRankResamplingKernel

open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open AssignmentParameterFibreKernel (fibreMass fibreMeasure successfulSlowSet)
open ReferenceLaterOptionalControlResampling (controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open ContinuousLearningRows (TimeControl)
open BootstrapPrivateRoundStreams (sourceInputLaw)
open ReferenceFirstCollectionOriginalSourceFibreTransport
  (SourceInput Outcome AssignmentVector JointY originalSourceSection)

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance fibreMeasure_probability (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) (a : Outcome p) :
    IsProbabilityMeasure (fibreMeasure p theta a) :=
  ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
    (κ := AssignmentParameterFibreKernel.assignmentParameterFibreKernel p) (theta, a)

abbrev VectorRemainder (p : ConstructorDimensions.Parameters) :=
  AssignmentVector p × ReferenceLaterOptionalControlResampling.ControlRemainder p

private theorem measurable_optionElimWith {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (f : X → Option A) (hf : Measurable f)
    (g : A × X → B) (hg : Measurable g)
    (h : X → B) (hh : Measurable h) :
    Measurable (fun x => (f x).elim (h x) (fun a => g (a, x))) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv A X
  have hd : Measurable (Sum.elim g (fun q : PUnit × X => h q.2)) :=
    measurable_fun_sum hg (hh.comp measurable_snd)
  convert hd.comp (e.measurable.comp (hf.prodMk measurable_id)) using 1
  funext x
  change (f x).elim (h x) (fun a => g (a, x)) =
    Sum.elim g (fun q : PUnit × X => h q.2) (e (f x, x))
  cases f x <;> rfl

private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (fun l : List A => l[k]?) := by
  have htag : Measurable (fun l : List A =>
      ReferenceActiveHorizonMeasurability.listObservationAt l k) :=
    (measurable_pi_apply k).comp
      (measurable_snd.comp
        ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates)
  have hdecode : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_fun_sum measurable_const
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hdecode.comp htag using 1
  funext l
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationAt]
  cases l[k]? <;> rfl

local instance prodMeasurableEq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableEq A] [MeasurableEq B] : MeasurableEq (A × B) where
  measurableSet_diagonal := by
    have h := (measurableSet_eq_fun
      (measurable_fst.fst : Measurable (fun x : (A × B) × (A × B) => x.1.1))
      measurable_snd.fst).inter
        (measurableSet_eq_fun measurable_fst.snd measurable_snd.snd)
    convert h using 1
    ext x
    exact Prod.ext_iff

local instance piMeasurableEq {ι : Type*} [Countable ι] {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableEq (A i)] :
    MeasurableEq (∀ i, A i) where
  measurableSet_diagonal := by
    have h : MeasurableSet (⋂ i : ι, {x : (∀ i, A i) × (∀ i, A i) |
        x.1 i = x.2 i}) := MeasurableSet.iInter fun i =>
      measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd)
    convert h using 1
    ext x
    simp only [Set.mem_diagonal_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact funext_iff

local instance optionMeasurableEq {A : Type*} [MeasurableSpace A] [MeasurableEq A] :
    MeasurableEq (Option A) where
  measurableSet_diagonal := by
    have hnone : MeasurableSet ({none} : Set (Option A)) := by
      change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit A)] _
      rw [MeasurableSpace.measurableSet_comap]
      refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
      ext o
      cases o <;> simp
    have hleft : Measurable (fun q : A × (Option A × Option A) =>
        q.2.2.elim False (fun b => q.1 = b)) :=
      measurable_optionElimWith _ measurable_snd.snd
        (fun q : A × (A × (Option A × Option A)) => q.2.1 = q.1)
        (measurable_snd.fst.eq measurable_fst) _ measurable_const
    have hright : Measurable (fun q : Option A × Option A => q.2 = none) :=
      measurableSet_setOfPred.mp (measurable_snd hnone)
    have h := measurable_optionElimWith _ measurable_fst _ hleft _ hright
    convert measurableSet_setOfPred.mpr h using 1
    ext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp

local instance listMeasurableEq {A : Type*} [MeasurableSpace A] [MeasurableEq A] :
    MeasurableEq (List A) where
  measurableSet_diagonal := by
    have h : MeasurableSet (⋂ n : ℕ, {x : List A × List A | x.1[n]? = x.2[n]?}) :=
      MeasurableSet.iInter fun n => measurableSet_eq_fun
        ((measurable_list_getElem? n).comp measurable_fst)
        ((measurable_list_getElem? n).comp measurable_snd)
    convert h using 1
    ext x
    simp only [Set.mem_diagonal_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun heq n => congrArg (fun l : List A => l[n]?) heq, List.ext_getElem?⟩

private theorem measurable_list_take {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (List.take k : List A → List A) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · change Measurable (fun l : List A => (l.take k).length)
    simp only [List.length_take]
    exact ((measurable_of_countable (fun n : ℕ => min k n))).comp
      (measurable_fst.comp
        ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates)
  · apply measurable_pi_iff.mpr
    intro n
    change Measurable (fun l : List A =>
      ReferenceActiveHorizonMeasurability.listObservationAt (l.take k) n)
    by_cases hn : n < k
    · have heq : (fun l : List A =>
          ReferenceActiveHorizonMeasurability.listObservationAt (l.take k) n) =
          fun l => ReferenceActiveHorizonMeasurability.listObservationAt l n := by
        funext l
        simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_take_of_lt hn]
      rw [heq]
      exact (measurable_pi_apply n).comp (measurable_snd.comp
        ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates)
    · have heq : (fun l : List A =>
          ReferenceActiveHorizonMeasurability.listObservationAt (l.take k) n) =
          fun _ => (Sum.inl () : Unit ⊕ A) := by
        funext l
        simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_take_eq_none (Nat.le_of_not_lt hn)]
      rw [heq]
      exact measurable_const

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual invocation list is Borel in its continuous parameter space. -/
theorem collectionCalls_measurable (control0 : TimeControl p) :
    Measurable (ReferenceCollectionSamplerChronology.collectionCalls
      rate rewards C_star C_h) := by
  have heq : ReferenceCollectionEarlierMarkedPrefix.earlierCalls
      rate rewards C_star C_h p.T =
      ReferenceCollectionSamplerChronology.collectionCalls rate rewards C_star C_h := by
    funext z
    apply List.filter_eq_self.mpr
    intro a _
    simp only [decide_eq_true_eq]
    exact a.2.1.isLt
  rw [← heq]
  exact ReferenceCollectionEarlierMarkedPrefix.earlierCalls_measurable
    rate rewards C_star C_h control0 p.T

/-- The rank selector retains ordinary Borel theta coordinates. -/
theorem nthCollectionCall_measurable (control0 : TimeControl p) (k : ℕ) :
    Measurable (ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k) :=
  (measurable_list_getElem? k).comp
    (collectionCalls_measurable rate rewards C_star C_h control0)

/-- Literal replacement and marked payload for one present outcome. -/
def fibreOutput (control0 : TimeControl p) (u s : Fin p.T) (a : Outcome p)
    (z : SourceInput p) (vw : VectorRemainder p) : JointY p :=
  (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw),
    some (u, (s, (sourcePrefix control0 s.val z, (some a, vw.1)))))

/-- The finite mixture includes checked failure and every zero-weight fibre. -/
def presentFibreMeasure (control0 : TimeControl p) (u s : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p) (z : SourceInput p) :
    Measure (JointY p) :=
  ∑ a : Outcome p, fibreMass p theta a •
    (((fibreMeasure p theta a).prod (controlRemainderLaw p)).map
      (fibreOutput control0 u s a z))

theorem fibreOutput_measurable (control0 : TimeControl p) (u s : Fin p.T)
    (a : Outcome p) :
    Measurable (fun x : SourceInput p × VectorRemainder p =>
      fibreOutput control0 u s a x.1 x.2) := by
  have hsource := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
    p s).comp (measurable_fst.prodMk
      ((controlAssignmentSplitEquiv p).symm.measurable.comp measurable_snd))
  have hprefix := (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
    control0 s.val).comp (measurable_fst : Measurable (Prod.fst :
      SourceInput p × VectorRemainder p → SourceInput p))
  exact hsource.prodMk
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_const.prodMk (measurable_const.prodMk
        (hprefix.prodMk (measurable_const.prodMk measurable_snd.fst)))))

/-- Joint Borelness uses the admitted parameter-fibre kernel and its product
with the original remainder law, before taking the finite weighted sum. -/
theorem presentFibreMeasure_measurable (control0 : TimeControl p) (u s : Fin p.T) :
    Measurable (fun x : AssignmentParameterFibreKernel.Theta p × SourceInput p =>
      presentFibreMeasure control0 u s x.1 x.2) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have hterm (a : Outcome p) : Measurable (fun x :
      AssignmentParameterFibreKernel.Theta p × SourceInput p =>
      fibreMass p x.1 a *
        (((fibreMeasure p x.1 a).prod (controlRemainderLaw p)).map
          (fibreOutput control0 u s a x.2)) B) := by
    let κ := ((AssignmentParameterFibreKernel.assignmentParameterFibreKernel p).comap
      (fun x : AssignmentParameterFibreKernel.Theta p × SourceInput p => (x.1, a))
      (measurable_fst.prodMk measurable_const)).prod
        (ProbabilityTheory.Kernel.const
          (AssignmentParameterFibreKernel.Theta p × SourceInput p) (controlRemainderLaw p))
    have hmap : Measurable (fun x :
        (AssignmentParameterFibreKernel.Theta p × SourceInput p) × VectorRemainder p =>
        fibreOutput control0 u s a x.1.2 x.2) :=
      (fibreOutput_measurable control0 u s a).comp
        (measurable_fst.snd.prodMk measurable_snd)
    have hsection := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
      (κ := κ) (hmap hB)
    have hmass := (AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
      (measurable_fst.prodMk (measurable_const : Measurable (fun _ :
        AssignmentParameterFibreKernel.Theta p × SourceInput p => a)))
    apply hmass.mul
    convert hsection using 1
    funext x
    have hout : Measurable (fibreOutput control0 u s a x.2) :=
      (fibreOutput_measurable control0 u s a).comp measurable_prodMk_left
    rw [Measure.map_apply hout hB]
    simp only [κ, ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.const_apply,
      AssignmentParameterFibreKernel.assignmentParameterFibreKernel_apply]
    rfl
  simpa only [presentFibreMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul] using Finset.measurable_sum Finset.univ (fun a _ => hterm a)

/-- Literal sourcewise measure, with actual absence as its sole absent branch. -/
def rankResamplingMeasure (k : ℕ) (control0 : TimeControl p) (z : SourceInput p) :
    Measure (JointY p) :=
  match ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none => Measure.dirac (z, none)
  | some (u, (s, theta)) => presentFibreMeasure control0 u s theta z

private theorem presentFibreMeasure_dates_measurable (control0 : TimeControl p) :
    Measurable (fun x : Fin p.T ×
      (Fin p.T × (AssignmentParameterFibreKernel.Theta p × SourceInput p)) =>
      presentFibreMeasure control0 x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  apply measurable_from_prod_countable_right
  intro u
  apply measurable_from_prod_countable_right
  intro s
  exact presentFibreMeasure_measurable control0 u s

private theorem presentFibreMeasure_call_measurable (control0 : TimeControl p) :
    Measurable (fun x :
      ReferenceFirstCollectionSamplerCall.Call p × SourceInput p =>
      presentFibreMeasure control0 x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  let e₁ := MeasurableEquiv.prodAssoc (α := Fin p.T)
    (β := Fin p.T × AssignmentParameterFibreKernel.Theta p) (γ := SourceInput p)
  let e₂ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin p.T))
    (MeasurableEquiv.prodAssoc (α := Fin p.T)
      (β := AssignmentParameterFibreKernel.Theta p) (γ := SourceInput p))
  have h := (presentFibreMeasure_dates_measurable control0).comp (e₁.trans e₂).measurable
  convert h using 1
  funext x
  rfl

theorem rankResamplingMeasure_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (rankResamplingMeasure rate rewards C_star C_h k control0) := by
  have hnone : Measurable (fun z : SourceInput p =>
      Measure.dirac (z, (none : ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p))) :=
    Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const)
  have h := measurable_optionElimWith
    (ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k)
    (nthCollectionCall_measurable rate rewards C_star C_h control0 k)
    (fun x : ReferenceFirstCollectionSamplerCall.Call p × SourceInput p =>
      presentFibreMeasure control0 x.1.1 x.1.2.1 x.1.2.2 x.2)
    (presentFibreMeasure_call_measurable control0)
    (fun z : SourceInput p => Measure.dirac
      (z, (none : ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p))) hnone
  convert h using 1
  funext z
  unfold rankResamplingMeasure
  cases ReferenceCollectionSamplerChronology.nthCollectionCall
    rate rewards C_star C_h k z with
  | none => rfl
  | some call => rcases call with ⟨u, s, theta⟩; rfl

/-- Actual rank-adapted full-vector fibre kernel on the original source. -/
def rankResamplingKernel (k : ℕ) (control0 : TimeControl p) :
    ProbabilityTheory.Kernel (SourceInput p) (JointY p) where
  toFun := rankResamplingMeasure rate rewards C_star C_h k control0
  measurable' := rankResamplingMeasure_measurable rate rewards C_star C_h k control0

theorem rankResamplingKernel_apply_none (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = none) :
    rankResamplingKernel rate rewards C_star C_h k control0 z = Measure.dirac (z, none) := by
  change rankResamplingMeasure rate rewards C_star C_h k control0 z = _
  rw [rankResamplingMeasure, hcall]

/-- Beyond the actual finite invocation list, resampling is exactly identity
with an absent invocation mark, including every physical continuation. -/
theorem rankResamplingKernel_apply_of_length_le (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p)
    (hk : (ReferenceCollectionSamplerChronology.collectionCalls
      rate rewards C_star C_h z).length ≤ k) :
    rankResamplingKernel rate rewards C_star C_h k control0 z = Measure.dirac (z, none) := by
  apply rankResamplingKernel_apply_none rate rewards C_star C_h k control0 z
  exact List.getElem?_eq_none_iff.mpr hk

theorem rankResamplingKernel_apply_some (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) (u s : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    rankResamplingKernel rate rewards C_star C_h k control0 z =
      ∑ a : Outcome p, fibreMass p theta a •
        (((fibreMeasure p theta a).prod (controlRemainderLaw p)).map
          (fun vw =>
            (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw),
              some (u, (s, (sourcePrefix control0 s.val z, (some a, vw.1))))))) := by
  change rankResamplingMeasure rate rewards C_star C_h k control0 z = _
  rw [rankResamplingMeasure, hcall]
  rfl

instance instIsMarkovKernelRankResamplingKernel (k : ℕ) (control0 : TimeControl p) :
    ProbabilityTheory.IsMarkovKernel
      (rankResamplingKernel rate rewards C_star C_h k control0) where
  isProbabilityMeasure z := by
    apply isProbabilityMeasure_iff.mpr
    cases hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
        rate rewards C_star C_h k z with
    | none =>
        rw [rankResamplingKernel_apply_none rate rewards C_star C_h k control0 z hcall]
        exact measure_univ
    | some call =>
        rcases call with ⟨u, s, theta⟩
        rw [rankResamplingKernel_apply_some rate rewards C_star C_h k control0 z u s theta hcall]
        rw [Measure.finsetSum_apply]
        · simp only [Measure.smul_apply, smul_eq_mul]
          have hmap (a : Outcome p) :
              (((fibreMeasure p theta a).prod (controlRemainderLaw p)).map
                (fibreOutput control0 u s a z)) Set.univ = 1 := by
            have hout : Measurable (fibreOutput control0 u s a z) :=
              (fibreOutput_measurable control0 u s a).comp measurable_prodMk_left
            rw [Measure.map_apply hout MeasurableSet.univ, Set.preimage_univ]
            exact measure_univ
          change (∑ a : Outcome p, fibreMass p theta a *
            (((fibreMeasure p theta a).prod (controlRemainderLaw p)).map
              (fibreOutput control0 u s a z)) Set.univ) = 1
          simp only [hmap, mul_one]
          exact AssignmentParameterFibreKernel.sum_fibreMass_eq_one p theta

/-- The analytical list of the original marks of the first `k` actual calls. -/
def markedPrefix (k : ℕ) (control0 : TimeControl p) (z : SourceInput p) :
    List (Fin p.T × (Fin p.T × ReferenceFirstCollectionPastSamplerFibreLaw.MarkedPayload p)) :=
  ((ReferenceCollectionSamplerChronology.collectionCalls
    rate rewards C_star C_h z).take k).map (fun call =>
      (call.1, (call.2.1, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 call.2.1 z)))

theorem markedPrefix_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (markedPrefix rate rewards C_star C_h k control0) := by
  have hfull (z : SourceInput p) :
      ReferenceCollectionEarlierMarkedPrefix.earlierCalls rate rewards C_star C_h p.T z =
      ReferenceCollectionSamplerChronology.collectionCalls rate rewards C_star C_h z := by
    apply List.filter_eq_self.mpr
    intro a _
    simp only [decide_eq_true_eq]
    exact a.2.1.isLt
  have heq : markedPrefix rate rewards C_star C_h k control0 =
      fun z => (ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls
        rate rewards C_star C_h control0 p.T z).take k := by
    funext z
    simp only [markedPrefix, ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls,
      hfull, List.map_take]
  rw [heq]
  exact (measurable_list_take k).comp
    (ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls_measurable
      rate rewards C_star C_h control0 p.T)

/-- Every present branch preserves its actual rank, cutoff, date, parameter,
and the complete list of earlier original marks, for every replacement. -/
theorem presentRank_markedPrefix_replaceSourceControl (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) (u s : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) (c : TimeControl p) :
    ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k
        (replaceSourceControl p s z c) = some (u, (s, theta)) ∧
      markedPrefix rate rewards C_star C_h k control0 (replaceSourceControl p s z c) =
        markedPrefix rate rewards C_star C_h k control0 z := by
  obtain ⟨hnew, _, hmarks⟩ :=
    ReferenceCollectionEarlierMarkedPrefix.presentRank_prefix_and_marks_replaceSourceControl
      rate rewards C_star C_h control0 k u s theta z c hcall
  refine ⟨hnew, ?_⟩
  exact (ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls_eq_mapped_take_of_present_rank
    rate rewards C_star C_h control0 k u s theta _ hnew).symm.trans hmarks

private theorem split_assignmentVector (vw : VectorRemainder p) :
    ContinuousControlSlice.assignmentVector ((controlAssignmentSplitEquiv p).symm vw).1 =
      vw.1 := by
  have hfirst (c : TimeControl p) : (controlAssignmentSplitEquiv p c).1 =
      ContinuousControlSlice.assignmentVector c.1 := by
    funext r
    rfl
  rw [← hfirst, (controlAssignmentSplitEquiv p).apply_symm_apply]

private theorem currentAssignmentVector_replace (s : Fin p.T) (z : SourceInput p)
    (vw : VectorRemainder p) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s
      (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw)) = vw.1 := by
  rw [show ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s
      (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw)) =
      ContinuousControlSlice.assignmentVector ((controlAssignmentSplitEquiv p).symm vw).1 by
    simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
      ReferenceSourceCurrentControlFreshness.u_t, replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex]]
  exact split_assignmentVector vw

/-- On its sampler fibre, the emitted mark is recomputed from the replaced
source's actual invocation and checked sampler. -/
theorem fibreOutput_graph (k : ℕ) (control0 : TimeControl p) (z : SourceInput p)
    (u s : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta)))
    (a : Outcome p) (vw : VectorRemainder p) (ha : successfulSlowSet p theta vw.1 = a) :
    (fibreOutput control0 u s a z vw).2 =
      ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput
        rate rewards C_star C_h k control0 (fibreOutput control0 u s a z vw).1 := by
  have hnew := (presentRank_markedPrefix_replaceSourceControl
    rate rewards C_star C_h k control0 z u s theta hcall
      ((controlAssignmentSplitEquiv p).symm vw)).1
  have hcell : (fibreOutput control0 u s a z vw).1 ∈
      ReferenceCollectionRankCellPhysicalTransport.rankCell rate rewards C_star C_h k u s :=
    (ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_exists_call
      rate rewards C_star C_h k u s _).mpr ⟨theta, hnew⟩
  obtain ⟨theta', _, _, _, hcall', _, _, _, _, _, _, _, _, _, houtcome⟩ :=
    ReferenceCollectionRankCellPhysicalTransport.rankCell_actualSamplerTrace
      rate rewards C_star C_h k u s _ hcell
  have ht : theta' = theta := by
    have heq := Option.some.inj (hcall'.symm.trans hnew)
    exact congrArg (fun c : ReferenceFirstCollectionSamplerCall.Call p => c.2.2) heq
  simp only [ht] at houtcome
  change ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h s
      (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw)) =
    some (successfulSlowSet p theta
      (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s
        (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw)))) at houtcome
  rw [currentAssignmentVector_replace, ha] at houtcome
  change some (u, (s, (sourcePrefix control0 s.val z, (some a, vw.1)))) = _
  rw [ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput_on_cell
    rate rewards C_star C_h k control0 u s _ hcell]
  simp only [ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair,
    fibreOutput, ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl,
    houtcome, currentAssignmentVector_replace]

private theorem ae_rankResamplingKernel_of_fibres (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) (P : JointY p → Prop) (hP : MeasurableSet {y | P y})
    (hnone : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = none → P (z, none))
    (hpresent : ∀ (u s : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      ReferenceCollectionSamplerChronology.nthCollectionCall
        rate rewards C_star C_h k z = some (u, (s, theta)) →
      ∀ (a : Outcome p) (vw : VectorRemainder p), successfulSlowSet p theta vw.1 = a →
        P (fibreOutput control0 u s a z vw)) :
    ∀ᵐ y ∂rankResamplingKernel rate rewards C_star C_h k control0 z, P y := by
  cases hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none =>
      rw [rankResamplingKernel_apply_none rate rewards C_star C_h k control0 z hcall]
      exact (ae_dirac_iff hP).mpr (hnone hcall)
  | some call =>
      rcases call with ⟨u, s, theta⟩
      rw [rankResamplingKernel_apply_some rate rewards C_star C_h k control0 z u s theta hcall]
      apply ae_finsetSum_measure_iff.mpr
      intro a _
      by_cases hzero : fibreMass p theta a = 0
      · simp [hzero]
      · apply Measure.ae_smul_measure
        have hout : Measurable (fibreOutput control0 u s a z) :=
          (fibreOutput_measurable control0 u s a).comp measurable_prodMk_left
        apply (ae_map_iff hout.aemeasurable hP).mpr
        have ha := AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos
          p theta a (pos_iff_ne_zero.mpr hzero)
        have hprod : ∀ᵐ vw ∂(fibreMeasure p theta a).prod (controlRemainderLaw p),
            successfulSlowSet p theta vw.1 = a :=
          (Measure.quasiMeasurePreserving_fst (μ := fibreMeasure p theta a)
            (ν := controlRemainderLaw p)).ae ha
        filter_upwards [hprod] with vw hv
        exact hpresent u s theta hcall a vw hv

/-- On every original source, the mark agrees almost surely with the actual
ranked sampler graph recomputed on the new source. -/
theorem ae_rankResamplingKernel_graph (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) :
    ∀ᵐ y ∂rankResamplingKernel rate rewards C_star C_h k control0 z,
      y.2 = ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput
        rate rewards C_star C_h k control0 y.1 := by
  apply ae_rankResamplingKernel_of_fibres rate rewards C_star C_h k control0 z _
  · exact measurableSet_eq_fun measurable_snd
      ((ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput_measurable
        rate rewards C_star C_h k control0).comp measurable_fst)
  · intro hcall
    simp only [ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput,
      hcall, Option.map_none]
  · intro u s theta hcall a vw ha
    exact fibreOutput_graph rate rewards C_star C_h k control0 z u s theta hcall a vw ha

/-- All previously accumulated original marks survive the actual kernel. -/
theorem ae_rankResamplingKernel_markedPrefix (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) :
    ∀ᵐ y ∂rankResamplingKernel rate rewards C_star C_h k control0 z,
      markedPrefix rate rewards C_star C_h k control0 y.1 =
        markedPrefix rate rewards C_star C_h k control0 z := by
  apply ae_rankResamplingKernel_of_fibres rate rewards C_star C_h k control0 z _
  · exact measurableSet_eq_fun
      ((markedPrefix_measurable rate rewards C_star C_h k control0).comp measurable_fst)
      measurable_const
  · intro _
    rfl
  · intro u s theta hcall a vw _
    exact (presentRank_markedPrefix_replaceSourceControl
      rate rewards C_star C_h k control0 z u s theta hcall
        ((controlAssignmentSplitEquiv p).symm vw)).2

/-- The same current actual rank, cutoff, date and theta are retained.
This asserts no invariance of the current outcome or future invocations. -/
theorem ae_rankResamplingKernel_nthCollectionCall (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) :
    ∀ᵐ y ∂rankResamplingKernel rate rewards C_star C_h k control0 z,
      ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k y.1 =
        ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k z := by
  apply ae_rankResamplingKernel_of_fibres rate rewards C_star C_h k control0 z _
  · exact measurableSet_eq_fun
      ((nthCollectionCall_measurable rate rewards C_star C_h control0 k).comp measurable_fst)
      measurable_const
  · intro _
    rfl
  · intro u s theta hcall a vw _
    exact (presentRank_markedPrefix_replaceSourceControl
      rate rewards C_star C_h k control0 z u s theta hcall
        ((controlAssignmentSplitEquiv p).symm vw)).1.trans hcall.symm

private theorem indicator_norm_le_one {Y : Type*} (B : Set Y) (y : Y) :
    ‖B.indicator (fun _ => (1 : ℝ)) y‖ ≤ 1 := by
  by_cases hy : y ∈ B <;> simp only [Set.indicator, hy, ↓reduceIte, norm_one,
    norm_zero, le_refl, zero_le_one]

private theorem bounded_integrable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ) (hf : Measurable f)
    (hb : ∀ y, ‖f y‖ ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hb

/-- The ordinary real Borel indicator test of the actual kernel. -/
def kernelTest (k : ℕ) (control0 : TimeControl p) (B : Set (JointY p))
    (z : SourceInput p) : ℝ :=
  ∫ y, B.indicator (fun _ => (1 : ℝ)) y
    ∂rankResamplingKernel rate rewards C_star C_h k control0 z

theorem kernelTest_measurable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Measurable (kernelTest rate rewards C_star C_h k control0 B) :=
  (measurable_const.indicator hB).stronglyMeasurable.integral_kernel.measurable

theorem kernelTest_norm_le_one (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (z : SourceInput p) :
    ‖kernelTest rate rewards C_star C_h k control0 B z‖ ≤ 1 := by
  simpa only [kernelTest, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := rankResamplingKernel rate rewards C_star C_h k control0 z)
      (Filter.Eventually.of_forall (indicator_norm_le_one B)))

theorem kernelTest_integrable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (kernelTest rate rewards C_star C_h k control0 B) (sourceInputLaw p) :=
  bounded_integrable _ _ (kernelTest_measurable rate rewards C_star C_h k control0 B hB)
    (kernelTest_norm_le_one rate rewards C_star C_h k control0 B)

/-- Every real Borel indicator is integrable under each actual kernel law. -/
theorem kernel_indicator_integrable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p) :
    Integrable (B.indicator (fun _ => (1 : ℝ)))
      (rankResamplingKernel rate rewards C_star C_h k control0 z) :=
  bounded_integrable _ _ (measurable_const.indicator hB) (indicator_norm_le_one B)

/-- The same indicator is integrable under the actual composed source law. -/
theorem bind_indicator_integrable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (B.indicator (fun _ => (1 : ℝ)))
      ((sourceInputLaw p).bind (rankResamplingKernel rate rewards C_star C_h k control0)) :=
  bounded_integrable _ _ (measurable_const.indicator hB) (indicator_norm_le_one B)

/-- Exact conversion between the real indicator test and kernel evaluation. -/
theorem kernelTest_eq_toReal (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p) :
    kernelTest rate rewards C_star C_h k control0 B z =
      (rankResamplingKernel rate rewards C_star C_h k control0 z B).toReal :=
  integral_indicator_one hB

private theorem fibreMass_ne_top (theta : AssignmentParameterFibreKernel.Theta p)
    (a : Outcome p) : fibreMass p theta a ≠ ∞ :=
  FiniteFibreLift.fibreMass_ne_top _ _ _

/-- A present-cell kernel test is the admitted original-source section sum. -/
theorem kernelTest_on_cell (k : ℕ) (control0 : TimeControl p) (u s : Fin p.T)
    (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p)
    (hz : z ∈ ReferenceCollectionRankCellPhysicalTransport.rankCell
      rate rewards C_star C_h k u s) :
    kernelTest rate rewards C_star C_h k control0 B z =
      ∑ a : Outcome p, originalSourceSection rate rewards C_star C_h control0 u s a B z := by
  obtain ⟨theta, _, _, _, hcall, _, _, _, _, htheta, _, _, _, _, _⟩ :=
    ReferenceCollectionRankCellPhysicalTransport.rankCell_actualSamplerTrace
      rate rewards C_star C_h k u s z hz
  let μ (a : Outcome p) := (((fibreMeasure p theta a).prod (controlRemainderLaw p)).map
    (fibreOutput control0 u s a z))
  have hfinite (a : Outcome p) : IsFiniteMeasure (fibreMass p theta a • μ a) :=
    Measure.smul_finite _ (fibreMass_ne_top theta a)
  have hint (a : Outcome p) : Integrable (B.indicator (fun _ => (1 : ℝ)))
      (fibreMass p theta a • μ a) := by
    let := hfinite a
    exact bounded_integrable _ _ (measurable_const.indicator hB) (indicator_norm_le_one B)
  unfold kernelTest
  rw [rankResamplingKernel_apply_some rate rewards C_star C_h k control0 z u s theta hcall]
  change (∫ y, B.indicator (fun _ => (1 : ℝ)) y
    ∂∑ a : Outcome p, fibreMass p theta a • μ a) = _
  rw [integral_finsetSum_measure (fun a _ => hint a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_smul_measure]
  have hout : Measurable (fibreOutput control0 u s a z) :=
    (fibreOutput_measurable control0 u s a).comp measurable_prodMk_left
  rw [show (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂μ a) =
      ∫ vw, B.indicator (fun _ => (1 : ℝ)) (fibreOutput control0 u s a z vw)
        ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) from
      integral_map_of_stronglyMeasurable hout (measurable_const.indicator hB).stronglyMeasurable]
  simp only [originalSourceSection, htheta, smul_eq_mul, fibreOutput]

private theorem rank_partition (k : ℕ) (f : SourceInput p → ℝ) (z : SourceInput p) :
    f z = (ReferenceCollectionRankCellPhysicalTransport.rankNoCall
      rate rewards C_star C_h k).indicator f z +
      ∑ u : Fin p.T, ∑ s : Fin p.T,
        (ReferenceCollectionRankCellPhysicalTransport.rankCell
          rate rewards C_star C_h k u s).indicator f z := by
  cases hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none =>
      have hnone : z ∈ ReferenceCollectionRankCellPhysicalTransport.rankNoCall
          rate rewards C_star C_h k := hcall
      have hcell (u s : Fin p.T) : z ∉
          ReferenceCollectionRankCellPhysicalTransport.rankCell
            rate rewards C_star C_h k u s := by
        rw [ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_originalTags, hcall]
        simp only [Option.map_none, reduceCtorEq, not_false_eq_true]
      simp only [Set.indicator_of_mem hnone, Set.indicator_of_notMem (hcell _ _),
        Finset.sum_const_zero, add_zero]
  | some call =>
      have hnone : z ∉ ReferenceCollectionRankCellPhysicalTransport.rankNoCall
          rate rewards C_star C_h k := by
        change ¬ ReferenceCollectionSamplerChronology.nthCollectionCall
          rate rewards C_star C_h k z = none
        simp only [hcall, reduceCtorEq, not_false_eq_true]
      have hcell (u s : Fin p.T) : z ∈
          ReferenceCollectionRankCellPhysicalTransport.rankCell
            rate rewards C_star C_h k u s ↔ call.1 = u ∧ call.2.1 = s := by
        rw [ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_originalTags, hcall]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      simp only [Set.indicator_of_notMem hnone, zero_add]
      simp only [Set.indicator, hcell, ite_and,
        Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const_zero]

/-- The no-call part is an actual restriction of the original source law. -/
theorem kernelTest_noCall_integral (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z in ReferenceCollectionRankCellPhysicalTransport.rankNoCall
        rate rewards C_star C_h k,
      kernelTest rate rewards C_star C_h k control0 B z ∂sourceInputLaw p) =
      ∫ z in ReferenceCollectionRankCellPhysicalTransport.rankNoCall
          rate rewards C_star C_h k,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p := by
  apply setIntegral_congr_fun
    (ReferenceCollectionRankCellPhysicalTransport.rankNoCall_measurable
      rate rewards C_star C_h control0 k)
  intro z hz
  unfold kernelTest
  rw [rankResamplingKernel_apply_none rate rewards C_star C_h k control0 z hz]
  exact integral_dirac' _ _ (measurable_const.indicator hB).stronglyMeasurable

/-- The actual kernel has the complete own-date finite-cell test law. -/
theorem kernelTest_integral_partition (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z, kernelTest rate rewards C_star C_h k control0 B z ∂sourceInputLaw p) =
      (∫ z in ReferenceCollectionRankCellPhysicalTransport.rankNoCall
          rate rewards C_star C_h k,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p) +
      ∑ u : Fin p.T, ∑ s : Fin p.T, ∑ a : Outcome p,
        ∫ z in ReferenceCollectionRankCellPhysicalTransport.rankCell
            rate rewards C_star C_h k u s,
          originalSourceSection rate rewards C_star C_h control0 u s a B z
            ∂sourceInputLaw p := by
  let f := kernelTest rate rewards C_star C_h k control0 B
  let N := ReferenceCollectionRankCellPhysicalTransport.rankNoCall rate rewards C_star C_h k
  let E := ReferenceCollectionRankCellPhysicalTransport.rankCell rate rewards C_star C_h k
  have hN : MeasurableSet N :=
    ReferenceCollectionRankCellPhysicalTransport.rankNoCall_measurable
      rate rewards C_star C_h control0 k
  have hE (u s : Fin p.T) : MeasurableSet (E u s) :=
    ReferenceCollectionRankCellPhysicalTransport.rankCell_borel
      rate rewards C_star C_h control0 k u s
  have hf : Integrable f (sourceInputLaw p) :=
    kernelTest_integrable rate rewards C_star C_h k control0 B hB
  have hsum : Integrable (fun z => ∑ u : Fin p.T, ∑ s : Fin p.T,
      (E u s).indicator f z) (sourceInputLaw p) := by
    apply integrable_finsetSum
    intro u _
    apply integrable_finsetSum
    intro s _
    exact hf.indicator (hE u s)
  calc
    _ = ∫ z, N.indicator f z + (∑ u : Fin p.T, ∑ s : Fin p.T,
        (E u s).indicator f z) ∂sourceInputLaw p :=
      integral_congr_ae (Filter.Eventually.of_forall
        (rank_partition rate rewards C_star C_h k f))
    _ = (∫ z in N, f z ∂sourceInputLaw p) +
        ∑ u : Fin p.T, ∑ s : Fin p.T, ∫ z in E u s, f z ∂sourceInputLaw p := by
      rw [integral_add (hf.indicator hN) hsum, integral_indicator hN,
        integral_finsetSum Finset.univ (fun u _ => integrable_finsetSum Finset.univ
          (fun s _ => hf.indicator (hE u s)))]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      rw [integral_finsetSum Finset.univ (fun s _ => hf.indicator (hE u s))]
      apply Finset.sum_congr rfl
      intro s _
      exact integral_indicator (hE u s)
    _ = _ := by
      rw [kernelTest_noCall_integral rate rewards C_star C_h k control0 B hB]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro s _
      calc
        _ = ∫ z in E u s, (∑ a : Outcome p,
            originalSourceSection rate rewards C_star C_h control0 u s a B z)
            ∂sourceInputLaw p := by
          apply setIntegral_congr_fun (hE u s)
          intro z hz
          exact kernelTest_on_cell rate rewards C_star C_h k control0 u s B hB z hz
        _ = _ := integral_finsetSum Finset.univ fun a _ =>
          (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_integrable
            rate rewards C_star C_h control0 u s a B hB).integrableOn

/-- Every Borel test agrees with the actual marked output under the original
source law, with no source-stratum positivity or conditioning premise. -/
theorem integral_kernelTest_eq_originalTest (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z, kernelTest rate rewards C_star C_h k control0 B z ∂sourceInputLaw p) =
      ∫ z, B.indicator (fun _ => (1 : ℝ))
        (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput
          rate rewards C_star C_h k control0 z) ∂sourceInputLaw p := by
  rw [kernelTest_integral_partition rate rewards C_star C_h k control0 B hB,
    ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput_borel_test_law
      rate rewards C_star C_h k control0 B hB]

/-- Conversion of the real kernel test to the actual composed measure. -/
theorem integral_kernelTest_eq_bind_toReal (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z, kernelTest rate rewards C_star C_h k control0 B z ∂sourceInputLaw p) =
      (((sourceInputLaw p).bind
        (rankResamplingKernel rate rewards C_star C_h k control0)) B).toReal := by
  simp_rw [kernelTest_eq_toReal rate rewards C_star C_h k control0 B hB]
  rw [Measure.bind_apply hB
    (rankResamplingKernel rate rewards C_star C_h k control0).aemeasurable]
  exact integral_toReal
    ((rankResamplingKernel rate rewards C_star C_h k control0).measurable_coe hB).aemeasurable
    (Filter.Eventually.of_forall fun z => measure_lt_top _ B)

/-- The composed actual rank kernel has exactly the original joint law. -/
theorem bind_rankResamplingKernel_eq_map (k : ℕ) (control0 : TimeControl p) :
    (sourceInputLaw p).bind (rankResamplingKernel rate rewards C_star C_h k control0) =
      (sourceInputLaw p).map
        (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput
          rate rewards C_star C_h k control0) := by
  apply Measure.ext
  intro B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ B) (measure_ne_top _ B)).mp
  rw [← integral_kernelTest_eq_bind_toReal rate rewards C_star C_h k control0 B hB,
    integral_kernelTest_eq_originalTest rate rewards C_star C_h k control0 B hB]
  have hout := ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput_measurable
    rate rewards C_star C_h k control0
  rw [← show (∫ y, B.indicator (fun _ => (1 : ℝ)) y
        ∂(sourceInputLaw p).map
          (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput
            rate rewards C_star C_h k control0)) =
      (((sourceInputLaw p).map
        (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput
          rate rewards C_star C_h k control0)) B).toReal from integral_indicator_one hB]
  exact (integral_map_of_stronglyMeasurable hout
    (measurable_const.indicator hB).stronglyMeasurable).symm

/-- Equivalent extended-integral formulation on every Borel joint set. -/
theorem lintegral_rankResamplingKernel_apply (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫⁻ z, rankResamplingKernel rate rewards C_star C_h k control0 z B ∂sourceInputLaw p) =
      (sourceInputLaw p).map
        (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput
          rate rewards C_star C_h k control0) B := by
  rw [← Measure.bind_apply hB
    (rankResamplingKernel rate rewards C_star C_h k control0).aemeasurable,
    bind_rankResamplingKernel_eq_map rate rewards C_star C_h k control0]

/-- In particular, the complete new source has exactly its original law. -/
theorem bind_rankResamplingKernel_first_marginal (k : ℕ) (control0 : TimeControl p) :
    ((sourceInputLaw p).bind
      (rankResamplingKernel rate rewards C_star C_h k control0)).map Prod.fst =
      sourceInputLaw p := by
  rw [bind_rankResamplingKernel_eq_map rate rewards C_star C_h k control0,
    Measure.map_map measurable_fst
      (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput_measurable
        rate rewards C_star C_h k control0)]
  exact Measure.map_id

end Bandits.Support.ReferenceCollectionRankResamplingKernel

end
