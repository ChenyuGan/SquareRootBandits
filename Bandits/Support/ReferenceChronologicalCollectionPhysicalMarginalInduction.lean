/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionRankResamplingKernel

/-!
# Finite adaptive transport of the complete original physical source

The step reads the actual rank on the current source, resamples with the
accepted rank kernel, and appends its optional mark to an analytical list.
The law is defined by finite measure bind recursion. Its joint graph law is
proved from the actual kernel's graph, preservation of earlier marks, and
original-source transport. No future invocation list is held fixed.

An absent invocation appends nothing. A present checked failure retains its
genuine payload, strict source prefix, dates, and complete assignment vector.
All measures are the original unnormalized measures, without conditioning on
positive cells. This is physical-source transport only, for a later actual
physical/logical assignment coupling; it asserts no logical assignment law.

Sources: `06_interruptions.tex:391-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceChronologicalCollectionPhysicalMarginalInduction

open ContinuousLearningRows (TimeControl)
open BootstrapPrivateRoundStreams (sourceInputLaw)
open ReferenceFirstCollectionOriginalSourceFibreTransport (SourceInput JointY Outcome)
open ReferenceCollectionRankResamplingKernel
  (rankResamplingKernel rankResamplingKernel_apply_of_length_le markedPrefix
    markedPrefix_measurable ae_rankResamplingKernel_graph
    ae_rankResamplingKernel_markedPrefix bind_rankResamplingKernel_eq_map)

/-- Exactly the mark used by the accepted rank kernel and its marked prefix. -/
abbrev Mark (p : ConstructorDimensions.Parameters) :=
  Fin p.T × (Fin p.T × ReferenceFirstCollectionPastSamplerFibreLaw.MarkedPayload p)

/-- The entire original source together with its analytical accumulated marks. -/
abbrev AccumulatedSource (p : ConstructorDimensions.Parameters) :=
  SourceInput p × List (Mark p)

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

private theorem measurable_list_append_singleton {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A]
    (l : X → List A) (hl : Measurable l) (a : X → A) (ha : Measurable a) :
    Measurable (fun x => l x ++ [a x]) := by
  apply measurable_comap_iff.mpr
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hl
  have hlen : Measurable (fun x => (l x).length) := measurable_fst.comp hc
  apply Measurable.prodMk
  · change Measurable (fun x => (l x ++ [a x]).length)
    simp only [List.length_append, List.length_singleton]
    exact (measurable_of_countable (fun n : ℕ => n + 1)).comp hlen
  · apply measurable_pi_iff.mpr
    intro n
    have htag : Measurable (fun x =>
        ReferenceActiveHorizonMeasurability.listObservationAt (l x) n) :=
      (measurable_pi_apply n).comp (measurable_snd.comp hc)
    have hformula : (fun x =>
        ReferenceActiveHorizonMeasurability.listObservationAt (l x ++ [a x]) n) =
        fun x => if n < (l x).length then
          ReferenceActiveHorizonMeasurability.listObservationAt (l x) n
        else if n = (l x).length then Sum.inr (a x) else Sum.inl () := by
      funext x
      by_cases hn : n < (l x).length
      · simp only [hn, ↓reduceIte, ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_append_left hn]
      · have hnle : (l x).length ≤ n := Nat.le_of_not_lt hn
        simp only [hn, ↓reduceIte, ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_append_right hnle]
        by_cases heq : n = (l x).length
        · simp only [heq, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero]
        · have hsub : 1 ≤ n - (l x).length := by omega
          rw [List.getElem?_eq_none_iff.mpr (by simpa only [List.length_singleton] using hsub)]
          simp only [heq, ↓reduceIte]
    rw [hformula]
    exact htag.ite (measurableSet_lt measurable_const hlen)
      ((measurable_inr.comp ha).ite (measurableSet_eq_fun measurable_const hlen)
        measurable_const)

variable {p : ConstructorDimensions.Parameters}

/-- Append precisely a present invocation mark; absence retains the list. -/
def appendMark (marks : List (Mark p)) (y : JointY p) : AccumulatedSource p :=
  (y.1, y.2.elim marks (fun a => marks ++ [a]))

/-- Borelness retains the existing continuous product, option, and list spaces. -/
theorem appendMark_measurable :
    Measurable (fun q : List (Mark p) × JointY p => appendMark q.1 q.2) := by
  apply Measurable.prodMk measurable_snd.fst
  exact measurable_optionElimWith _ measurable_snd.snd
    (fun q : Mark p × (List (Mark p) × JointY p) => q.2.1 ++ [q.1])
    (measurable_list_append_singleton _ measurable_snd.fst _ measurable_fst)
    _ measurable_fst

theorem measurable_appendMark (marks : List (Mark p)) : Measurable (appendMark marks) :=
  appendMark_measurable.comp (measurable_const.prodMk measurable_id)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual accumulated-mark step, recomputing rank `k` on `x.1`. -/
def stepKernel (k : ℕ) (control0 : TimeControl p) :
    ProbabilityTheory.Kernel (AccumulatedSource p) (AccumulatedSource p) where
  toFun x := (rankResamplingKernel rate rewards C_star C_h k control0 x.1).map
    (appendMark x.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    let κ : ProbabilityTheory.Kernel (AccumulatedSource p) (JointY p) :=
      (rankResamplingKernel rate rewards C_star C_h k control0).comap
      (Prod.fst : AccumulatedSource p → SourceInput p) measurable_fst
    have hmap : Measurable (fun q : AccumulatedSource p × JointY p =>
        appendMark q.1.2 q.2) :=
      appendMark_measurable.comp (measurable_fst.snd.prodMk measurable_snd)
    have h := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) (hmap hB)
    convert h using 1
    funext x
    rw [Measure.map_apply (measurable_appendMark x.2) hB]
    rfl

theorem stepKernel_apply (k : ℕ) (control0 : TimeControl p) (x : AccumulatedSource p) :
    stepKernel rate rewards C_star C_h k control0 x =
      (rankResamplingKernel rate rewards C_star C_h k control0 x.1).map
        (fun y => (y.1, y.2.elim x.2 (fun a => x.2 ++ [a]))) := rfl

theorem stepKernel_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (fun x : AccumulatedSource p =>
      stepKernel rate rewards C_star C_h k control0 x) :=
  (stepKernel rate rewards C_star C_h k control0).measurable

instance instIsMarkovKernelStepKernel (k : ℕ) (control0 : TimeControl p) :
    ProbabilityTheory.IsMarkovKernel (stepKernel rate rewards C_star C_h k control0) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure
      ((rankResamplingKernel rate rewards C_star C_h k control0 x.1).map (appendMark x.2))
    exact (Measure.isProbabilityMeasure_map_iff (measurable_appendMark x.2).aemeasurable).mpr
      inferInstance

/-- Beyond the actual current call list the full accumulated state is unchanged. -/
theorem stepKernel_apply_of_length_le (k : ℕ) (control0 : TimeControl p)
    (x : AccumulatedSource p)
    (hk : (ReferenceCollectionSamplerChronology.collectionCalls
      rate rewards C_star C_h x.1).length ≤ k) :
    stepKernel rate rewards C_star C_h k control0 x = Measure.dirac x := by
  change (rankResamplingKernel rate rewards C_star C_h k control0 x.1).map
    (appendMark x.2) = _
  rw [rankResamplingKernel_apply_of_length_le rate rewards C_star C_h k control0 x.1 hk,
    Measure.map_dirac' (measurable_appendMark x.2)]
  rfl

/-- The literal first-`k` analytical observation of its own complete source. -/
def accumulatedOutput (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) : AccumulatedSource p :=
  (z, markedPrefix rate rewards C_star C_h k control0 z)

theorem accumulatedOutput_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (accumulatedOutput rate rewards C_star C_h k control0) :=
  measurable_id.prodMk (markedPrefix_measurable rate rewards C_star C_h k control0)

/-- Literal take-successor identity, distinguishing no invocation from failed sampling. -/
theorem markedPrefix_succ (k : ℕ) (control0 : TimeControl p) (z : SourceInput p) :
    markedPrefix rate rewards C_star C_h (k + 1) control0 z =
      (ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput
        rate rewards C_star C_h k control0 z).elim
          (markedPrefix rate rewards C_star C_h k control0 z)
          (fun a => markedPrefix rate rewards C_star C_h k control0 z ++ [a]) := by
  unfold markedPrefix ReferenceCollectionRankCellPhysicalTransport.rankPastFibreOutput
    ReferenceCollectionSamplerChronology.nthCollectionCall
  rw [List.take_add_one, List.map_append]
  cases (ReferenceCollectionSamplerChronology.collectionCalls
    rate rewards C_star C_h z)[k]? <;> simp only [Option.toList, Option.map_none,
      Option.map_some, Option.elim_none, Option.elim_some, List.map_nil, List.map_cons,
      List.append_nil]

/-- Both accepted support laws give the next joint graph on each original source. -/
theorem ae_rank_step_accumulatedOutput (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) :
    ∀ᵐ y ∂rankResamplingKernel rate rewards C_star C_h k control0 z,
      appendMark (markedPrefix rate rewards C_star C_h k control0 z) y =
        accumulatedOutput rate rewards C_star C_h (k + 1) control0 y.1 := by
  filter_upwards [ae_rankResamplingKernel_graph rate rewards C_star C_h k control0 z,
    ae_rankResamplingKernel_markedPrefix rate rewards C_star C_h k control0 z]
    with y hgraph hprefix
  apply Prod.ext
  · rfl
  change y.2.elim (markedPrefix rate rewards C_star C_h k control0 z)
    (fun a => markedPrefix rate rewards C_star C_h k control0 z ++ [a]) =
      markedPrefix rate rewards C_star C_h (k + 1) control0 y.1
  rw [hgraph, ← hprefix, markedPrefix_succ]

/-- The actual accumulated step on a graph state, derived rather than assumed. -/
theorem stepKernel_accumulatedOutput (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) :
    stepKernel rate rewards C_star C_h k control0
        (accumulatedOutput rate rewards C_star C_h k control0 z) =
      (rankResamplingKernel rate rewards C_star C_h k control0 z).map
        (fun y => accumulatedOutput rate rewards C_star C_h (k + 1) control0 y.1) := by
  exact Measure.map_congr (ae_rank_step_accumulatedOutput rate rewards C_star C_h k control0 z)

/-- Finite adaptive iteration, defined by the actual step and measure bind. -/
def eta (control0 : TimeControl p) : ℕ → Measure (AccumulatedSource p)
  | 0 => (sourceInputLaw p).map (fun z => (z, ([] : List (Mark p))))
  | k + 1 => (eta control0 k).bind (stepKernel rate rewards C_star C_h k control0)

theorem eta_zero (control0 : TimeControl p) :
    eta rate rewards C_star C_h control0 0 =
      (sourceInputLaw p).map (fun z => (z, ([] : List (Mark p)))) := rfl

theorem eta_succ (k : ℕ) (control0 : TimeControl p) :
    eta rate rewards C_star C_h control0 (k + 1) =
      (eta rate rewards C_star C_h control0 k).bind
        (stepKernel rate rewards C_star C_h k control0) := rfl

/-- One coherent original-source joint law for every finite number of steps. -/
theorem eta_eq_map (k : ℕ) (control0 : TimeControl p) :
    eta rate rewards C_star C_h control0 k =
      (sourceInputLaw p).map (accumulatedOutput rate rewards C_star C_h k control0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [eta_succ, ih, Measure.bind_map
        (accumulatedOutput_measurable rate rewards C_star C_h k control0).aemeasurable
        (stepKernel rate rewards C_star C_h k control0).aemeasurable]
      calc
        _ = (sourceInputLaw p).bind (fun z =>
            (rankResamplingKernel rate rewards C_star C_h k control0 z).map
              (fun y => accumulatedOutput rate rewards C_star C_h (k + 1) control0 y.1)) :=
          Measure.bind_congr_right (Filter.Eventually.of_forall
            (stepKernel_accumulatedOutput rate rewards C_star C_h k control0))
        _ = ((sourceInputLaw p).bind
            (rankResamplingKernel rate rewards C_star C_h k control0)).map
              (fun y => accumulatedOutput rate rewards C_star C_h (k + 1) control0 y.1) :=
          (Measure.map_bind
            (rankResamplingKernel rate rewards C_star C_h k control0).aemeasurable
            ((accumulatedOutput_measurable rate rewards C_star C_h (k + 1) control0).comp
              measurable_fst).aemeasurable).symm
        _ = _ := by
          have hm : Measurable (fun y : JointY p =>
              accumulatedOutput rate rewards C_star C_h (k + 1) control0 y.1) :=
            (accumulatedOutput_measurable rate rewards C_star C_h (k + 1) control0).comp
              measurable_fst
          rw [bind_rankResamplingKernel_eq_map rate rewards C_star C_h k control0,
            Measure.map_map hm
              (ReferenceCollectionRankCellPhysicalTransport.rankOriginalSourceOutput_measurable
                rate rewards C_star C_h k control0)]
          rfl

instance instIsProbabilityMeasureEta (k : ℕ) (control0 : TimeControl p) :
    IsProbabilityMeasure (eta rate rewards C_star C_h control0 k) := by
  rw [eta_eq_map]
  exact (Measure.isProbabilityMeasure_map_iff
    (accumulatedOutput_measurable rate rewards C_star C_h k control0).aemeasurable).mpr
      inferInstance

/-- The first marginal is the full original physical source, including private arrays. -/
theorem eta_first_marginal (k : ℕ) (control0 : TimeControl p) :
    (eta rate rewards C_star C_h control0 k).map Prod.fst = sourceInputLaw p := by
  rw [eta_eq_map, Measure.map_map measurable_fst
    (accumulatedOutput_measurable rate rewards C_star C_h k control0)]
  exact Measure.map_id

/-- The accumulated graph is Borel in the genuine source/list product. -/
theorem accumulatedGraph_measurableSet (k : ℕ) (control0 : TimeControl p) :
    MeasurableSet {x : AccumulatedSource p |
      x.2 = markedPrefix rate rewards C_star C_h k control0 x.1} :=
  measurableSet_eq_fun measurable_snd
    ((markedPrefix_measurable rate rewards C_star C_h k control0).comp measurable_fst)

/-- Almost every accumulated list is exactly the recomputed prefix of its own source. -/
theorem ae_eta_markedPrefix (k : ℕ) (control0 : TimeControl p) :
    ∀ᵐ x ∂eta rate rewards C_star C_h control0 k,
      x.2 = markedPrefix rate rewards C_star C_h k control0 x.1 := by
  rw [eta_eq_map]
  apply (ae_map_iff
    (accumulatedOutput_measurable rate rewards C_star C_h k control0).aemeasurable
    (accumulatedGraph_measurableSet rate rewards C_star C_h k control0)).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Equivalent joint law on every Borel set, without a normalized source cell. -/
theorem eta_apply (k : ℕ) (control0 : TimeControl p)
    (B : Set (AccumulatedSource p)) (hB : MeasurableSet B) :
    eta rate rewards C_star C_h control0 k B =
      sourceInputLaw p {z | (z, markedPrefix rate rewards C_star C_h k control0 z) ∈ B} := by
  rw [eta_eq_map, Measure.map_apply
    (accumulatedOutput_measurable rate rewards C_star C_h k control0) hB]
  rfl

/-- All nonnegative Borel tests have the same original-source joint law. -/
theorem lintegral_eta (k : ℕ) (control0 : TimeControl p)
    (f : AccumulatedSource p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂eta rate rewards C_star C_h control0 k) =
      ∫⁻ z, f (z, markedPrefix rate rewards C_star C_h k control0 z) ∂sourceInputLaw p := by
  rw [eta_eq_map]
  exact lintegral_map hf
    (accumulatedOutput_measurable rate rewards C_star C_h k control0)

end Bandits.Support.ReferenceChronologicalCollectionPhysicalMarginalInduction

end
