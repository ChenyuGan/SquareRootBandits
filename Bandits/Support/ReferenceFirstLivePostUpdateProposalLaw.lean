/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

/-!
# First-live pre-proposal observations

Separate only the original current `prop` scalar from the actual recorder,
reserved fast draw and all-arm numerical update. Original-source cylinders
retain every other scalar, every affine sample and the whole source remainder.
No logical prefix construction or manuscript closure is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

open ConstructorDimensions ContinuousControlSlice ContinuousLearningRows

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Label (p : Parameters) := ContinuousControlSlice.Label p.m p.K
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Slice (p : Parameters) := ContinuousControlSlice.Slice p.m p.K
abbrev AffineSamples (p : Parameters) := ContinuousLearningRows.AffineSamples p

def propLabel (p : Parameters) : Label p := ContinuousControlSlice.Label.prop

abbrev PropRestLabel (p : Parameters) := {c : Label p // c ≠ propLabel p}
abbrev PropRestSlice (p : Parameters) := PropRestLabel p → Scalar
abbrev PropRestControl (p : Parameters) := PropRestSlice p × AffineSamples p

private instance propSingleton (p : Parameters) :
    Unique {c : Label p // c = propLabel p} :=
  ⟨⟨propLabel p, rfl⟩, fun c => Subtype.ext c.property⟩

/-- Reindex the full scalar slice so that only its literal `prop` label is
exposed as the first coordinate. -/
def proposalSliceSplit (p : Parameters) :
    Slice p ≃ᵐ Scalar × PropRestSlice p := by
  let pred : Label p → Prop := fun c => c = propLabel p
  exact (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Label p => Scalar) pred).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piUnique
        (fun _ : {c : Label p // c = propLabel p} => Scalar))
      (MeasurableEquiv.refl _))

private theorem proposalSliceSplit_measurePreserving (p : Parameters) :
    MeasurePreserving (proposalSliceSplit p)
      (ContinuousControlSlice.sliceLaw p.m p.K)
      (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : PropRestLabel p => ContinuousControlSlice.scalarLaw))) := by
  classical
  let pred : Label p → Prop := fun c => c = propLabel p
  let _ : Fintype {c : Label p // c = propLabel p} := Subtype.fintype pred
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Label p => ContinuousControlSlice.scalarLaw) pred
  have hcollapse := measurePreserving_piUnique
    (fun _ : {c : Label p // c = propLabel p} => ContinuousControlSlice.scalarLaw)
  exact (hcollapse.prod (MeasurePreserving.id (Measure.pi
    (fun _ : PropRestLabel p => ContinuousControlSlice.scalarLaw)))).comp hsplit

/-- Split the original current control at `prop`, retaining all other scalars
and the complete affine-sample family in the residual coordinate. -/
def proposalControlSplit (p : Parameters) :
    TimeControl p ≃ᵐ Scalar × PropRestControl p :=
  (MeasurableEquiv.prodCongr (proposalSliceSplit p) (MeasurableEquiv.refl _)).trans
    MeasurableEquiv.prodAssoc

def proposalRestControlLaw (p : Parameters) : Measure (PropRestControl p) :=
  (Measure.pi (fun _ : PropRestLabel p => ContinuousControlSlice.scalarLaw)).prod
    (ContinuousLearningRows.affineSamplesLaw p)

instance proposalRestControlLaw_probability (p : Parameters) :
    IsProbabilityMeasure (proposalRestControlLaw p) := by
  unfold proposalRestControlLaw
  infer_instance

private theorem proposalControlSplit_measurePreserving (p : Parameters) :
    MeasurePreserving (proposalControlSplit p)
      (ContinuousLearningRows.timeControlLaw p)
      (ContinuousControlSlice.scalarLaw.prod (proposalRestControlLaw p)) := by
  have hpair := (proposalSliceSplit_measurePreserving p).prod
    (MeasurePreserving.id (ContinuousLearningRows.affineSamplesLaw p))
  exact (measurePreserving_prodAssoc ContinuousControlSlice.scalarLaw
    (Measure.pi (fun _ : PropRestLabel p => ContinuousControlSlice.scalarLaw))
    (ContinuousLearningRows.affineSamplesLaw p)).comp hpair

/-- Replace only the current physical proposal scalar. All other labels and
the entire affine-sample family are unchanged. -/
def replaceProposalScalar (p : Parameters) (u : TimeControl p) (a : Scalar) :
    TimeControl p := (Function.update u.1 (propLabel p) a, u.2)

theorem replaceProposalScalar_prop (p : Parameters) (u : TimeControl p) (a : Scalar) :
    (replaceProposalScalar p u a).1 (propLabel p) = a := by
  simp [replaceProposalScalar]

theorem replaceProposalScalar_other (p : Parameters) (u : TimeControl p) (a : Scalar)
    (c : Label p) (hc : c ≠ propLabel p) :
    (replaceProposalScalar p u a).1 c = u.1 c := by
  simp [replaceProposalScalar, hc]

theorem proposalControlSplit_symm_prop (p : Parameters) (a : Scalar)
    (r : PropRestControl p) :
    ((proposalControlSplit p).symm (a, r)).1 (propLabel p) = a := by
  change (if h : propLabel p = propLabel p then a else r.1 ⟨propLabel p, h⟩) = a
  simp only [↓reduceDIte]

theorem proposalControlSplit_prop (p : Parameters) (u : TimeControl p) :
    (proposalControlSplit p u).1 = u.1 (propLabel p) := by
  rfl

theorem proposalControlSplit_symm_other (p : Parameters) (a b : Scalar)
    (r : PropRestControl p) (c : Label p) (hc : c ≠ propLabel p) :
    ((proposalControlSplit p).symm (a, r)).1 c =
      ((proposalControlSplit p).symm (b, r)).1 c := by
  change (if h : c = propLabel p then a else r.1 ⟨c, h⟩) =
    (if h : c = propLabel p then b else r.1 ⟨c, h⟩)
  simp only [hc, ↓reduceDIte]

theorem proposalControlSplit_symm_replace (p : Parameters) (a b : Scalar)
    (r : PropRestControl p) :
    (proposalControlSplit p).symm (a, r) =
      replaceProposalScalar p ((proposalControlSplit p).symm (b, r)) a := by
  apply Prod.ext
  · funext c
    by_cases hc : c = propLabel p
    · subst c
      rw [proposalControlSplit_symm_prop, replaceProposalScalar_prop]
    · rw [proposalControlSplit_symm_other p a b r c hc,
        replaceProposalScalar_other p _ a c hc]
  · rfl

/-- The original physical proposal bit at the current control. Its threshold
is strictly `4*m*eta`, matching the coordinator's successful live finish. -/
def physicalProposalBit {p : Parameters} (rate : RateInput p) (u : TimeControl p) : Bool :=
  FollowerCutoffScan.thresholdProposalBit (u.1 (propLabel p))
    (FollowerCutoffScan.proposalHazard p rate.eta.val)

private theorem measurable_thresholdProposalBit (h : ℝ) :
    Measurable (fun a : Scalar => FollowerCutoffScan.thresholdProposalBit a h) := by
  have hs : MeasurableSet {a : Scalar | a.val < h} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro b
  cases b
  · have heq : {a : Scalar | FollowerCutoffScan.thresholdProposalBit a h = false} =
        {a | a.val < h}ᶜ := by
      ext a
      simp [FollowerCutoffScan.thresholdProposalBit]
    rw [heq]
    exact hs.compl
  · have heq : {a : Scalar | FollowerCutoffScan.thresholdProposalBit a h = true} =
        {a | a.val < h} := by
      ext a
      simp [FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq]
    rw [heq]
    exact hs

theorem measurable_physicalProposalBit {p : Parameters} (rate : RateInput p) :
    Measurable (physicalProposalBit rate) :=
  (measurable_thresholdProposalBit
    (FollowerCutoffScan.proposalHazard p rate.eta.val)).comp
    ((measurable_pi_apply (propLabel p)).comp measurable_fst)

/-- The Bernoulli law induced by the literal current `prop` coordinate. -/
def proposalBitLaw {p : Parameters} (rate : RateInput p) : Measure Bool :=
  ContinuousControlSlice.scalarLaw.map
    (fun a => FollowerCutoffScan.thresholdProposalBit a
      (FollowerCutoffScan.proposalHazard p rate.eta.val))

instance proposalBitLaw_probability {p : Parameters} (rate : RateInput p) :
    IsProbabilityMeasure (proposalBitLaw rate) := by
  unfold proposalBitLaw
  infer_instance

/-- The source cap gives the proposal threshold `0 < h ≤ 1/4`. -/
theorem physicalProposalThreshold_bounds {p : Parameters} (rate : RateInput p) :
    0 < FollowerCutoffScan.proposalHazard p rate.eta.val ∧
      FollowerCutoffScan.proposalHazard p rate.eta.val ≤ 1 / 4 := by
  constructor
  · rw [FollowerCutoffScan.proposalHazard]
    have hm : 0 < p.m := lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hm)) rate.eta.property
  · simpa [FollowerCutoffScan.proposalHazard, RecordedSlowRefresh.hazard,
      ReferenceFirstLaunchNumericalCell.queueParameters] using
      (RecordedSlowRefresh.hazard_le_quarter p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) rate.sourceCap)

private def proposalIndicator {p : Parameters} (rate : RateInput p) (a : Scalar) : ℝ :=
  if FollowerCutoffScan.thresholdProposalBit a
      (FollowerCutoffScan.proposalHazard p rate.eta.val) = true then 1 else 0

/-- The exact mass of the strict proposal interval under the original scalar
coordinate law. -/
theorem proposalThreshold_mass {p : Parameters} (rate : RateInput p) :
    ContinuousControlSlice.scalarLaw
      {a : Scalar | a.val < FollowerCutoffScan.proposalHazard p rate.eta.val} =
    ENNReal.ofReal (FollowerCutoffScan.proposalHazard p rate.eta.val) := by
  let h := FollowerCutoffScan.proposalHazard p rate.eta.val
  have hh := physicalProposalThreshold_bounds rate
  have himage : Subtype.val '' {a : Scalar | a.val < h} = Set.Ico 0 h := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property.1, ha⟩
    · rintro ⟨hy0, hyh⟩
      refine ⟨⟨y, ⟨hy0, lt_of_lt_of_le hyh (by linarith [hh.2])⟩⟩, ?_, rfl⟩
      simpa [h, FollowerCutoffScan.proposalHazard,
        FollowerCutoffScan.thresholdProposalBit] using hyh
  rw [ContinuousControlSlice.scalarLaw_apply, himage, Real.volume_Ico]
  simp [h]

/-- The true atom has probability exactly the clipped-source proposal hazard. -/
theorem proposalBitLaw_true {p : Parameters} (rate : RateInput p) :
    proposalBitLaw rate {true} =
      ENNReal.ofReal (FollowerCutoffScan.proposalHazard p rate.eta.val) := by
  rw [proposalBitLaw, Measure.map_apply
    (measurable_thresholdProposalBit (FollowerCutoffScan.proposalHazard p rate.eta.val))
    (measurableSet_singleton true)]
  change ContinuousControlSlice.scalarLaw
      {a : Scalar | FollowerCutoffScan.thresholdProposalBit a
        (FollowerCutoffScan.proposalHazard p rate.eta.val) = true} = _
  have hpre : {a : Scalar |
      FollowerCutoffScan.thresholdProposalBit a
        (FollowerCutoffScan.proposalHazard p rate.eta.val) = true} =
      {a : Scalar | a.val < FollowerCutoffScan.proposalHazard p rate.eta.val} := by
    ext a
    simp [FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq]
  rw [hpre, proposalThreshold_mass]

/-- The literal original-row proposal bit is the bit saved by a successful
live Finish when the row's current `prop` coordinate agrees with `u.prop`. -/
theorem completeRowProposalBit_eq_physicalProposalBit {p : Parameters}
    (rate : RateInput p) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (u : TimeControl p)
    (hprop : (CompletePublicTable.completeRowLearning p row t).1 (propLabel p) =
      u.1 (propLabel p)) :
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t =
      physicalProposalBit rate u := by
  exact congrArg (fun a : Scalar => FollowerCutoffScan.thresholdProposalBit a
    (FollowerCutoffScan.proposalHazard p rate.eta.val)) hprop

/-- Keep the actual operational success conditions and identify the saved
proposal value exactly; this local live-branch case does not define a READ. -/
theorem liveFinish_savedProposal_is_physicalProposalBit {p : Parameters}
    (rate : RateInput p) (t : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (row : CompletePublicTable.CompleteRow p)
    (u : TimeControl p)
    (hprop : (CompletePublicTable.completeRowLearning p row t).1 (propLabel p) =
      u.1 (propLabel p))
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock)
    (htime : CoordinatorPhaseClock.finishRoundTimeValid t clock)
    (hσ : clock.sigma ≠ none) (hu : clock.u = none)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val) :
    ∃ result,
      CoordinatorPhaseClock.finishRound p rate.eta.val t clock pending row = .ok result ∧
        result.clock = ({ clock with
          lastProposal := some (t, physicalProposalBit rate u) }) ∧
        result.pending = pending ∧ result.ledgerCommand = none := by
  obtain ⟨result, hfinish, hresultClock, hpending, hledger⟩ :=
    CoordinatorPhaseClock.finishRound_live_savedProposal p rate.eta.val t clock pending row
      hclock htime hσ hu hparam
  refine ⟨result, hfinish, ?_, hpending, hledger⟩
  rw [← completeRowProposalBit_eq_physicalProposalBit rate row t u hprop]
  exact hresultClock

private theorem proposalIndicator_integral {p : Parameters} (rate : RateInput p) :
    ∫ a : Scalar, proposalIndicator rate a ∂ContinuousControlSlice.scalarLaw =
      FollowerCutoffScan.proposalHazard p rate.eta.val := by
  let h := FollowerCutoffScan.proposalHazard p rate.eta.val
  have hh := physicalProposalThreshold_bounds rate
  have hset : MeasurableSet {a : Scalar | a.val < h} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hindicator : (fun a : Scalar => proposalIndicator rate a) =
      {a : Scalar | a.val < h}.indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases ha : a.val < h
    · simp [proposalIndicator, h, FollowerCutoffScan.thresholdProposalBit, ha]
    · simp [proposalIndicator, h, FollowerCutoffScan.thresholdProposalBit, ha]
  calc
    (∫ a : Scalar, proposalIndicator rate a ∂ContinuousControlSlice.scalarLaw) =
        (ContinuousControlSlice.scalarLaw).real {a : Scalar | a.val < h} := by
      rw [hindicator]
      rw [integral_indicator_const (1 : ℝ) hset]
      simp
    _ = h := by
      rw [measureReal_def, proposalThreshold_mass]
      simp [h, le_of_lt hh.1]

private def proposalSourceSplitEquiv {p : Parameters} {α : Type*} [MeasurableSpace α] :
    (α × TimeControl p) ≃ᵐ ((α × PropRestControl p) × Scalar) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) (proposalControlSplit p)).trans
    (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _)).trans
        (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm)))

private theorem proposalSourceSplitEquiv_fst {p : Parameters} {α : Type*}
    [MeasurableSpace α] (z : α × TimeControl p) :
    (proposalSourceSplitEquiv (p := p) (α := α) z).1 =
      (z.1, (proposalControlSplit p z.2).2) := by
  rfl

private theorem proposalSourceSplitEquiv_snd {p : Parameters} {α : Type*}
    [MeasurableSpace α] (z : α × TimeControl p) :
    (proposalSourceSplitEquiv (p := p) (α := α) z).2 =
      (proposalControlSplit p z.2).1 := by
  rfl

private theorem proposalSourceSplit_measurePreserving {p : Parameters}
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    MeasurePreserving (proposalSourceSplitEquiv (p := p) (α := α))
      (μ.prod (ContinuousLearningRows.timeControlLaw p))
      ((μ.prod (proposalRestControlLaw p)).prod ContinuousControlSlice.scalarLaw) := by
  let ν := proposalRestControlLaw p
  have hfirst := (MeasurePreserving.id μ).prod (proposalControlSplit_measurePreserving p)
  have hassoc := measurePreserving_prodAssoc μ ContinuousControlSlice.scalarLaw ν
  have hswap := (Measure.measurePreserving_swap
      (μ := μ) (ν := ContinuousControlSlice.scalarLaw)).prod
    (MeasurePreserving.id ν)
  have hassoc' := measurePreserving_prodAssoc ContinuousControlSlice.scalarLaw μ ν
  have hswap' := Measure.measurePreserving_swap
    (μ := ContinuousControlSlice.scalarLaw) (ν := μ.prod ν)
  have hcomp := hswap'.comp (hassoc'.comp (hswap.comp (hassoc.symm.comp hfirst)))
  have hfun :
      ((fun z : α × (Scalar × PropRestControl p) =>
        (((z.1, z.2.2), z.2.1))) ∘
        (fun z : α × TimeControl p => (z.1, proposalControlSplit p z.2))) =
      (proposalSourceSplitEquiv (p := p) (α := α) :
        α × TimeControl p → (α × PropRestControl p) × Scalar) := by
    funext z
    rfl
  exact hcomp.congr (proposalSourceSplitEquiv (p := p) (α := α)).measurable
    (Filter.Eventually.of_forall fun z => congrFun hfun z)

/-- The original source paired with any Borel retained observable has the
pushforward law of that observable times the independent physical proposal
bit. The observable may include the actual dependent recorder/fast pair and
the computed update fields, provided those literal fields depend only on the
retained source and non-proposal control. -/
theorem proposalSplit_joint_pushforward {p : Parameters} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (g : α × PropRestControl p → β) (hg : Measurable g)
    (rate : RateInput p) :
    (μ.prod (ContinuousLearningRows.timeControlLaw p)).map
      (fun z : α × TimeControl p =>
        (g (z.1, (proposalControlSplit p z.2).2), physicalProposalBit rate z.2)) =
      ((μ.prod (proposalRestControlLaw p)).map g).prod (proposalBitLaw rate) := by
  let bit : Scalar → Bool := fun a =>
    FollowerCutoffScan.thresholdProposalBit a
      (FollowerCutoffScan.proposalHazard p rate.eta.val)
  let splitObservation : ((α × PropRestControl p) × Scalar) → β × Bool :=
    fun y => (g y.1, bit y.2)
  have hbit : Measurable bit :=
    measurable_thresholdProposalBit
      (FollowerCutoffScan.proposalHazard p rate.eta.val)
  have hsplitObservation : Measurable splitObservation :=
    (hg.comp measurable_fst).prodMk (hbit.comp measurable_snd)
  have hsplit := proposalSourceSplit_measurePreserving (p := p) (α := α) μ
  have hpoint :
      (fun z : α × TimeControl p =>
        (g (z.1, (proposalControlSplit p z.2).2), physicalProposalBit rate z.2)) =
      splitObservation ∘ proposalSourceSplitEquiv (p := p) (α := α) := by
    funext z
    simp [splitObservation, bit, physicalProposalBit,
      proposalSourceSplitEquiv_fst, proposalSourceSplitEquiv_snd,
      proposalControlSplit_prop]
  calc
    (μ.prod (ContinuousLearningRows.timeControlLaw p)).map
        (fun z : α × TimeControl p =>
          (g (z.1, (proposalControlSplit p z.2).2), physicalProposalBit rate z.2)) =
        (μ.prod (ContinuousLearningRows.timeControlLaw p)).map
          (splitObservation ∘ proposalSourceSplitEquiv (p := p) (α := α)) := by
            rw [hpoint]
    _ = ((μ.prod (ContinuousLearningRows.timeControlLaw p)).map
        (proposalSourceSplitEquiv (p := p) (α := α))).map splitObservation := by
          rw [← Measure.map_map hsplitObservation
            (proposalSourceSplitEquiv (p := p) (α := α)).measurable]
    _ = ((μ.prod (proposalRestControlLaw p)).prod
        ContinuousControlSlice.scalarLaw).map splitObservation := by
          rw [hsplit.map_eq]
    _ = ((μ.prod (proposalRestControlLaw p)).map g).prod
        (proposalBitLaw rate) := by
          change ((μ.prod (proposalRestControlLaw p)).prod
            ContinuousControlSlice.scalarLaw).map
              (Prod.map g bit) =
            ((μ.prod (proposalRestControlLaw p)).map g).prod
              (ContinuousControlSlice.scalarLaw.map bit)
          exact (Measure.map_prod_map (μ.prod (proposalRestControlLaw p))
            ContinuousControlSlice.scalarLaw (f := g) (g := bit) hg hbit).symm

private theorem originalSource_jointFactor {p : Parameters} {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure γ) [IsFiniteMeasure ν]
    (rate : RateInput p) (split : α → γ × TimeControl p) (hsplit : Measurable split)
    (hproduct : μ.map split = ν.prod (ContinuousLearningRows.timeControlLaw p))
    (g : γ × PropRestControl p → β) (hg : Measurable g) :
    μ.map (fun z => (g ((split z).1, (proposalControlSplit p (split z).2).2),
      physicalProposalBit rate (split z).2)) =
    ((ν.prod (proposalRestControlLaw p)).map g).prod (proposalBitLaw rate) := by
  let H := fun xu : γ × TimeControl p =>
    (g (xu.1, (proposalControlSplit p xu.2).2), physicalProposalBit rate xu.2)
  have hH : Measurable H :=
    (hg.comp (measurable_fst.prodMk
      (measurable_snd.comp ((proposalControlSplit p).measurable.comp measurable_snd)))).prodMk
        ((measurable_physicalProposalBit rate).comp measurable_snd)
  change μ.map (H ∘ split) = _
  rw [← Measure.map_map hH hsplit, hproduct]
  exact proposalSplit_joint_pushforward ν g hg rate

/-- Every positive-offset first-live cell on the actual source stratum belongs
to exactly one of the continuing-live or empty-pending source branches. -/
theorem positiveFirstLiveSource_exhaustion {p : Parameters}
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    (0 < t.val - s ∧ t.val - s <
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z.val).length) ↔
      ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
        rate rewards C_star C_h q t s hs control0
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z) ∨
      ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty rate rewards C_star C_h q t s hs
        control0 (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z) :=
  ReferenceFirstLiveSourcePhasePartition.source_positive_cell_iff_branches
    rate rewards C_star C_h q t s hs control0 z

/-- The canonical correlated pair reads no proposal scalar. This is a
pathwise statement; it makes no independence assertion about its components. -/
theorem liveRecordingFastPair_replaceProposal {p : Parameters} (rate : RateInput p)
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (assignment : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot assignment)
    (u : TimeControl p) (a : Scalar) :
    FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
      rate.sourceCap v w hv hw hvw hwv assignment snapshot
        (replaceProposalScalar p u a).1 =
      FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
        rate.sourceCap v w hv hw hvw hwv assignment snapshot u.1 := by
  classical
  have hnamed (c : ContinuousControlSlice.NamedLabel) :
      (replaceProposalScalar p u a).1 (.inl c) =
        if c = .prop then a else u.1 (.inl c) := by
    simp [replaceProposalScalar, propLabel, ContinuousControlSlice.Label.prop, Function.update_apply]
  have hpilot (i : Fin p.m) :
      (replaceProposalScalar p u a).1 (ContinuousControlSlice.Label.pilot i) =
        u.1 (ContinuousControlSlice.Label.pilot i) :=
    replaceProposalScalar_other p u a _ (by simp [propLabel,
      ContinuousControlSlice.Label.pilot, ContinuousControlSlice.Label.prop])
  have haction (source : Fin p.m) :
      SnapshotRecordingKernel.dataAction p (.live assignment snapshot)
        rate.eta.val rate.eta.property rate.sourceCap v w hv hw hvw hwv
          (replaceProposalScalar p u a).1 source =
        SnapshotRecordingKernel.dataAction p (.live assignment snapshot)
          rate.eta.val rate.eta.property rate.sourceCap v w hv hw hvw hwv u.1 source := by
    simp only [SnapshotRecordingKernel.dataAction, PublicDiscreteDraws.pilotDraw,
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.fast,
      hnamed, reduceCtorEq, ↓reduceIte, hpilot]
  have hmask (source : Fin p.m) (j : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (K_pos p) source j
        (replaceProposalScalar p u a).1 ↔
      CanonicalRecordingSlice.recordingMask (K_pos p) source j u.1 := by
    simp only [CanonicalRecordingSlice.recordingMask, PublicDiscreteDraws.pilotDraw,
      ContinuousControlSlice.coordinate, hpilot]
  apply Prod.ext
  · simp only [FastRewardSliceLaw.liveRecordingFastPair, SnapshotRecordingKernel.recordingMap,
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.slot,
      ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.thin,
      hnamed, reduceCtorEq, ↓reduceIte, haction, hmask]
    rfl
  · simp only [FastRewardSliceLaw.liveRecordingFastPair, SnapshotRecordingKernel.fastArmDraw,
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.fast,
      hnamed, reduceCtorEq, ↓reduceIte]

open ReferenceLiveDispatchOutputMeasurability ReferenceActivePhysicalStepMeasurability
  ReferenceLiveDispatchMeasurability LaterAssignmentAnchorMeasurability

/-- The reserved fast draw on live input coordinates. Empty pending is used
only to evaluate that reserved draw, including when physical play is a pilot. -/
def reservedFastCoordinates {p : Parameters} (rate : RateInput p)
    (z : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate) : Option (Fin p.K) := by
  classical
  exact if CoordinatorLocalArmChoice.assignmentIsLive z.1 none z.2.2.1 then
    CoordinatorLocalArmChoice.coordinatorArmChoice z.1 ∅ none z.2.2.1
      (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates z).registers.complementWeights
      z.2.2.2
  else none

private theorem measurable_reservedFastCoordinates {p : Parameters} (rate : RateInput p) :
    Measurable (reservedFastCoordinates rate) := by
  classical
  let started : CoordinatorPhaseClock.StartRoundResult p :=
    ⟨CoordinatorPhaseClock.initialClock p, rfl, ∅, none, none⟩
  have hslice (old : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p)
      (time : Fin p.T) : Measurable
      (fun a : SliceCoordinates p => reservedFastCoordinates rate
        (payloadWithAnchor old a.1, code, time, a.2)) := by
    change Measurable (fun a : SliceCoordinates p =>
      if CoordinatorLocalArmChoice.assignmentIsLive old none time then
        CoordinatorLocalArmChoice.coordinatorArmChoice (payloadWithAnchor old a.1) ∅ none time
          (sliceInput old code time a).registers.complementWeights a.2 else none)
    by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive old none time
    · simp only [hlive, ↓reduceIte]
      exact measurable_sliceArmChoice old code time started
    · simp only [hlive, ↓reduceIte]
      exact measurable_const
  have hp : Measurable (fun z : LiveDispatchCoordinates p rate =>
      LaterAssignmentStartMeasurability.payloadObservation z.1) :=
    (comap_measurable _).comp measurable_fst
  have hinput : Measurable (inputDiscrete (p := p) (rate := rate)) := by
    apply measurable_to_countable'
    rintro ⟨⟨n, sigma, slow, queues⟩, code, time⟩
    change MeasurableSet {z : LiveDispatchCoordinates p rate |
      ((z.1.n, z.1.sigma, z.1.slowSet.1, z.1.queues), z.2.1, z.2.2.1) =
        ((n, sigma, slow, queues), code, time)}
    simp only [Prod.mk.injEq, Set.ofPred_and]
    exact ((measurableSet_eq_fun hp.fst measurable_const).inter
      ((measurableSet_eq_fun hp.snd.fst measurable_const).inter
        ((measurableSet_eq_fun hp.snd.snd.fst measurable_const).inter
          (measurableSet_eq_fun hp.snd.snd.snd.snd measurable_const)))).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
        (measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd))
          measurable_const))
  have hkey : Measurable (discreteRange (p := p) (rate := rate)) := hinput.subtype_mk
  have ha : Measurable (fun z : LiveDispatchCoordinates p rate =>
      (⟨z.1.anchor, z.1.anchor_pos⟩ : LaterAssignmentAnchorMeasurability.PositiveAnchor p)) :=
    (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp measurable_fst).subtype_mk
  have hf (c : InputDiscreteRange p rate) : Measurable
      (fun z : LiveDispatchCoordinates p rate => reservedFastCoordinates rate
        (payloadWithAnchor (sliceRepresentative c).1 ⟨z.1.anchor, z.1.anchor_pos⟩,
          (sliceRepresentative c).2.1, (sliceRepresentative c).2.2.1, z.2.2.2)) :=
    (hslice (sliceRepresentative c).1 (sliceRepresentative c).2.1
      (sliceRepresentative c).2.2.1).comp
        (ha.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have h := CoordinatorCollectionRunMeasurabilityRepair.measurable_of_countable_cases
    discreteRange hkey _ hf
  convert h using 1
  funext z
  rw [sliceRepresentative_reconstruction]

private theorem measurable_sumParameter {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (f : α × γ → δ) (g : β × γ → δ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : (α ⊕ β) × γ =>
      match z.1 with | .inl a => f (a, z.2) | .inr b => g (b, z.2)) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib α β γ).measurable using 1
  funext z
  rcases z with ⟨x, y⟩
  cases x <;> rfl

/-- All phase tags remain explicit. This reads only incoming registers and
the current pre-choice control; no finish or saved current proposal is run. -/
def reservedFastForRegisters {p : Parameters} {rate : RateInput p}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p) : Option (Fin p.K) := by
  classical
  exact if CoordinatorLocalArmChoice.assignmentIsLive r.payload none time then
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload ∅ none time r.complementWeights row
  else none

def reservedFastAtInput {p : Parameters} {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Fin p.K) :=
  match x.state.coordinator with
  | .live r _ _ => reservedFastForRegisters (rate := rate) r x.time x.row
  | _ => none

private theorem reservedFastAtInput_prepare {p : Parameters} {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    reservedFastAtInput x =
      match (ReferenceActivePhysicalStep.prepare x).coordinator with
      | .live r _ _ _ => reservedFastForRegisters (rate := rate) r x.time x.row
      | _ => none := by
  rw [(ReferenceActivePhysicalStep.prepare x).coordinator_eq]
  cases hc : x.state.coordinator with
  | first =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc,
        CoordinatorRoundDispatch.dispatch]
      rfl
  | dagger => simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc]
  | collection payload ledger saved =>
      simp only [reservedFastAtInput, ReferenceActivePhysicalStep.dispatch, hc]
      split_ifs <;> rfl

private theorem reservedFastForRegisters_ne_none {p : Parameters} {rate : RateInput p}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload cutoff time r.complementWeights) :
    reservedFastForRegisters (rate := rate) r time row ≠ none := by
  have hcut : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.cutoffRound (p := p) none := by
    have hstart := hvalid.time.assignment_started
    simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none,
      CoordinatorLocalArmChoice.sourceRound] at *
    omega
  have hv := CoordinatorLocalArmChoice.choiceInputsValid_mk r.payload none time r.complementWeights
    hvalid.time.assignment_started hcut
    (fun j => ⟨hvalid.current_weight_pos j, hvalid.anchor_le_current j,
      hvalid.current_le_twice_anchor j⟩)
  have hl : CoordinatorLocalArmChoice.assignmentIsLive r.payload none time :=
    ⟨hvalid.time.assignment_started, by
      simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none,
        CoordinatorLocalArmChoice.sourceRound]
      omega⟩
  simp only [reservedFastForRegisters, hl, ↓reduceIte, CoordinatorLocalArmChoice.coordinatorArmChoice]
  rw [CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty _ _ _ _ _ _ hv hl rfl]
  exact Option.some_ne_none _

private theorem measurable_reservedFastAtInput {p : Parameters} (rate : RateInput p) :
    Measurable (reservedFastAtInput (p := p) (rate := rate)) := by
  let read : CoordinatorCode p rate × (Fin p.T × CompletePublicTable.CompleteRow p) →
      Option (Fin p.K) := fun z =>
    match z.1 with
    | .inl _ => none
    | .inr branch => match branch with
      | .inl live => reservedFastCoordinates rate (live.1, live.2, z.2)
      | .inr other => match other with | .inl _ => none | .inr _ => none
  have hlive : Measurable (fun z :
      (ReferenceActivePhysicalStep.Payload rate × LiveDiscrete p) ×
        (Fin p.T × CompletePublicTable.CompleteRow p) =>
      reservedFastCoordinates rate (z.1.1, z.1.2, z.2)) :=
    (measurable_reservedFastCoordinates rate).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hread : Measurable read := by
    convert measurable_sumParameter (fun _ => (none : Option (Fin p.K))) _ measurable_const
      (measurable_sumParameter _ _ hlive
        (measurable_sumParameter (fun _ => (none : Option (Fin p.K)))
          (fun _ => (none : Option (Fin p.K))) measurable_const measurable_const)) using 2
    rename_i z
    rcases z with ⟨phase, rest⟩
    rcases phase with first | live | collection | dagger <;> rfl
  have hcoords : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (encodeCoordinator x.state.coordinator, x.time, x.row)) :=
    (measurable_coordinatorCode.comp measurable_state).prodMk
      (measurable_time.prodMk measurable_row)
  convert hread.comp hcoords using 1
  funext x
  cases hc : x.state.coordinator with
  | first => simp only [reservedFastAtInput, hc, Function.comp_apply, read, encodeCoordinator]
  | collection payload ledger saved =>
      simp only [reservedFastAtInput, hc, Function.comp_apply, read, encodeCoordinator]
  | dagger => simp only [reservedFastAtInput, hc, Function.comp_apply, read, encodeCoordinator]
  | live r owned base =>
      simp only [reservedFastAtInput, reservedFastForRegisters, hc, Function.comp_apply, read, encodeCoordinator,
        reservedFastCoordinates, ReferenceLiveDispatchMeasurability.liveInputOfCoordinates]
      have hw : (ReferenceActivePhysicalStep.liveRegistersAt
          (decodeLiveRegisters r.payload (encodeLive r owned base)) x.time).complementWeights =
          r.complementWeights := by
        funext a
        exact congrArg (ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p))
          (extendComplement_apply r.payload r.complementScores a)
      rw [hw]

private theorem reservedFastAtInput_replaceProposal {p : Parameters} {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (u : TimeControl p) (a : Scalar) :
    reservedFastAtInput (ReferenceContinuingLiveSlicePreparation.inputAtControl x
      (replaceProposalScalar p u a)) =
    reservedFastAtInput (ReferenceContinuingLiveSlicePreparation.inputAtControl x u) := by
  classical
  have hf : (replaceProposalScalar p u a).1 ContinuousControlSlice.Label.fast =
      u.1 ContinuousControlSlice.Label.fast :=
    replaceProposalScalar_other p u a _ (by simp [propLabel,
      ContinuousControlSlice.Label.fast, ContinuousControlSlice.Label.prop])
  simp only [reservedFastAtInput, reservedFastForRegisters,
    ReferenceContinuingLiveSlicePreparation.inputAtControl_state,
    ReferenceContinuingLiveSlicePreparation.inputAtControl_time]
  cases hc : x.state.coordinator with
  | first => rfl
  | collection payload ledger saved => rfl
  | dagger => rfl
  | live r owned base =>
      by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload none x.time
      · simp only [hlive, ↓reduceIte, CoordinatorLocalArmChoice.coordinatorArmChoice,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
          ReferenceContinuingLiveSlicePreparation.rowAtControl_time,
          CoordinatorLocalArmChoice.coordinatorArmChoiceCore, eq_self, and_self,
          CoordinatorLocalArmChoice.localFastDraw, ContinuousControlSlice.coordinate, hf]
      · simp only [hlive, ↓reduceIte]

private theorem integral_true_of_jointFactor {p : Parameters} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsFiniteMeasure ν]
    (rate : RateInput p) (obs : α → β) (bit : α → Bool)
    (ho : Measurable obs) (hb : Measurable bit)
    (hjoint : μ.map (fun z => (obs z, bit z)) = ν.prod (proposalBitLaw rate))
    (F : β → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    Integrable (fun z => F (obs z)) μ ∧
    Integrable (fun z => F (obs z) * (if bit z = true then 1 else 0)) μ ∧
    (∫ z, F (obs z) * (if bit z = true then 1 else 0) ∂μ) =
      FollowerCutoffScan.proposalHazard p rate.eta.val * (∫ z, F (obs z) ∂μ) := by
  classical
  let indicator : Bool → ℝ := fun b => if b = true then 1 else 0
  have hi : Measurable indicator := measurable_of_finite _
  have hp := ho.prodMk hb
  have hw : Measurable (fun y : β × Bool => F y.1 * indicator y.2) :=
    (hF.comp measurable_fst).mul (hi.comp measurable_snd)
  have hmean : ∫ b, indicator b ∂proposalBitLaw rate =
      FollowerCutoffScan.proposalHazard p rate.eta.val := by
    rw [proposalBitLaw, integral_map (measurable_thresholdProposalBit _).aemeasurable
      hi.aestronglyMeasurable]
    exact proposalIndicator_integral rate
  have hmarg : μ.map obs = ν := by
    have h := congrArg (fun jointMeasure : Measure (β × Bool) => jointMeasure.map Prod.fst) hjoint
    rw [Measure.map_map measurable_fst hp, Measure.map_fst_prod, measure_univ, one_smul] at h
    exact h
  have hobsIntegral : (∫ z, F (obs z) ∂μ) = ∫ y, F y ∂ν := by
    rw [← hmarg, integral_map ho.aemeasurable hF.aestronglyMeasurable]
  refine ⟨Integrable.of_bound (hF.comp ho).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => hC (obs z)), ?_, ?_⟩
  · apply Integrable.of_bound (hw.comp hp).aestronglyMeasurable (max C 0)
    filter_upwards [] with z
    change ‖F (obs z) * (if bit z = true then 1 else 0)‖ ≤ max C 0
    by_cases h : bit z = true
    · simpa only [h, ↓reduceIte, mul_one] using (hC (obs z)).trans (le_max_left C 0)
    · simp only [h, Bool.false_eq_true, ↓reduceIte, mul_zero, norm_zero]
      exact le_max_right C 0
  · change (∫ z, (fun y : β × Bool => F y.1 * indicator y.2) (obs z, bit z) ∂μ) = _
    rw [← integral_map hp.aemeasurable hw.aestronglyMeasurable, hjoint,
      integral_prod_mul, hmean, hobsIntegral, mul_comm]

section ActualMarkers

open ReferenceFirstLiveRecordingReadoutMeasurability

variable {p : Parameters} (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

/-- Replacing only current `prop` preserves the actual continuing recorder.
The all-controls formula is derived from the actual zero-origin launch seed. -/
theorem continuingMarker_replaceProposal
    (x : XPlus rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    currentPhysicalMarker (x, replaceProposalScalar p u a) =
      currentPhysicalMarker (x, u) := by
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, _, _, _, hfirst, hseed, _, _, _, _, _, hunoccupied, _,
      hvalid, hpairwise, htime, _, _⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
      rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := selectedBaselinePayload_eq_of_continuing x
    r owned base d hsStart c arm hcoord
  have hpair := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
    (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).followers
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).memory
    hfirst hseed hunoccupied hvalid hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  have hmarker (v : TimeControl p) : currentPhysicalMarker (x, v) =
      (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
        rate.sourceCap r.payload.anchor
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights r (sourceCurrentInput x.val).time)
        r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        r.payload.assignment
        (ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
          r owned base (sourceCurrentInput x.val).time d states) v.1).1 := by
    unfold currentPhysicalMarker
    rw [hpayload, sourcePhysicalMarker_eq_candidatePhysicalMarker]
    exact congrArg Prod.fst (hpair v)
  rw [hmarker, hmarker, liveRecordingFastPair_replaceProposal]

/-- The after-confirmation empty-pending branch has the same pathwise
invariance, without assuming a pending pilot exists. -/
theorem emptyMarker_replaceProposal
    (x : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
      rate rewards C_star C_h q t s hs control0 (x, replaceProposalScalar p u a) =
    ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
      rate rewards C_star C_h q t s hs control0 (x, u) := by
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hfirst, hseed, hunoccupied, hvalid, hpairwise, htime⟩ :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
      rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty_payload_eq
    rate rewards C_star C_h q t s hs control0 x
    r owned base d hsStart c arm hcoord
  have hpair := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    (retainedSourceInitial x.val) (retainedSourceSplit x.val).1.2 q rewards s
    (t.val - s) (retainedSourceCurrentSpan hs) (retainedSourceInitialMode x.val)
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).followers
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).memory
    hfirst hseed hunoccupied hvalid hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  have hmarker (v : TimeControl p) :
      ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
        rate rewards C_star C_h q t s hs control0 (x, v) =
      (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
        rate.sourceCap r.payload.anchor
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights r (sourceCurrentInput x.val).time)
        r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r (sourceCurrentInput x.val).time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm.choiceInputsValid)
        r.payload.assignment
        (ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
          r owned base (sourceCurrentInput x.val).time d states) v.1).1 := by
    unfold ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
    rw [hpayload, sourcePhysicalMarker_eq_candidatePhysicalMarker]
    exact congrArg Prod.fst (hpair v)
  rw [hmarker, hmarker, liveRecordingFastPair_replaceProposal]

/-- The two exhaustive positive-offset source branches remain tagged. -/
abbrev LiveRemainder := XPlus rate rewards C_star C_h q t s hs control0 ⊕
  ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty rate rewards C_star C_h q t s hs control0

instance liveRemainder_measurableSpace :
    MeasurableSpace (LiveRemainder rate rewards C_star C_h q t s hs control0) := by
  exact @Sum.instMeasurableSpace
    (XPlus rate rewards C_star C_h q t s hs control0)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty rate rewards C_star C_h q t s hs control0)
    inferInstance inferInstance

/-- Forget only the branch tag, retaining the same whole original source. -/
def liveRetained : LiveRemainder rate rewards C_star C_h q t s hs control0 →
    SourceX rate rewards C_star C_h q t s hs control0 :=
  Sum.elim Subtype.val Subtype.val

private instance sumSingletons {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := ⟨fun tag => by
      cases tag with
      | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
      | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image⟩

private instance recordListSingletons : MeasurableSingletonClass (List (Bool × ℕ)) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := Bool × ℕ)) := by
    intro left right h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt left n =
      ReferenceActiveHorizonMeasurability.listObservationAt right n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hl : left[n]? <;> cases hr : right[n]? <;> simp_all
  constructor
  intro records
  have heq : ({records} : Set (List (Bool × ℕ))) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

/-- The actual physical recorder in each of the distinct live branches. -/
def liveMarker (xu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
    TimeControl p) : Option (Fin p.K) :=
  match xu.1 with
  | .inl x => currentPhysicalMarker (x, xu.2)
  | .inr x => ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
      rate rewards C_star C_h q t s hs control0 (x, xu.2)

/-- The rate of the same actual selected payload, with no current-control
law or numerical agreement premise. -/
def liveRate (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (j : Fin p.K) : ℝ :=
  match x with
  | .inl x => ReferenceFirstLiveRecordingSourceCylinder.markerRate
      rate rewards C_star C_h q t s hs control0 x j
  | .inr x => ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
      rate rewards C_star C_h q t s hs control0 x j

theorem measurable_liveRetained :
    Measurable (liveRetained rate rewards C_star C_h q t s hs control0) :=
  measurable_subtype_coe.sumElim measurable_subtype_coe

theorem measurable_liveMarker :
    Measurable (liveMarker rate rewards C_star C_h q t s hs control0) := by
  let : MeasurableSpace
      ((XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) ⊕
        (ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
          rate rewards C_star C_h q t s hs control0 × TimeControl p)) :=
    @Sum.instMeasurableSpace _ _ inferInstance inferInstance
  convert ((measurable_currentPhysicalMarker
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)).sumElim
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_currentEmptyMarker
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0))).comp
        (MeasurableEquiv.sumProdDistrib _ _ _).measurable using 1
  funext xu
  rcases xu with ⟨x, u⟩
  cases x <;> rfl

theorem measurable_liveRate (j : Fin p.K) :
    Measurable (fun x => liveRate rate rewards C_star C_h q t s hs control0 x j) :=
  (ReferenceFirstLiveRecordingSourceCylinder.measurable_markerRate
    rate rewards C_star C_h q t s hs control0 j).sumElim
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
        rate rewards C_star C_h q t s hs control0 j)

theorem liveMarker_replaceProposal
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    liveMarker rate rewards C_star C_h q t s hs control0
      (x, replaceProposalScalar p u a) =
    liveMarker rate rewards C_star C_h q t s hs control0 (x, u) := by
  cases x with
  | inl x =>
      exact continuingMarker_replaceProposal
        rate rewards C_star C_h q t s hs control0 x u a
  | inr x =>
      exact emptyMarker_replaceProposal
        rate rewards C_star C_h q t s hs control0 x u a

/-- The complete strict-past numerical registers, flag and accepted records.
This is computed on the original source recovered at the fixed baseline. -/
def liveNumericalPast (x : LiveRemainder rate rewards C_star C_h q t s hs control0) :
    (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) :=
  ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
    rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
      rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0))

theorem measurable_liveNumericalPast :
    Measurable (liveNumericalPast rate rewards C_star C_h q t s hs control0) :=
  (ReferenceFirstLiveNumericalQueueBorel.measurable_numericalCountRunReadout
    rate rewards C_star C_h q t s hs control0).comp
      ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRecover
        rate rewards C_star C_h q t s hs control0).comp
        ((measurable_liveRetained rate rewards C_star C_h q t s hs control0).prodMk
          measurable_const))

/-- Raw ALL-arm arrivals, before the strict-past overflow flag is applied. -/
def liveRawArrivals (xu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
    TimeControl p) (j : Fin p.K) : ℕ :=
  if liveMarker rate rewards C_star C_h q t s hs control0 xu = some j then
    Nat.floor ((rate.n : ℝ) * (((rewards t j).val : ℝ) / (D p : ℝ)) /
      liveRate rate rewards C_star C_h q t s hs control0 xu.1 j)
  else 0

theorem measurable_liveRawArrivals :
    Measurable (liveRawArrivals rate rewards C_star C_h q t s hs control0) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (Nat.measurable_floor.comp
    (measurable_const.div ((measurable_liveRate
      rate rewards C_star C_h q t s hs control0 j).comp measurable_fst))).ite
    (measurableSet_eq_fun (measurable_liveMarker
      rate rewards C_star C_h q t s hs control0) measurable_const) measurable_const

/-- Literal all-arm pre-proposal numerical fields. `raw` remains distinct
from the accepted records, and `beforeOverflow` tests only the strict past. -/
structure NumericalUpdateFields (p : Parameters) where
  raw : Fin p.K → ℕ
  beforeRegisters : Fin p.K → ℕ × ℕ
  beforeOverflow : Bool
  beforeRecords : Fin p.K → List (Bool × ℕ)
  accepted : Fin p.K → Bool × ℕ
  service : Fin p.K → ℕ
  afterRegisters : Fin p.K → ℕ × ℕ
  afterOverflow : Bool
  afterRecords : Fin p.K → List (Bool × ℕ)
  deriving Countable

instance numericalUpdateFields_measurableSpace : MeasurableSpace (NumericalUpdateFields p) := ⊤
instance numericalUpdateFields_discrete : DiscreteMeasurableSpace (NumericalUpdateFields p) :=
  ⟨fun _ => trivial⟩

/-- Enabled zero arrivals still serve every arm; a prior overflow preserves
registers. The current detecting update is performed before setting its flag. -/
def numericalUpdateFields
    (before : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (raw : Fin p.K → ℕ) : NumericalUpdateFields p :=
  let accepted := fun j => if before.2.1 then (false, 0) else (true, raw j)
  let after := fun j => QueueReplay.transition (4 * rate.n) (before.1 j) (accepted j)
  { raw := raw
    beforeRegisters := before.1
    beforeOverflow := before.2.1
    beforeRecords := before.2.2
    accepted := accepted
    service := fun j => RecordedQueueRun.recordService (4 * rate.n) (before.1 j) (accepted j)
    afterRegisters := after
    afterOverflow := before.2.1 || decide (∃ j, 32 * (after j).2 > D p)
    afterRecords := fun j => before.2.2 j ++ [accepted j] }

/-- The literal numerical fields are exactly the existing queue step on
an enabled current input; this lemma has no probabilistic hypothesis. -/
theorem numericalUpdateFields_eq_step
    (before : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (henabled : round.enabled = true) :
    numericalUpdateFields rate (before.registers, before.overflow, before.records)
      (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) round) =
    { raw := RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) round
      beforeRegisters := before.registers
      beforeOverflow := before.overflow
      beforeRecords := before.records
      accepted := RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) before round
      service := fun j => RecordedQueueRun.recordService (4 * rate.n) (before.registers j)
        (RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) before round j)
      afterRegisters := (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) before round).registers
      afterOverflow := (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) before round).overflow
      afterRecords := (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) before round).records } := by
  simp only [numericalUpdateFields, RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
    henabled, ↓reduceIte, ReferenceFirstLaunchNumericalCell.queueParameters]
  congr 1
  funext j
  simp only [RecordedQueueRun.acceptedRecord, henabled, ↓reduceIte]

/-- Actual recorder and actual computed all-arm numerical update, before
exposing the current proposal scalar. No post-Finish field occurs here. -/
def livePreProposalReadout
    (xu : LiveRemainder rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    Option (Fin p.K) × NumericalUpdateFields p :=
  (liveMarker rate rewards C_star C_h q t s hs control0 xu,
    numericalUpdateFields rate
      (liveNumericalPast rate rewards C_star C_h q t s hs control0 xu.1)
      (liveRawArrivals rate rewards C_star C_h q t s hs control0 xu))

theorem measurable_livePreProposalReadout :
    Measurable (livePreProposalReadout rate rewards C_star C_h q t s hs control0) := by
  have hupdate : Measurable (fun z :
      ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) × (Fin p.K → ℕ) =>
      numericalUpdateFields rate z.1 z.2) := measurable_of_countable _
  exact (measurable_liveMarker rate rewards C_star C_h q t s hs control0).prodMk
    (hupdate.comp (((measurable_liveNumericalPast
      rate rewards C_star C_h q t s hs control0).comp measurable_fst).prodMk
      (measurable_liveRawArrivals rate rewards C_star C_h q t s hs control0)))

/-- Literal replacement of only `prop` preserves every pre-proposal field,
including arrivals, service, all scores and queues, and the overflow update. -/
theorem livePreProposalReadout_replaceProposal
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    livePreProposalReadout rate rewards C_star C_h q t s hs control0
      (x, replaceProposalScalar p u a) =
    livePreProposalReadout rate rewards C_star C_h q t s hs control0 (x, u) := by
  have hm := liveMarker_replaceProposal rate rewards C_star C_h q t s hs control0 x u a
  have hraw : liveRawArrivals rate rewards C_star C_h q t s hs control0
      (x, replaceProposalScalar p u a) =
      liveRawArrivals rate rewards C_star C_h q t s hs control0 (x, u) := by
    funext j
    simp only [liveRawArrivals, hm]
  simp only [livePreProposalReadout, hm, hraw]

private theorem numericalPast_eq_of_retained
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))
    (hx : liveRetained rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z) :
    liveNumericalPast rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z := by
  let baseline := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)
  have hbaseline : ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0 baseline =
      liveRetained rate rewards C_star C_h q t s hs control0 x :=
    congrArg Prod.fst (ReferenceFirstLiveRecordingSourceCylinder.sourceSplit_sourceRecover
      rate rewards C_star C_h q t s hs control0 (_, control0))
  have hprefix (w : ReferenceTotalSourceDisintegration.SourceStratum
      rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
      ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix
        rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 w) =
      ReferenceSourceCurrentControlFreshness.c_t p control0 t w.val := by
    rw [ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix_sourceRetained,
      ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val,
      ← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  change ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
    rate rewards C_star C_h q t s hs control0 baseline = _
  apply (ReferenceFirstLiveNumericalPrefixAdaptation.measurable_numericalCountRunReadout
    rate rewards C_star C_h q t s hs control0).factorsThrough
  change ReferenceSourceCurrentControlFreshness.c_t p control0 t baseline.val =
    ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val
  rw [← hprefix baseline, ← hprefix z, hbaseline, hx]

/-- The fields computed from the continuing remainder are the actual
current cell's raw arrivals and the actual strict-past numerical run. -/
theorem continuingPreProposalReadout_actual
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) :
    let xu := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0 z
    livePreProposalReadout rate rewards C_star C_h q t s hs control0
      (.inl xu.1, xu.2) =
    (ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
      rate rewards C_star C_h q t s hs control0 z,
      numericalUpdateFields rate
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
          rate rewards C_star C_h q t s hs control0 z.val)
        (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstLiveSourceCellReadout.cell
            rate rewards C_star C_h q t s hs control0 z).input)) := by
  intro xu
  have hpast := numericalPast_eq_of_retained
    rate rewards C_star C_h q t s hs control0 (.inl xu.1) z.val rfl
  have hraw : liveRawArrivals rate rewards C_star C_h q t s hs control0
      (.inl xu.1, xu.2) = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 z).input := by
    funext j
    exact ((ReferenceFirstLiveSourceCellReadout.source_current_cell_fields
      rate rewards C_star C_h q t s hs control0 z).2.2.2.2 j).symm
  exact congrArg₂ Prod.mk rfl (congrArg₂ (numericalUpdateFields rate) hpast hraw)

/-- The distinct empty-pending original source has the same actual numerical
readout, with its own actual marker and current cell. -/
theorem emptyPreProposalReadout_actual
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) :
    let xu := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0 z
    livePreProposalReadout rate rewards C_star C_h q t s hs control0
      (.inr xu.1, xu.2) =
    (ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker
      rate rewards C_star C_h q t s hs control0 z,
      numericalUpdateFields rate
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
          rate rewards C_star C_h q t s hs control0 z.val)
        (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstLiveEmptyPendingSourceMoments.cell
            rate rewards C_star C_h q t s hs control0 z))) := by
  intro xu
  have hpast := numericalPast_eq_of_retained
    rate rewards C_star C_h q t s hs control0 (.inr xu.1) z.val rfl
  have hmarker := ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker_eq_control
    rate rewards C_star C_h q t s hs control0 z
  have hraw : liveRawArrivals rate rewards C_star C_h q t s hs control0
      (.inr xu.1, xu.2) = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLiveEmptyPendingSourceMoments.cell
          rate rewards C_star C_h q t s hs control0 z) := by
    funext j
    rw [(ReferenceFirstLiveEmptyPendingSourceMoments.cell_actual_facts
      rate rewards C_star C_h q t s hs control0 z).2.2.2.2.1 j]
    simp only [liveRawArrivals, liveMarker, liveRate,
      ReferenceFirstLiveEmptyPendingSourceMoments.rho, hmarker, xu]
    rfl
  exact congrArg₂ Prod.mk hmarker.symm (congrArg₂ (numericalUpdateFields rate) hpast hraw)

/-- The reserved fast operation on the existing original-source/current-control product. -/
def sourceReservedFastAtControl :
    SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p → Option (Fin p.K) :=
  reservedFastAtInput (p := p) (rate := rate) ∘
    sourceInputAtControlProduct (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)

theorem measurable_sourceReservedFastAtControl :
    Measurable (sourceReservedFastAtControl rate rewards C_star C_h q t s hs control0) := by
  have hi := measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0)
  exact (measurable_reservedFastAtInput rate).comp hi

/-- The original reserved fast coordinate, before any Finish or proposal exposure. -/
def liveReservedFastOption :
    LiveRemainder rate rewards C_star C_h q t s hs control0 × TimeControl p → Option (Fin p.K) :=
  sourceReservedFastAtControl rate rewards C_star C_h q t s hs control0 ∘
    Prod.map (liveRetained rate rewards C_star C_h q t s hs control0) id

theorem measurable_liveReservedFastOption :
    Measurable (liveReservedFastOption rate rewards C_star C_h q t s hs control0) :=
  (measurable_sourceReservedFastAtControl rate rewards C_star C_h q t s hs control0).comp
    (((measurable_liveRetained rate rewards C_star C_h q t s hs control0).comp
      measurable_fst).prodMk measurable_snd)

theorem liveReservedFastOption_replaceProposal
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    liveReservedFastOption rate rewards C_star C_h q t s hs control0
      (x, replaceProposalScalar p u a) =
    liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) :=
  reservedFastAtInput_replaceProposal _ u a

/-- The optional fast representation is present on BOTH actual live
branches. Its checks are discharged from the actual pre-choice preparation. -/
theorem liveReservedFastOption_ne_none
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :
    liveReservedFastOption rate rewards C_star C_h q t s hs control0 (x, u) ≠ none := by
  cases x with
  | inl x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord, _⟩ :=
        ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
      change reservedFastAtInput
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (sourceCurrentInput x.val) u) ≠ none
      rw [reservedFastAtInput_prepare, hu]
      exact reservedFastForRegisters_ne_none r _ _ _ c.choiceInputsValid
  | inr x =>
      obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord, _⟩ :=
        ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
          rate rewards C_star C_h q t s hs control0 x.val x.property
      obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        (sourceCurrentInput x.val) r owned base d hsStart c arm hcoord u
      change reservedFastAtInput
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (sourceCurrentInput x.val) u) ≠ none
      rw [reservedFastAtInput_prepare, hu]
      exact reservedFastForRegisters_ne_none r _ _ _ c.choiceInputsValid

/-- The correlated marker/fast observation and ALL-arm numerical update.
All three components use the same original current control. -/
def liveFullPreProposalReadout
    (xu : LiveRemainder rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  (liveReservedFastOption rate rewards C_star C_h q t s hs control0 xu,
    livePreProposalReadout rate rewards C_star C_h q t s hs control0 xu)

theorem measurable_liveFullPreProposalReadout :
    Measurable (liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0) :=
  (measurable_liveReservedFastOption rate rewards C_star C_h q t s hs control0).prodMk
    (measurable_livePreProposalReadout rate rewards C_star C_h q t s hs control0)

theorem liveFullPreProposalReadout_replaceProposal
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (a : Scalar) :
    liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0
      (x, replaceProposalScalar p u a) =
    liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0 (x, u) := by
  rw [liveFullPreProposalReadout, liveFullPreProposalReadout,
    liveReservedFastOption_replaceProposal, livePreProposalReadout_replaceProposal]

/-- The nonproposal representation retains the entire remainder and every
unused nonproposal scalar/affine input, together with the computed update. -/
def liveNonpropObservation
    (xr : LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) :=
  (xr, liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0
    (xr.1, (proposalControlSplit p).symm (⟨0, by norm_num⟩, xr.2)))

theorem measurable_liveNonpropObservation :
    Measurable (liveNonpropObservation rate rewards C_star C_h q t s hs control0) :=
  measurable_id.prodMk
    ((measurable_liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0).comp
      (measurable_fst.prodMk ((proposalControlSplit p).symm.measurable.comp
        (measurable_const.prodMk measurable_snd))))

theorem liveNonpropObservation_atControl
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :
    liveNonpropObservation rate rewards C_star C_h q t s hs control0
      (x, (proposalControlSplit p u).2) =
    ((x, (proposalControlSplit p u).2),
      liveFullPreProposalReadout rate rewards C_star C_h q t s hs control0 (x, u)) := by
  have hu : (proposalControlSplit p).symm
      (⟨0, by norm_num⟩, (proposalControlSplit p u).2) =
        replaceProposalScalar p u ⟨0, by norm_num⟩ := by
    simpa only [(proposalControlSplit p).symm_apply_apply] using
      proposalControlSplit_symm_replace p ⟨0, by norm_num⟩
        (proposalControlSplit p u).1 (proposalControlSplit p u).2
  simp only [liveNonpropObservation, hu, liveFullPreProposalReadout_replaceProposal]

/-- Every bounded Borel test of the actual continuing source, unused
nonproposal controls, and actual update satisfies the true-bit integral law. -/
theorem continuingSource_actualUpdate_integral (_hpos : s < t.val)
    (F : ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
      (.inl (split z).1, (proposalControlSplit p (split z).2).2)
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    Integrable (fun z => F (obs z)) μ ∧
    Integrable (fun z => F (obs z) * (if physicalProposalBit rate (split z).2 = true then 1 else 0)) μ ∧
    (∫ z, F (obs z) * (if physicalProposalBit rate (split z).2 = true then 1 else 0) ∂μ) =
      FollowerCutoffScan.proposalHazard p rate.eta.val * (∫ z, F (obs z) ∂μ) := by
  intro split obs μ
  let g := fun xr : XPlus rate rewards C_star C_h q t s hs control0 × PropRestControl p =>
    liveNonpropObservation rate rewards C_star C_h q t s hs control0 (.inl xr.1, xr.2)
  have hg : Measurable g :=
    (measurable_liveNonpropObservation rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
  have hspl := ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  exact integral_true_of_jointFactor μ _ rate obs (fun z => physicalProposalBit rate (split z).2)
    (hg.comp (hspl.fst.prodMk ((proposalControlSplit p).measurable.comp hspl.snd).snd))
    ((measurable_physicalProposalBit rate).comp hspl.snd)
    (originalSource_jointFactor
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0)
      rate (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product rate rewards C_star C_h q t s hs control0) g hg) F hF C hC

/-- The empty-pending original restriction has its own bounded-test law;
no successful future assignment or no-proposal survival is conditioned on. -/
theorem emptySource_actualUpdate_integral (_hpos : s < t.val)
    (F : ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
      (Option (Fin p.K) × (Option (Fin p.K) × NumericalUpdateFields p))) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let obs := fun z => liveNonpropObservation rate rewards C_star C_h q t s hs control0
      (.inr (split z).1, (proposalControlSplit p (split z).2).2)
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    Integrable (fun z => F (obs z)) μ ∧
    Integrable (fun z => F (obs z) * (if physicalProposalBit rate (split z).2 = true then 1 else 0)) μ ∧
    (∫ z, F (obs z) * (if physicalProposalBit rate (split z).2 = true then 1 else 0) ∂μ) =
      FollowerCutoffScan.proposalHazard p rate.eta.val * (∫ z, F (obs z) ∂μ) := by
  intro split obs μ
  let g := fun xr : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 × PropRestControl p =>
    liveNonpropObservation rate rewards C_star C_h q t s hs control0 (.inr xr.1, xr.2)
  have hg : Measurable g :=
    (measurable_liveNonpropObservation rate rewards C_star C_h q t s hs control0).comp
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)
  have hspl := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  exact integral_true_of_jointFactor μ _ rate obs (fun z => physicalProposalBit rate (split z).2)
    (hg.comp (hspl.fst.prodMk ((proposalControlSplit p).measurable.comp hspl.snd).snd))
    ((measurable_physicalProposalBit rate).comp hspl.snd)
    (originalSource_jointFactor
      (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty rate rewards C_star C_h q t s hs control0)
      rate (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit rate rewards C_star C_h q t s hs control0)
      (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product rate rewards C_star C_h q t s hs control0) g hg) F hF C hC

/-- On either actual positive-offset branch, the incoming physical
complement weights agree with the all-arm zero-origin numerical replay up to
the first overflow. The current detecting update is not excluded. -/
theorem liveSource_preOverflow_complementWeights
    (tagged : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 ⊕
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0) :
    let z := Sum.elim Subtype.val Subtype.val tagged
    let n := t.val - s
    let span : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
            (n + 1) ≤ p.T := by
      have he : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
        z.property.2.2
      rw [he]
      omega
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate z.val rewards C_star C_h z.property.2.1 (n + 1) span
    let queue := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let past := RecordedQueueRun.run queue (cells.take n)
    past.overflow = false →
      ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
      ∃ base : Fin (p.m - 1) → ℕ,
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z).input.state.coordinator =
          .live r owned base ∧
        (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
          (r.complementScores a, owned.queue a) = past.registers a.1 ∧
          r.complementWeights a = RecordedQueueRun.scoreWeight queue past a.1) := by
  intro z n span cells queue past hno
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z.val rewards C_star C_h z.property.2.1
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z.val rewards C_star C_h z.property.2.1
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z.val rewards C_star C_h z.property.2.1 (n + 1) span
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h z.property.2.1 (n + 1) span
  let original := ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
    rate rewards C_star C_h q t s hs control0 z
  have hpos : 0 < n := by
    cases tagged with
    | inl point => exact point.property.1
    | inr point => exact point.property.1
  have hcurrent : ∃ hn : n < W.length, W[n]'hn = original := by
    cases tagged with
    | inl point =>
        exact (ReferenceFirstLiveSourceCellReadout.source_current_window
          rate rewards C_star C_h q t s hs control0 point).2.2
    | inr point =>
        exact ReferenceFirstLiveEmptyPendingSourceMoments.currentOriginalWindowIndex
          rate rewards C_star C_h q t s hs control0 point
  obtain ⟨hindex, hrecord⟩ := hcurrent
  have hpref : W <+: E.records := List.takeWhile_prefix _
  have hspanPast : start + n ≤ p.T := by omega
  let V := ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards
    start n hspanPast seed.activeAtStart
  let input := ReferenceContinuingDataCandidateLogging.candidateInput initial z.val.1.2
    selected rewards start n span seed.activeAtStart
  let last : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
  have hrecords : E.records = V.records ++ [last] := by
    dsimp only [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    rfl
  have hlength : V.records.length = n :=
    ReferenceActivePhysicalHorizon.run_record_count initial z.val.1.2 selected rewards
      start n hspanPast seed.activeAtStart
  have hgetOption : E.records[n]? = some last := by
    rw [hrecords, List.getElem?_append_right (by omega)]
    simp only [hlength, Nat.sub_self, List.getElem?_cons_zero]
  have hget : E.records[n]'(hindex.trans_le hpref.length_le) = last := by
    rw [List.getElem?_eq_getElem (hindex.trans_le hpref.length_le)] at hgetOption
    exact Option.some.inj hgetOption
  have hlast : last = original := hget.symm.trans ((hpref.getElem hindex).symm.trans hrecord)
  have hstate : original.input.state = V.finalState :=
    (congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input.state) hlast).symm
  have hcommon := ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
    rate z.val rewards C_star C_h z.property.2.1 (n + 1) span n hindex.le
  dsimp only at hcommon
  have hle : n ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells := by
    have hlt : n < UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells := by
      by_contra h
      have htrue := hcommon.2.2.2.1.mpr (Nat.le_of_not_gt h)
      rw [hno] at htrue
      cases htrue
    exact hlt.le
  obtain ⟨hboundary, _, hpositive⟩ := hcommon.2.2.2.2.1 hle
  obtain ⟨r, owned, base, hr, _, _, _, _, hcomp, _⟩ := hpositive hpos
  refine ⟨r, owned, base, ?_, ?_⟩
  · change original.input.state.coordinator = _
    rw [hstate]
    exact hr
  · intro a
    refine ⟨(hcomp a).1, ?_⟩
    have hscore := congrArg Prod.fst (hcomp a).1
    change r.complementScores a = (past.registers a.1).1 at hscore
    change ScoreWeights.scoreWeight (1 + 1 / (D p : ℝ)) (r.complementScores a) =
      ScoreWeights.scoreWeight (1 + 1 / (D p : ℝ)) (past.registers a.1).1
    exact congrArg (ScoreWeights.scoreWeight (1 + 1 / (D p : ℝ))) hscore

end ActualMarkers

end Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

end
