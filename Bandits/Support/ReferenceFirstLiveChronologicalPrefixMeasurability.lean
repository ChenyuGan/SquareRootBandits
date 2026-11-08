/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation

import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability of the original first-live chronological prefix

The measurable structure introduced here retains every field of the accepted
logical cell. Continuous physical and numerical fields keep their product
Borel structures; only the canonical queue registers are discrete.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.FastComplementLocality
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability

open ReferenceFirstLiveChronologicalPrefixFoundation

variable {p : Parameters}

instance firstLiveRunStateMeasurableSpace (K : ℕ) :
    MeasurableSpace (RecordedQueueRun.RunState K) := ⊤

instance firstLiveRunStateDiscreteMeasurableSpace (K : ℕ) :
    DiscreteMeasurableSpace (RecordedQueueRun.RunState K) :=
  ⟨fun _ => trivial⟩

private def firstLiveRunStateCodeEquiv (K : ℕ) :
    RecordedQueueRun.RunState K ≃
      ((Fin K → RecordedQueueRun.Registers) ×
        (Bool × (Fin K → List (Bool × ℕ)))) where
  toFun state := (state.registers, (state.overflow, state.records))
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv := by intro state; cases state; rfl
  right_inv := by intro code; cases code; rfl

instance firstLiveRunStateCountable (K : ℕ) : Countable (RecordedQueueRun.RunState K) :=
  Countable.of_equiv _ (firstLiveRunStateCodeEquiv K).symm

local instance firstLiveSlowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤

local instance firstLiveSlowSetDiscreteMeasurableSpace : DiscreteMeasurableSpace (SlowSet p) :=
  ⟨fun _ => trivial⟩

/-- The full product code of one logical cell, in its declared field order. -/
abbrev LogicalCellProductCode (rate : RateInput p) :=
  Fin p.T ×
    (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
      (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p ×
        (RecordedQueueRun.RunState p.K ×
          (RecordedQueueRun.RunState p.K ×
            ((Fin p.K → Bool × ℕ) ×
              ((Fin p.K → ℕ) ×
                (SlowSet p × (Fin p.K × (Bool × SlowSet p)))))))))

/-- The literal full-field product code; in particular no physical or real
numerical coordinate is erased. -/
def logicalCellProductCode {rate : RateInput p} (cell : LogicalCell p rate) :
    LogicalCellProductCode rate :=
  (cell.time,
    (cell.physical,
      (cell.numerical,
        (cell.before,
          (cell.after,
            (cell.arrivals,
              (cell.service,
                (cell.slowSet,
                  (cell.fastArm, (cell.proposal, cell.nextSlowSet))))))))))

/-- The code reconstructs the complete accepted logical cell. -/
theorem logicalCellProductCode_injective {rate : RateInput p} :
    Function.Injective (logicalCellProductCode (p := p) (rate := rate)) := by
  intro left right h
  cases left with
  | mk leftTime leftPhysical leftNumerical leftBefore leftAfter leftArrivals
      leftService leftSlow leftFast leftProposal leftNext =>
    cases right with
    | mk rightTime rightPhysical rightNumerical rightBefore rightAfter rightArrivals
        rightService rightSlow rightFast rightProposal rightNext =>
      simp only [logicalCellProductCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

instance firstLiveLogicalCellMeasurableSpace (rate : RateInput p) :
    MeasurableSpace (LogicalCell p rate) :=
  MeasurableSpace.comap (logicalCellProductCode (p := p) (rate := rate)) inferInstance

theorem measurable_logicalCellProductCode {rate : RateInput p} :
    Measurable (logicalCellProductCode (p := p) (rate := rate)) :=
  comap_measurable _

theorem measurable_logicalCell_time {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.time) :=
  measurable_fst.comp measurable_logicalCellProductCode

theorem measurable_logicalCell_physical {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.physical) := by
  exact (measurable_fst.comp (measurable_snd.comp measurable_logicalCellProductCode))

theorem measurable_logicalCell_numerical {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.numerical) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp measurable_logicalCellProductCode))

theorem measurable_logicalCell_before {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.before) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_logicalCellProductCode)))

theorem measurable_logicalCell_after {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.after) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_logicalCellProductCode))))

theorem measurable_logicalCell_arrivals {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.arrivals) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_logicalCellProductCode)))))

theorem measurable_logicalCell_service {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.service) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        measurable_logicalCellProductCode))))))

theorem measurable_logicalCell_slowSet {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.slowSet) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp measurable_logicalCellProductCode)))))))

theorem measurable_logicalCell_fastArm {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.fastArm) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_logicalCellProductCode))))))))

theorem measurable_logicalCell_proposal {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.proposal) := by
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_logicalCellProductCode)))))))))

theorem measurable_logicalCell_nextSlowSet {rate : RateInput p} :
    Measurable (fun cell : LogicalCell p rate => cell.nextSlowSet) := by
  exact measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_logicalCellProductCode)))))))))

/-- The complete physical projection of the constructed path is Borel on the
original source and auxiliary product. The list observation keeps every
round-record field in its accepted product Borel structure. -/
theorem measurable_firstLiveChronologicalPrefix_physicalProjection
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      (firstLiveChronologicalPrefix rate rewards C_star C_h z).map LogicalCell.physical) := by
  have h := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveWindowCensus
    rate rewards C_star C_h).comp
      (measurable_fst : Measurable (fun z : SourceInput p × AuxiliaryArray p => z.1))
  convert h using 1
  funext z
  exact firstLiveChronologicalPrefix_physical rate rewards C_star C_h z.1 z.2

/-- The complete original numerical projection is Borel, including both
whole reward and rate vectors in every logical cell. -/
theorem measurable_firstLiveChronologicalPrefix_numericalProjection
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      (firstLiveChronologicalPrefix rate rewards C_star C_h z).map LogicalCell.numerical) := by
  have h := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveCellReadout
    rate rewards C_star C_h).comp
      (measurable_fst : Measurable (fun z : SourceInput p × AuxiliaryArray p => z.1))
  convert h using 1
  funext z
  exact firstLiveChronologicalPrefix_numerical rate rewards C_star C_h z.1 z.2

/-- The finite path length is Borel on the original source and auxiliary
product, including absent-launch, terminal, and empty-window branches. -/
theorem measurable_firstLiveChronologicalPrefix_length
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      (firstLiveChronologicalPrefix rate rewards C_star C_h z).length) := by
  have h := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveLength
    rate rewards C_star C_h).comp
      (measurable_fst : Measurable (fun z : SourceInput p × AuxiliaryArray p => z.1))
  convert h using 1
  funext z
  exact firstLiveChronologicalPrefix_length rate rewards C_star C_h z

/-- The physical observation graph is Borel with the full source as its first
coordinate and the complete accepted round-record codes as its second. -/
def firstLivePhysicalProjectionGraph (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p × AuxiliaryArray p) :=
  (z.1, (firstLiveChronologicalPrefix rate rewards C_star C_h z).map LogicalCell.physical)

theorem measurable_firstLivePhysicalProjectionGraph
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (firstLivePhysicalProjectionGraph rate rewards C_star C_h) := by
  exact measurable_fst.prodMk
    (measurable_firstLiveChronologicalPrefix_physicalProjection rate rewards C_star C_h)

/-- The measurable physical graph preserves the original source marginal under
the product source and independent auxiliary law. -/
theorem firstLivePhysicalProjectionGraph_sourceMarginal
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (firstLivePhysicalProjectionGraph rate rewards C_star C_h)).map Prod.fst =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
  rw [MeasureTheory.Measure.map_map measurable_fst
    (measurable_firstLivePhysicalProjectionGraph rate rewards C_star C_h)]
  have hfst : Prod.fst ∘ firstLivePhysicalProjectionGraph rate rewards C_star C_h = Prod.fst := by
    funext z
    rfl
  rw [hfst]
  exact ReferenceFirstCollectionAuxiliarySeeds.auxiliarySourceLaw_fst p

/-- Adding the independent auxiliary array leaves the original physical source
law unchanged under the actual product projection. -/
theorem firstLiveAuxiliaryProduct_sourceMarginal (p : Parameters) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map Prod.fst =
        BootstrapPrivateRoundStreams.sourceInputLaw p := by
  exact ReferenceFirstCollectionAuxiliarySeeds.auxiliarySourceLaw_fst p

/-- Source-varying residual refreshes are Borel once the actual finite
residual masses are observed measurably. The fibres are the exact cumulative
CDF intervals from `residualDraw_eq_iff`; no fixed-mass sampling argument is
used. -/
theorem measurable_residualDraw_of_measurable_residualMass
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (state : X → RecordedQueueRun.RunState p.K)
    (round : X → RecordedQueueRun.RoundInput p.K)
    (anchor : X → Fin p.K → ℝ) (hanchor : ∀ x i, 0 < anchor x i)
    (u : X → ContinuousControlSlice.Scalar) (hu : Measurable u)
    (hmass : ∀ U : SlowSet p, Measurable (fun x =>
      RecordedSlowRefresh.residualMass p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state x) (round x) (anchor x) (hanchor x) U)) :
    Measurable (fun x => residualDraw rate (state x) (round x) (anchor x)
      (hanchor x) (u x)) := by
  classical
  let masses (x : X) (k : Fin (Fintype.card (SlowSet p))) :=
    RecordedSlowRefresh.residualMass p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (state x) (round x) (anchor x) (hanchor x) (slowSetEnumeration p k)
  have hm (k : Fin (Fintype.card (SlowSet p))) : Measurable (fun x => masses x k) := by
    exact hmass (slowSetEnumeration p k)
  have hlower (U : SlowSet p) : Measurable (fun x =>
      ContinuousCategorical.lower (masses x) ((slowSetEnumeration p).symm U)) := by
    unfold ContinuousCategorical.lower
    exact Finset.measurable_fun_sum _ fun k _ => hm k
  have hupper (U : SlowSet p) : Measurable (fun x =>
      ContinuousCategorical.upper (masses x) ((slowSetEnumeration p).symm U)) := by
    unfold ContinuousCategorical.upper
    exact Finset.measurable_fun_sum _ fun k _ => hm k
  apply measurable_to_countable'
  intro U
  have hfiber : {x | residualDraw rate (state x) (round x) (anchor x)
      (hanchor x) (u x) = U} =
      {x | ContinuousCategorical.lower (masses x) ((slowSetEnumeration p).symm U) ≤
        (u x).val ∧ (u x).val <
          ContinuousCategorical.upper (masses x) ((slowSetEnumeration p).symm U)} := by
    ext x
    exact residualDraw_eq_iff rate (state x) (round x) (anchor x) (hanchor x)
      (u x) U
  change MeasurableSet {x | residualDraw rate (state x) (round x) (anchor x)
    (hanchor x) (u x) = U}
  rw [hfiber]
  exact (measurableSet_le (hlower U) (measurable_subtype_coe.comp hu)).inter
    (measurableSet_lt (measurable_subtype_coe.comp hu) (hupper U))

private theorem measurable_orientationProbability_varyingAnchor
    {X : Type*} [MeasurableSpace X] (anchor : X → Fin p.K → ℝ)
    (hanchorMap : Measurable anchor) (hpositive : ∀ x i, 0 < anchor x i)
    (S : Finset (Fin p.K)) (hS : S.Nonempty) (j : {j // j ∈ S}) :
    Measurable (fun x => FiniteOrientationDisintegration.orientationProbability
      (anchor x) S hS (fun i _hi => hpositive x i) j) := by
  have hinv (i : Fin p.K) : Measurable (fun x => 1 / anchor x i) :=
    measurable_const.div ((measurable_pi_apply i).comp hanchorMap)
  have hden : Measurable (fun x => ∑ i ∈ S, 1 / anchor x i) := by
    exact Finset.measurable_fun_sum S fun i _ => hinv i
  unfold FiniteOrientationDisintegration.orientationProbability
  exact (hinv j.1).div hden

theorem measurable_recordedSlowMass_varyingStateAnchor
    {X : Type*} [MeasurableSpace X] (q : RecordedQueueRun.Parameters)
    (state : X → RecordedQueueRun.RunState p.K) (hstate : Measurable state)
    (anchor : X → Fin p.K → ℝ) (hanchorMap : Measurable anchor)
    (hpositive : ∀ x i, 0 < anchor x i) (U : SlowSet p) :
    Measurable (fun x => RecordedSlowRefresh.recordedSlowMass p q
      (state x) (anchor x) (hpositive x) U) := by
  classical
  let weights (x : X) (i : Fin p.K) := RecordedQueueRun.scoreWeight q (state x) i
  have hw (i : Fin p.K) : Measurable (fun x => weights x i) := by
    exact (measurable_of_countable (fun s : RecordedQueueRun.RunState p.K =>
      RecordedQueueRun.scoreWeight q s i)).comp hstate
  have hweights : Measurable weights := by
    apply measurable_pi_iff.mpr
    exact hw
  have ha (i : Fin p.K) : Measurable (fun x => anchor x i) :=
    (measurable_pi_apply i).comp hanchorMap
  have hprod (S : Finset (Fin p.K)) : Measurable (fun x => ∏ i ∈ S, weights x i) := by
    exact Finset.measurable_fun_prod S fun i _ => hw i
  have hnormalizer : Measurable (fun x =>
      FiniteOrientationDisintegration.partitionFunction (Finset.univ : Finset (Fin p.K))
        p.m (weights x)) := by
    unfold FiniteOrientationDisintegration.partitionFunction
    exact Finset.measurable_fun_sum _ fun S _ => hprod S
  have hterm (j : {j // j ∈ (Finset.univ : Finset (Fin p.K)) \ U.1}) :
      Measurable (fun x => FiniteOrientationDisintegration.orientedJointMass
        (Finset.univ : Finset (Fin p.K)) p.m (weights x) (anchor x) U.1
        (Finset.subset_univ _) (CanonicalOrientedSetLaw.slowSet_card p.two_le_m U)
        (fun i _ => RecordedSlowRefresh.scoreWeight_pos q (state x) i)
        (fun i _ => hpositive x i) j) := by
    have hprob := measurable_orientationProbability_varyingAnchor (p := p)
      anchor hanchorMap hpositive (insert j.1 U.1) (Finset.insert_nonempty _ _)
        ⟨j.1, Finset.mem_insert_self _ _⟩
    have hfactor : Measurable (fun x =>
        (∏ i ∈ insert j.1 U.1, weights x i) /
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin p.K)) p.m (weights x)) :=
      (hprod (insert j.1 U.1)).div hnormalizer
    unfold FiniteOrientationDisintegration.orientedJointMass
    exact hfactor.mul hprob
  unfold RecordedSlowRefresh.recordedSlowMass CanonicalOrientedSetLaw.slowMarginal
    FiniteOrientationDisintegration.slowMarginal
  apply Finset.measurable_fun_sum
  intro j hj
  exact hterm j

/-- The finite canonical slow marginal is Borel in a varying positive anchor
and discrete all-arm register state. -/
theorem measurable_residualMass_of_prePost
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (before after : X → RecordedQueueRun.RunState p.K)
    (hbefore : Measurable before) (hafter : Measurable after)
    (anchor : X → Fin p.K → ℝ) (hanchorMap : Measurable anchor)
    (hpositive : ∀ x i, 0 < anchor x i) (U : SlowSet p) :
    Measurable (fun x =>
      (RecordedSlowRefresh.recordedSlowMass p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (after x) (anchor x) (hpositive x) U -
       (1 - RecordedSlowRefresh.hazard p
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)) *
         RecordedSlowRefresh.recordedSlowMass p
           (ReferenceFirstLaunchNumericalCell.queueParameters rate)
           (before x) (anchor x) (hpositive x) U) /
         RecordedSlowRefresh.hazard p
           (ReferenceFirstLaunchNumericalCell.queueParameters rate)) := by
  have hafterMass := measurable_recordedSlowMass_varyingStateAnchor
    (p := p) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    after hafter anchor hanchorMap hpositive U
  have hbeforeMass := measurable_recordedSlowMass_varyingStateAnchor
    (p := p) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    before hbefore anchor hanchorMap hpositive U
  fun_prop

/-- The source-varying mass above is the exact accepted residual mass whenever
the post-state is the canonical actual queue update. -/
theorem measurable_residualMass_of_actualStep
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (before after : X → RecordedQueueRun.RunState p.K)
    (round : X → RecordedQueueRun.RoundInput p.K)
    (hbefore : Measurable before) (hafter : Measurable after)
    (hstep : ∀ x, after x = RecordedQueueRun.step
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (before x) (round x))
    (anchor : X → Fin p.K → ℝ) (hanchorMap : Measurable anchor)
    (hpositive : ∀ x i, 0 < anchor x i) (U : SlowSet p) :
    Measurable (fun x => RecordedSlowRefresh.residualMass p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (before x) (round x) (anchor x) (hpositive x) U) := by
  have hm := measurable_residualMass_of_prePost (p := p) rate before after
    hbefore hafter anchor hanchorMap hpositive U
  convert hm using 1
  funext x
  rw [RecordedSlowRefresh.residualMass, hstep x]

/-- The exact source-varying residual draw is Borel from measurable PRE and
POST canonical states, their actual queue-step identity, and the actual
positive anchor and auxiliary scalar. -/
theorem measurable_residualDraw_of_actualPrePost
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (before after : X → RecordedQueueRun.RunState p.K)
    (round : X → RecordedQueueRun.RoundInput p.K)
    (hbefore : Measurable before) (hafter : Measurable after)
    (hstep : ∀ x, after x = RecordedQueueRun.step
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (before x) (round x))
    (anchor : X → Fin p.K → ℝ) (hanchorMap : Measurable anchor)
    (hpositive : ∀ x i, 0 < anchor x i)
    (u : X → ContinuousControlSlice.Scalar) (hu : Measurable u) :
    Measurable (fun x => residualDraw rate (before x) (round x) (anchor x)
      (hpositive x) (u x)) := by
  apply measurable_residualDraw_of_measurable_residualMass rate before round anchor
    hpositive u hu
  intro U
  exact measurable_residualMass_of_actualStep rate before after round hbefore hafter
    hstep anchor hanchorMap hpositive U

/-- Fast complement sampling remains Borel when both the full anchor and the
actual complement weights vary. The fixed-slow-set branch is explicit so no
fixed-complement-weight assumption is hidden in the sampler. -/
theorem measurable_sampleLocalFast_varyingWeights
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (U : SlowSet p) (v : X → Fin p.K → ℝ) (hv : Measurable v)
    (w : X → CanonicalFastSampling.FastArm U → ℝ) (hw : Measurable w)
    (hpos : ∀ x i, 0 < v x i) (hwpos : ∀ x j, 0 < w x j)
    (hlow : ∀ x j, v x j.1 ≤ w x j) (hhigh : ∀ x j, w x j ≤ 2 * v x j.1)
    (u : X → ContinuousControlSlice.Scalar) (hu : Measurable u) :
    Measurable (fun x => FastComplementLocality.sampleLocalFast p rate.eta.val
      rate.eta.property rate.sourceCap (v x) (hpos x) U (w x) (hwpos x)
      (hlow x) (hhigh x) (u x)) := by
  classical
  have hc (j : CanonicalFastSampling.FastArm U) : Measurable (fun x =>
      localFastCandidateMass (v x) U (w x) j) := by
    unfold localFastCandidateMass FiniteOrientationDisintegration.inverseAnchorSum
    exact ((measurable_pi_apply j).comp hw).div (measurable_const.add
      ((Finset.measurable_fun_sum U.val fun i _ =>
        measurable_const.div ((measurable_pi_apply i).comp hv)).mul
          ((measurable_pi_apply j.1).comp hv)))
  have hn : Measurable (fun x => localFastNormalizer (v x) U (w x)) :=
    Finset.measurable_fun_sum Finset.univ fun j _ => hc j
  let masses (x : X) (k : Fin (p.K - p.m + 1)) :=
    localFastLaw p rate.eta.val rate.eta.property rate.sourceCap
      (v x) U (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (fastArmOrderIso U k)
  have hm (k : Fin (p.K - p.m + 1)) : Measurable (fun x => masses x k) :=
    (measurable_const.mul ((hc _).div hn)).add measurable_const
  have hsum (x : X) : ∑ k, masses x k = 1 := by
    change (∑ k, localFastLaw p rate.eta.val rate.eta.property rate.sourceCap
      (v x) U (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (fastArmOrderIso U k)) = 1
    calc
      _ = ∑ j : CanonicalFastSampling.FastArm U,
          localFastLaw p rate.eta.val rate.eta.property rate.sourceCap
            (v x) U (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) j :=
        Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := localFastLaw_sum_eq_one p rate.eta.property rate.sourceCap
        (v x) (hpos x) U (w x) (hwpos x) (hlow x) (hhigh x)
  have hnonneg (x : X) (k : Fin (p.K - p.m + 1)) : 0 ≤ masses x k :=
    (localFastLaw_pos p rate.eta.property rate.sourceCap
      (v x) (hpos x) U (w x) (hwpos x) (hlow x) (hhigh x) _).le
  apply measurable_to_countable'
  intro j
  have hfiber : {x | sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap (v x) (hpos x) U (w x) (hwpos x) (hlow x) (hhigh x) (u x) = j} =
      {x | ContinuousCategorical.lower (masses x) ((fastArmOrderIso U).symm j) ≤
        (u x).val ∧ (u x).val <
          ContinuousCategorical.upper (masses x) ((fastArmOrderIso U).symm j)} := by
    ext x
    change fastArmOrderIso U (ContinuousCategorical.sample _ (masses x) (hsum x) (u x)) = j ↔ _
    rw [← OrderIso.eq_symm_apply]
    exact ContinuousCategorical.sample_eq_iff _ (hnonneg x) (hsum x) _ _
  change MeasurableSet {x | sampleLocalFast p rate.eta.val rate.eta.property
    rate.sourceCap (v x) (hpos x) U (w x) (hwpos x) (hlow x) (hhigh x) (u x) = j}
  rw [hfiber]
  exact (measurableSet_le
    (Finset.measurable_fun_sum _ fun k _ => hm k)
    (measurable_subtype_coe.comp hu)).inter
      (measurableSet_lt (measurable_subtype_coe.comp hu)
        (Finset.measurable_fun_sum _ fun k _ => hm k))

private theorem measurable_of_countable_code_fibers
    {X β γ : Type*} [MeasurableSpace X] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : X → β) (hkey : Measurable key) (f : X → γ)
    (hf : ∀ b, Measurable (fun x : {x // key x = b} => f x.val)) : Measurable f := by
  classical
  intro s hs
  have heq : f ⁻¹' s = ⋃ b, (Subtype.val : {x // key x = b} → X) ''
      ((fun x : {x // key x = b} => f x.val) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨key x, ⟨x, rfl⟩, hx, rfl⟩
    · rintro ⟨b, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun b =>
    MeasurableSet.subtype_image ((measurableSet_singleton b).preimage hkey) (hf b hs)

private theorem measurable_of_slowSet_fibers
    {X γ : Type*} [MeasurableSpace X] [MeasurableSpace γ]
    (key : X → SlowSet p) (hkey : Measurable key) (f : X → γ)
    (hf : ∀ U, Measurable (fun x : {x // key x = U} => f x.val)) :
    Measurable f :=
  measurable_of_countable_code_fibers key hkey f hf

private theorem sampleLocalFast_value_congr_slowSet
    (rate : RateInput p) (anchor : Fin p.K → ℝ) (hpositive : ∀ i, 0 < anchor i)
    (U V : SlowSet p) (weights : Fin p.K → ℝ)
    (hweightPositiveU : ∀ j : CanonicalFastSampling.FastArm U, 0 < weights j.1)
    (hweightLowerU : ∀ j : CanonicalFastSampling.FastArm U, anchor j.1 ≤ weights j.1)
    (hweightUpperU : ∀ j : CanonicalFastSampling.FastArm U, weights j.1 ≤ 2 * anchor j.1)
    (hweightPositiveV : ∀ j : CanonicalFastSampling.FastArm V, 0 < weights j.1)
    (hweightLowerV : ∀ j : CanonicalFastSampling.FastArm V, anchor j.1 ≤ weights j.1)
    (hweightUpperV : ∀ j : CanonicalFastSampling.FastArm V, weights j.1 ≤ 2 * anchor j.1)
    (u : ContinuousControlSlice.Scalar) (hUV : U = V) :
    (FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap anchor hpositive U (fun j => weights j.1) hweightPositiveU
      hweightLowerU hweightUpperU u).1 =
    (FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap anchor hpositive V (fun j => weights j.1) hweightPositiveV
      hweightLowerV hweightUpperV u).1 := by
  cases hUV
  rfl

/-- Fast complement sampling with a varying finite slow set, full anchor, and
full current-weight vector is Borel. Each slow-set fibre uses the exact
varying-weight finite CDF proved above. -/
theorem measurable_sampleLocalFast_varyingSlowSet
    {X : Type*} [MeasurableSpace X] (rate : RateInput p)
    (slow : X → SlowSet p) (hslow : Measurable slow)
    (anchor : X → Fin p.K → ℝ) (hanchor : Measurable anchor)
    (weights : X → Fin p.K → ℝ) (hweights : Measurable weights)
    (hpositive : ∀ x i, 0 < anchor x i)
    (hweightPositive : ∀ x i, i ∉ (slow x).val → 0 < weights x i)
    (hweightLower : ∀ x i, i ∉ (slow x).val → anchor x i ≤ weights x i)
    (hweightUpper : ∀ x i, i ∉ (slow x).val → weights x i ≤ 2 * anchor x i)
    (u : X → ContinuousControlSlice.Scalar) (hu : Measurable u) :
    Measurable (fun x =>
      (FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
        rate.sourceCap (anchor x) (hpositive x) (slow x)
        (fun j => weights x j.1)
        (fun j => hweightPositive x j.1 (Finset.mem_sdiff.mp j.2).2)
        (fun j => hweightLower x j.1 (Finset.mem_sdiff.mp j.2).2)
        (fun j => hweightUpper x j.1 (Finset.mem_sdiff.mp j.2).2) (u x)).1) := by
  classical
  apply measurable_of_slowSet_fibers slow hslow _
  intro U
  let fiber := {x : X // slow x = U}
  let anchorU : fiber → Fin p.K → ℝ := fun x => anchor x.val
  let weightsU : fiber → Fin p.K → ℝ := fun x => weights x.val
  let scalarU : fiber → ContinuousControlSlice.Scalar := fun x => u x.val
  have hanchorU : Measurable anchorU := hanchor.comp measurable_subtype_coe
  have hweightsU : Measurable weightsU := hweights.comp measurable_subtype_coe
  have hscalarU : Measurable scalarU := hu.comp measurable_subtype_coe
  have hpositiveU (x : fiber) i : 0 < anchorU x i := hpositive x.val i
  have hweightPositiveU (x : fiber) (j : CanonicalFastSampling.FastArm U) :
      0 < weightsU x j.1 := by
    have hnotU : j.1 ∉ U.val := (Finset.mem_sdiff.mp j.2).2
    have hnot : j.1 ∉ (slow x.val).val := by simpa [x.property] using hnotU
    exact hweightPositive x.val j.1 hnot
  have hweightLowerU (x : fiber) (j : CanonicalFastSampling.FastArm U) :
      anchorU x j.1 ≤ weightsU x j.1 := by
    have hnotU : j.1 ∉ U.val := (Finset.mem_sdiff.mp j.2).2
    have hnot : j.1 ∉ (slow x.val).val := by simpa [x.property] using hnotU
    exact hweightLower x.val j.1 hnot
  have hweightUpperU (x : fiber) (j : CanonicalFastSampling.FastArm U) :
      weightsU x j.1 ≤ 2 * anchorU x j.1 := by
    have hnotU : j.1 ∉ U.val := (Finset.mem_sdiff.mp j.2).2
    have hnot : j.1 ∉ (slow x.val).val := by simpa [x.property] using hnotU
    exact hweightUpper x.val j.1 hnot
  let fastSample (x : fiber) : CanonicalFastSampling.FastArm U :=
    FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
      rate.sourceCap (anchorU x) (hpositiveU x) U
      (fun j => weightsU x j.1) (hweightPositiveU x)
      (hweightLowerU x) (hweightUpperU x) (scalarU x)
  have hlocal : Measurable fastSample := measurable_sampleLocalFast_varyingWeights
    (p := p) rate U anchorU hanchorU
    (fun x j => weightsU x j.1) (by
      apply measurable_pi_iff.mpr
      intro j
      exact (measurable_pi_apply j.1).comp hweightsU)
    hpositiveU hweightPositiveU hweightLowerU hweightUpperU scalarU hscalarU
  have htarget : (fun x : fiber =>
      (FastComplementLocality.sampleLocalFast p rate.eta.val rate.eta.property
        rate.sourceCap (anchor x.val) (hpositive x.val) (slow x.val)
        (fun j => weights x.val j.1)
        (fun j => hweightPositive x.val j.1 (Finset.mem_sdiff.mp j.2).2)
        (fun j => hweightLower x.val j.1 (Finset.mem_sdiff.mp j.2).2)
        (fun j => hweightUpper x.val j.1 (Finset.mem_sdiff.mp j.2).2) (u x.val)).1) =
      fun x => (fastSample x).1 := by
    funext x
    exact sampleLocalFast_value_congr_slowSet (p := p) rate (anchor x.val)
      (hpositive x.val) (slow x.val) U (weights x.val)
      (fun j => hweightPositive x.val j.1 (Finset.mem_sdiff.mp j.2).2)
      (fun j => hweightLower x.val j.1 (Finset.mem_sdiff.mp j.2).2)
      (fun j => hweightUpper x.val j.1 (Finset.mem_sdiff.mp j.2).2)
      (hweightPositiveU x) (hweightLowerU x) (hweightUpperU x) (u x.val) x.property
  rw [htarget]
  exact measurable_subtype_coe.comp hlocal


private theorem measurable_of_inr {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α] (f : X → α)
    (hf : Measurable (fun x => (Sum.inr (f x) : Unit ⊕ α))) : Measurable f := by
  intro u hu
  convert hf hu.inr_image using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Sum.inr.injEq, exists_eq_right]

private theorem measurable_of_some {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α] (f : X → α)
    (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hsum := (comap_measurable (Equiv.optionEquivSumPUnit α)).comp hf
  have hinl : MeasurableEmbedding (@Sum.inl α PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp hsum

private theorem measurable_list_get {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hrecords : Measurable records)
    (k : ℕ) (hk : ∀ x, k < (records x).length) :
    Measurable (fun x => (records x)[k]'(hk x)) := by
  apply measurable_of_inr
  have h := (measurable_pi_apply k).comp (measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords))
  simpa only [Function.comp_def, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt,
    List.getElem?_eq_getElem (hk _)] using h

private theorem measurable_list_take {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hrecords : Measurable records) (n : ℕ) :
    Measurable (fun x => (records x).take n) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords
  apply measurable_comap_iff.mpr
  have hlen : Measurable (fun x => min n (records x).length) :=
    (measurable_of_countable (fun l : ℕ => min n l)).comp (measurable_fst.comp hc)
  change Measurable (fun x => (((records x).take n).length,
    fun j => ReferenceActiveHorizonMeasurability.listObservationAt ((records x).take n) j))
  simp only [List.length_take]
  apply hlen.prodMk
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < n
  · simpa only [Function.comp_def, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
      ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take,
      hj, ite_true] using
        (measurable_pi_apply j).comp (measurable_snd.comp hc)
  · have heq : (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
        ((records x).take n) j) = fun _ => (Sum.inl () : Unit ⊕ α) := by
      funext x
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_take, hj, ite_false]
    rw [heq]
    exact measurable_const

private instance firstLiveSumSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := ⟨fun tag => by
      cases tag with
      | inl value => simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inl_image
      | inr value => simpa only [Set.image_singleton] using
          (measurableSet_singleton value).inr_image⟩

private instance firstLiveListSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
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
  have heq : ({records} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private abbrev ArrivalCode (K : ℕ) := Bool × (Fin K → ℕ)

private def arrivalCode (q : RecordedQueueRun.Parameters)
    (cell : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) : ArrivalCode p.K :=
  (cell.1, fun i => if cell.2.1 = some i then
    Nat.floor ((q.n : ℝ) * cell.2.2.1 i / cell.2.2.2 i) else 0)

private theorem measurable_arrivalCode (q : RecordedQueueRun.Parameters) :
    Measurable (arrivalCode (p := p) q) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro i
  have hm : Measurable (fun c : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p =>
      c.2.1) := measurable_fst.comp measurable_snd
  have hr : Measurable (fun c : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p =>
      c.2.2.1 i) := (measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hx : Measurable (fun c : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p =>
      c.2.2.2 i) := (measurable_pi_apply i).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact (Nat.measurable_floor.comp ((measurable_const.mul hr).div hx)).ite
    ((measurableSet_singleton (some i)).preimage hm) measurable_const

private def acceptedCode (state : RecordedQueueRun.RunState p.K)
    (code : ArrivalCode p.K) (i : Fin p.K) : Bool × ℕ :=
  if state.overflow then (false, 0) else if code.1 then (true, code.2 i) else (false, 0)

/-- This is the existing queue transition factored through its countable
arrival coordinates, including its complete accepted-record history. -/
private def stepArrivalCode (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (code : ArrivalCode p.K) :
    RecordedQueueRun.RunState p.K := by
  classical
  let records := acceptedCode state code
  let registers := fun i => QueueReplay.transition (4 * q.n) (state.registers i) (records i)
  exact ⟨registers, state.overflow || decide (∃ i, 32 * (registers i).2 > q.D),
    fun i => state.records i ++ [records i]⟩

private def numericalCode (round : RecordedQueueRun.RoundInput p.K) :
    ReferenceFirstLiveOverflowReadout.NumericalCellReadout p :=
  (round.enabled, (round.recordedArm, (round.reward, round.rate)))

private theorem stepArrivalCode_eq (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K) :
    stepArrivalCode q state (arrivalCode q (numericalCode round)) =
      RecordedQueueRun.step q state round := by
  rfl

private theorem foldArrivalCode_eq (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) :
    ((rounds.map numericalCode).map (arrivalCode q)).foldl (stepArrivalCode q) state =
      RecordedQueueRun.execute q rounds state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
    simpa only [List.map_cons, List.foldl_cons, RecordedQueueRun.execute,
      stepArrivalCode_eq] using ih (RecordedQueueRun.step q state round)

private theorem measurable_queueRun_of_readout {X : Type*} [MeasurableSpace X]
    (q : RecordedQueueRun.Parameters) (rounds : X → List (RecordedQueueRun.RoundInput p.K))
    (hrounds : Measurable (fun x => (rounds x).map numericalCode)) :
    Measurable (fun x => RecordedQueueRun.run q (rounds x)) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_list_map _ hrounds
    (arrivalCode q) (measurable_arrivalCode q)
  have hf : Measurable (fun codes : List (ArrivalCode p.K) =>
      codes.foldl (stepArrivalCode q) (RecordedQueueRun.initialState p.K)) :=
    measurable_of_countable _
  convert hf.comp hc using 1
  funext x
  exact (foldArrivalCode_eq q (rounds x) (RecordedQueueRun.initialState p.K)).symm

/-- The entire canonical zero-origin queue state after any fixed number of
actual first-live cells is Borel on the whole original source. In particular,
this observes every register, overflow flag and chronological record list. -/
theorem measurable_wholeFirstLiveQueuePrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) (k : ℕ) :
    Measurable (fun source : SourceInput p => RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source).take k)) := by
  apply measurable_queueRun_of_readout
  have h := measurable_list_take _
    (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveCellReadout
      rate rewards C_star C_h) k
  change Measurable (fun source => ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    rate rewards C_star C_h source).take k).map
      (fun c => (c.enabled, (c.recordedArm, (c.reward, c.rate)))))
  simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout, List.map_take] using h


section ActualFields

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)

/-- The actual indexed domain; there is no padded logical cell. -/
private abbrev PresentSource (k : ℕ) :=
  {z : SourceInput p × AuxiliaryArray p //
    k < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.1}

private def presentRecord (k : ℕ) (z : PresentSource rate rewards C_star C_h k) :
    Record rate :=
  (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val.1)[k]'z.property

private def presentWitness (k : ℕ) (z : PresentSource rate rewards C_star C_h k) :=
  wholeLiveCell rate rewards C_star C_h z.val.1
    (presentRecord rate rewards C_star C_h k z) (List.getElem_mem z.property)

private def presentBefore (k : ℕ) (z : PresentSource rate rewards C_star C_h k) :=
  RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val.1).take k)

private theorem wholeWindow_prefix (source : SourceInput p) :
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h source <+:
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h :=
  List.takeWhile_prefix _

private def presentSuffixSource (k : ℕ) (z : PresentSource rate rewards C_star C_h k) :
    ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k :=
  ⟨z.val.1, lt_of_lt_of_le z.property (wholeWindow_prefix rate rewards C_star C_h z.val.1).length_le⟩

private theorem presentRecord_eq_suffix (k : ℕ)
    (z : PresentSource rate rewards C_star C_h k) :
    presentRecord rate rewards C_star C_h k z =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val.1 rewards C_star C_h)[k]'(presentSuffixSource rate rewards C_star C_h k z).property :=
  (wholeWindow_prefix rate rewards C_star C_h z.val.1).getElem z.property

private theorem measurable_presentInput (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      (presentRecord rate rewards C_star C_h k z).input) := by
  have hm : Measurable (presentSuffixSource rate rewards C_star C_h k) :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk
  convert (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
    rate rewards C_star C_h k).comp hm using 1
  funext z
  exact congrArg (fun r : Record rate => r.input)
    (presentRecord_eq_suffix rate rewards C_star C_h k z)

private theorem measurable_presentPhysical (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      ReferenceActiveHorizonMeasurability.roundRecordCode
        (presentRecord rate rewards C_star C_h k z)) := by
  have hm : Measurable (presentSuffixSource rate rewards C_star C_h k) :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk
  convert (ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
    rate rewards C_star C_h k).comp hm using 1
  funext z
  exact congrArg ReferenceActiveHorizonMeasurability.roundRecordCode
    (presentRecord_eq_suffix rate rewards C_star C_h k z)

private theorem measurable_presentNumerical (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      numericalCode (presentWitness rate rewards C_star C_h k z).input) := by
  have hm := (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveCellReadout
    rate rewards C_star C_h).comp (measurable_fst.comp
      (measurable_subtype_coe : Measurable (fun z : PresentSource rate rewards C_star C_h k => z.val)))
  have hlen (z : PresentSource rate rewards C_star C_h k) :
      k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout
        rate rewards C_star C_h z.val.1).length := by
    simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCellReadout, List.length_map,
      wholeFirstLiveCells_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using z.property
  convert measurable_list_get _ hm k hlen using 1
  funext z
  exact (congrArg numericalCode (wholeLiveCell_input_eq rate rewards C_star C_h z.val.1
    ⟨k, z.property⟩)).trans (List.getElem_map numericalCode).symm

private theorem measurable_presentBefore (k : ℕ) :
    Measurable (presentBefore rate rewards C_star C_h k) :=
  (measurable_wholeFirstLiveQueuePrefix rate rewards C_star C_h k).comp
    (measurable_fst.comp measurable_subtype_coe)

private theorem measurable_presentAfter (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k => RecordedQueueRun.step
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (presentBefore rate rewards C_star C_h k z)
      (presentWitness rate rewards C_star C_h k z).input) := by
  have hm := (measurable_wholeFirstLiveQueuePrefix rate rewards C_star C_h (k + 1)).comp
    (measurable_fst.comp
      (measurable_subtype_coe : Measurable (fun z : PresentSource rate rewards C_star C_h k => z.val)))
  convert hm using 1
  funext z
  have hk : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val.1).length := by
    rw [wholeFirstLiveCells_length]
    exact z.property
  dsimp only [Function.comp_def]
  rw [RecordedPotentialStep.run_take_succ_eq_step _ _ k hk]
  rw [← wholeLiveCell_input_eq rate rewards C_star C_h z.val.1 ⟨k, z.property⟩]
  rfl

/-- The actual selection is recovered through the stored full physical code
and its proved `some` equation, rather than by a measurable-choice assumption. -/
private theorem measurable_presentView (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      (presentWitness rate rewards C_star C_h k z).selected.view) := by
  have hm : Measurable (fun z : PresentSource rate rewards C_star C_h k =>
      (ReferenceActiveHorizonMeasurability.roundRecordCode
        (presentRecord rate rewards C_star C_h k z)).2.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_presentPhysical rate rewards C_star C_h k))))
  have hsome : Measurable (fun z : PresentSource rate rewards C_star C_h k =>
      some (ReferenceLiveDispatchOutputMeasurability.encodeSelection
        (presentWitness rate rewards C_star C_h k z).selected)) := by
    convert hm using 1
    funext z
    have hfront := (ReferenceActiveHorizonMeasurability.roundRecordCode_front
      (presentRecord rate rewards C_star C_h k z)).1
    rw [hfront]
    have hs := (presentWitness rate rewards C_star C_h k z).selection_actual
    have hout := (presentRecord rate rewards C_star C_h k z).output_eq
    have heq : (presentRecord rate rewards C_star C_h k z).output.preparation.coordinator.selection =
        (ReferenceActivePhysicalStep.dispatch
          (presentRecord rate rewards C_star C_h k z).input).selection := by
      rw [hout]
      rfl
    rw [← heq, hs]
    rfl
  exact measurable_fst.comp (measurable_of_some _ hsome)

private theorem measurable_presentAnchor (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      (presentWitness rate rewards C_star C_h k z).selected.view.payload.anchor) := by
  have hview := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_presentView rate rewards C_star C_h k)
  exact AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_fst.comp hview)

private theorem measurable_presentSlowSet (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      (presentWitness rate rewards C_star C_h k z).selected.view.payload.slowSet) := by
  have hview := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_presentView rate rewards C_star C_h k)
  have hp := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst.comp hview)
  have hs := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hp))
  apply measurable_to_countable'
  intro U
  have heq : {z : PresentSource rate rewards C_star C_h k |
      (presentWitness rate rewards C_star C_h k z).selected.view.payload.slowSet = U} =
      {z | (presentWitness rate rewards C_star C_h k z).selected.view.payload.slowSet.val = U.val} := by
    ext z
    exact Subtype.ext_iff
  change MeasurableSet {z | (presentWitness rate rewards C_star C_h k z).selected.view.payload.slowSet = U}
  rw [heq]
  exact (measurableSet_singleton U.val).preimage hs

private theorem measurable_presentWeights (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
        (presentWitness rate rewards C_star C_h k z).selected.view) := by
  have hview := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_presentView rate rewards C_star C_h k)
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hview))


private theorem measurable_presentFastScalar (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        ((presentRecord rate rewards C_star C_h k z).input.row.2
          (presentRecord rate rewards C_star C_h k z).input.time).1) := by
  have hi := measurable_presentInput rate rewards C_star C_h k
  have heval : Measurable (fun v : Fin p.T × ContinuousLearningRows.LearningRow p =>
      (v.2 v.1).1) :=
    measurable_from_prod_countable_right fun t => measurable_fst.comp (measurable_pi_apply t)
  exact (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast).comp
    (heval.comp ((ReferenceActivePhysicalStepMeasurability.measurable_time.comp hi).prodMk
      (measurable_snd.comp (ReferenceActivePhysicalStepMeasurability.measurable_row.comp hi))))

private theorem measurable_presentReservedFast (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      (reservedFastArm (presentRecord rate rewards C_star C_h k z)
        (presentWitness rate rewards C_star C_h k z)).val) := by
  classical
  let cell := presentWitness rate rewards C_star C_h k
  let weights := fun z => ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
    (cell z).selected.view
  have hweights (z : PresentSource rate rewards C_star C_h k)
      (i : Fin p.K) (hi : i ∉ (cell z).selected.view.payload.slowSet.val) :
      weights z i = (cell z).selected.view.complementWeights
        ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩ := by
    simp only [weights, ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector,
      dite_eq_left (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)]
  have hpos (z : PresentSource rate rewards C_star C_h k) i
      (hi : i ∉ (cell z).selected.view.payload.slowSet.val) : 0 < weights z i := by
    rw [hweights z i hi]
    exact (cell z).choiceInputsValid.current_weight_pos _
  have hlo (z : PresentSource rate rewards C_star C_h k) i
      (hi : i ∉ (cell z).selected.view.payload.slowSet.val) :
      (cell z).selected.view.payload.anchor i ≤ weights z i := by
    rw [hweights z i hi]
    exact (cell z).choiceInputsValid.anchor_le_current
      ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hhi (z : PresentSource rate rewards C_star C_h k) i
      (hi : i ∉ (cell z).selected.view.payload.slowSet.val) :
      weights z i ≤ 2 * (cell z).selected.view.payload.anchor i := by
    rw [hweights z i hi]
    exact (cell z).choiceInputsValid.current_le_twice_anchor _
  have hm := measurable_sampleLocalFast_varyingSlowSet rate
    (fun z => (cell z).selected.view.payload.slowSet)
    (measurable_presentSlowSet rate rewards C_star C_h k)
    (fun z => (cell z).selected.view.payload.anchor)
    (measurable_presentAnchor rate rewards C_star C_h k)
    weights (measurable_presentWeights rate rewards C_star C_h k)
    (fun z => (cell z).choiceInputsValid.anchor_pos) hpos hlo hhi
    _ (measurable_presentFastScalar rate rewards C_star C_h k)
  convert hm using 1
  funext z
  have hw : (fun j : FastArm (cell z).selected.view.payload.slowSet => weights z j.val) =
      (cell z).selected.view.complementWeights := by
    funext j
    exact hweights z j.val (Finset.mem_sdiff.mp j.property).2
  dsimp only [reservedFastArm]
  apply congrArg Subtype.val
  congr 1
  exact hw.symm

private theorem measurable_presentCell (k : ℕ) : Measurable
    (fun z : PresentSource rate rewards C_star C_h k =>
      appendLogicalCell (presentRecord rate rewards C_star C_h k z)
        (presentWitness rate rewards C_star C_h k z)
        (presentBefore rate rewards C_star C_h k z) z.val.2) := by
  classical
  let record := presentRecord rate rewards C_star C_h k
  let cell := presentWitness rate rewards C_star C_h k
  let before := presentBefore rate rewards C_star C_h k
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hb := measurable_presentBefore rate rewards C_star C_h k
  have hn := measurable_presentNumerical rate rewards C_star C_h k
  have hi := measurable_presentInput rate rewards C_star C_h k
  have ht := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hi
  have ho : Measurable (fun z => (before z).overflow) :=
    (measurable_of_countable (fun s : RecordedQueueRun.RunState p.K => s.overflow)).comp hb
  have hcut : MeasurableSet {z | (before z).overflow = true} :=
    (measurableSet_singleton true).preimage ho
  have harrivals : Measurable (fun z => RecordedQueueRun.acceptedRecord q (before z)
      (cell z).input) := by
    have h := (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × ArrivalCode p.K =>
      acceptedCode v.1 v.2)).comp (hb.prodMk ((measurable_arrivalCode q).comp hn))
    exact h
  have hservice : Measurable (fun z => fun i => RecordedQueueRun.recordService (4 * q.n)
      ((before z).registers i) (RecordedQueueRun.acceptedRecord q (before z) (cell z).input i)) :=
    (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
      fun i => RecordedQueueRun.recordService (4 * q.n) (v.1.registers i) (v.2 i))).comp
        (hb.prodMk harrivals)
  have hslow : Measurable (fun z => if (before z).overflow then frozenSlowSet p
      else (cell z).selected.view.payload.slowSet) :=
    (measurable_const (a := frozenSlowSet p)).ite hcut
      (measurable_presentSlowSet rate rewards C_star C_h k)
  have hfast : Measurable (fun z => if (before z).overflow then frozenFastArm p
      else (reservedFastArm (record z) (cell z)).val) :=
    (measurable_const (a := frozenFastArm p)).ite hcut
      (measurable_presentReservedFast rate rewards C_star C_h k)
  let proposal := fun z => !(before z).overflow &&
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val (record z).input.row
      (record z).input.time
  have hp : Measurable proposal :=
    (measurable_of_countable (fun v : Bool × Bool => !v.1 && v.2)).comp
      (ho.prodMk ((FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
        p rate.eta.val).comp
          ((ReferenceActivePhysicalStepMeasurability.measurable_row.comp hi).prodMk ht)))
  have heval : Measurable (fun v : Fin p.T × AuxiliaryArray p => v.2 (v.1, 1)) :=
    measurable_from_prod_countable_right fun t => measurable_pi_apply (t, 1)
  have hu : Measurable (fun z : PresentSource rate rewards C_star C_h k =>
      z.val.2 ((record z).input.time, 1)) :=
    heval.comp (ht.prodMk (measurable_snd.comp measurable_subtype_coe))
  have hrefresh := measurable_residualDraw_of_actualPrePost rate before
    (fun z => RecordedQueueRun.step q (before z) (cell z).input)
    (fun z => (cell z).input) hb (measurable_presentAfter rate rewards C_star C_h k)
    (fun _ => rfl) (fun z => (cell z).selected.view.payload.anchor)
    (measurable_presentAnchor rate rewards C_star C_h k)
    (fun z => (cell z).selected.view.payload.anchor_pos) _ hu
  have hnext : Measurable (fun z => if (before z).overflow then frozenSlowSet p
      else if proposal z then residualDraw rate (before z) (cell z).input
        (cell z).selected.view.payload.anchor (cell z).selected.view.payload.anchor_pos
          (z.val.2 ((record z).input.time, 1))
      else (cell z).selected.view.payload.slowSet) :=
    (measurable_const (a := frozenSlowSet p)).ite hcut
      (hrefresh.ite ((measurableSet_singleton true).preimage hp)
        (measurable_presentSlowSet rate rewards C_star C_h k))
  apply measurable_comap_iff.mpr
  exact ht.prodMk ((measurable_presentPhysical rate rewards C_star C_h k).prodMk
    (hn.prodMk (hb.prodMk ((measurable_presentAfter rate rewards C_star C_h k).prodMk
      (harrivals.prodMk (hservice.prodMk (hslow.prodMk (hfast.prodMk (hp.prodMk hnext)))))))))

end ActualFields


/-- The SAME complete chronological logical prefix is Borel on the whole
original source and independent auxiliary array. Every logical-cell field is
retained, with continuous coordinates in their original product Borel spaces.
The index-domain split includes no launch, terminal launch and empty windows. -/
theorem measurable_firstLiveChronologicalPrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (firstLiveChronologicalPrefix rate rewards C_star C_h) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z : SourceInput p × AuxiliaryArray p =>
    ((firstLiveChronologicalPrefix rate rewards C_star C_h z).length,
      fun k => ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h z) k))
  apply (measurable_firstLiveChronologicalPrefix_length rate rewards C_star C_h).prodMk
  apply measurable_pi_iff.mpr
  intro k
  have hl : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.1) :=
    (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveLength
      rate rewards C_star C_h).comp measurable_fst
  have hdom : MeasurableSet {z : SourceInput p × AuxiliaryArray p |
      k < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.1} :=
    measurableSet_lt measurable_const hl
  apply measurable_of_restrict_of_restrict_compl hdom
  · have hm := (measurable_inr : Measurable (@Sum.inr Unit (LogicalCell p rate))).comp
      (measurable_presentCell rate rewards C_star C_h k)
    convert hm using 1
    funext z
    dsimp only [Set.domRestrict, ReferenceActiveHorizonMeasurability.listObservationAt]
    rw [List.getElem?_eq_getElem (by
      rw [firstLiveChronologicalPrefix_length]
      exact z.property)]
    rw [firstLiveChronologicalPrefix_get rate rewards C_star C_h z.val.1 z.val.2 ⟨k, z.property⟩]
    rfl
  · have heq : (fun z : ↥({z : SourceInput p × AuxiliaryArray p |
          k < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
            rate rewards C_star C_h z.1}ᶜ) =>
        ReferenceActiveHorizonMeasurability.listObservationAt
          (firstLiveChronologicalPrefix rate rewards C_star C_h z.val) k) =
        fun _ => (Sum.inl () : Unit ⊕ LogicalCell p rate) := by
      funext z
      have hk : (firstLiveChronologicalPrefix rate rewards C_star C_h z.val).length ≤ k := by
        rw [firstLiveChronologicalPrefix_length]
        exact Nat.le_of_not_gt z.property
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_none hk]
    change Measurable (fun z : ↥({z : SourceInput p × AuxiliaryArray p |
      k < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
        rate rewards C_star C_h z.1}ᶜ) =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h z.val) k)
    rw [heq]
    exact measurable_const

/-- The full logical-path graph retains the entire original physical source,
including all continuous rows, private arrays and the original index. -/
def firstLiveChronologicalPrefixGraph (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p × AuxiliaryArray p) :=
  (z.1, firstLiveChronologicalPrefix rate rewards C_star C_h z)

/-- Deterministic Borel graph construction; no logical or physical round law
is an input or a conclusion. -/
theorem measurable_firstLiveChronologicalPrefixGraph
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Measurable (firstLiveChronologicalPrefixGraph rate rewards C_star C_h) :=
  measurable_fst.prodMk (measurable_firstLiveChronologicalPrefix rate rewards C_star C_h)

/-- The full graph pushforward has exactly the original source marginal,
by the actual first-projection identity under the original product law. -/
theorem firstLiveChronologicalPrefixGraph_sourceMarginal
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (firstLiveChronologicalPrefixGraph rate rewards C_star C_h)).map Prod.fst =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
  rw [MeasureTheory.Measure.map_map measurable_fst
    (measurable_firstLiveChronologicalPrefixGraph rate rewards C_star C_h)]
  have hfst : Prod.fst ∘ firstLiveChronologicalPrefixGraph rate rewards C_star C_h = Prod.fst := by
    funext z
    rfl
  rw [hfst]
  exact ReferenceFirstCollectionAuxiliarySeeds.auxiliarySourceLaw_fst p

end Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability

end
