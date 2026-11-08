/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowSetCylinder
public import Bandits.Support.ReferenceGeneratedCalendarRetainedFastTerminalLaw
public import Bandits.Support.ReferenceGeneratedCalendarEpisodeRetainedReindex
public import Bandits.Support.ReferenceGeneratedCalendarRetainedMarginalBridge
public import Bandits.Support.ReferenceGeneratedCalendarOverflowTail
public import Bandits.Support.MixedAuxiliaryReward

/-!
# Actual all-enabled signed auxiliary expectation

Sources: ZIP4 `04_slow_fast_learner.tex:323-390,467-483`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.

The laws, histories, incoming states, anchors and retained events below are
those of the original exhaustive terminal experiment. The retained comparison
integrates the accepted slow-set cylinder and FAST marginal, allowing their
recorder dependence. The numerical learning mean and overflow tail are consumed
from their accepted providers. These are internal results, not manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell SlowSet)
open ReferenceExhaustiveGeneratedCalendarSourceLaw
  (terminalLaw fixedIDTerminalLaw terminalReadout)
open ReferenceGeneratedCalendarEpisodeSlowLaw
  (archive currentMark episodeStartEvent retainedEvent)
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarRetainedFastCore
open ReferenceGeneratedCalendarEpisodeRetainedReindex

namespace Bandits.Support.ReferenceGeneratedCalendarAuxiliaryExpectation

variable {p : Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega
  rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Lambda" ids => Option.elim ids (terminalLaw rate rewards C_star C_h control0)
  (fixedIDTerminalLaw rate rewards C_star C_h control0)

local instance selectedLaw_probability (ids : Option (CompletePublicTable.IDArray p)) :
    IsProbabilityMeasure (Lambda ids) := by
  cases ids <;> dsimp only [Option.elim_none, Option.elim_some] <;> infer_instance

omit control0 in
private theorem sourceEpisodeMass_le_one (s q : Fin p.T)
    (h : History rate s q) (U : SlowSet p) :
    sourceEpisodeMass rate rewards C_star C_h s q h U ≤ 1 := by
  unfold sourceEpisodeMass
  split
  · exact PMF.coe_le_one _ _
  · exact zero_le_one

omit control0 in
private theorem sourceEpisodeMass_ne_top (s q : Fin p.T)
    (h : History rate s q) (U : SlowSet p) :
    sourceEpisodeMass rate rewards C_star C_h s q h U ≠ ∞ :=
  ne_of_lt ((sourceEpisodeMass_le_one rate rewards C_star C_h s q h U).trans_lt
    ENNReal.one_lt_top)

omit control0 in
private theorem sourceEpisodeMass_sum_le_one (s q : Fin p.T) (h : History rate s q) :
    (∑ U : SlowSet p, (sourceEpisodeMass rate rewards C_star C_h s q h U).toReal) ≤ 1 := by
  unfold sourceEpisodeMass
  split
  · next A B hA hB =>
      let P := RecordedSlowRefresh.recordedSlowPMF p Q B
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)
      have hP : (∑ U : SlowSet p, P U) = 1 := by
        simpa only [tsum_fintype] using P.tsum_coe
      rw [← ENNReal.toReal_sum (fun U _ => P.apply_ne_top U), hP, ENNReal.toReal_one]
  · simp only [ENNReal.toReal_zero, Finset.sum_const_zero, zero_le_one]

omit control0 in
/-- The finite slow-set mixture of the accepted FAST reward at the SAME source
history. Both optional numerical observations are read literally. -/
def historyRewardMixture (s q : Fin p.T) (h : History rate s q) : ℝ :=
  ∑ U : SlowSet p, (sourceEpisodeMass rate rewards C_star C_h s q h U).toReal *
    historyFastReward rate rewards C_star C_h s q h U

omit control0 in
theorem measurable_historyRewardMixture (s q : Fin p.T) :
    Measurable (historyRewardMixture rate rewards C_star C_h s q) := by
  apply Finset.measurable_sum
  intro U _
  exact (measurable_sourceEpisodeMass rate rewards C_star C_h s q U).ennreal_toReal.mul
    ((measurable_historyFastReward rate rewards C_star C_h s q).comp
      (measurable_id.prodMk measurable_const))

omit control0 in
theorem historyRewardMixture_bounds (s q : Fin p.T) (h : History rate s q) :
    0 ≤ historyRewardMixture rate rewards C_star C_h s q h ∧
      historyRewardMixture rate rewards C_star C_h s q h ≤ p.m := by
  constructor
  · exact Finset.sum_nonneg fun U _ => mul_nonneg ENNReal.toReal_nonneg
      (historyFastReward_bounds rate rewards C_star C_h s q h U).1
  · calc
      _ ≤ ∑ U : SlowSet p,
          (sourceEpisodeMass rate rewards C_star C_h s q h U).toReal * (p.m : ℝ) :=
        Finset.sum_le_sum fun U _ => mul_le_mul_of_nonneg_left
          (historyFastReward_bounds rate rewards C_star C_h s q h U).2 ENNReal.toReal_nonneg
      _ = (∑ U : SlowSet p,
          (sourceEpisodeMass rate rewards C_star C_h s q h U).toReal) * (p.m : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (p.m : ℝ) := mul_le_mul_of_nonneg_right
        (sourceEpisodeMass_sum_le_one rate rewards C_star C_h s q h) (Nat.cast_nonneg _)
      _ = p.m := one_mul _

private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  convert (hf.sumElim measurable_const).comp
    (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext o
  cases o <;> rfl

/-- Integrating the arbitrary-history slow-set cylinder gives the finite
bounded real FAST-reward mixture. No incoming-set distribution is assumed. -/
theorem terminalLaw_retained_historyRewardMixture
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    (∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => historyFastReward rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet)
      ∂Lambda ids) =
    ∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      historyRewardMixture rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) ∂Lambda ids := by
  let H := sourceEstimateHistory rate rewards C_star C_h control0 s q
  let E := retainedDomain rate rewards C_star C_h control0 s q
  let A : Omega → ℝ := fun w => (currentMark rate rewards C_star C_h control0 q w).elim 0
    (fun e => historyFastReward rate rewards C_star C_h s q (H w) e.slowSet)
  let B : Omega → ℝ := fun w => historyRewardMixture rate rewards C_star C_h s q (H w)
  let f : SlowSet p → Omega → ℝ≥0∞ := fun U w =>
    ENNReal.ofReal (historyFastReward rate rewards C_star C_h s q (H w) U) *
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => if e.slowSet = U then 1 else 0)
  let g : SlowSet p → Omega → ℝ≥0∞ := fun U w =>
    ENNReal.ofReal (historyFastReward rate rewards C_star C_h s q (H w) U) *
      sourceEpisodeMass rate rewards C_star C_h s q (H w) U
  have hH : Measurable H := measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q
  have hPhi (U : SlowSet p) : Measurable (fun h : History rate s q =>
      ENNReal.ofReal (historyFastReward rate rewards C_star C_h s q h U)) :=
    ((measurable_historyFastReward rate rewards C_star C_h s q).comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hf (U : SlowSet p) : Measurable (f U) := by
    apply ((hPhi U).comp hH).mul
    apply (measurable_option_elim _ ?_ 0).comp
      (ReferenceGeneratedCalendarEpisodeSlowLaw.measurable_currentMark
        rate rewards C_star C_h control0 q)
    have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.mono le_rfl le_top
    exact (measurable_of_finite (fun V : SlowSet p =>
      if V = U then (1 : ℝ≥0∞) else 0)).comp hU
  have hg (U : SlowSet p) : Measurable (g U) :=
    ((hPhi U).comp hH).mul
      ((measurable_sourceEpisodeMass rate rewards C_star C_h s q U).comp hH)
  have hA (w : Omega) : ENNReal.ofReal (A w) = ∑ U : SlowSet p, f U w := by
    cases he : currentMark rate rewards C_star C_h control0 q w <;>
      simp [A, f, he, mul_ite]
  have hB (w : Omega) : ENNReal.ofReal (B w) = ∑ U : SlowSet p, g U w := by
    dsimp only [B, historyRewardMixture]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun U _ => mul_nonneg ENNReal.toReal_nonneg
        (historyFastReward_bounds rate rewards C_star C_h s q (H w) U).1)]
    apply Finset.sum_congr rfl
    intro U _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (sourceEpisodeMass_ne_top rate rewards C_star C_h s q (H w) U)]
    exact mul_comm _ _
  have hlin : (∫⁻ w, ENNReal.ofReal (A w) ∂(Lambda ids).restrict E) =
      ∫⁻ w, ENNReal.ofReal (B w) ∂(Lambda ids).restrict E := by
    simp_rw [hA, hB]
    rw [lintegral_finsetSum Finset.univ (fun U _ => hf U),
      lintegral_finsetSum Finset.univ (fun U _ => hg U)]
    apply Finset.sum_congr rfl
    intro U _
    exact ReferenceGeneratedCalendarEpisodeSlowSetCylinder.terminalLaw_retained_slowSet_cylinder
      rate rewards C_star C_h control0 ids s q hsq U _ (hPhi U)
  have hAi : Integrable A ((Lambda ids).restrict E) := by
    have h := integrable_meanRewardTest rate rewards C_star C_h control0 ids s q
      (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp only [norm_one, le_refl])
    have heq : A = meanRewardTest rate rewards C_star C_h control0 s q (fun _ => 1) := by
      funext w
      cases he : currentMark rate rewards C_star C_h control0 q w <;>
        simp only [A, H, meanRewardTest, he, Option.elim_none, Option.elim_some, one_mul]
    rw [heq]
    exact h
  have hBi : Integrable B ((Lambda ids).restrict E) := by
    apply Integrable.of_bound
      ((measurable_historyRewardMixture rate rewards C_star C_h s q).comp hH).aestronglyMeasurable
      (p.m : ℝ)
    exact Filter.Eventually.of_forall fun w => by
      change ‖historyRewardMixture rate rewards C_star C_h s q (H w)‖ ≤ p.m
      rw [Real.norm_of_nonneg (historyRewardMixture_bounds rate rewards C_star C_h s q (H w)).1]
      exact (historyRewardMixture_bounds rate rewards C_star C_h s q (H w)).2
  have hAn (w : Omega) : 0 ≤ A w := by
    cases he : currentMark rate rewards C_star C_h control0 q w with
    | none => simp only [A, he, Option.elim_none, le_refl]
    | some e =>
      simpa only [A, he, Option.elim_some] using
        (historyFastReward_bounds rate rewards C_star C_h s q (H w) e.slowSet).1
  have hBn (w : Omega) : 0 ≤ B w :=
    (historyRewardMixture_bounds rate rewards C_star C_h s q (H w)).1
  change (∫ w, A w ∂(Lambda ids).restrict E) = ∫ w, B w ∂(Lambda ids).restrict E
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hAn) hAi.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hBn) hBi.aestronglyMeasurable]
  exact congrArg ENNReal.toReal hlin

/-- Actual retained histories identify the finite mixture with the canonical
mixed auxiliary expectation at the current weights and the operative anchor. -/
theorem ae_historyRewardMixture_ge_marginal
    (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂Lambda ids, ∀ (s q : Fin p.T),
      w ∈ retainedDomain rate rewards C_star C_h control0 s q →
      ∃ e : LogicalCell p rate,
        currentMark rate rewards C_star C_h control0 q w = some e ∧
        (∑ i : Fin p.K, ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight Q e.before) i *
            (((rewards q i).val : ℝ) / (D p : ℝ))) ≤
          historyRewardMixture rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) +
              CanonicalRecordingRates.gamma p rate.eta.val := by
  filter_upwards
    [ReferenceGeneratedCalendarRetainedFastTerminalLaw.ae_retained_reward_conversions
      rate rewards C_star C_h control0 ids,
      ae_sourceEpisodeMass_actual rate rewards C_star C_h control0 ids] with w hfast hmass
  intro s q hE
  obtain ⟨e, A, hlo, hhi, he, hA, hS, _hselected, _hfinite, _hcontinuous⟩ := hfast s q hE
  obtain ⟨e', rho, P, A', he', _ht, _hbirth, hA', _hclear, ha, hm⟩ :=
    hmass s q hE.1 hE.2
  have hee : e' = e := Option.some.inj (he'.symm.trans he)
  subst e'
  change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
    (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A' at hA'
  have hAA : A' = A := Option.some.inj (hA'.symm.trans hA)
  subst A'
  let v := RecordedQueueRun.scoreWeight Q A
  let b := RecordedQueueRun.scoreWeight Q e.before
  let hv := RecordedSlowRefresh.scoreWeight_pos Q A
  let hb := RecordedSlowRefresh.scoreWeight_pos Q e.before
  let r : Fin p.K → ℝ := fun i => ((rewards q i).val : ℝ) / (D p : ℝ)
  have hmU (U : SlowSet p) :
      sourceEpisodeMass rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U =
      CanonicalOrientedSetLaw.slowSetPMF b v p.two_le_m p.m_lt_K hb hv U := by
    simpa only [RecordedSlowRefresh.recordedSlowPMF, ha] using hm U
  have hfU (U : SlowSet p) :
      historyFastReward rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U =
      ∑ j : CanonicalFastSampling.FastArm U,
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
          v b hv hb hlo hhi U j * MixedAuxiliaryReward.oneRoundAuxiliaryReward r U j := by
    simp only [historyFastReward, hA, hS]
    unfold numericalFastReward
    rw [numericalFastPMF_eq_qGamma rate A e.before hlo hhi U]
    apply Finset.sum_congr rfl
    intro j _
    rw [CanonicalFastSampling.qGammaPMF_apply, ENNReal.toReal_ofReal
      (CanonicalFastSampling.qGamma_nonneg p rate.eta.property rate.sourceCap
        v b hv hb hlo hhi U j)]
    rfl
  have hmix : historyRewardMixture rate rewards C_star C_h s q
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w) =
      MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation p rate.eta.val
        rate.eta.property rate.sourceCap v b hv hb hlo hhi r := by
    unfold historyRewardMixture MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation
    apply Finset.sum_congr rfl
    intro U _
    rw [hmU U, hfU U]
  refine ⟨e, he, ?_⟩
  rw [hmix]
  have h := MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation_ge_theta_sub_gamma
    p rate.eta.val rate.eta.property rate.sourceCap v b hv hb hlo hhi r
      (fun i => ReferenceGeneratedCalendarQuantizedRoundKernel.gridReward_mem rewards q i)
  exact (sub_le_iff_le_add.mp h)

private theorem integral_episodeDateTerm_eq
    (ids : Option (CompletePublicTable.IDArray p)) (f : LogicalCell p rate → ℝ)
    (s q : Fin p.T) :
    (∫ w, episodeDateTerm rate rewards C_star C_h control0 f s q w ∂Lambda ids) =
      ∫ w in retainedDomain rate rewards C_star C_h control0 s q,
        (currentMark rate rewards C_star C_h control0 q w).elim 0 f ∂Lambda ids := by
  have hfun : episodeDateTerm rate rewards C_star C_h control0 f s q =
      (retainedDomain rate rewards C_star C_h control0 s q).indicator
        (fun w => (currentMark rate rewards C_star C_h control0 q w).elim 0 f) := by
    funext w
    by_cases hw : w ∈ retainedDomain rate rewards C_star C_h control0 s q
    · have hw' : w ∈ episodeDateEvent rate rewards C_star C_h control0 s q := hw
      simp only [episodeDateTerm, Set.indicator_of_mem hw, Set.indicator_of_mem hw', mul_one]
    · have hw' : w ∉ episodeDateEvent rate rewards C_star C_h control0 s q := hw
      simp only [episodeDateTerm, Set.indicator_of_notMem hw, Set.indicator_of_notMem hw', mul_zero]
  rw [hfun, integral_indicator (measurableSet_retainedDomain rate rewards C_star C_h control0 s q)]

omit C_star C_h control0 in
private theorem comparatorReward_bounds (S : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T) :
    0 ≤ ∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ) ∧
      (∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ)) ≤ p.m := by
  have hr := ReferenceGeneratedCalendarQuantizedRoundKernel.gridReward_mem rewards q
  refine ⟨Finset.sum_nonneg (fun i _ => (hr i).1), ?_⟩
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
    (Finset.mem_powersetCard.mp S.property).2] using
    Finset.sum_le_sum (fun i (_hi : i ∈ S.val) => (hr i).2)

omit C_star C_h control0 in
private theorem marginalCell_bounds (S : ProductSetLaw.ProductSet p.K p.m)
    (e : LogicalCell p rate) :
    |ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S e| ≤ p.m := by
  let r : Fin p.K → ℝ := fun i => ((rewards e.time i).val : ℝ) / (D p : ℝ)
  let theta := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.before)
  have hr := ReferenceGeneratedCalendarQuantizedRoundKernel.gridReward_mem rewards e.time
  have ht (i : Fin p.K) : 0 ≤ theta i :=
    (RecordedMarginalGrowth.state_theta_pos Q e.before i
      (by have hm := p.two_le_m; omega) p.m_lt_K).le
  have hw : 0 ≤ ∑ i : Fin p.K, theta i * r i ∧
      (∑ i : Fin p.K, theta i * r i) ≤ p.m := by
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (ht i) (hr i).1), ?_⟩
    calc
      _ ≤ ∑ i : Fin p.K, theta i :=
        Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (ht i) (hr i).2)
      _ = _ := RecordedMarginalGrowth.state_sum_theta_eq_m Q e.before
        (by have hm := p.two_le_m; omega) p.m_lt_K
  have hc := comparatorReward_bounds rewards S e.time
  unfold ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
  simp_rw [mul_div_assoc]
  exact abs_le.mpr ⟨by linarith only [hc.1, hw.2], by linarith only [hc.2, hw.1]⟩

omit C_star C_h control0 in
private theorem measurable_marginalCell (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S) := by
  let mark : LogicalCell p rate → Fin p.T × RecordedQueueRun.RunState p.K :=
    fun e => (e.time, e.before)
  have hm : Measurable mark :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time.prodMk
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before
  let F : Fin p.T × RecordedQueueRun.RunState p.K → ℝ := fun x =>
    (∑ i ∈ S.val, ((rewards x.1 i).val : ℝ) / (D p : ℝ)) -
      ∑ i : Fin p.K, ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight Q x.2) i * ((rewards x.1 i).val : ℝ) / (D p : ℝ)
  have hF : Measurable F := measurable_of_countable F
  have h := hF.comp hm
  convert h using 1
  funext e
  simp only [Function.comp_apply, mark,
    ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap]
  rfl

/-- One actual episode/date comparison. Its exploration charge is itself an
episode/date term, so unique coverage will charge each retained date once. -/
theorem episodeDate_integral_signedGap_le_marginal_add_gamma
    (ids : Option (CompletePublicTable.IDArray p)) (S : ProductSetLaw.ProductSet p.K p.m)
    (s q : Fin p.T) :
    (∫ w, episodeDateTerm rate rewards C_star C_h control0
      (retainedSignedCellGap rate rewards S) s q w ∂Lambda ids) ≤
    (∫ w, episodeDateTerm rate rewards C_star C_h control0
      (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S)
      s q w ∂Lambda ids) +
    ∫ w, episodeDateTerm rate rewards C_star C_h control0
      (fun _ => CanonicalRecordingRates.gamma p rate.eta.val) s q w ∂Lambda ids := by
  by_cases hsq : s.val ≤ q.val
  · let E := retainedDomain rate rewards C_star C_h control0 s q
    let H := sourceEstimateHistory rate rewards C_star C_h control0 s q
    let c : ℝ := ∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ)
    let A := actualRewardTest rate rewards C_star C_h control0 s q (fun _ => 1)
    let B : Omega → ℝ := fun w => historyRewardMixture rate rewards C_star C_h s q (H w)
    let G : Omega → ℝ := fun w => (currentMark rate rewards C_star C_h control0 q w).elim 0
      (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S)
    let gamma := CanonicalRecordingRates.gamma p rate.eta.val
    have hE : MeasurableSet E := measurableSet_retainedDomain rate rewards C_star C_h control0 s q
    have hgood := ae_historyRewardMixture_ge_marginal rate rewards C_star C_h control0 ids
    have hAi : Integrable A ((Lambda ids).restrict E) :=
      integrable_actualRewardTest rate rewards C_star C_h control0 ids s q
        (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp only [norm_one, le_refl])
    have hBi : Integrable B ((Lambda ids).restrict E) := by
      apply Integrable.of_bound
        ((measurable_historyRewardMixture rate rewards C_star C_h s q).comp
          (measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q)).aestronglyMeasurable
        (p.m : ℝ)
      exact Filter.Eventually.of_forall fun w => by
        change ‖historyRewardMixture rate rewards C_star C_h s q (H w)‖ ≤ p.m
        rw [Real.norm_of_nonneg (historyRewardMixture_bounds rate rewards C_star C_h s q (H w)).1]
        exact (historyRewardMixture_bounds rate rewards C_star C_h s q (H w)).2
    have hGi : Integrable G ((Lambda ids).restrict E) := by
      apply Integrable.of_bound
        ((measurable_option_elim _ (measurable_marginalCell rate rewards S) 0).comp
          (ReferenceGeneratedCalendarEpisodeSlowLaw.measurable_currentMark
            rate rewards C_star C_h control0 q)).aestronglyMeasurable (p.m : ℝ)
      exact Filter.Eventually.of_forall fun w => by
        change ‖G w‖ ≤ p.m
        cases he : currentMark rate rewards C_star C_h control0 q w with
        | none => simp only [G, he, Option.elim_none, norm_zero]; exact Nat.cast_nonneg _
        | some e => simpa only [G, he, Option.elim_some, Real.norm_eq_abs] using
            marginalCell_bounds rate rewards S e
    have hsig :
        (∫ w, episodeDateTerm rate rewards C_star C_h control0
          (retainedSignedCellGap rate rewards S) s q w ∂Lambda ids) =
        ∫ w in E, c - A w ∂Lambda ids := by
      rw [integral_episodeDateTerm_eq]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hE] with w hw hwE
      obtain ⟨e, he, _hmix⟩ := hw s q hwE
      have ht := ((ReferenceGeneratedCalendarEpisodeSlowLaw.currentMark_eq_some_iff
        rate rewards C_star C_h control0 q w e).mp he).2
      simp only [he, Option.elim_some, retainedSignedCellGap, A, actualRewardTest, ht, one_mul, c]
    have hmean : (∫ w in E, A w ∂Lambda ids) = ∫ w in E, B w ∂Lambda ids := by
      have hAeq : A = fun w : Omega => (currentMark rate rewards C_star C_h control0 q w).elim 0
          (ReferenceInitialStoppedCalendar.cellReward rate rewards) := by
        funext w
        cases he : currentMark rate rewards C_star C_h control0 q w <;>
          simp only [A, actualRewardTest, he, Option.elim_none, Option.elim_some, one_mul]
      rw [hAeq]
      exact (ReferenceGeneratedCalendarRetainedFastTerminalLaw.terminalLaw_retained_cellReward_test
        rate rewards C_star C_h control0 ids s q).trans
          (terminalLaw_retained_historyRewardMixture rate rewards C_star C_h control0 ids s q hsq)
    have hcomp : ∀ᵐ w ∂(Lambda ids).restrict E, c - B w ≤ G w + gamma := by
      filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hE] with w hw hwE
      obtain ⟨e, he, hmix⟩ := hw s q hwE
      have ht := ((ReferenceGeneratedCalendarEpisodeSlowLaw.currentMark_eq_some_iff
        rate rewards C_star C_h control0 q w e).mp he).2
      dsimp only [G]
      rw [he, Option.elim_some]
      unfold ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
      rw [ht]
      simp_rw [mul_div_assoc]
      change c - B w ≤ c - _ + gamma
      linarith only [hmix]
    have hgamma :
        (∫ w, episodeDateTerm rate rewards C_star C_h control0 (fun _ => gamma) s q w ∂Lambda ids) =
        ∫ w in E, gamma ∂Lambda ids := by
      rw [integral_episodeDateTerm_eq]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hE] with w hw hwE
      obtain ⟨e, he, _hmix⟩ := hw s q hwE
      simp only [he, Option.elim_some]
    rw [hsig, hgamma, integral_episodeDateTerm_eq]
    change (∫ w in E, c - A w ∂Lambda ids) ≤
      (∫ w in E, G w ∂Lambda ids) + ∫ w in E, gamma ∂Lambda ids
    calc
      _ = (∫ _ in E, c ∂Lambda ids) - ∫ w in E, B w ∂Lambda ids := by
        rw [integral_sub (integrable_const c) hAi, hmean]
      _ = ∫ w in E, c - B w ∂Lambda ids :=
        (integral_sub (integrable_const c) hBi).symm
      _ ≤ ∫ w in E, G w + gamma ∂Lambda ids :=
        integral_mono_ae ((integrable_const c).sub hBi) (hGi.add (integrable_const gamma)) hcomp
      _ = _ := integral_add hGi (integrable_const gamma)
  · have hE : retainedDomain rate rewards C_star C_h control0 s q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hsq hw.2.1
    simp only [integral_episodeDateTerm_eq, hE, Measure.restrict_empty, integral_zero_measure,
      zero_add, le_refl]

/-- The retained signed auxiliary mean is bounded by the accepted incoming
current-marginal mean plus `gamma*T`, under the raw law and EVERY original
fixed-ID law. The first detecting update remains retained. -/
theorem integral_retainedSignedGap_le_marginal_add_gamma
    (ids : Option (CompletePublicTable.IDArray p)) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ w, ReferenceGeneratedCalendarOverflowTail.retainedSignedGap
      rate rewards C_star C_h control0 S w ∂Lambda ids) ≤
    (∫ w, ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap
      rate rewards C_star C_h control0 S w ∂Lambda ids) +
      CanonicalRecordingRates.gamma p rate.eta.val * p.T := by
  let gamma := CanonicalRecordingRates.gamma p rate.eta.val
  have hg0 : 0 ≤ gamma :=
    (CanonicalRecordingRates.gamma_nonneg_and_le_half p rate.eta.property rate.sourceCap).1
  let charge : Fin p.T → Fin p.T → Omega → ℝ := fun s q =>
    episodeDateTerm rate rewards C_star C_h control0 (fun _ => gamma) s q
  have hcharge (s q : Fin p.T) : Integrable (charge s q) (Lambda ids) :=
    integrable_episodeDateTerm rate rewards C_star C_h control0 ids (fun _ => gamma)
      gamma hg0 measurable_const (fun _ => (abs_of_nonneg hg0).le) s q
  have hinner (s : Fin p.T) : Integrable (fun w => ∑ q : Fin p.T, charge s q w) (Lambda ids) := by
    simpa only [← Finset.sum_apply] using
      integrable_finsetSum Finset.univ (fun q _ => hcharge s q)
  have htotal : Integrable (fun w => ∑ s : Fin p.T, ∑ q : Fin p.T, charge s q w)
      (Lambda ids) := by
    simpa only [← Finset.sum_apply] using
      integrable_finsetSum Finset.univ (fun s _ => hinner s)
  have hcount : ∀ᵐ w ∂Lambda ids,
      (∑ s : Fin p.T, ∑ q : Fin p.T, charge s q w) ≤ gamma * p.T := by
    filter_upwards [episodeDateSum_eq_retainedArchiveSum rate rewards C_star C_h control0 ids]
      with w hw
    change (∑ s : Fin p.T, ∑ q : Fin p.T,
      episodeDateTerm rate rewards C_star C_h control0 (fun _ => gamma) s q w) ≤ gamma * p.T
    rw [hw (fun _ => gamma)]
    let L := (archive rate rewards C_star C_h control0 w).filter (fun e => e.before.overflow = false)
    have hn : ((archive rate rewards C_star C_h control0 w).map LogicalCell.time).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
        rate rewards C_star C_h control0 w).imp fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h)
    have hlen : (archive rate rewards C_star C_h control0 w).length ≤ p.T := by
      simpa only [List.length_map, Fintype.card_fin] using hn.length_le_card
    have hL : L.length ≤ p.T := (List.length_filter_le _ _).trans hlen
    change (L.map (fun _ => gamma)).sum ≤ gamma * p.T
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_comm (L.length : ℝ)]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hL) hg0
  have hchargeIntegral :
      (∑ s : Fin p.T, ∑ q : Fin p.T, ∫ w, charge s q w ∂Lambda ids) ≤ gamma * p.T := by
    have hmono := integral_mono_ae htotal (integrable_const (gamma * p.T)) hcount
    rw [integral_finsetSum Finset.univ (fun s _ => hinner s)] at hmono
    simp_rw [integral_finsetSum Finset.univ (fun q _ => hcharge _ q)] at hmono
    simpa only [integral_const, probReal_univ, one_smul] using hmono
  rw [(retainedSignedGap_episodeDateIntegral rate rewards C_star C_h control0 ids S).2.2.2,
    (retainedMarginalGap_episodeDateIntegral rate rewards C_star C_h control0 ids S).2.2.2]
  calc
    _ ≤ ∑ s : Fin p.T, ∑ q : Fin p.T,
        ((∫ w, episodeDateTerm rate rewards C_star C_h control0
          (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S)
          s q w ∂Lambda ids) + ∫ w, charge s q w ∂Lambda ids) :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun q _ =>
        episodeDate_integral_signedGap_le_marginal_add_gamma rate rewards C_star C_h control0 ids S s q
    _ = (∑ s : Fin p.T, ∑ q : Fin p.T,
        ∫ w, episodeDateTerm rate rewards C_star C_h control0
          (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S)
          s q w ∂Lambda ids) + ∑ s : Fin p.T, ∑ q : Fin p.T, ∫ w, charge s q w ∂Lambda ids := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl hchargeIntegral

/-- The full literal all-enabled signed auxiliary expectation under EVERY
original fixed-ID terminal law, with the source's auxiliary-learning constants.
Integrability is returned from the accepted original terminal API. -/
theorem fixedID_integral_signedGap_le_auxiliaryLearningBound
    (ids : CompletePublicTable.IDArray p) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun w => ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
      (terminalReadout rate rewards C_star C_h control0 w).2.2)
      (fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ∧
    (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
      (terminalReadout rate rewards C_star C_h control0 w).2.2
      ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val +
      (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ) +
        1024 * ((p.K - p.m + 1 : ℕ) : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) *
          rate.eta.val * p.T +
      (p.m : ℝ) * p.T / (rate.eta.val * D p) + (p.m : ℝ) * p.T / (N p : ℝ) ^ 2 := by
  refine ⟨(ReferenceExhaustiveGeneratedCalendarSourceLaw.integrable_signedGap
    rate rewards C_star C_h control0 (some ids) S).1, ?_⟩
  have htail := ReferenceGeneratedCalendarOverflowTail.fixedID_integral_signedGap_le_retained_add_inv_N_sq
    rate rewards C_star C_h control0 ids S
  have hret := integral_retainedSignedGap_le_marginal_add_gamma
    rate rewards C_star C_h control0 (some ids) S
  have hmean := (ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap_fixedID_mean
    rate rewards C_star C_h control0 ids S).2
  have hgamma : CanonicalRecordingRates.gamma p rate.eta.val * (p.T : ℝ) =
      (1024 * ((p.K - p.m + 1 : ℕ) : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) *
        rate.eta.val * p.T := by
    unfold CanonicalRecordingRates.gamma CanonicalRecordingRates.beta
    ring
  change (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
    (terminalReadout rate rewards C_star C_h control0 w).2.2
    ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ≤
      (∫ w, ReferenceGeneratedCalendarOverflowTail.retainedSignedGap rate rewards C_star C_h control0 S w
        ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) +
          (p.m : ℝ) * p.T / (N p : ℝ) ^ 2 at htail
  simp only [Option.elim_some] at hret
  rw [hgamma] at hret
  have hall := htail.trans (add_le_add (hret.trans (add_le_add hmean le_rfl)) le_rfl)
  exact hall.trans_eq (by simp only [Nat.cast_add, Nat.cast_one]; ring)

end Bandits.Support.ReferenceGeneratedCalendarAuxiliaryExpectation

end
