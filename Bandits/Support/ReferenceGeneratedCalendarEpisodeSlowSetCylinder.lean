/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeTerminalTransition
public import Bandits.Support.ReferenceGeneratedCalendarEpisodeInitialLaw

/-!
# Retained source-estimate slow-set cylinders

Sources: ZIP4 `04_slow_fast_learner.tex:151-174,176-215,329-362` and
`06_interruptions.tex:391-426`.

The observer is the accepted strict start history and normalized floor-estimate
history. The current old slow set is a separate argument of the common kernel.
All laws below concern the original exhaustive terminal experiment and its
original fixed-ID laws. These are internal construction results.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarQuantizedRoundKernel

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowSetCylinder

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0
local notation "fixedLambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
  rate rewards C_star C_h control0

omit rewards C_star C_h control0 in
/-- The history at its own start has an empty estimate-index type. -/
def historyAtStart (s : Fin p.T)
    (h : Source p × List (LogicalCell p rate)) : History rate s s :=
  (h, fun v => False.elim (by have := v.property; omega))

omit rewards C_star C_h control0 in
theorem measurable_historyAtStart (s : Fin p.T) : Measurable (historyAtStart rate s) :=
  measurable_id.prodMk (measurable_pi_iff.mpr fun v =>
    False.elim (by have := v.property; omega))

theorem historyAtStart_actual (s : Fin p.T) (w : Omega) :
    historyAtStart rate s (startHistory rate rewards C_star C_h control0 s w) =
      sourceEstimateHistory rate rewards C_star C_h control0 s s w := by
  apply Prod.ext
  · rfl
  · funext v
    have := v.property
    omega

omit control0 in
theorem sourceEpisodeReplay_at_start (s : Fin p.T) (h : History rate s s) :
    sourceEpisodeReplay rate rewards C_star C_h s s h =
      ReferencePostInvocationNoncallGeometry.prefixNumerical
        rate rewards C_star C_h s.castSucc h.1.1 := by
  simp only [sourceEpisodeReplay, sourceReplayPrefix, Nat.sub_self]
  rfl

/-- The actual initial producer supplies the base of the retained cylinder
with the SAME start observer. The incoming-clear gate is supplied by the
accepted source-history equivalence, rather than an assumed numerical seed. -/
theorem terminalLaw_retained_initial_cylinder
    (ids : Option (CompletePublicTable.IDArray p)) (s : Fin p.T) (U : SlowSet p)
    (Phi : History rate s s → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s s w) *
      (currentMark rate rewards C_star C_h control0 s w).elim 0
        (fun e => if e.slowSet = U then 1 else 0)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s s)) =
    ∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s s w) *
      sourceEpisodeMass rate rewards C_star C_h s s
        (sourceEstimateHistory rate rewards C_star C_h control0 s s w) U
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s s) := by
  let mu := ids.elim Lambda fixedLambda
  let G : Source p × List (LogicalCell p rate) → ℝ≥0∞ := fun h =>
    if historyAtStart rate s h ∈ sourceHistoryRetained rate rewards C_star C_h s s
    then Phi (historyAtStart rate s h) else 0
  have hG : Measurable G := (hPhi.comp (measurable_historyAtStart rate s)).ite
    ((measurableSet_sourceHistoryRetained rate rewards C_star C_h s s).preimage
      (measurable_historyAtStart rate s)) measurable_const
  have hbase := ReferenceGeneratedCalendarEpisodeInitialLaw.terminalLaw_initial_cylinder
    rate rewards C_star C_h control0 ids s U G hG
  have hstart := ReferenceGeneratedCalendarEpisodeInitialLaw.measurableSet_episodeStartEvent
    rate rewards C_star C_h control0 s
  have hret := measurableSet_retainedEvent rate rewards C_star C_h control0 s s
  rw [← lintegral_indicator (hstart.inter hret),
    ← lintegral_indicator (hstart.inter hret)]
  rw [← lintegral_indicator hstart, ← lintegral_indicator hstart] at hbase
  calc
    _ = ∫⁻ w : Omega, (episodeStartEvent rate rewards C_star C_h control0 s).indicator
        (fun w => G (startHistory rate rewards C_star C_h control0 s w) *
          initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w)) w
        ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids,
        ae_retained_source_input rate rewards C_star C_h control0 ids] with w hg hi
      by_cases hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s
      · have hequiv := hg s s hs
        by_cases hr : w ∈ retainedEvent rate rewards C_star C_h control0 s s
        · obtain ⟨e, A, i, he, hc, _⟩ := hi s s hs hr
          simp only [Set.indicator, Set.mem_inter_iff, hs, hr, and_self, ite_true,
            G, historyAtStart_actual, hequiv.mp hr, initialSetCylinder,
            he, hc, Bool.false_eq_true, ite_false, Option.elim_some]
        · have hn := mt hequiv.mpr hr
          simp only [Set.indicator, Set.mem_inter_iff, hs, hr, and_false, ite_false,
            ite_true, G, historyAtStart_actual, hn, zero_mul]
      · simp only [Set.indicator, Set.mem_inter_iff, hs, false_and, ite_false]
    _ = ∫⁻ w : Omega, (episodeStartEvent rate rewards C_star C_h control0 s).indicator
        (fun w => G (startHistory rate rewards C_star C_h control0 s w) *
          initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w)) w
        ∂mu := hbase
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids,
        ae_retained_source_input rate rewards C_star C_h control0 ids] with w hg hi
      by_cases hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s
      · have hequiv := hg s s hs
        by_cases hr : w ∈ retainedEvent rate rewards C_star C_h control0 s s
        · obtain ⟨e, A, i, he, hc, hAc, hA, hS, _, _, _, _, hm⟩ := hi s s hs hr
          have hAS : A = e.before := by
            rw [sourceEpisodeReplay_at_start, hA] at hS
            exact Option.some.inj hS
          have hmass := hm U
          rw [hAS] at hmass
          simp only [Set.indicator, Set.mem_inter_iff, hs, hr, and_self, ite_true,
            G, historyAtStart_actual, hequiv.mp hr, initialMassCylinder,
            he, hc, Bool.false_eq_true, ite_false, initialMass, hmass]
        · have hn := mt hequiv.mpr hr
          simp only [Set.indicator, Set.mem_inter_iff, hs, hr, and_false, ite_false,
            ite_true, G, historyAtStart_actual, hn, zero_mul]
      · simp only [Set.indicator, Set.mem_inter_iff, hs, false_and, ite_false]

omit control0 in
private theorem replayPrefix_historySuccessor (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (h : History rate s q) (x : Estimate p) (n : ℕ) (hn : n ≤ q.val - s.val) :
    replayPrefix rate rewards C_star C_h s r (historySuccessor rate s q r hqr (h, x))
        n (by omega) = replayPrefix rate rewards C_star C_h s q h n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replayPrefix_succ, replayPrefix_succ, ih (by omega)]
    apply congrArg (fun f => (replayPrefix rate rewards C_star C_h s q h n (by omega)).map f)
    funext S
    have hne : (⟨s.val + n, by omega⟩ : Fin p.T) ≠ q := by
      intro he
      have hv := congrArg Fin.val he
      change s.val + n = q.val at hv
      omega
    simp only [historySuccessor, hne, dite_false]

omit control0 in
/-- Appending the current source vector performs exactly one complete enabled
queue UPDATE, with the same strict seed and all previous source vectors. -/
theorem sourceEpisodeReplay_historySuccessor (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (h : History rate s q) (x : Estimate p) :
    sourceEpisodeReplay rate rewards C_star C_h s r
        (historySuccessor rate s q r hqr (h, x)) =
      (sourceEpisodeReplay rate rewards C_star C_h s q h).map
        (fun S => estimateStep rate S true x) := by
  have hd : r.val - s.val = (q.val - s.val) + 1 := by omega
  simp only [sourceEpisodeReplay, sourceReplayPrefix, hd]
  rw [replayPrefix_succ,
    replayPrefix_historySuccessor rate rewards C_star C_h s q r hsq hqr h x
      (q.val - s.val) le_rfl]
  apply congrArg (fun f => (replayPrefix rate rewards C_star C_h s q h
    (q.val - s.val) le_rfl).map f)
  funext S
  have ht : (⟨s.val + (q.val - s.val), by omega⟩ : Fin p.T) = q :=
    Fin.ext (by change s.val + (q.val - s.val) = q.val; omega)
  simp only [historySuccessor, ht, dite_true]

omit C_star C_h control0 in
private theorem episodeNextLaw_proposal_sum (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K) (hS : S.overflow = false)
    (old U : SlowSet p) (i : Option (Fin p.K)) :
    (∑ B : Bool, episodeNextLaw rate rewards q A S old i B {U} *
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}) =
    RecordedSlowRefresh.refreshKernel (RecordedSlowRefresh.hazard p Q)
      (RecordedSlowRefresh.hazard_pos p Q).le
      (le_trans (RecordedSlowRefresh.hazard_le_quarter p Q rate.sourceCap) (by norm_num))
      (RecordedSlowRefresh.residualPMF p Q S (episodeRoundInput rate rewards q A i)
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) old U := by
  rw [RecordedSlowRefresh.refreshKernel_apply]
  have hh : RecordedSlowRefresh.hazard p Q =
      FollowerCutoffScan.proposalHazard p rate.eta.val := rfl
  rw [hh]
  simp only [Fintype.sum_bool, episodeNextLaw, hS, Bool.false_eq_true, ite_false,
    ite_true, PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U),
    Measure.dirac_apply' _ (measurableSet_singleton U),
    ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true,
    ReferenceRankInstallationPostUpdateProposalLaw.proposalBitLaw_false]
  simp only [Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
  by_cases he : old = U
  · subst old
    simp only [ite_true, one_mul]
    ac_rfl
  · have he' : U ≠ old := Ne.symm he
    simp only [he, he', ite_false, zero_mul, zero_add, add_zero]
    exact mul_comm _ _

omit C_star C_h control0 in
private theorem episodeRoundTest_next_indicator (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K) (old U : SlowSet p)
    (f : Estimate p → ℝ≥0∞) :
    episodeRoundTest rate rewards q A S old
      (fun x _ V => f x * if V = U then 1 else 0) =
      ∑ i : Option (Fin p.K), f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
        (episodeRoundInput rate rewards q A i)) *
        (∑ B : Bool, episodeNextLaw rate rewards q A S old i B {U} *
          ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}) *
        RecordedRoundMoments.recordingOutcomePMF
          (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
            (RecordedSlowRefresh.scoreWeight_pos Q A)) i := by
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _
  ac_rfl

omit C_star C_h control0 in
/-- The old set is mixed only after the common source estimate is revealed.
This is the accepted SAME-anchor residual identity, on the entire recorder
sum including bottom and every zero-estimate atom. POST overflow is ungated. -/
theorem episodeRoundTest_slow_mixture (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K) (hS : S.overflow = false)
    (U : SlowSet p) (f : Estimate p → ℝ≥0∞) :
    (∑ old : SlowSet p,
      RecordedSlowRefresh.recordedSlowPMF p Q S (RecordedQueueRun.scoreWeight Q A)
        (RecordedSlowRefresh.scoreWeight_pos Q A) old *
      episodeRoundTest rate rewards q A S old
        (fun x _ V => f x * if V = U then 1 else 0)) =
    ∑ i : Option (Fin p.K), f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
      (episodeRoundInput rate rewards q A i)) *
      RecordedSlowRefresh.recordedSlowPMF p Q
        (RecordedQueueRun.step Q S (episodeRoundInput rate rewards q A i))
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U *
      RecordedRoundMoments.recordingOutcomePMF
        (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
          (RecordedSlowRefresh.scoreWeight_pos Q A)) i := by
  simp_rw [episodeRoundTest_next_indicator,
    episodeNextLaw_proposal_sum rate rewards q A S hS, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hm := congrArg (fun v : PMF (SlowSet p) => v U)
    (RecordedSlowRefresh.active_step_refresh_law p Q S (episodeRoundInput rate rewards q A i)
      (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) rate.sourceCap)
  simp only [PMF.bind_apply, tsum_fintype] at hm
  calc
    _ = f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
          (episodeRoundInput rate rewards q A i)) *
        (∑ old : SlowSet p, RecordedSlowRefresh.recordedSlowPMF p Q S
          (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) old *
          RecordedSlowRefresh.refreshKernel (RecordedSlowRefresh.hazard p Q)
            (RecordedSlowRefresh.hazard_pos p Q).le
            (le_trans (RecordedSlowRefresh.hazard_le_quarter p Q rate.sourceCap) (by norm_num))
            (RecordedSlowRefresh.residualPMF p Q S (episodeRoundInput rate rewards q A i)
              (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) old U) *
        RecordedRoundMoments.recordingOutcomePMF
          (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
            (RecordedSlowRefresh.scoreWeight_pos Q A)) i := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro old _
      ac_rfl
    _ = _ := by rw [hm]

omit rewards C_star C_h control0 in
private theorem measurable_optional_elim
    (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun o : Option (LogicalCell p rate) => o.elim 0 f) := by
  have hm : Measurable (Sum.elim f (fun _ : PUnit => (0 : ℝ≥0∞))) :=
    hf.sumElim measurable_const
  convert hm.comp (comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))) using 1
  funext o
  cases o <;> rfl

omit rewards C_star C_h control0 in
private theorem measurable_slow_indicator (U : SlowSet p) :
    Measurable (fun o : Option (LogicalCell p rate) =>
      o.elim (0 : ℝ≥0∞) (fun e => if e.slowSet = U then 1 else 0)) := by
  apply measurable_optional_elim
  exact measurable_const.ite
    ((measurableSet_singleton U).preimage
      (measurable_logicalCell_slowSet.mono le_rfl le_top)) measurable_const

private theorem terminal_retained_transition_integral
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w : Omega, optionalTransitionTest rate s q F
      (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q)) =
    ∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
      (fun e => episodeTransitionTest rate rewards C_star C_h s q F
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q) := by
  have hE := (ReferenceGeneratedCalendarEpisodeInitialLaw.measurableSet_episodeStartEvent
    rate rewards C_star C_h control0 s).inter
      (measurableSet_retainedEvent rate rewards C_star C_h control0 s q)
  rw [← lintegral_indicator hE, ← lintegral_indicator hE]
  calc
    _ = ∫⁻ w : Omega, retainedSourceTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
        ∂ids.elim Lambda fixedLambda := by
      apply lintegral_congr_ae
      filter_upwards [ae_retainedSourceTest rate rewards C_star C_h control0 ids] with w hw
      rw [hw s q F]
      simp only [Set.indicator, Set.mem_inter_iff]
    _ = ∫⁻ w : Omega, retainedKernelTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
        ∂ids.elim Lambda fixedLambda :=
      ReferenceGeneratedCalendarEpisodeTerminalTransition.terminal_retained_transition_test
        rate rewards C_star C_h control0 ids s q hsq F hF
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_retainedKernelTest rate rewards C_star C_h control0 ids] with w hw
      rw [hw s q F]
      by_cases h : w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q
      · simp only [Set.indicator, Set.mem_inter_iff] at h ⊢
        rw [ite_eq_left h, ite_eq_left h]
        cases currentMark rate rewards C_star C_h control0 q w <;> rfl
      · simp only [Set.indicator, Set.mem_inter_iff] at h ⊢
        rw [ite_eq_right h, ite_eq_right h]

private theorem retained_marginal_of_cylinders
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hcylinder : ∀ (U : SlowSet p) (Phi : History rate s q → ℝ≥0∞), Measurable Phi →
      (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
        (currentMark rate rewards C_star C_h control0 q w).elim 0
          (fun e => if e.slowSet = U then 1 else 0)
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s q)) =
      ∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
        sourceEpisodeMass rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s q))
    (G : History rate s q × SlowSet p → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
      (fun e => G (sourceEstimateHistory rate rewards C_star C_h control0 s q w, e.slowSet))
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q)) =
    ∫⁻ w : Omega, ∑ U : SlowSet p,
      G (sourceEstimateHistory rate rewards C_star C_h control0 s q w, U) *
        sourceEpisodeMass rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q) := by
  have hGU (U : SlowSet p) : Measurable (fun h : History rate s q => G (h, U)) :=
    hG.comp (measurable_id.prodMk measurable_const)
  have hH := measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q
  have hmark := measurable_currentMark rate rewards C_star C_h control0 q
  calc
    _ = ∫⁻ w : Omega, ∑ U : SlowSet p,
        G (sourceEstimateHistory rate rewards C_star C_h control0 s q w, U) *
          (currentMark rate rewards C_star C_h control0 q w).elim 0
            (fun e => if e.slowSet = U then 1 else 0) ∂_ := by
      apply lintegral_congr
      intro w
      cases he : currentMark rate rewards C_star C_h control0 q w with
      | none => simp only [Option.elim_none, mul_zero, Finset.sum_const_zero]
      | some e => simp only [Option.elim_some, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = ∑ U : SlowSet p, ∫⁻ w : Omega,
        G (sourceEstimateHistory rate rewards C_star C_h control0 s q w, U) *
          (currentMark rate rewards C_star C_h control0 q w).elim 0
            (fun e => if e.slowSet = U then 1 else 0) ∂_ :=
      lintegral_finsetSum _ (fun U _ => ((hGU U).comp hH).mul
        ((measurable_slow_indicator rate U).comp hmark))
    _ = ∑ U : SlowSet p, ∫⁻ w : Omega,
        G (sourceEstimateHistory rate rewards C_star C_h control0 s q w, U) *
          sourceEpisodeMass rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U ∂_ := by
      apply Finset.sum_congr rfl
      intro U _
      exact hcylinder U _ (hGU U)
    _ = _ := (lintegral_finsetSum _ (fun U _ => ((hGU U).comp hH).mul
      ((measurable_sourceEpisodeMass rate rewards C_star C_h s q U).comp hH))).symm

omit control0 in
theorem sourceEpisodeMass_historySuccessor (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (h : History rate s q) (x : Estimate p) (A S : RecordedQueueRun.RunState p.K)
    (hA : ReferencePostInvocationNoncallGeometry.prefixNumerical
      rate rewards C_star C_h s.castSucc h.1.1 = some A)
    (hS : sourceEpisodeReplay rate rewards C_star C_h s q h = some S) (U : SlowSet p) :
    sourceEpisodeMass rate rewards C_star C_h s r
        (historySuccessor rate s q r hqr (h, x)) U =
      RecordedSlowRefresh.recordedSlowPMF p Q (estimateStep rate S true x)
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U := by
  unfold sourceEpisodeMass
  rw [sourceEpisodeReplay_historySuccessor rate rewards C_star C_h s q r hsq hqr,
    hS, Option.map_some]
  change (match ReferencePostInvocationNoncallGeometry.prefixNumerical
    rate rewards C_star C_h s.castSucc h.1.1, some (estimateStep rate S true x) with
    | some A, some S => RecordedSlowRefresh.recordedSlowPMF p Q S
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U
    | _, _ => 0) = _
  rw [hA]

omit control0 in
/-- The next retained gate implies the incoming gate. No post-update success
condition is imposed on the current round's transition law. -/
theorem sourceHistoryRetained_historySuccessor (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (h : History rate s q) (x : Estimate p)
    (hr : historySuccessor rate s q r hqr (h, x) ∈
      sourceHistoryRetained rate rewards C_star C_h s r) :
    h ∈ sourceHistoryRetained rate rewards C_star C_h s q := by
  rcases hr with ⟨_, hbound, hclear⟩
  refine ⟨hsq, by omega, ?_⟩
  rw [sourceEpisodeReplay_historySuccessor rate rewards C_star C_h s q r hsq hqr] at hclear
  cases hS : sourceEpisodeReplay rate rewards C_star C_h s q h with
  | none => simp only [hS, Option.map_none, Option.any_none, Bool.false_eq_true] at hclear
  | some S =>
    simp only [hS, Option.map_some, Option.any_some, Bool.not_eq_true'] at hclear
    have hc : S.overflow = false := by
      cases ho : S.overflow with
      | false => rfl
      | true =>
        have hstop : (estimateStep rate S true x).overflow = true := by
          simp only [estimateStep, ho, Bool.true_or]
        rw [hstop] at hclear
        cases hclear
    simp only [Option.any_some, hc, Bool.not_false]

omit C_star C_h control0 in
private theorem episodeRoundTest_forget_next (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K) (old : SlowSet p)
    (f : Estimate p → ℝ≥0∞) :
    episodeRoundTest rate rewards q A S old (fun x _ _ => f x) =
      ∑ i : Option (Fin p.K), f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
        (episodeRoundInput rate rewards q A i)) *
        RecordedRoundMoments.recordingOutcomePMF
          (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
            (RecordedSlowRefresh.scoreWeight_pos Q A)) i := by
  have hn (i : Option (Fin p.K)) (B : Bool) :
      (∑ V : SlowSet p, episodeNextLaw rate rewards q A S old i B {V}) = 1 := by
    unfold episodeNextLaw
    split
    · simp only [sum_measure_singleton, Finset.coe_univ, measure_univ]
    · split
      · simp only [sum_measure_singleton, Finset.coe_univ, measure_univ]
      · simp only [sum_measure_singleton, Finset.coe_univ, measure_univ]
  have hb : (∑ B : Bool,
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}) = 1 := by
    simp only [sum_measure_singleton, Finset.coe_univ, measure_univ]
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  have hsum (B : Bool) :
      (∑ V : SlowSet p, f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
        (episodeRoundInput rate rewards q A i)) *
          (episodeNextLaw rate rewards q A S old i B {V} *
            (RecordedRoundMoments.recordingOutcomePMF
              (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
                (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
              ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}))) =
        f (RecordedQuantizedEstimateReplay.sourceEstimate Q S
          (episodeRoundInput rate rewards q A i)) *
          ((∑ V : SlowSet p, episodeNextLaw rate rewards q A S old i B {V}) *
            (RecordedRoundMoments.recordingOutcomePMF
              (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
                (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
              ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B})) := by
    rw [Finset.sum_mul, Finset.mul_sum]
  simp only [hsum, hn, one_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hb, mul_one]

omit control0 in
private theorem episodeTransitionTest_slow_mixture (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (h : History rate s q) (A S : RecordedQueueRun.RunState p.K)
    (hA : ReferencePostInvocationNoncallGeometry.prefixNumerical
      rate rewards C_star C_h s.castSucc h.1.1 = some A)
    (hS : sourceEpisodeReplay rate rewards C_star C_h s q h = some S)
    (hclear : S.overflow = false) (U old : SlowSet p)
    (f : History rate s r → ℝ≥0∞) :
    (∑ V : SlowSet p, sourceEpisodeMass rate rewards C_star C_h s q h V *
      episodeTransitionTest rate rewards C_star C_h s q
        (fun y => f (historySuccessor rate s q r hqr (y.1, y.2.2.1)) *
          if y.2.2.2.2 = U then 1 else 0) h V) =
    episodeTransitionTest rate rewards C_star C_h s q
      (fun y => f (historySuccessor rate s q r hqr (y.1, y.2.2.1)) *
        sourceEpisodeMass rate rewards C_star C_h s r
          (historySuccessor rate s q r hqr (y.1, y.2.2.1)) U) h old := by
  have hmV (V : SlowSet p) : sourceEpisodeMass rate rewards C_star C_h s q h V =
      RecordedSlowRefresh.recordedSlowPMF p Q S (RecordedQueueRun.scoreWeight Q A)
        (RecordedSlowRefresh.scoreWeight_pos Q A) V := by
    simp only [sourceEpisodeMass, hA, hS]
  simp only [hmV, episodeTransitionTest, hA, hS]
  rw [episodeRoundTest_slow_mixture rate rewards q A S hclear,
    episodeRoundTest_forget_next]
  apply Finset.sum_congr rfl
  intro i _
  have hm := sourceEpisodeMass_historySuccessor rate rewards C_star C_h
    s q r hsq hqr h (RecordedQuantizedEstimateReplay.sourceEstimate Q S
      (episodeRoundInput rate rewards q A i)) A S hA hS U
  have hstep : estimateStep rate S true (RecordedQuantizedEstimateReplay.sourceEstimate Q S
      (episodeRoundInput rate rewards q A i)) =
      RecordedQueueRun.step Q S (episodeRoundInput rate rewards q A i) :=
    RecordedQuantizedEstimateReplay.stepFromSourceEstimate_eq_step Q S
      (episodeRoundInput rate rewards q A i)
  rw [hstep] at hm
  rw [hm]

private theorem transition_cylinder_from_incoming
    (ids : Option (CompletePublicTable.IDArray p)) (s q r : Fin p.T)
    (hsq : s.val ≤ q.val) (hqr : r.val = q.val + 1)
    (hcylinder : ∀ (U : SlowSet p) (Phi : History rate s q → ℝ≥0∞), Measurable Phi →
      (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
        (currentMark rate rewards C_star C_h control0 q w).elim 0
          (fun e => if e.slowSet = U then 1 else 0)
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s q)) =
      ∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
        sourceEpisodeMass rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s q))
    (U : SlowSet p) (f : History rate s r → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
      (fun e => f (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        if e.nextSlowSet = U then 1 else 0)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q)) =
    ∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
      (fun _ => f (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        sourceEpisodeMass rate rewards C_star C_h s r
          (sourceEstimateHistory rate rewards C_star C_h control0 s r w) U)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q) := by
  let F : TransitionData rate s q → ℝ≥0∞ := fun y =>
    f (historySuccessor rate s q r hqr (y.1, y.2.2.1)) *
      if y.2.2.2.2 = U then 1 else 0
  let G : TransitionData rate s q → ℝ≥0∞ := fun y =>
    f (historySuccessor rate s q r hqr (y.1, y.2.2.1)) *
      sourceEpisodeMass rate rewards C_star C_h s r
        (historySuccessor rate s q r hqr (y.1, y.2.2.1)) U
  have hh : Measurable (fun y : TransitionData rate s q =>
      historySuccessor rate s q r hqr (y.1, y.2.2.1)) :=
    (measurable_historySuccessor rate s q r hqr).comp
      (measurable_fst.prodMk measurable_snd.snd.fst)
  have hF : Measurable F := (hf.comp hh).mul
    (measurable_const.ite ((measurableSet_singleton U).preimage
      measurable_snd.snd.snd.snd) measurable_const)
  have hG : Measurable G := (hf.comp hh).mul
    ((measurable_sourceEpisodeMass rate rewards C_star C_h s r U).comp hh)
  let E := episodeStartEvent rate rewards C_star C_h control0 s ∩
    retainedEvent rate rewards C_star C_h control0 s q
  let mu := (ids.elim Lambda fixedLambda).restrict E
  have hactual (J : History rate s r → SlowSet p → ℝ≥0∞) (w : Omega) :
      optionalTransitionTest rate s q
        (fun y => J (historySuccessor rate s q r hqr (y.1, y.2.2.1)) y.2.2.2.2)
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) =
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => J (sourceEstimateHistory rate rewards C_star C_h control0 s r w) e.nextSlowSet) := by
    dsimp only [optionalTransitionTest, terminalSourceJoint]
    cases he : currentMark rate rewards C_star C_h control0 q w with
    | none => rfl
    | some e =>
      dsimp only [Option.elim_some]
      rw [historySuccessor_sourceEstimateHistory]
  calc
    _ = ∫⁻ w : Omega, optionalTransitionTest rate s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) ∂mu := by
      apply lintegral_congr
      intro w
      exact (hactual (fun h V => f h * if V = U then 1 else 0) w).symm
    _ = ∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => episodeTransitionTest rate rewards C_star C_h s q F
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet) ∂mu :=
      terminal_retained_transition_integral rate rewards C_star C_h control0 ids s q hsq F hF
    _ = ∫⁻ w : Omega, ∑ V : SlowSet p,
        episodeTransitionTest rate rewards C_star C_h s q F
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) V *
        sourceEpisodeMass rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) V ∂mu :=
      retained_marginal_of_cylinders rate rewards C_star C_h control0 ids s q hcylinder
        (fun v => episodeTransitionTest rate rewards C_star C_h s q F v.1 v.2)
        (measurable_episodeTransitionTest rate rewards C_star C_h s q F hF)
    _ = ∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => episodeTransitionTest rate rewards C_star C_h s q G
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet) ∂mu := by
      apply lintegral_congr_ae
      have hi := ae_restrict_of_ae (s := E)
        (ae_retained_source_input rate rewards C_star C_h control0 ids)
      have hE : MeasurableSet E :=
        (ReferenceGeneratedCalendarEpisodeInitialLaw.measurableSet_episodeStartEvent
          rate rewards C_star C_h control0 s).inter
          (measurableSet_retainedEvent rate rewards C_star C_h control0 s q)
      filter_upwards [hi, ae_restrict_mem (μ := ids.elim Lambda fixedLambda) hE] with w hw hwE
      obtain ⟨e, A, i, he, hc, _, hA, hS, _⟩ := hw s q hwE.1 hwE.2
      rw [he, Option.elim_some]
      simp_rw [mul_comm]
      exact episodeTransitionTest_slow_mixture rate rewards C_star C_h s q r hsq hqr
        _ A e.before hA hS hc U e.slowSet f
    _ = ∫⁻ w : Omega, optionalTransitionTest rate s q G
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) ∂mu :=
      (terminal_retained_transition_integral rate rewards C_star C_h control0 ids s q hsq G hG).symm
    _ = _ := by
      apply lintegral_congr
      intro w
      exact hactual (fun h _ => f h * sourceEpisodeMass rate rewards C_star C_h s r h U) w

/-- The first actual UPDATE's post-set cylinder, with its revealed source
estimate and without a POST-clear restriction. This is the base producer
followed by the common transition producer, including a detecting overflow
UPDATE. The post-set is not identified here with a later physical mark. -/
theorem terminalLaw_retained_initial_update_cylinder
    (ids : Option (CompletePublicTable.IDArray p)) (s r : Fin p.T)
    (hsr : r.val = s.val + 1) (U : SlowSet p)
    (Phi : History rate s r → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 s w).elim 0
      (fun e => Phi (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        if e.nextSlowSet = U then 1 else 0)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s s)) =
    ∫⁻ w : Omega, (currentMark rate rewards C_star C_h control0 s w).elim 0
      (fun _ => Phi (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        sourceEpisodeMass rate rewards C_star C_h s r
          (sourceEstimateHistory rate rewards C_star C_h control0 s r w) U)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s s) :=
  transition_cylinder_from_incoming rate rewards C_star C_h control0 ids s s r le_rfl hsr
    (terminalLaw_retained_initial_cylinder rate rewards C_star C_h control0 ids s) U Phi hPhi

/-- Actual next-round retention implies current-round retention, derived
from the SAME source-history fold and its absorbing overflow flag. -/
theorem ae_retainedEvent_successor (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim Lambda fixedLambda, ∀ (s q r : Fin p.T),
      w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
      s.val ≤ q.val → r.val = q.val + 1 →
      w ∈ retainedEvent rate rewards C_star C_h control0 s r →
      w ∈ retainedEvent rate rewards C_star C_h control0 s q := by
  filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids] with w hw
  intro s q r hs hsq hqr hr
  apply (hw s q hs).mpr
  have hnext := (hw s r hs).mp hr
  rw [← historySuccessor_sourceEstimateHistory rate rewards C_star C_h control0 s q r hqr] at hnext
  exact sourceHistoryRetained_historySuccessor rate rewards C_star C_h s q r hsq hqr _ _ hnext

omit control0 in
private theorem wholeLiveCell_payload_eq (z : Source p)
    (j k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length) :
    (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem j.isLt)).selected.view.payload =
      (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem k.isLt)).selected.view.payload := by
  let W := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hp : W <+: R := List.takeWhile_prefix _
  obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z ⟨j.val, j.isLt.trans_le hp.length_le⟩
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hc
  have hR := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hl
  let cj := wholeLiveCell rate rewards C_star C_h z W[j.val] (List.getElem_mem j.isLt)
  let ck := wholeLiveCell rate rewards C_star C_h z W[k.val] (List.getElem_mem k.isLt)
  exact ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate z rewards C_star C_h initial hl)
    seed.coordinatorFirst W[j.val] W[k.val] cj.selected ck.selected
    (by rw [← hR]; exact hp.subset (List.getElem_mem j.isLt))
    (by rw [← hR]; exact hp.subset (List.getElem_mem k.isLt))
    cj.selection_actual ck.selection_actual
    ((wholeLiveCell_geometry rate rewards C_star C_h z j).2.1.trans
      (wholeLiveCell_geometry rate rewards C_star C_h z k).2.1.symm)

omit control0 in
private theorem firstLive_next_slow (z : Source p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (j k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length) (hjk : j.val < k.val)
    (hjclear : ((firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[j.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact j.isLt)).before.overflow = false)
    (hkclear : ((firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact k.isLt)).before.overflow = false) :
    ((firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[j.val]'(by
      rw [firstLiveChronologicalPrefix_length]; exact j.isLt)).nextSlowSet =
      ((firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[k.val]'(by
        rw [firstLiveChronologicalPrefix_length]; exact k.isLt)).slowSet := by
  have hprop := firstLiveChronologicalPrefix_earlier_proposal
    rate rewards C_star C_h z a j k hjk
  simp only [firstLiveChronologicalPrefix_get, appendLogicalCell] at hjclear hkclear hprop ⊢
  rw [hprop]
  simp only [hjclear, hkclear, Bool.false_eq_true, ite_false]
  exact congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.slowSet)
    (wholeLiveCell_payload_eq rate rewards C_star C_h z j k)

omit rewards C_star C_h control0 in
private theorem incomingFromList_filter_successor
    (L : List (LogicalCell p rate))
    (hL : L.Pairwise (fun e f => e.time.val < f.time.val))
    (q r : Fin p.T) (hqr : r.val = q.val + 1)
    (e : LogicalCell p rate) (he : e ∈ L) (ht : e.time = q) :
    ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate
      (L.filter (fun f => f.time.val < r.val)) = some e.nextSlowSet := by
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp he
  rw [hsplit] at hL ⊢
  obtain ⟨_, htail, hcross⟩ := List.pairwise_append.mp hL
  have hbefore : before.filter (fun f => f.time.val < r.val) = before := by
    apply List.filter_eq_self.mpr
    intro f hf
    have hlt := hcross f hf e (List.mem_cons_self)
    rw [ht] at hlt
    exact decide_eq_true (by omega)
  have hafter : after.filter (fun f => f.time.val < r.val) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro f hf
    have hlt := (List.pairwise_cons.mp htail).1 f hf
    rw [ht] at hlt
    simp only [decide_eq_true_eq]
    omega
  simp only [List.filter_append, hbefore, List.filter_cons, ht,
    decide_eq_true (by omega : q.val < r.val), ite_true, hafter,
    ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList,
    List.getLast?_append_cons, List.getLast?_singleton, Option.map_some]

omit control0 in
private theorem extendedPast_next_slow (z : Source p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (n : Fin (p.T + 1))
    (hL : (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      n (z, a)).Pairwise (fun e f => e.time.val < f.time.val))
    (q r : Fin p.T) (hqr : r.val = q.val + 1) (hrn : r.val < n.val)
    (e f : LogicalCell p rate)
    (he : e ∈ ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h n (z, a))
    (hf : f ∈ ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h n (z, a))
    (hte : e.time = q) (htf : f.time = r)
    (heclear : e.before.overflow = false) (hfclear : f.before.overflow = false) :
    e.nextSlowSet = f.slowSet := by
  let L := firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)
  by_cases hflive : f ∈ L
  · obtain ⟨k, hk, hkf⟩ := List.mem_iff_getElem.mp hflive
    dsimp only [L] at hkf
    have hkW : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length := by
      simpa only [L, firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    have hkt := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
      rate rewards C_star C_h z a ⟨k, hkW⟩
    rw [hkf, htf] at hkt
    have hkcal : r.val = ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h + k :=
      (congrArg Fin.val hkt).trans (wholeLiveCell_geometry rate rewards C_star C_h z ⟨k, hkW⟩).2.2.1
    have helive : e ∈ L := by
      by_contra hn
      obtain ⟨t, rec, hr, hm, U, _, _, _, ht, _⟩ :=
        ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields
          rate rewards C_star C_h n z a e he hn
      have hstart := ReferenceFirstCollectionLogicalPrefixExtension.collectionStart_le_of_actualDomain
        rate rewards C_star C_h t z ⟨rec, hr, hm⟩
      have hte' : t = q := ht.symm.trans hte
      rw [hte'] at hstart
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z ≤ q.val at hstart
      unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength at hstart
      omega
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp helive
    dsimp only [L] at hje
    have hjW : j < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length := by
      simpa only [L, firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hj
    have hjt := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
      rate rewards C_star C_h z a ⟨j, hjW⟩
    rw [hje, hte] at hjt
    have hjcal : q.val = ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h + j :=
      (congrArg Fin.val hjt).trans (wholeLiveCell_geometry rate rewards C_star C_h z ⟨j, hjW⟩).2.2.1
    have hjk : j < k := by omega
    have h := firstLive_next_slow rate rewards C_star C_h z a ⟨j, hjW⟩ ⟨k, hkW⟩ hjk
      (by simpa only [hje] using heclear) (by simpa only [hkf] using hfclear)
    simpa only [hje, hkf] using h
  · obtain ⟨t, rec, hr, hm, U, _, hU, _, ht, _, _, hpre, _, _, _, hslow, _⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields
        rate rewards C_star C_h n z a f hf hflive
    have htr : t = r := ht.symm.trans htf
    have hU' : (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux
        rate rewards C_star C_h r.val r.isLt.le (z, a)).1 = some U := by
      cases htr
      exact hU
    have hslow' : f.slowSet = U := by
      rw [← hpre, hfclear] at hslow
      exact hslow
    have hseed := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_seed
      rate rewards C_star C_h r.val r.isLt.le (z, a)
    change _ = ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        r.castSucc (z, a)) at hseed
    have hlast := incomingFromList_filter_successor rate
      (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h n (z, a))
      hL q r hqr e he hte
    have hfilter := ReferenceGeneratedCalendarEpisodePrefixRecombination.extendedPast_filter
      rate rewards C_star C_h r.castSucc n hrn.le (z, a)
    change (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      n (z, a)).filter (fun f => f.time.val < r.val) = _ at hfilter
    rw [hfilter, ← hseed, hU'] at hlast
    exact (Option.some.inj hlast).symm.trans hslow'.symm

/-- Before the first call, actual adjacent marks join through the accepted
extended-prefix recurrence. The LIVE case uses the original common payload
and derives the earlier proposal's false value; COLLECTION uses the carried
seed. No recorder label is added to the exposed estimate history. -/
theorem beforeFirstCall_next_slow (q r : Fin p.T) (hqr : r.val = q.val + 1)
    (w : Omega)
    (hbefore : w ∈ ReferenceGeneratedCalendarEpisodePrefixRecombination.beforeFirstCall
      rate rewards C_star C_h r.succ)
    (e f : LogicalCell p rate)
    (he : currentMark rate rewards C_star C_h control0 q w = some e)
    (hf : currentMark rate rewards C_star C_h control0 r w = some f)
    (heclear : e.before.overflow = false) (hfclear : f.before.overflow = false) :
    e.nextSlowSet = f.slowSet := by
  let z := ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w
  let a := ReferenceGeneratedCalendarEpisodePrefixRecombination.auxiliary rate rewards C_star C_h control0 w
  have hp := ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore_eq_extendedPast
    rate rewards C_star C_h control0 r.succ w hbefore
  change (archive rate rewards C_star C_h control0 w).filter
    (fun c => c.time.val < r.val + 1) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
        rate rewards C_star C_h r.succ (z, a) at hp
  obtain ⟨hem, het⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he
  obtain ⟨hfm, hft⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 r w f).mp hf
  have he' : e ∈ ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
      rate rewards C_star C_h r.succ (z, a) := by
    rw [← hp]
    exact List.mem_filter.mpr ⟨hem, decide_eq_true (by rw [het]; omega)⟩
  have hf' : f ∈ ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
      rate rewards C_star C_h r.succ (z, a) := by
    rw [← hp]
    exact List.mem_filter.mpr ⟨hfm, decide_eq_true (by rw [hft]; omega)⟩
  have hchron : (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
      rate rewards C_star C_h r.succ (z, a)).Pairwise
        (fun e f => e.time.val < f.time.val) := by
    rw [← hp]
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).filter _
  exact extendedPast_next_slow rate rewards C_star C_h z a r.succ hchron
    q r hqr (by simp only [Fin.val_succ]; omega) e f he' hf' het hft heclear hfclear

section CalendarChronology

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarLaterRenewalSlowInitialization
open ReferenceFirstCollectionLogicalPrefixExtension ReferencePostInvocationNoncallGeometry
open ReferenceNextRetainedEndpointFibreLaw

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "flags" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "stepCell" => calendarStepCell rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0

private theorem calendarStoredState_seed (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) : some (stored k hk w).1 = incomingFromList rate (stored k hk w).2 := by
  induction k with
  | zero =>
    rw [(calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 hk w).2.1]
    simp only [incomingFromList, List.getLast?_append_cons, List.getLast?_singleton,
      Option.map_some]
  | succ k ih =>
    change Sample k × AssignmentParameterFibreKernel.AssignmentVector p at w
    rw [calendarStoredState_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2]
    cases he : stepCell k (by omega) w.1 w.2 with
    | none => exact ih (by omega) w.1
    | some e =>
      simp only [incomingFromList, List.getLast?_append_cons, List.getLast?_singleton,
        Option.map_some]

private theorem ancestor_fst (k : ℕ) (w : Sample k) (j : ℕ) (hj : j < k) :
    (ancestor k (j + 1) (by omega) w).1 = ancestor k j (by omega) w := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hjk : j = k
    · subst j
      rw [calendarAncestor_self,
        calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k k le_rfl w,
        calendarAncestor_self]
    · have hjk' : j < k := by omega
      rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w,
        calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j (by omega) w]
      exact ih w.1 hjk'

private theorem ae_calendar_later_next_slow (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    ∀ᵐ w ∂law k hk, ∀ (j : ℕ) (hj : j < k),
      let r : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
      ∀ (q : Fin p.T), r.val = q.val + 1 → ∀ (e f : LogicalCell p rate),
        e ∈ (stored k hk w).2 → e.time = q →
        (stored k hk w).2.find? (fun c => c.time == r) = some f →
        f.before.overflow = false →
        prefixNumerical rate rewards C_star C_h r.castSucc (current k hk w) = some f.before →
        current k hk w ∉ sourceStartEvent rate rewards C_star C_h r →
        e.nextSlowSet = f.slowSet := by
  filter_upwards [ae_calendarLaw_archived_path rate rewards C_star C_h control0 b0 u0 t0 k hk]
    with w hpath
  intro j hj r q hqr e f he hte hf hfclear hpre hnotstart
  let x : Sample j × AssignmentParameterFibreKernel.AssignmentVector p := ancestor k (j + 1) (by omega) w
  have hx : x.1 = ancestor k j (by omega) w := ancestor_fst rate rewards C_star C_h b0 u0 t0 k w j hj
  have hlast := incomingFromList_filter_successor rate (stored k hk w).2 hpath.2.2.2.2.1
    q r hqr e he hte
  have hfilter := calendar_archiveBefore_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj.le
  change ((stored k hk w).2.filter (fun c => c.time.val < r.val)) = _ at hfilter
  rw [hfilter, ← hx, ← calendarStoredState_seed rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1] at hlast
  have hcarry : (stored j (by omega) x.1).1 = e.nextSlowSet := Option.some.inj hlast
  have hstep : stepCell j (by omega) x.1 x.2 = some f := by
    rw [← calendar_find_time_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj]
    exact hf
  have hnum := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0
    b0 u0 t0 k hk w j hj.le).2.2
  rw [← hx] at hnum
  have hnum' : (observe j (by omega) x.1).2.val.2.2.1 = some f.before := hnum.symm.trans hpre
  have hclear : (flags j (by omega) x.1).2 = true := by
    change ((observe j (by omega) x.1).2.val.2.2.1).any (fun S => !S.overflow) = true
    rw [hnum', Option.any_some, hfclear]
    rfl
  have hprefix := calendar_step_prefix rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj
  have hn : current j (by omega) x.1 ∉ sourceStartEvent rate rewards C_star C_h r := by
    intro hs
    apply hnotstart
    apply (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 r _).mpr
    rw [hprefix]
    exact (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 r _).mp hs
  have hjoins := hpath.2.2.2.2.2.2.2 j hj
  cases hc : callFlag j (by omega) x.1 with
  | false =>
    rw [calendarStepCell, dite_eq_right (by rw [hc]; exact Bool.false_ne_true)] at hstep
    have hjoin := calendarObservation_noncall_clear_cell rate rewards C_star C_h control0
      b0 u0 t0 j (by omega) x.1 x.2 hc hclear f hstep
    exact hcarry.symm.trans hjoin.1.symm
  | true =>
    have hcall : (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
        r (current j (by omega) x.1)).isSome = true := hc
    have hnr : renewalFlag rate rewards C_star C_h (t := (observe j (by omega) x.1).1)
        r (observe j (by omega) x.1).2.val = false := by
      apply Bool.eq_false_iff.mpr
      intro hrenew
      apply hn
      refine ⟨Or.inr ⟨hcall, ?_⟩, ?_⟩
      · rw [incomingFreezeAt_eq_oldFreezeAt_on_call rate rewards C_star C_h r _ hcall]
        exact hrenew
      · have hlocal : prefixNumerical rate rewards C_star C_h r.castSucc
            (current j (by omega) x.1) = some f.before :=
          (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0
            j (by omega) x.1).symm.trans hnum'
        rw [hlocal, Option.any_some, hfclear]
        rfl
    obtain ⟨_, _, cutoff, theta, _, _, hjoin, _⟩ := (hjoins.1 hc hclear)
    change (if renewalFlag rate rewards C_star C_h (t := (observe j (by omega) x.1).1)
        r (observe j (by omega) x.1).2.val then
      freshEndpoint theta ((calendarOriginalLift rate rewards C_star C_h b0 u0 t0 j x.1).1.2 (r, 1))
      else some (stored j (by omega) x.1).1) =
        some (calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 j (by omega)
          x.1 x.2 hc).slowSet at hjoin
    simp only [hnr, Bool.false_eq_true, ite_false] at hjoin
    rw [calendarStepCell, dite_eq_left hc] at hstep
    have hcell := Option.some.inj hstep
    rw [hcell] at hjoin
    exact hcarry.symm.trans (Option.some.inj hjoin)

end CalendarChronology

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension ReferencePostInvocationNoncallGeometry

omit control0 in
private theorem firstCell_noCallBefore (u t r : Fin p.T) (hrt : r.val < t.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) : NoCallBefore rate rewards C_star C_h r.succ z := by
  intro v hv
  apply (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mpr
  apply (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
    rate rewards C_star C_h v z).mp ?_ v le_rfl
  rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz]
  simp only [Fin.val_succ] at hv
  omega

omit control0 in
private theorem firstCell_call_present (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true := by
  obtain ⟨c, hc, hct⟩ := Option.map_eq_some_iff.mp hz
  have ht : c.2.1 = t := congrArg Prod.snd hct
  have hf := ReferenceCalendarCollectionCallControlLaw.firstAt_eq rate rewards C_star C_h t z
  unfold ReferenceCalendarCollectionCallControlLaw.firstAt at hf
  rw [hc, Option.bind_some, ht, ite_eq_left rfl] at hf
  split at hf
  · rw [← hf]
    rfl
  · cases hf

omit rate rewards C_star C_h control0 in
private theorem measurableEmbedding_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : MeasurableEmbedding (Sigma.mk i : B i → Sigma B) := by
  refine ⟨fun _ _ h => by cases h; rfl,
    measurable_iff_le_map.mpr (iInf_le _ i), ?_⟩
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' ((Sigma.mk i) '' U))
  by_cases hji : j = i
  · subst j
    rwa [Set.preimage_image_eq _ (show Function.Injective (Sigma.mk i : B i → Sigma B) from
      fun _ _ h => by cases h; rfl)]
  · have he : (Sigma.mk j) ⁻¹' ((Sigma.mk i) '' U) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨y, _, hy⟩
      exact hji (congrArg Sigma.fst hy).symm
    rw [he]
    exact MeasurableSet.empty

private theorem ae_terminal_next_slow_raw :
    ∀ᵐ w ∂Lambda, ∀ (q r : Fin p.T), r.val = q.val + 1 → ∀ (e f : LogicalCell p rate),
      currentMark rate rewards C_star C_h control0 q w = some e →
      currentMark rate rewards C_star C_h control0 r w = some f →
      e.before.overflow = false → f.before.overflow = false →
      prefixNumerical rate rewards C_star C_h r.castSucc
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w) = some f.before →
      w ∉ episodeStartEvent rate rewards C_star C_h control0 r → e.nextSlowSet = f.slowSet := by
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw]
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_sigma_mk i).ae_map_iff.mpr
  cases i with
  | noCall =>
    filter_upwards [] with w
    intro q r hqr e f he hf hec hfc _ _
    apply beforeFirstCall_next_slow rate rewards C_star C_h control0 q r hqr _ ?_ e f he hf hec hfc
    intro v hv
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
      rate rewards C_star C_h w.1.val).mpr w.1.property v v.isLt
  | stopped u t =>
    filter_upwards [] with w
    intro q r hqr e f he hf hec hfc _ _
    by_cases hrt : r.val < t.val
    · have hb : (⟨.stopped u t, w⟩ : Omega) ∈ beforeFirstCall rate rewards C_star C_h r.succ := by
        change NoCallBefore rate rewards C_star C_h r.succ w.1.val
        exact firstCell_noCallBefore rate rewards C_star C_h u t r hrt w.1.val w.1.property.1.1
      exact beforeFirstCall_next_slow rate rewards C_star C_h control0 q r hqr _ hb e f he hf hec hfc
    · obtain ⟨hm, ht⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 r _ f).mp hf
      have hdate : t.val ≤ f.time.val := by rw [ht]; omega
      have hs := (ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
        rate rewards C_star C_h control0 u t (Fin.last p.T) w f hm hdate).2
      have hstop : f.before.overflow = true := by
        rw [hs]
        exact ReferenceInitialStoppedCalendar.suffixBefore_stopped rate rewards C_star C_h u t f.time hdate w.1
      rw [hfc] at hstop
      cases hstop
  | generated b u t =>
    let k := p.T - (t.val + 1)
    have hk : t.val + 1 + k ≤ p.T := by dsimp only [k]; omega
    filter_upwards [ae_calendar_later_next_slow rate rewards C_star C_h control0 b u t k hk,
      ae_calendarLaw_archived_path rate rewards C_star C_h control0 b u t k hk] with w hlater hpath
    intro q r hqr e f he hf hec hfc hpre hn
    let original := calendarOriginalLift rate rewards C_star C_h b u t k w
    have hcell : original.1.1.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t := by
      cases b with
      | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
          rate rewards C_star C_h u t _ original.1.1.property).1
      | true => exact original.1.1.property.1
    by_cases hrt : r.val < t.val
    · have hb : (⟨.generated b u t, w⟩ : Omega) ∈ beforeFirstCall rate rewards C_star C_h r.succ := by
        change NoCallBefore rate rewards C_star C_h r.succ original.1.1.val
        exact firstCell_noCallBefore rate rewards C_star C_h u t r hrt original.1.1.val hcell
      exact beforeFirstCall_next_slow rate rewards C_star C_h control0 q r hqr _ hb e f he hf hec hfc
    · obtain ⟨hem, het⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 q _ e).mp he
      change e ∈ (calendarStoredState rate rewards C_star C_h control0 b u t k hk w).2 at hem
      have hfg := hf
      change (calendarStoredState rate rewards C_star C_h control0 b u t k hk w).2.find?
        (fun c => c.time == r) = some f at hfg
      have hpreG := hpre
      change prefixNumerical rate rewards C_star C_h r.castSucc
        (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w) = some f.before at hpreG
      have hnG := hn
      change calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w ∉
        sourceStartEvent rate rewards C_star C_h r at hnG
      by_cases hrtEq : r = t
      · subst r
        let root := calendarAncestor rate rewards C_star C_h b u t k 0 (Nat.zero_le _) w
        let c := calendarLastNativeCell rate rewards C_star C_h control0 b u t 0 (by omega) root
        have hct : c.time = t := by
          rw [show c = calendarRootCell rate rewards C_star C_h control0 b u t root from hpath.1]
          cases b <;> exact ReferenceFirstNextInstallationCellFactors.actualFirstCell_time
            rate rewards C_star C_h control0 t _ _
        have hcm : c ∈ archive rate rewards C_star C_h control0 ⟨.generated b u t, w⟩ := by
          apply (hpath.2.2.2.2.2.2.1 0 (Nat.zero_le _)).1.subset
          rw [hpath.2.1]
          rw [show c = calendarRootCell rate rewards C_star C_h control0 b u t root from hpath.1]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hcf : c = f := Option.some.inj
          (((currentMark_eq_some_iff rate rewards C_star C_h control0 t _ c).mpr ⟨hcm, hct⟩).symm.trans hf)
        have hcclear : c.before.overflow = false := by rw [hcf]; exact hfc
        have hjoin := hpath.2.2.1 hcclear
        change calendarRootEndpoint rate rewards C_star C_h b u t root = some c.slowSet at hjoin
        rw [hcf] at hjoin
        cases b with
        | false =>
          have hlast := incomingFromList_filter_successor rate _ hpath.2.2.2.2.1 q t hqr e hem het
          have hfilter := generated_archiveBefore rate rewards C_star C_h control0
            false u t t.castSucc le_rfl k hk w
          change ((calendarStoredState rate rewards C_star C_h control0 false u t k hk w).2.filter
            (fun c => c.time.val < t.val)) = _ at hfilter
          rw [hfilter] at hlast
          have hseed := extendedPrefixStateAux_seed rate rewards C_star C_h t.val t.isLt.le
            (original.1.1.val, original.1.2)
          change _ = incomingFromList rate (extendedPast rate rewards C_star C_h
            t.castSucc (original.1.1.val, original.1.2)) at hseed
          rw [← hseed] at hlast
          have horig := calendarAncestor_original rate rewards C_star C_h false u t k 0 (Nat.zero_le _) w
          change root = original at horig
          rw [← horig] at hlast
          change calendarRootEndpoint rate rewards C_star C_h false u t root = some e.nextSlowSet at hlast
          exact (Option.some.inj (hlast.symm.trans hjoin))
        | true =>
          apply False.elim
          apply hn
          apply (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 t _).mpr
          have hp := ReferenceGeneratedCalendarEpisodeInitialLaw.generated_sourcePrefix_root
            rate rewards C_star C_h control0 true u t w
          rw [hp]
          apply (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 t _).mp
          have hc := firstCell_call_present rate rewards C_star C_h u t original.1.1.val hcell
          refine ⟨Or.inr ⟨hc, ?_⟩, ?_⟩
          · obtain ⟨g, hg, hgt⟩ := original.1.1.property.2
            rw [incomingFreezeAt_eq_oldFreezeAt_on_call rate rewards C_star C_h t _ hc,
              hg, Option.any_some, decide_eq_true hgt]
          · rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
              rate rewards C_star C_h control0 t.castSucc t.val le_rfl,
              ← hp, ← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
                rate rewards C_star C_h control0 t.castSucc t.val le_rfl, hpre,
              Option.any_some, hfc]
            rfl
      · have htr : t.val < r.val := by
          have hne : r.val ≠ t.val := fun h => hrtEq (Fin.ext h)
          omega
        let j := r.val - t.val - 1
        have hj : j < k := by dsimp only [j, k]; have := r.isLt; omega
        have hrj : (⟨t.val + 1 + j, by omega⟩ : Fin p.T) = r := Fin.ext (by dsimp only [j]; omega)
        have h := hlater j hj q (by rw [hrj]; exact hqr) e f hem het
          (by simpa only [hrj] using hfg) hfc (by simpa only [hrj] using hpreG)
          (by simpa only [hrj] using hnG)
        exact h

/-- On next-round retention in the same episode, both actual marks exist
and the later current set is the previous UPDATE's next set. Original fixed
IDs inherit the same chronology by restriction of the original raw law. -/
theorem ae_retained_successor_marks (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim Lambda fixedLambda, ∀ (s q r : Fin p.T),
      w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
      s.val ≤ q.val → r.val = q.val + 1 →
      w ∈ retainedEvent rate rewards C_star C_h control0 s r →
      w ∈ retainedEvent rate rewards C_star C_h control0 s q ∧
        ∃ e f : LogicalCell p rate,
          currentMark rate rewards C_star C_h control0 q w = some e ∧
          currentMark rate rewards C_star C_h control0 r w = some f ∧
          e.nextSlowSet = f.slowSet := by
  have hac : ids.elim Lambda fixedLambda ≪ Lambda := by
    cases ids with
    | none => exact Measure.AbsolutelyContinuous.rfl
    | some ids =>
      rw [Option.elim_some, ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_eq_restrict]
      exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  filter_upwards [hac.ae_le (ae_terminal_next_slow_raw rate rewards C_star C_h control0),
    ae_source_estimate_numerical_update rate rewards C_star C_h control0 ids,
    ae_retainedEvent_currentMark rate rewards C_star C_h control0 ids,
    ReferenceGeneratedCalendarEpisodeInitialLaw.ae_retained_unique_episodeStart
      rate rewards C_star C_h control0 ids,
    ae_retainedEvent_successor rate rewards C_star C_h control0 ids,
    ae_retained_source_input rate rewards C_star C_h control0 ids] with w hraw hnum hret huniq hmono hi
  intro s q r hs hsq hqr hr
  have hq := hmono s q r hs hsq hqr hr
  obtain ⟨e, A, i, he, hec, _⟩ := hi s q hs hq
  obtain ⟨f, B, j, hf, hfc, _⟩ := hi s r hs hr
  refine ⟨hq, e, f, he, hf, ?_⟩
  apply hraw q r hqr e f he hf hec hfc (hnum r f hf).2.1
  intro hstart
  have hrr := (hret r r f hf).mpr ⟨le_rfl,
    (FollowerCutoffScan.gridBoundary_bounds p rate.eta.val rate.eta.property rate.sourceCap r).1, hfc⟩
  obtain ⟨origin, _, hu⟩ := huniq r f hf hfc
  have hsr : s = r := (hu s ⟨hs, hr⟩).trans (hu r ⟨hstart, hrr⟩).symm
  have hsv := congrArg Fin.val hsr
  omega

/-- The actual retained slow-set cylinder under the raw exhaustive terminal
law and every original fixed-ID law. The only test history is the SAME strict
start history and past source-quantized estimate vectors. No boundedness or
integrability of the nonnegative test is required. -/
theorem terminalLaw_retained_slowSet_cylinder
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (U : SlowSet p) (Phi : History rate s q → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => if e.slowSet = U then 1 else 0)
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q)) =
    ∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w) *
      sourceEpisodeMass rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U
      ∂(ids.elim Lambda fixedLambda).restrict
        (episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q) := by
  have hzero (o : Option (LogicalCell p rate)) : o.elim (0 : ℝ≥0∞) (fun _ => 0) = 0 := by
    cases o <;> rfl
  let P : Fin p.T → Prop := fun r =>
    ∀ (U : SlowSet p) (Phi : History rate s r → ℝ≥0∞), Measurable Phi →
      (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        (currentMark rate rewards C_star C_h control0 r w).elim 0
          (fun e => if e.slowSet = U then 1 else 0)
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s r)) =
      ∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        sourceEpisodeMass rate rewards C_star C_h s r
          (sourceEstimateHistory rate rewards C_star C_h control0 s r w) U
        ∂(ids.elim Lambda fixedLambda).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s ∩
            retainedEvent rate rewards C_star C_h control0 s r)
  have hall : ∀ n : ℕ, ∀ r : Fin p.T, r.val = s.val + n → P r := by
    intro n
    induction n with
    | zero =>
      intro r hr
      have hrs : r = s := Fin.ext (by omega)
      subst r
      exact terminalLaw_retained_initial_cylinder rate rewards C_star C_h control0 ids s
    | succ n ih =>
      intro r hr U Phi hPhi
      let v : Fin p.T := ⟨s.val + n, by have := r.isLt; omega⟩
      have hsv : s.val ≤ v.val := by dsimp only [v]; omega
      have hvr : r.val = v.val + 1 := by dsimp only [v]; omega
      let f : History rate s r → ℝ≥0∞ :=
        (sourceHistoryRetained rate rewards C_star C_h s r).indicator Phi
      have hf : Measurable f := hPhi.indicator
        (measurableSet_sourceHistoryRetained rate rewards C_star C_h s r)
      have hstep := transition_cylinder_from_incoming rate rewards C_star C_h control0
        ids s v r hsv hvr (ih v rfl) U f hf
      have hstart := ReferenceGeneratedCalendarEpisodeInitialLaw.measurableSet_episodeStartEvent
        rate rewards C_star C_h control0 s
      have hEv := hstart.inter (measurableSet_retainedEvent rate rewards C_star C_h control0 s v)
      have hEr := hstart.inter (measurableSet_retainedEvent rate rewards C_star C_h control0 s r)
      rw [← lintegral_indicator hEv, ← lintegral_indicator hEv] at hstep
      change (∫⁻ w : Omega, Phi (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
        (currentMark rate rewards C_star C_h control0 r w).elim 0
          (fun e => if e.slowSet = U then 1 else 0) ∂_) = _
      rw [← lintegral_indicator hEr, ← lintegral_indicator hEr]
      calc
        _ = ∫⁻ w : Omega, (episodeStartEvent rate rewards C_star C_h control0 s ∩
              retainedEvent rate rewards C_star C_h control0 s v).indicator
            (fun w => (currentMark rate rewards C_star C_h control0 v w).elim 0
              (fun e => f (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
                if e.nextSlowSet = U then 1 else 0)) w ∂ids.elim Lambda fixedLambda := by
          apply lintegral_congr_ae
          filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids,
            ae_retained_successor_marks rate rewards C_star C_h control0 ids] with w hgate hmarks
          by_cases hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s
          · by_cases hret : w ∈ retainedEvent rate rewards C_star C_h control0 s r
            · obtain ⟨hv, e, d, he, hd, hnext⟩ := hmarks s v r hs hsv hvr hret
              have hg := (hgate s r hs).mp hret
              simp only [f, Set.indicator, Set.mem_inter_iff, hs, hret, hv, and_self,
                ite_true, he, hd, Option.elim_some, hg, hnext]
            · have hg := mt (hgate s r hs).mpr hret
              simp only [f, Set.indicator, Set.mem_inter_iff, hs, hret, true_and,
                ite_false, hg, zero_mul, hzero, ite_self]
          · simp only [Set.indicator, Set.mem_inter_iff, hs, false_and, ite_false]
        _ = ∫⁻ w : Omega, (episodeStartEvent rate rewards C_star C_h control0 s ∩
              retainedEvent rate rewards C_star C_h control0 s v).indicator
            (fun w => (currentMark rate rewards C_star C_h control0 v w).elim 0
              (fun _ => f (sourceEstimateHistory rate rewards C_star C_h control0 s r w) *
                sourceEpisodeMass rate rewards C_star C_h s r
                  (sourceEstimateHistory rate rewards C_star C_h control0 s r w) U)) w
            ∂ids.elim Lambda fixedLambda := hstep
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids,
            ae_retained_successor_marks rate rewards C_star C_h control0 ids] with w hgate hmarks
          by_cases hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s
          · by_cases hret : w ∈ retainedEvent rate rewards C_star C_h control0 s r
            · obtain ⟨hv, e, d, he, _, _⟩ := hmarks s v r hs hsv hvr hret
              have hg := (hgate s r hs).mp hret
              simp only [f, Set.indicator, Set.mem_inter_iff, hs, hret, hv, and_self,
                ite_true, he, Option.elim_some, hg]
            · have hg := mt (hgate s r hs).mpr hret
              simp only [f, Set.indicator, Set.mem_inter_iff, hs, hret, true_and,
                ite_false, hg, zero_mul, hzero, ite_self]
          · simp only [Set.indicator, Set.mem_inter_iff, hs, false_and, ite_false]
  exact hall (q.val - s.val) q (by omega) U Phi hPhi

end Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowSetCylinder
