/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport
public import Bandits.Support.ReferenceGeneratedCalendarQuantizedRoundKernel

/-!
# ROOT and calendar history transition components

Sources: ZIP4 `04_slow_fast_learner.tex:151-174,176-215,329-390` and
`06_interruptions.tex:391-426`.

This internal component ports the established ROOT transition identity,
chronological history replay, and proposal nonuse results. Its before-first
call and generated-component statements are transport results; they do not
evaluate the missing stochastic kernels. No before-first or later full-kernel
law is established here. The original whole terminal estimate/refresh law and
exhaustive terminal recombination remain open.
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
open ReferenceGeneratedCalendarQuantizedRoundKernel
open ReferenceOriginalCalendarEpisodeChronology
open RecordedQuantizedEstimateReplay

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore

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

local instance optionSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton a := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit A) a))
    convert h using 1
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit A).injective.eq_iff.symm

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0

omit rewards C_star C_h control0 in
/-- A present original raw cell retains its entire original reward row. -/
theorem cell0_reward (r : Record rate) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    c.reward = fun i => ((r.input.rewards r.input.time i).val : ℝ) / (D p : ℝ) := by
  unfold ReferenceFirstCollectionCurrentRetainedGate.cell0 at hc
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some d =>
    rw [hl, Option.some_or] at hc
    cases Option.some.inj hc
    obtain ⟨_, v, _, hr, _⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl
    exact hr
  | none =>
    rw [hl, Option.none_or] at hc
    obtain ⟨P, ledger, started, weights, out, _, _, _, _, _, _, hr, _⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hc
    exact hr

omit C_star C_h control0 in
/-- The actual entire reward row with the recording rates of the strict seed.
The recorder argument is not inferred from the quantized estimate. -/
def episodeRoundInput (q : Fin p.T) (A : RecordedQueueRun.RunState p.K)
    (i : Option (Fin p.K)) : RecordedQueueRun.RoundInput p.K :=
  RecordedRoundMoments.fixedRoundInput Q
    (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A))
    (fun j => ((rewards q j).val : ℝ) / (D p : ℝ)) (gridReward_mem rewards q) true i

/-- The current input has the episode's actual fixed anchor and frozen rates.
This is simultaneous in all dates and in all tests; no slow-set law is used. -/
theorem ae_retained_source_input (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim Lambda
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        w ∈ retainedEvent rate rewards C_star C_h control0 s q →
        ∃ (e : LogicalCell p rate) (A : RecordedQueueRun.RunState p.K)
          (i : Option (Fin p.K)),
          currentMark rate rewards C_star C_h control0 q w = some e ∧
          e.before.overflow = false ∧ A.overflow = false ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A ∧
          sourceEpisodeReplay rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) = some e.before ∧
          e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
            (episodeRoundInput rate rewards q A i) ∧
          sourceEstimateAt rate rewards C_star C_h control0 q w =
            sourceEstimate Q e.before (episodeRoundInput rate rewards q A i) ∧
          e.after = RecordedQueueRun.step Q e.before (episodeRoundInput rate rewards q A i) ∧
          e.arrivals = RecordedQueueRun.acceptedRecord Q e.before (episodeRoundInput rate rewards q A i) ∧
          ∀ U : SlowSet p, sourceEpisodeMass rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U =
            RecordedSlowRefresh.recordedSlowPMF p Q e.before
              (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U := by
  filter_upwards [ae_sourceEpisodeMass_actual rate rewards C_star C_h control0 ids,
    ae_sourceEpisodeReplay rate rewards C_star C_h control0 ids,
    ae_source_estimate_numerical_update rate rewards C_star C_h control0 ids,
    ae_retainedEvent_currentMark rate rewards C_star C_h control0 ids,
    ae_sourceEstimateAt_original_input rate rewards C_star C_h control0 ids] with w hw hr hu ht hi
  intro s q hs hret
  obtain ⟨e, rho, P, A, he, htime, hbirth, hA, hclear, hanchor, hmass⟩ := hw s q hs hret
  obtain ⟨_, hpre, _, harr, hafter, _⟩ := hu q e he
  obtain ⟨hsq, hq, heclear⟩ := (ht s q e he).mp hret
  have hrep := (hr s q hs hsq hq).trans hpre
  obtain ⟨hl, hiW, hnumW, hxW⟩ := hi q e he
  have het := ((currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he).2
  simp only [het] at hiW hnumW hxW
  have hnom := (currentMark_isSome_iff rate rewards C_star C_h control0 q w).mp
    (by rw [he]; rfl)
  obtain ⟨root, P', r, c, v, hr, hc, hcen, _, huniq, hb', _, _, _, _, hrate, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h (Z w) q hnom
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate (Z w) rewards C_star C_h ≤ q.val := by
    by_contra h
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
    rw [ite_eq_right h] at hr
    cases hr
  obtain ⟨_, hin⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt
    rate rewards C_star C_h (Z w) hl q hstart
  rw [hr, Option.bind_some, hc] at hin
  have hcc := Option.some.inj hin
  rw [← hcc] at hnumW hxW
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q (Z w) r hr
  have hreward : c.reward = (fun i => ((rewards q i).val : ℝ) / (D p : ℝ)) := by
    rw [cell0_reward rate r c hc, hf.2.2.1, hf.2.2.2]
  obtain ⟨root0, ht0, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs
  have hcover0 : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[root0.val] q :=
    ⟨hb0, ht0 ▸ hret.1, ht0 ▸ hret.2.1⟩
  have hroot0 := huniq root0 hcover0
  have hroot : rho = root := by
    apply Fin.ext
    have htr := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h (Z w) rho
    have ht0' := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h (Z w) root0
    have hv := congrArg Fin.val (htime.trans ht0.symm)
    have hv0 := congrArg Fin.val hroot0
    omega
  rw [← hroot] at hb'
  have hP : P' = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    _ P' P hb' hbirth
  subst P'
  have hcanonical : c = episodeRoundInput rate rewards q A c.recordedArm := by
    have hrates : c.rate = (episodeRoundInput rate rewards q A c.recordedArm).rate := by
      funext j
      change c.rate j = CanonicalRecordingRates.xi p rate.eta.val (RecordedQueueRun.scoreWeight Q A) j
      rw [hrate, hanchor]
    have hen : c.enabled = (episodeRoundInput rate rewards q A c.recordedArm).enabled := hcen
    have hrew : c.reward = (episodeRoundInput rate rewards q A c.recordedArm).reward := hreward
    have hmarker : c.recordedArm = (episodeRoundInput rate rewards q A c.recordedArm).recordedArm := rfl
    generalize episodeRoundInput rate rewards q A c.recordedArm = d at hrates hen hrew hmarker ⊢
    cases c
    cases d
    cases hen
    cases hrew
    cases hmarker
    cases hrates
    rfl
  refine ⟨e, A, c.recordedArm, he, heclear, hclear, hA, hrep,
    hnumW.trans (congrArg ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates hcanonical),
    hxW.trans (congrArg (sourceEstimate Q e.before) hcanonical), ?_, ?_, ?_⟩
  · rw [hafter, hxW]
    rw [← hcanonical]
    rw [← hcen]
    exact stepFromSourceEstimate_eq_step Q e.before c
  · rw [harr, hxW]
    rw [← hcanonical]
    rw [← hcen]
    funext j
    exact acceptedRecordFromSourceEstimate_eq Q e.before c j
  · intro U
    simpa only [hanchor] using hmass U

omit C_star C_h control0 in
/-- The accepted residual at the same complete UPDATE, or literal retention
of the old set. Only incoming overflow suppresses the proposal. -/
def episodeNextLaw (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K)
    (U : SlowSet p) (i : Option (Fin p.K)) (B : Bool) : Measure (SlowSet p) :=
  if S.overflow then Measure.dirac (frozenSlowSet p) else if B then
    (RecordedSlowRefresh.residualPMF p Q S (episodeRoundInput rate rewards q A i)
      (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)).toMeasure
  else Measure.dirac U

omit C_star C_h control0 in
/-- Explicit finite recorder/proposal/residual test, keeping every recorder
atom even if several atoms give the same source estimate. -/
def episodeRoundTest (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K)
    (U : SlowSet p) (f : Estimate p → Bool → SlowSet p → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Option (Fin p.K), ∑ B : Bool, ∑ V : SlowSet p,
    f (sourceEstimate Q S (episodeRoundInput rate rewards q A i)) (!S.overflow && B) V *
      (episodeNextLaw rate rewards q A S U i B {V} *
        (RecordedRoundMoments.recordingOutcomePMF
          (anchorRates rate (RecordedQueueRun.scoreWeight Q A)
            (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
          ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}))

omit C_star C_h control0 in
/-- The native installation law is exactly this episode law when its actual
anchor is the strict seed's weight. This identifies the whole residual body. -/
theorem episodeNextLaw_eq_installationNextLaw (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (ha : v.payload.anchor = RecordedQueueRun.scoreWeight Q A)
    (i : Option (Fin p.K)) (B : Bool) :
    episodeNextLaw rate rewards q A S v.payload.slowSet i B =
      installationNextLaw rate rewards q v S i B := by
  have hc : episodeRoundInput rate rewards q A i = installationRound rate rewards q v i := by
    simp only [episodeRoundInput, installationRound, ha]
  simp only [episodeNextLaw, installationNextLaw, hc, ha]

omit C_star C_h control0 in
/-- The explicit episode sum is the accepted ROOT/CALL projection, after
FAST has been summed through its actual correlated recorder marginal. -/
theorem episodeRoundTest_eq_installationTestSum (q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (ha : v.payload.anchor = RecordedQueueRun.scoreWeight Q A)
    (f : Estimate p → Bool → SlowSet p → ℝ≥0∞) :
    episodeRoundTest rate rewards q A S v.payload.slowSet f =
      installationTestSum rate rewards q v S f := by
  unfold episodeRoundTest installationTestSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro B _
  rw [lintegral_fintype, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro V _
  have hc : episodeRoundInput rate rewards q A i = installationRound rate rewards q v i := by
    simp only [episodeRoundInput, installationRound, ha]
  rw [episodeNextLaw_eq_installationNextLaw rate rewards q A S v ha]
  simp only [hc, ha, mul_assoc]
  rfl

/-- Arbitrary tests keep E, the actual old U, the revealed source estimate,
the effective proposal, and the next set in one joint carrier. -/
abbrev TransitionData (s q : Fin p.T) :=
  History rate s q × (SlowSet p × (Estimate p × (Bool × SlowSet p)))

omit control0 in
/-- Evaluate the common kernel from the history's actual optional seed and
replayed PRE. Missing numerical states contribute no present-cell test. -/
def episodeTransitionTest (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) : ℝ≥0∞ :=
  match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc h.1.1,
      sourceEpisodeReplay rate rewards C_star C_h s q h with
  | some A, some S => episodeRoundTest rate rewards q A S U
      (fun x B V => F (h, (U, (x, (B, V)))))
  | _, _ => 0

omit C_star C_h control0 in
private theorem measurable_episodeRoundTest (s q : Fin p.T)
    (A S : RecordedQueueRun.RunState p.K) (U : SlowSet p)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun h => episodeRoundTest rate rewards q A S U
      (fun x B V => F (h, (U, (x, (B, V)))))) := by
  unfold episodeRoundTest
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro B _
  apply Finset.measurable_sum
  intro V _
  exact (hF.comp (measurable_id.prodMk
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_const))))).mul_const _

omit control0 in
theorem measurable_episodeTransitionTest (s q : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun v : History rate s q × SlowSet p =>
      episodeTransitionTest rate rewards C_star C_h s q F v.1 v.2) := by
  let g : (Option (RecordedQueueRun.RunState p.K) ×
      (Option (RecordedQueueRun.RunState p.K) × SlowSet p)) × History rate s q → ℝ≥0∞ :=
    fun v => match v.1.1, v.1.2.1 with
    | some A, some S => episodeRoundTest rate rewards q A S v.1.2.2
        (fun x B V => F (v.2, (v.1.2.2, (x, (B, V)))))
    | _, _ => 0
  have hg : Measurable g := by
    apply measurable_from_prod_countable_right
    intro v
    rcases v with ⟨A, S, U⟩
    cases A with
    | none => exact measurable_const
    | some A =>
      cases S with
      | none => exact measurable_const
      | some S => exact measurable_episodeRoundTest rate rewards s q A S U F hF
  have hseed : Measurable (fun v : History rate s q × SlowSet p =>
      ReferencePostInvocationNoncallGeometry.prefixNumerical
        rate rewards C_star C_h s.castSucc v.1.1.1) :=
    (ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
      rate rewards C_star C_h s.castSucc).comp measurable_fst.fst.fst
  exact hg.comp ((hseed.prodMk
    (((measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp measurable_fst).prodMk
      measurable_snd)).prodMk measurable_fst)

omit rewards C_star C_h control0 in
/-- A joint source test reads a present mark's actual old set, effective
proposal and next set. An absent mark contributes zero without a state. -/
def optionalTransitionTest (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (v : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  match v.2.2 with
  | none => 0
  | some e => F (v.1, (e.slowSet, (v.2.1, (e.proposal, e.nextSlowSet))))

omit rewards C_star C_h control0 in
theorem measurable_optionalTransitionTest (s q : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (optionalTransitionTest rate s q F) := by
  let A := History rate s q × Estimate p
  let g : (A × LogicalCell p rate) ⊕ (A × PUnit) → ℝ≥0∞ :=
    Sum.elim (fun v => F (v.1.1,
      (v.2.slowSet, (v.1.2, (v.2.proposal, v.2.nextSlowSet))))) (fun _ => 0)
  have hg : Measurable g :=
    (hF.comp (measurable_fst.fst.prodMk
      (((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd).prodMk
        (measurable_fst.snd.prodMk
          ((measurable_logicalCell_proposal.comp measurable_snd).prodMk
            ((measurable_logicalCell_nextSlowSet.mono le_rfl le_top).comp measurable_snd)))))).sumElim measurable_const
  have hm : Measurable (fun v : History rate s q × (Estimate p × Option (LogicalCell p rate)) =>
      ((v.1, v.2.1), (Equiv.optionEquivSumPUnit (LogicalCell p rate)) v.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk
      ((comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))).comp measurable_snd.snd)
  convert hg.comp ((MeasurableEquiv.prodSumDistrib A (LogicalCell p rate) PUnit).measurable.comp hm) using 1
  funext v
  rcases v with ⟨h, x, e⟩
  cases e <;> rfl

omit control0 in
/-- Both actual source gates, evaluated on the same exposed history. -/
def retainedSourceTest (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (v : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  if v.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      v.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q
  then optionalTransitionTest rate s q F v else 0

include control0 in
theorem measurable_retainedSourceTest (s q : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (retainedSourceTest rate rewards C_star C_h s q F) :=
  (measurable_optionalTransitionTest rate s q F hF).ite
    (((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage measurable_fst.fst.fst).inter
      ((measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage measurable_fst))
    measurable_const

/-- Replace the actual retained gate by its proved history readout, on the
raw terminal experiment and every original fixed-ID experiment. -/
theorem ae_retainedSourceTest (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim Lambda
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞),
        retainedSourceTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) =
        if w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
            w ∈ retainedEvent rate rewards C_star C_h control0 s q
        then optionalTransitionTest rate s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 := by
  filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids] with w hw
  intro s q F
  have hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s ↔
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 ∈
        sourceStartEvent rate rewards C_star C_h s := by
    rw [episodeStartEvent_eq_history_preimage]
    rfl
  unfold retainedSourceTest terminalSourceJoint
  by_cases hstart : w ∈ episodeStartEvent rate rewards C_star C_h control0 s
  · simp only [← hs, hstart, true_and, ← hw s q hstart]
  · simp only [← hs, hstart, false_and, ite_false]

omit rate rewards C_star C_h control0 in
private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (fun L : List A => L[n]?) := by
  have ht := (measurable_pi_apply n).comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)).snd
  have hd : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_const.sumElim (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hd.comp ht using 1
  funext L
  change L[n]? = Sum.elim (fun _ : Unit => (none : Option A)) some
    (ReferenceActiveHorizonMeasurability.listObservationAt L n)
  unfold ReferenceActiveHorizonMeasurability.listObservationAt
  cases L[n]? <;> rfl

omit rate rewards C_star C_h control0 in
private theorem measurable_list_tail {A : Type*} [MeasurableSpace A] :
    Measurable (List.tail : List A → List A) := by
  apply measurable_comap_iff.mpr
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)
  have hn := (measurable_of_countable (fun n : ℕ => n - 1)).comp hc.fst
  have ht : Measurable (fun L : List A => fun n =>
      ReferenceActiveHorizonMeasurability.listObservationAt L (n + 1)) :=
    measurable_pi_iff.mpr fun n => (measurable_pi_apply (n + 1)).comp hc.snd
  convert hn.prodMk ht using 1
  funext L
  apply Prod.ext
  · exact List.length_tail
  · funext n
    cases L <;> rfl

omit rate rewards C_star C_h control0 in
private theorem measurable_list_cons {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (a : X → A) (ha : Measurable a) (L : X → List A) (hL : Measurable L) :
    Measurable (fun x => a x :: L x) := by
  apply measurable_comap_iff.mpr
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hL
  have hn := (measurable_of_countable (fun n : ℕ => n + 1)).comp hc.fst
  apply hn.prodMk
  apply measurable_pi_iff.mpr
  intro n
  cases n with
  | zero => exact measurable_inr.comp ha
  | succ n => exact (measurable_pi_apply n).comp hc.snd

omit rate rewards C_star C_h control0 in
private theorem measurable_option_cons {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (a : X → Option A) (ha : Measurable a) (L : X → List A) (hL : Measurable L) :
    Measurable (fun x => (a x).elim (L x) (fun v => v :: L x)) := by
  let g : (A × X) ⊕ (PUnit × X) → List A :=
    Sum.elim (fun v => v.1 :: L v.2) (fun v => L v.2)
  have hg : Measurable g :=
    (measurable_list_cons Prod.fst measurable_fst (fun v : A × X => L v.2)
      (hL.comp measurable_snd)).sumElim (hL.comp measurable_snd)
  have hm := ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ha).prodMk measurable_id
  convert hg.comp ((MeasurableEquiv.sumProdDistrib A PUnit X).measurable.comp hm) using 1
  funext x
  cases h : a x <;> simp only [Function.comp_apply, h]
  all_goals rfl

omit rate rewards C_star C_h control0 in
private def filterMask {A : Type*} : List Bool → List A → List A
  | [], _ => []
  | b :: bs, L => if b then (L[0]?).elim (filterMask bs L.tail)
      (fun a => a :: filterMask bs L.tail) else filterMask bs L.tail

omit rate rewards C_star C_h control0 in
private theorem measurable_filterMask {A : Type*} [MeasurableSpace A] (mask : List Bool) :
    Measurable (filterMask (A := A) mask) := by
  induction mask with
  | nil => exact measurable_const
  | cons b bs ih =>
    cases b with
    | false => exact ih.comp measurable_list_tail
    | true =>
      exact measurable_option_cons (fun L : List A => L[0]?)
        (measurable_list_getElem? 0) (fun L => filterMask bs L.tail) (ih.comp measurable_list_tail)

omit rate rewards C_star C_h control0 in
private theorem filterMask_map {A : Type*} (P : A → Bool) (L : List A) :
    filterMask (L.map P) L = L.filter P := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases h : P a <;> simp only [List.map_cons, filterMask, h, Bool.false_eq_true,
      ite_false, ite_true, List.getElem?_cons_zero, List.tail_cons, Option.elim_some,
      List.filter_cons, ih]

omit rewards C_star C_h control0 in
private theorem measurable_filter_time (n : ℕ) :
    Measurable (fun L : List (LogicalCell p rate) => L.filter (fun e => e.time.val < n)) := by
  have hm := ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id
    (fun e : LogicalCell p rate => decide (e.time.val < n))
    ((measurable_of_countable (fun t : Fin p.T => decide (t.val < n))).comp measurable_logicalCell_time)
  have hf : Measurable (fun v : List Bool × List (LogicalCell p rate) => filterMask v.1 v.2) :=
    measurable_from_prod_countable_right fun mask => measurable_filterMask mask
  convert hf.comp (hm.prodMk measurable_id) using 1
  funext L
  exact (filterMask_map _ L).symm

omit rewards C_star C_h control0 in
private theorem measurable_find_time (q : Fin p.T) :
    Measurable (fun L : List (LogicalCell p rate) => L.find? (fun e => e.time == q)) := by
  have ht := ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id
    LogicalCell.time (measurable_logicalCell_time (rate := rate))
  have hn := (measurable_of_countable (fun L : List (Fin p.T) => L.findIdx (fun t => t == q))).comp ht
  have hg : Measurable (fun v : ℕ × List (LogicalCell p rate) => v.2[v.1]?) :=
    measurable_from_prod_countable_right fun n => measurable_list_getElem? n
  convert hg.comp (hn.prodMk measurable_id) using 1
  funext L
  simp only [Function.comp_apply, List.find?_eq_getElem?_findIdx, List.findIdx_map, id_eq]
  rfl

omit rewards C_star C_h in
/-- The literal source-history readout of the recombined before-draw observer.
Its label-zero array is not added to the exposed history. -/
def prefixSourceHistory {B : Type*} (s q : Fin p.T)
    (o : Source p × (B × List (LogicalCell p rate))) : History rate s q :=
  ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val o.1,
    o.2.2.filter (fun e => e.time.val < s.val)),
    fun v => sourceOptionalEstimate rate (o.2.2.find? (fun e => e.time == v.val)))

omit rewards C_star C_h in
theorem measurable_prefixSourceHistory {B : Type*} [MeasurableSpace B] (s q : Fin p.T) :
    Measurable (prefixSourceHistory (B := B) rate control0 s q) :=
  (((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).comp measurable_fst).prodMk
    ((measurable_filter_time rate s.val).comp measurable_snd.snd)).prodMk
    (measurable_pi_iff.mpr fun v => (measurable_sourceOptionalEstimate rate).comp
      ((measurable_find_time rate v.val).comp measurable_snd.snd))

/-- Changing the actual current COLLECTION proposal leaves the original
pre-round source history and incoming old-set readout unchanged. -/
theorem prefixSourceHistory_proposal_nonuse (s q : Fin p.T) (z : Source p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (x : ContinuousControlSlice.Scalar) :
    let read := fun a => ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation
      rate rewards C_star C_h control0 q.castSucc (z, a)
    (prefixSourceHistory rate control0 s q (read (Function.update a (q, 0) x)),
      ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate (read (Function.update a (q, 0) x)).2.2) =
    (prefixSourceHistory rate control0 s q (read a),
      ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate (read a).2.2) := by
  have hp := congrArg Prod.snd
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h q.val q.isLt.le z (Function.update a (q, 0) x) a (by
        intro t ht l
        exact Function.update_of_ne (fun h => (ne_of_lt ht)
          (congrArg (fun v : Fin p.T × Fin 2 => v.1.val) h)) _ _))
  simpa only [ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation, prefixSourceHistory,
    ReferenceFirstCollectionLogicalPrefixExtension.extendedPast, Fin.val_castSucc] using
    congrArg (fun L => (prefixSourceHistory rate control0 s q
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val z, (a, L)),
      ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate L)) hp

section Prefix

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarRootRoundLaw
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceGeneratedCalendarEpisodePrefixRecombination

private theorem calendar_sourcePrefix_original (b : Bool) (u t : Fin p.T)
    (k : ℕ) (hk : t.val + 1 + k ≤ p.T)
    (w : CalendarSample rate rewards C_star C_h b u t k)
    (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val (calendarOriginalLift rate rewards C_star C_h b u t k w).1.1.val := by
  let root := calendarAncestor rate rewards C_star C_h b u t k 0 (Nat.zero_le _) w
  have hroot : root = calendarOriginalLift rate rewards C_star C_h b u t k w :=
    calendarAncestor_original rate rewards C_star C_h b u t k 0 (Nat.zero_le _) w
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b u t
    k hk w 0 (Nat.zero_le _)).2.1
  have ht := congrArg (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val) hp
  simp only [Nat.add_zero, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val (t.val + 1) (Nat.le_succ _)] at ht
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w) =
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val (calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) root) at ht
  have hi : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
      (calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) root) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val root.1.1.val := by
    cases b <;> exact congrArg Prod.fst
      (rootInstalledSource_history rate rewards C_star C_h control0 _ u t root.1.1 root.2)
  have he := ht.trans (hi.trans (congrArg (fun v : CalendarSample rate rewards C_star C_h b u t 0 =>
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val v.1.1.val) hroot))
  have hn := congrArg (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val) he
  simpa only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n.val t.val hnt] using hn

omit control0 in
private theorem noCallBefore_le_firstCell (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t)
    (n : Fin (p.T + 1)) (hn : NoCallBefore rate rewards C_star C_h n z) : n.val ≤ t.val := by
  by_contra h
  have ht : t.val < n.val := by omega
  have hb := (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
    rate rewards C_star C_h t z).mpr (fun v hv =>
      (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mp (hn v (hv.trans_lt ht)))
  rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz] at hb
  exact (Nat.lt_irrefl _ hb)

/-- Every insertion is later than this predictable original prefix. This is
a pointwise statement on all exhaustive components, including null ones. -/
theorem sourcePrefix_terminal_original (n : Fin (p.T + 1)) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h n) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val (Z w) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w) := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => rfl
  | stopped u t => rfl
  | generated b u t =>
    have hz : (calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.1.val ∈
        ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
      cases b with
      | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
          rate rewards C_star C_h u t _
            (calendarOriginalLift rate rewards C_star C_h false u t _ w).1.1.property).1
      | true => exact (calendarOriginalLift rate rewards C_star C_h true u t _ w).1.1.property.1
    exact calendar_sourcePrefix_original rate rewards C_star C_h control0 b u t _ (by omega) w n
      (noCallBefore_le_firstCell rate rewards C_star C_h u t _ hz n hw)

omit rewards C_star C_h control0 in
private theorem filter_time_filter (L : List (LogicalCell p rate)) (a b : ℕ) (hab : a ≤ b) :
    (L.filter (fun e => e.time.val < b)).filter (fun e => e.time.val < a) =
      L.filter (fun e => e.time.val < a) := by
  rw [List.filter_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h, h.trans_le hab⟩⟩

omit rewards C_star C_h control0 in
private theorem find_time_filter (L : List (LogicalCell p rate)) (q : Fin p.T)
    (n : ℕ) (hq : q.val < n) :
    (L.filter (fun e => e.time.val < n)).find? (fun e => e.time == q) =
      L.find? (fun e => e.time == q) := by
  rw [List.find?_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact ⟨And.right, fun h => ⟨h ▸ hq, h⟩⟩

/-- The recombined observer reconstructs exactly the same pre-draw H_s
and only the source floor estimates at s ≤ v < q. -/
theorem prefixSourceHistory_actual (s q : Fin p.T) (hsq : s.val ≤ q.val) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc) :
    prefixSourceHistory rate control0 s q
        (prefixObservation rate rewards C_star C_h control0 q.castSucc w) =
      sourceEstimateHistory rate rewards C_star C_h control0 s q w := by
  have hp := congrArg (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val)
    (sourcePrefix_terminal_original rate rewards C_star C_h control0 q.castSucc w hw)
  simp only [Fin.val_castSucc, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 s.val q.val hsq] at hp
  apply Prod.ext
  · apply Prod.ext
    · change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource
          rate rewards C_star C_h w)) = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val (Z w)
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hsq]
      exact hp.symm
    · change ((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.time.val < q.val)).filter (fun e => e.time.val < s.val) =
          (archive rate rewards C_star C_h control0 w).filter (fun e => e.time.val < s.val)
      exact filter_time_filter rate _ s.val q.val hsq
  · funext v
    change sourceOptionalEstimate rate (((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.time.val < q.val)).find? (fun e => e.time == v.val)) =
      sourceOptionalEstimate rate ((archive rate rewards C_star C_h control0 w).find? (fun e => e.time == v.val))
    rw [find_time_filter rate _ v.val q.val v.property.2]

omit control0 in
/-- The current optional mark is read after the one actual prefix operation.
No mark is supplied on an absent or disabled branch. -/
def prefixCurrentMark (q : Fin p.T)
    (v : Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar)) :
    Option (LogicalCell p rate) :=
  (extensionSample rate rewards C_star C_h q v).2.2.find? (fun e => e.time == q)

include control0 in
theorem measurable_prefixCurrentMark (q : Fin p.T) :
    Measurable (prefixCurrentMark rate rewards C_star C_h q) :=
  (measurable_find_time rate q).comp
    (measurable_extensionSample rate rewards C_star C_h control0 q).snd.snd

private theorem prefixStepObservation_actual (q : Fin p.T) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ) :
    extensionSample rate rewards C_star C_h q
        (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
          currentInnovation rate rewards C_star C_h control0 q w) =
      prefixObservation rate rewards C_star C_h control0 q.succ w := by
  have hpre : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc :=
    fun t ht => hw t (Nat.lt_succ_of_lt ht)
  rw [prefixObservation_eq_extendedObservation rate rewards C_star C_h control0 q.castSucc w hpre,
    prefixObservation_eq_extendedObservation rate rewards C_star C_h control0 q.succ w hw]
  exact extensionSample_actual rate rewards C_star C_h control0 q
    (originalPair rate rewards C_star C_h control0 w)

/-- Before the first call, the current mark is the actual function of the
same observer and innovation used in the recombined product law. -/
theorem prefixCurrentMark_actual (q : Fin p.T) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ) :
    prefixCurrentMark rate rewards C_star C_h q
        (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
          currentInnovation rate rewards C_star C_h control0 q w) =
      currentMark rate rewards C_star C_h control0 q w := by
  unfold prefixCurrentMark
  rw [prefixStepObservation_actual rate rewards C_star C_h control0 q w hw]
  change ((archive rate rewards C_star C_h control0 w).filter
    (fun e => e.time.val < q.val + 1)).find? (fun e => e.time == q) =
      (archive rate rewards C_star C_h control0 w).find? (fun e => e.time == q)
  exact find_time_filter rate _ q (q.val + 1) (Nat.lt_succ_self _)

/-- Same-source history, revealed estimate and optional complete mark on the
recombined prefix carrier, before any first-call conditioning. -/
def prefixSourceJoint (s q : Fin p.T)
    (v : Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar)) :
    History rate s q × (Estimate p × Option (LogicalCell p rate)) :=
  (prefixSourceHistory rate control0 s q v.1,
    (sourceOptionalEstimate rate (prefixCurrentMark rate rewards C_star C_h q v),
      prefixCurrentMark rate rewards C_star C_h q v))

theorem measurable_prefixSourceJoint (s q : Fin p.T) :
    Measurable (prefixSourceJoint rate rewards C_star C_h control0 s q) :=
  ((measurable_prefixSourceHistory rate control0 s q).comp measurable_fst).prodMk
    (((measurable_sourceOptionalEstimate rate).comp
      (measurable_prefixCurrentMark rate rewards C_star C_h control0 q)).prodMk
        (measurable_prefixCurrentMark rate rewards C_star C_h control0 q))

theorem prefixSourceJoint_actual (s q : Fin p.T) (hsq : s.val ≤ q.val) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ) :
    prefixSourceJoint rate rewards C_star C_h control0 s q
        (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
          currentInnovation rate rewards C_star C_h control0 q w) =
      terminalSourceJoint rate rewards C_star C_h control0 s q w := by
  have hpre : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc :=
    fun t ht => hw t (Nat.lt_succ_of_lt ht)
  unfold prefixSourceJoint
  rw [prefixSourceHistory_actual rate rewards C_star C_h control0 s q hsq w hpre,
    prefixCurrentMark_actual rate rewards C_star C_h control0 q w hw]
  rfl

/-- Actual retained joint tests strictly before the first invocation are
joined to the recombined observer and its ORIGINAL current innovation.
The right side still contains the literal prefix operation, rather than an
assumed or independently redrawn recorder/proposal pair. -/
theorem terminalLaw_beforeFirstCall_transition_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        retainedSourceTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0
      ∂ids.elim Lambda
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) =
      ∫⁻ v, if noCallAt rate rewards C_star C_h q v.1.1 then
        retainedSourceTest rate rewards C_star C_h s q F
          (prefixSourceJoint rate rewards C_star C_h control0 s q v) else 0
        ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
          (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).prod
            (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  let test : Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) → ℝ≥0∞ :=
    fun v => if noCallAt rate rewards C_star C_h q v.1.1 then
      retainedSourceTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q v) else 0
  have ht : Measurable test :=
    ((measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF).comp
      (measurable_prefixSourceJoint rate rewards C_star C_h control0 s q)).ite
        ((measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage measurable_fst.fst) measurable_const
  have hpred (w : Omega) : w ∈ beforeFirstCall rate rewards C_star C_h q.succ ↔
      w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc ∧
        noCallAt rate rewards C_star C_h q
          (prefixObservation rate rewards C_star C_h control0 q.castSucc w).1 :=
    (noCallBefore_succ rate rewards C_star C_h q
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w)).trans
      (and_congr Iff.rfl (noCallAt_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl _))
  calc
    _ = ∫⁻ w, test (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
        currentInnovation rate rewards C_star C_h control0 q w)
        ∂(ids.elim Lambda
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
            (beforeFirstCall rate rewards C_star C_h q.castSucc) := by
      rw [← lintegral_indicator (measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.castSucc)]
      apply lintegral_congr
      intro w
      by_cases hs : w ∈ beforeFirstCall rate rewards C_star C_h q.succ
      · obtain ⟨hp, hc⟩ := (hpred w).mp hs
        simp only [hs, ite_true, Set.indicator_apply, hp, test, hc,
          prefixSourceJoint_actual rate rewards C_star C_h control0 s q hsq w hs]
      · by_cases hp : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc
        · have hc : ¬ noCallAt rate rewards C_star C_h q
              (prefixObservation rate rewards C_star C_h control0 q.castSucc w).1 :=
            fun hc => hs ((hpred w).mpr ⟨hp, hc⟩)
          simp only [hs, ite_false, Set.indicator_apply, hp, ite_true, test, hc]
        · simp only [hs, ite_false, Set.indicator_apply, hp]
    _ = _ := by
      cases ids with
      | none => exact terminalLaw_prefix_innovation_test rate rewards C_star C_h control0 q test ht
      | some id => exact fixedIDTerminalLaw_prefix_innovation_test rate rewards C_star C_h control0 id q test ht

end Prefix

section CalendarInnovation

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarRoundInnovation ReferencePostInvocationSupportedDisintegration
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarMarkedPath

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0

/-- On every actual finite calendar prefix, the source floor history replays
the complete original PRE. Only the actual source opportunity and date domain
are required; no replay or coverage certificate is supplied. -/
theorem calendarSourceHistory_replay (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (hqk : q.val ≤ t0.val + 1 + k)
    (w : Sample k)
    (hs : (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hq : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s) :
    sourceEpisodeReplay rate rewards C_star C_h s q
        (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk w) =
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc
        (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk w) := by
  let z := calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk w
  let h := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk w
  have hstart : z ∈ sourceStartEvent rate rewards C_star C_h s :=
    (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s z).mpr hs
  obtain ⟨rho, ht, hb⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z hstart
  let hl := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u0 t0 z
    (ReferenceGeneratedCalendarLivePayoff.calendarCurrentSource_firstCell
      rate rewards C_star C_h control0 b0 u0 t0 k hk w)
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z hl
  have hs0 : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ s.val := by
    have hr := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
    rw [ht] at hr
    omega
  have fold_eq (n : ℕ) (hn : n ≤ q.val - s.val) :
      replayPrefix rate rewards C_star C_h s q h n hn =
        ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
          ⟨s.val + n, by omega⟩ z := by
    induction n with
    | zero => exact (ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
        rate rewards C_star C_h control0 s.castSucc s.val le_rfl z).symm
    | succ n ih =>
      let v : Fin p.T := ⟨s.val + n, by omega⟩
      have hv : EpisodeCovers
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] v :=
        by
          refine ⟨hb, ?_, ?_⟩ <;> rw [ht] <;> dsimp only [v] <;> omega
      have hen := (nominalEnabled_iff_unique_episode rate rewards C_star C_h z v).mpr
        ⟨rho, hv, fun other ho => complete_episode_interval_at_most_one rate rewards C_star C_h z v other rho ho hv⟩
      obtain ⟨e0, he0, ht0⟩ := (calendar_enabled_iff rate rewards C_star C_h control0 b0 u0 t0
        k hk w v (by dsimp only [v]; omega)).mpr hen
      have hsome : ((stored k hk w).2.find? (fun e => e.time == v)).isSome = true :=
        List.find?_isSome.mpr ⟨e0, he0, by simp only [ht0, beq_self_eq_true]⟩
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
      have het : e.time = v := beq_iff_eq.mp (List.find?_some (p := fun f : LogicalCell p rate => f.time == v) he)
      obtain ⟨_, hbefore, hafter, hi, hetrue, hnum, _⟩ :=
        calendar_cell_fields rate rewards C_star C_h control0 b0 u0 t0 k hk w e (List.mem_of_find?_eq_some he)
      simp only [het] at hi hetrue hnum hbefore hafter
      have hvstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ v.val := by
        change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ s.val + n
        omega
      change v.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < W.length at hi
      change e.before = RecordedQueueRun.run Q (W.take (v.val -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) at hbefore
      change e.after = RecordedQueueRun.run Q (W.take (v.val + 1 -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) at hafter
      have hp : ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h v.castSucc z =
          some e.before := by
        rw [ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
          rate rewards C_star C_h v.castSucc z hl hvstart]
        exact congrArg some hbefore.symm
      have hx : h.2 ⟨v, by dsimp only [v]; omega⟩ = sourceEstimate Q e.before W[v.val -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h] := by
        change sourceOptionalEstimate rate ((stored k hk w).2.find? (fun e => e.time == v)) = _
        rw [he, sourceOptionalEstimate_some]
        funext i
        exact sourceCellEstimate_eq_rawEstimate rate e _ hnum i
      rw [replayPrefix_succ, ih (by omega)]
      change (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h v.castSucc z).map _ = _
      rw [hp, Option.map_some, hx, ← stepFromEstimate_eq_estimateStep]
      rw [← hetrue, stepFromSourceEstimate_eq_step]
      have hstep : RecordedQueueRun.step Q e.before W[v.val -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h] = e.after := by
        rw [hbefore, hafter, Nat.sub_add_comm hvstart, ← List.take_append_getElem hi,
          RecordedSlowRefresh.run_append_singleton]
      rw [hstep, ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord rate rewards C_star C_h
        ⟨s.val + (n + 1), by omega⟩ z hl
          (by change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ s.val + (n + 1); omega)]
      exact congrArg some (by simpa only [v, Nat.add_assoc] using hafter)
  have heq := fold_eq (q.val - s.val) le_rfl
  have hdate : (⟨s.val + (q.val - s.val), by omega⟩ : Fin (p.T + 1)) = q.castSucc :=
    Fin.ext (Nat.add_sub_of_le hsq)
  simpa only [sourceEpisodeReplay, sourceReplayPrefix, hdate] using heq

/-- The exposed source history and carried PRE seed survive replacement of
the whole current control and BOTH current auxiliary labels. This supplies
the actual history nonuse needed by the later local-kernel calculation. -/
theorem calendarSourceHistory_fillInnovation (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (x : Innovation p) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let filled := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (by change t0.val < t0.val + 1 + k; omega) k (w, x)
    (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le filled,
      (stored k hk.le filled).1) =
    (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w,
      (stored k hk.le w).1) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let filled := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (by change t0.val < t0.val + 1 + k; omega) k (w, x)
  have hp := calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k hk.le le_rfl (w, x)
  have hsource := congrArg (fun v : BootstrapPrivateRoundStreams.SourceInput p ×
      (SlowSet p × List (LogicalCell p rate)) =>
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val v.1) hp
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t0.val + 1 + k)
        (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le filled)) =
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t0.val + 1 + k)
        (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w)) at hsource
  simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val _ hs] at hsource
  have hlist : (stored k hk.le filled).2 = (stored k hk.le w).2 :=
    congrArg (fun v => v.2.2) hp
  apply Prod.ext
  · unfold calendarSourceHistory
    rw [hsource, hlist]
  · exact congrArg (fun v => v.2.1) hp

/-- Actual later terminal joint tests use the SAME refilled current source
and the original whole-vector fibre, with E read before that innovation.
This constructs the joint source rather than combining separate marginals.
Its inner stochastic integral remains to be evaluated by the native kernels. -/
theorem generated_component_source_joint_innovation_test (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (F : History rate s ⟨t0.val + 1 + k, hk⟩ ×
      (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞) (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0)) =
      ∫⁻ w, ∫⁻ x, ∫⁻ v,
        let filled := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (by change t0.val < t0.val + 1 + k; omega) k (w, x)
        let mark := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk filled v
        F (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w,
          (sourceOptionalEstimate rate mark, mark))
        ∂calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
          (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (by change t0.val < t0.val + 1 + k; omega) k (w, x))
        ∂innovationLaw (p := p) ∂(law k hk.le).map
          (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (by change t0.val < t0.val + 1 + k; omega) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have htest := generated_component_source_joint_step_test rate rewards C_star C_h control0
    b0 u0 t0 none s k hk hs F hF
  refine htest.trans ?_
  have hm := hF.comp (measurable_calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s k hk)
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k hk le_rfl _ hm).trans ?_
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro v
  dsimp only [calendarStepSourceJoint, Function.comp_apply]
  apply congrArg F
  apply Prod.ext
  · exact congrArg (fun h : History rate s q × SlowSet p => h.1)
      (calendarSourceHistory_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w x)
  · rfl

end CalendarInnovation

omit control0 in
/-- Lift a common-kernel test to the joint carrier by retaining only its
history and old-set arguments. -/
def kernelLiftTest (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (y : TransitionData rate s q) : ℝ≥0∞ :=
  episodeTransitionTest rate rewards C_star C_h s q F y.1 y.2.1

omit control0 in
theorem measurable_kernelLiftTest (s q : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (kernelLiftTest rate rewards C_star C_h s q F) := by
  have hproj : Measurable (fun y : TransitionData rate s q =>
      ((y.1, y.2.1) : History rate s q × SlowSet p)) :=
    measurable_fst.prodMk measurable_snd.fst
  convert (measurable_episodeTransitionTest rate rewards C_star C_h s q F hF).comp hproj using 1
  funext y
  rfl

omit control0 in
/-- The common-kernel test at the SAME actual old set, with the same source
start/retention gates. This is a literal evaluated kernel expression; equality
of its terminal integral with `retainedSourceTest` is not asserted here. -/
def retainedKernelTest (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (v : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  retainedSourceTest rate rewards C_star C_h s q
    (kernelLiftTest rate rewards C_star C_h s q F) v

include control0 in
theorem measurable_retainedKernelTest (s q : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (retainedKernelTest rate rewards C_star C_h s q F) :=
  measurable_retainedSourceTest rate rewards C_star C_h control0 s q
    (kernelLiftTest rate rewards C_star C_h s q F)
    (measurable_kernelLiftTest rate rewards C_star C_h s q F hF)

/-- The literal right-hand kernel test uses the actual old U at a present
mark. There is no arbitrary slow set or numerical state on absent branches. -/
theorem ae_retainedKernelTest (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim Lambda
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞),
        retainedKernelTest rate rewards C_star C_h s q F
            (terminalSourceJoint rate rewards C_star C_h control0 s q w) =
          if w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
              w ∈ retainedEvent rate rewards C_star C_h control0 s q then
            match currentMark rate rewards C_star C_h control0 q w with
            | none => 0
            | some e => episodeTransitionTest rate rewards C_star C_h s q F
                (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet
          else 0 := by
  filter_upwards [ae_retainedSourceTest rate rewards C_star C_h control0 ids] with w hw
  intro s q F
  exact hw s q (kernelLiftTest rate rewards C_star C_h s q F)

section RootHistory

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarRootRoundLaw
open ReferenceGeneratedCalendarNativePreservation
open ReferenceFirstNextInstallationCellFactors ReferenceFirstNextInstallationTransitionLaw

omit rewards C_star C_h in
/-- E read from the root's proper past, with the same strict source seed and
earlier complete cells. The root UPDATE is not included in this history. -/
def rootHistoryReadout (s q : Fin p.T) (past : RootPast rate) : History rate s q :=
  prefixSourceHistory rate control0 s q past

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "RootSample" => CalendarSample rate rewards C_star C_h b0 u0 t0 0
local notation "rootCell" => calendarRootCell rate rewards C_star C_h control0 b0 u0 t0
local notation "rootPast" => calendarRootPast rate rewards C_star C_h control0 b0 u0 t0
local notation "RootEvent" => ReferencePostInvocationPrefixLocality.branchEvent rate rewards C_star C_h b0 u0 t0

/-- The actual root's source history is a function of its accepted proper
past, even when the tested episode began strictly before this first call. -/
theorem calendarSourceHistory_root_readout (s : Fin p.T) (hs : s.val ≤ t0.val) (w : RootSample) :
    calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w =
      rootHistoryReadout rate control0 s t0 (rootPast w) := by
  have ht : (rootCell w).time = t0 := by
    cases b0 <;> exact actualFirstCell_time
      rate rewards C_star C_h control0 t0 _ _
  have hstore := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).2.1
  apply Prod.ext
  · apply Prod.ext
    · change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
        (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t0.val
          (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w))
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val t0.val hs]
    · change ((calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).2.filter
        (fun e => e.time.val < s.val)) =
      (calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).filter
        (fun e => e.time.val < s.val)
      rw [hstore, List.filter_append]
      have hn : ¬ (rootCell w).time.val < s.val := by rw [ht]; omega
      simp only [List.filter_cons, decide_eq_false hn, Bool.false_eq_true, ite_false,
        List.filter_nil, List.append_nil]
  · funext v
    change sourceOptionalEstimate rate
        ((calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).2.find?
          (fun e => e.time == v.val)) =
      sourceOptionalEstimate rate
        ((calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).find?
          (fun e => e.time == v.val))
    rw [hstore, List.find?_append]
    have hn : (rootCell w).time ≠ v.val := by
      intro he
      have hv := v.property.2
      rw [← he, ht] at hv
      exact Nat.lt_irrefl _ hv
    simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hn, List.find?_nil, Option.or_none]

/-- Replacing the actual root control and the selected UPDATE scalar leaves
both E and the actual old set fixed. Initialization and its other scalar are
retained in the same original erased tape and whole assignment vector. -/
theorem rootRestore_sourceHistory_nonuse (s : Fin p.T) (hs : s.val ≤ t0.val)
    (j : Fin (M p))
    (r : EventRemainder control0 t0 RootEvent j)
    (a : ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray t0)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
    let w := rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x
    let w0 := rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v control0
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero
    (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w,
      (rootCell w).slowSet) =
    (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w0,
      (rootCell w0).slowSet) := by
  dsimp only
  have hp := congrArg Prod.fst
    (rootRestore_assignedPast_nonuse rate rewards C_star C_h control0 b0 u0 t0 j r a v c x)
  dsimp only [calendarRootAssignedPast] at hp
  have hh := congrArg (fun past : RootPast rate => (rootHistoryReadout rate control0 s t0 past, past.2.1)) hp
  rw [← calendarSourceHistory_root_readout rate rewards C_star C_h control0 b0 u0 t0 s hs,
    ← calendarSourceHistory_root_readout rate rewards C_star C_h control0 b0 u0 t0 s hs] at hh
  exact hh

private theorem prefixNumerical_native_root
    (z : FirstInvocationSource rate rewards C_star C_h t0) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h t0.castSucc z.val =
      some (firstBefore rate rewards C_star C_h control0 t0 z) := by
  have hr := (firstSourceCell_spec rate rewards C_star C_h t0 z).1
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t0.val := by
    by_contra hs
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
    rw [ite_eq_right hs] at hr
    cases hr
  simpa only [Fin.val_castSucc, rootBefore_originalWord] using
    ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord rate rewards C_star C_h t0.castSucc z.val
      (ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h t0 z) hs

/-- The native ROOT anchor is reconstructed from the actual episode's strict
seed. Coverage, payload identity and earlier PRE-clear are produced internally. -/
theorem rootSource_episode_anchor (s : Fin p.T) (hsq : s.val ≤ t0.val)
    (hq : t0.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : FirstInvocationSource rate rewards C_star C_h t0)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (firstBefore rate rewards C_star C_h control0 t0 z).overflow = false) :
    ∃ A : RecordedQueueRun.RunState p.K,
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (firstSourceCell rate rewards C_star C_h t0 z).selected.view.payload.anchor =
        RecordedQueueRun.scoreWeight Q A := by
  let cell := firstSourceCell rate rewards C_star C_h t0 z
  have hr := firstSourceCell_spec rate rewards C_star C_h t0 z
  have hen : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h t0 z.val = true := by
    simp only [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled, hr.1, Option.bind_some,
      ReferenceFirstCollectionCurrentRetainedGate.cell0, hr.2.2, Option.some_or, Option.any_some]
    exact cell.enabled
  obtain ⟨rho, P, r, c, v, hr', _, _, _, huniq, hb, _, _, hv, ha, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val t0 hen
  have hrr := Option.some.inj (hr'.symm.trans hr.1)
  subst r
  have hvv : v = cell.selected := Option.some.inj (hv.symm.trans cell.selection_actual)
  subst v
  obtain ⟨rho0, ht, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z.val hs
  have hcover : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] t0 :=
    ⟨hb0, ht ▸ hsq, ht ▸ hq⟩
  have he := huniq rho0 hcover
  rw [← he] at hb
  have hclear : (ReferencePostInvocationNoncallGeometry.prefixNumerical
      rate rewards C_star C_h t0.castSucc z.val).any (fun S => !S.overflow) = true := by
    rw [prefixNumerical_native_root rate rewards C_star C_h control0 t0 z, Option.any_some, hc]
    rfl
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover rate rewards C_star C_h control0
    z.val t0 rho0 P hcover hb hclear
  rw [ht] at hA
  exact ⟨A, hA, hAc, ha.trans hanchor⟩

/-- ROOT's replay is its actual complete native PRE, including the original
record stream. The current UPDATE is outside the source history. -/
theorem calendarSourceHistory_root_replay (s : Fin p.T) (hs : s.val ≤ t0.val) (w : RootSample)
    (hstart : (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hq : t0.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s) :
    sourceEpisodeReplay rate rewards C_star C_h s t0
        (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w) =
      some (rootCell w).before := by
  rw [calendarSourceHistory_replay rate rewards C_star C_h control0 b0 u0 t0 s t0 hs
    0 (by omega) (by omega) w hstart hq]
  have hsource : calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w =
      (rootInstalledSource rate rewards C_star C_h b0 u0 t0 w.1.1 w.2).val := by cases b0 <;> rfl
  rw [hsource, prefixNumerical_native_root rate rewards C_star C_h control0 t0]
  cases b0 <;> rfl

private theorem rootCell_slowSet (w : RootSample) :
    (rootCell w).slowSet = if (rootCell w).before.overflow then frozenSlowSet p else
      (firstSourceCell rate rewards C_star C_h t0
        (rootInstalledSource rate rewards C_star C_h b0 u0 t0 w.1.1 w.2)).selected.view.payload.slowSet := by
  cases b0 <;> rfl

/-- On the genuine retained ROOT domain the evaluated native kernel is the
literal history-reconstructed episode kernel, with the same actual old set. -/
theorem rootNativeTransitionTest_eq_history (s : Fin p.T) (hs : s.val ≤ t0.val)
    (F : TransitionData rate s t0 → ℝ≥0∞) (w : RootSample)
    (hstart : (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w ∈
      sourceHistoryRetained rate rewards C_star C_h s t0) :
    let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 w.1.1 w.2
    installationTestSum rate rewards t0
      (firstSourceCell rate rewards C_star C_h t0 z).selected.view
      (firstBefore rate rewards C_star C_h control0 t0 z)
      (fun x B V => F
        (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w,
          ((rootCell w).slowSet, (x, (B, V))))) =
      episodeTransitionTest rate rewards C_star C_h s t0 F
        (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w) (rootCell w).slowSet := by
  dsimp only
  let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 w.1.1 w.2
  let h := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w
  have hsource : calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w = z.val :=
    by cases b0 <;> rfl
  have hpre : sourceEpisodeReplay rate rewards C_star C_h s t0 h = some (rootCell w).before :=
    calendarSourceHistory_root_replay rate rewards C_star C_h control0 b0 u0 t0 s hs w hstart hret.2.1
  have hc : (rootCell w).before.overflow = false := by
    have ht := hret.2.2
    rw [hpre, Option.any_some, Bool.not_eq_true'] at ht
    exact ht
  have hbefore : (rootCell w).before =
      firstBefore rate rewards C_star C_h control0 t0 z :=
    by cases b0 <;> rfl
  have hsZ : z.val ∈ sourceStartEvent rate rewards C_star C_h s := by
    rw [← hsource]
    exact (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s _).mpr hstart
  obtain ⟨A, hA, _, ha⟩ := rootSource_episode_anchor rate rewards C_star C_h control0 t0
    s hs hret.2.1 z hsZ (hbefore ▸ hc)
  have hseed : ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 =
      some A := by
    change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val _) = _
    rw [hsource]
    exact hA
  have hU : (rootCell w).slowSet =
      (firstSourceCell rate rewards C_star C_h t0 z).selected.view.payload.slowSet := by
    rw [rootCell_slowSet rate rewards C_star C_h control0 b0 u0 t0 w, hc]
    rfl
  change _ = episodeTransitionTest rate rewards C_star C_h s t0 F h (rootCell w).slowSet
  simp only [episodeTransitionTest, hseed, hpre]
  rw [hbefore, hU]
  exact (episodeRoundTest_eq_installationTestSum rate rewards t0 A _ _ ha _).symm

/-- The actual native view and complete PRE are fixed before ROOT's current
control. They are derived from the same original prefix and assignment vector. -/
theorem rootRestore_fixed_parameters (j : Fin (M p))
    (r : EventRemainder control0 t0 RootEvent j)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (c : ContinuousLearningRows.TimeControl p) :
    let restore := restoreEventSource control0 t0 RootEvent
      (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) j
    let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, c)) v
    let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, control0)) v
    (firstSourceCell rate rewards C_star C_h t0 z).selected.view =
        (firstSourceCell rate rewards C_star C_h t0 z0).selected.view ∧
      firstBefore rate rewards C_star C_h control0 t0 z =
        firstBefore rate rewards C_star C_h control0 t0 z0 := by
  dsimp only
  let restore := restoreEventSource control0 t0 RootEvent
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) j
  let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, c)) v
  let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, control0)) v
  have hp := restoreEventSource_prefix control0 t0 RootEvent
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) j r c
  have hH : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t0 z.val =
      ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t0 z0.val := by
    rw [rootInstalledSource_history, rootInstalledSource_history, hp]
  have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t0.val z.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t0.val z0.val := congrArg Prod.fst hH
  constructor
  · apply Option.some.inj
    rw [← actualFirstCell_view rate rewards C_star C_h control0 t0 z,
      ← actualFirstCell_view rate rewards C_star C_h control0 t0 z0,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 0 t0 z.val,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 0 t0 z0.val, hH]
  · have hbefore : ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t0 z.val =
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t0 z0.val := by
      change ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t0
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t0.val z.val) = _
      rw [hprefix]
      rfl
    have he := Option.some.inj
      ((firstBefore_spec rate rewards C_star C_h control0 t0 z).symm.trans
        (hbefore.trans (firstBefore_spec rate rewards C_star C_h control0 t0 z0)))
    exact congrArg (fun S : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
      (⟨S.1, S.2.1, S.2.2⟩ : RecordedQueueRun.RunState p.K)) he

/-- ROOT's actual history, old set and normalized estimate are joined to the
accepted common UPDATE/proposal/residual kernel on the original refill fibre. -/
theorem rootRestore_quantized_test (s : Fin p.T) (hs : s.val ≤ t0.val)
    (j : Fin (M p))
    (r : EventRemainder control0 t0 RootEvent j)
    (a : ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray t0)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (F : TransitionData rate s t0 → ℝ≥0∞) :
    let restore := restoreEventSource control0 t0 RootEvent
      (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) j
    let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, control0)) v
    let w0 := rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v control0
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero
    let h0 := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w0
    (∫⁻ c, ∫⁻ x, optionalTransitionTest rate s t0 F
        (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s
          (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x))
      ∂ContinuousControlSlice.scalarLaw ∂ContinuousLearningRows.timeControlLaw p) =
      installationTestSum rate rewards t0
        (firstSourceCell rate rewards C_star C_h t0 z0).selected.view
        (firstBefore rate rewards C_star C_h control0 t0 z0)
        (fun x B V => F (h0, ((rootCell w0).slowSet, (x, (B, V))))) := by
  dsimp only
  let restore := restoreEventSource control0 t0 RootEvent
    (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) j
  let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, control0)) v
  let w0 := rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v control0
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero
  let h0 := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w0
  let f := fun x B V => F (h0, ((rootCell w0).slowSet, (x, (B, V))))
  calc
    _ = ∫⁻ c, commonUpdateTest rate rewards t0
        (firstSourceCell rate rewards C_star C_h t0 z0).selected.view
        (firstBefore rate rewards C_star C_h control0 t0 z0)
        f 0 (rootControlDraw rate rewards C_star C_h control0 t0 z0 c)
        ∂ContinuousLearningRows.timeControlLaw p := by
      apply lintegral_congr
      intro c
      let z := rootInstalledSource rate rewards C_star C_h b0 u0 t0 (restore (r, c)) v
      let S := firstBefore rate rewards C_star C_h control0 t0 z
      let cell := firstSourceCell rate rewards C_star C_h t0 z
      let B := ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
        (ReferenceSourceCurrentControlFreshness.u_t p t0 z.val)
      have hm : Measurable (rootRefreshDraw rate rewards C_star C_h control0 t0 z) :=
        (measurable_logicalCell_nextSlowSet.comp (Measurable.of_uncurry_left
          (measurable_actualFirstCell rate rewards C_star C_h control0 t0))).mono
            le_rfl le_top
      have he (x : ContinuousControlSlice.Scalar) :
          sourceCellEstimate rate (actualFirstCell
            rate rewards C_star C_h control0 t0 z x) = RecordedRoundMoments.rawEstimate Q S cell.input := by
        funext i
        exact sourceCellEstimate_eq_rawEstimate rate _ cell.input rfl i
      have hscalar : (∫⁻ x, optionalTransitionTest rate s t0 F
          (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s
            (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x))
          ∂ContinuousControlSlice.scalarLaw) =
          ∫⁻ V, f (RecordedRoundMoments.rawEstimate Q S cell.input) (!S.overflow && B) V
            ∂firstResidualLaw rate rewards C_star C_h control0 t0 z := by
        calc
          _ = ∫⁻ x, f (RecordedRoundMoments.rawEstimate Q S cell.input) (!S.overflow && B)
              (rootRefreshDraw rate rewards C_star C_h control0 t0 z x) ∂ContinuousControlSlice.scalarLaw := by
            apply lintegral_congr
            intro x
            obtain ⟨hh, hU⟩ := Prod.mk.inj
              (rootRestore_sourceHistory_nonuse rate rewards C_star C_h control0 b0 u0 t0 s hs j r a v c x)
            dsimp only [optionalTransitionTest, calendarRootSourceJoint]
            rw [hh, hU]
            change f (sourceCellEstimate rate (rootCell
                (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x)))
              (rootCell (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x)).proposal
              (rootCell (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x)).nextSlowSet = _
            simp only [rootRestore_cell rate rewards C_star C_h control0 b0 u0 t0 j r a v c x]
            change f (sourceCellEstimate rate (actualFirstCell
                rate rewards C_star C_h control0 t0 z x))
              (actualFirstCell rate rewards C_star C_h control0 t0 z x).proposal
              (rootRefreshDraw rate rewards C_star C_h control0 t0 z x) = _
            rw [he x, actualFirstCell_proposal]
            rfl
          _ = _ := by
            rw [← lintegral_map (measurable_of_countable _) hm,
              rootRefreshDraw_law rate rewards C_star C_h control0 t0 z]
      rw [hscalar]
      have hy := rootRestore_control rate rewards C_star C_h control0 b0 u0 t0 j r a v c
        ReferenceFirstLiveActualRefreshTestLaw.scalarZero
      dsimp only [calendarRootRoundReadout] at hy
      rw [rootRestore_currentSource] at hy
      obtain ⟨hv, hS⟩ := rootRestore_fixed_parameters rate rewards C_star C_h control0 b0 u0 t0 j r v c
      have ht := root_quantized_readout rate rewards C_star C_h t0 control0 z f 0
      dsimp only at ht
      rw [← ht, hv, hS, hy]
    _ = _ := root_source_quantized_test rate rewards C_star C_h t0 control0 z0 f 0

private theorem generated_component_root_history_event_test (s : Fin p.T) (hs : s.val ≤ t0.val)
    (E : Set (History rate s t0)) (hE : MeasurableSet E)
    (F : TransitionData rate s t0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩).1 ∈ E then
        retainedSourceTest rate rewards C_star C_h s t0 F
          (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩) else 0
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0
        (.generated b0 u0 t0)) =
      ∫⁻ w, if (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩).1 ∈ E then
        retainedKernelTest rate rewards C_star C_h s t0 F
          (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩) else 0
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0
        (.generated b0 u0 t0) := by
  let sourceTest := fun y : History rate s t0 × (Estimate p × Option (LogicalCell p rate)) =>
    if y.1 ∈ E then retainedSourceTest rate rewards C_star C_h s t0 F y else 0
  let kernelTest := fun y : History rate s t0 × (Estimate p × Option (LogicalCell p rate)) =>
    if y.1 ∈ E then retainedKernelTest rate rewards C_star C_h s t0 F y else 0
  have hsource : Measurable sourceTest :=
    (measurable_retainedSourceTest rate rewards C_star C_h control0 s t0 F hF).ite
      (hE.preimage measurable_fst) measurable_const
  have hkernel : Measurable kernelTest :=
    (measurable_retainedKernelTest rate rewards C_star C_h control0 s t0 F hF).ite
      (hE.preimage measurable_fst) measurable_const
  let A := sourceTest ∘ calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s
  let B := kernelTest ∘ calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s
  have hA := hsource.comp (measurable_calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s)
  have hB := hkernel.comp (measurable_calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s)
  have hleft := generated_component_source_joint_native_root_test rate rewards C_star C_h control0 b0 u0 t0
    none s hs sourceTest hsource
  have hright := generated_component_source_joint_native_root_test rate rewards C_star C_h control0 b0 u0 t0
    none s hs kernelTest hkernel
  refine hleft.trans ((calendarLaw_root_refill_test rate rewards C_star C_h control0 b0 u0 t0 A hA).trans ?_)
  refine Eq.trans ?_ ((calendarLaw_root_refill_test rate rewards C_star C_h control0 b0 u0 t0 B hB).symm.trans hright.symm)
  apply Finset.sum_congr rfl
  intro j _
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro v
  let w0 := rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v control0
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero
  let h0 := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w0
  let G : TransitionData rate s t0 → ℝ≥0∞ := fun y =>
    if y.1 ∈ E then if y.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      y.1 ∈ sourceHistoryRetained rate rewards C_star C_h s t0 then F y else 0 else 0
  have hb (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
      B (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x) =
        if h0 ∈ E then if h0.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
          h0 ∈ sourceHistoryRetained rate rewards C_star C_h s t0 then
          episodeTransitionTest rate rewards C_star C_h s t0 F h0 (rootCell w0).slowSet else 0 else 0 := by
    obtain ⟨hh, hU⟩ := Prod.mk.inj
      (rootRestore_sourceHistory_nonuse rate rewards C_star C_h control0 b0 u0 t0 s hs j r a v c x)
    simp only [B, kernelTest, Function.comp_apply, retainedKernelTest, retainedSourceTest,
      optionalTransitionTest, calendarRootSourceJoint, kernelLiftTest, hh, hU]
    rfl
  change (∫⁻ c, ∫⁻ x, optionalTransitionTest rate s t0 G
      (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s
        (rootRestore rate rewards C_star C_h control0 b0 u0 t0 j r a v c x))
      ∂ContinuousControlSlice.scalarLaw ∂ContinuousLearningRows.timeControlLaw p) = _
  refine (rootRestore_quantized_test rate rewards C_star C_h control0 b0 u0 t0 s hs j r a v G).trans ?_
  simp_rw [hb]
  simp only [lintegral_const, measure_univ, mul_one]
  let z0 := rootInstalledSource rate rewards C_star C_h b0 u0 t0 w0.1.1 w0.2
  change installationTestSum rate rewards t0
    (firstSourceCell rate rewards C_star C_h t0 z0).selected.view
    (firstBefore rate rewards C_star C_h control0 t0 z0)
    (fun x B V => G (h0, ((rootCell w0).slowSet, (x, (B, V))))) = _
  by_cases hE0 : h0 ∈ E
  · simp only [G, hE0, ite_true]
    by_cases hg : h0.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h0 ∈ sourceHistoryRetained rate rewards C_star C_h s t0
    · simp only [hg, ite_true, and_self]
      exact rootNativeTransitionTest_eq_history rate rewards C_star C_h control0 b0 u0 t0 s hs F w0 hg.1 hg.2
    · simp only [hg, ite_false, installationTestSum, lintegral_zero, zero_mul, Finset.sum_const_zero]
  · simp only [G, hE0, ite_false, installationTestSum, lintegral_zero, zero_mul, Finset.sum_const_zero]

/-- The retained ROOT identity under the raw experiment and every original
fixed-ID component law. Original component masses are never normalized. -/
theorem generated_component_root_retained_transition_test (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (hs : s.val ≤ t0.val)
    (F : TransitionData rate s t0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, retainedSourceTest rate rewards C_star C_h s t0 F
        (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
      ∫⁻ w, retainedKernelTest rate rewards C_star C_h s t0 F
        (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0)) := by
  cases ids with
  | none =>
    simpa only [Option.elim, Set.mem_univ, ite_true] using
      generated_component_root_history_event_test rate rewards C_star C_h control0 b0 u0 t0
        s hs Set.univ MeasurableSet.univ F hF
  | some id =>
    let E : Set (History rate s t0) := {h | h.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id}
    have hE : MeasurableSet E :=
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage measurable_fst.fst
    have h := generated_component_root_history_event_test rate rewards C_star C_h control0 b0 u0 t0 s hs E hE F hF
    simp only [Option.elim, ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw, lintegral_smul_measure]
    apply congrArg (fun x : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {id})⁻¹ * x)
    have hsection := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_componentSource
        rate rewards C_star C_h control0 (.generated b0 u0 t0))
    rw [← lintegral_indicator hsection, ← lintegral_indicator hsection]
    convert h using 1 <;> apply lintegral_congr <;> intro w <;> rfl

end RootHistory

end Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore
