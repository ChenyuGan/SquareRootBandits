/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeInitialLaw
public import Bandits.Support.ReferenceGeneratedCalendarRetainedMarginalBridge

import Mathlib.Tactic

/-!
# Actual episode/date reindexing of the retained terminal archive

Every retained archive mark is joined to its unique actual original-record
episode start. The resulting finite sum keeps the literal archive, source,
private coordinates, current mark, and PRE-clear retention event.

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell SlowSet)
open ReferenceExhaustiveGeneratedCalendarSourceLaw
  (Omega terminalSource terminalReadout terminalLaw fixedIDTerminalLaw)
open ReferenceGeneratedCalendarEpisodeSlowLaw (archive currentMark episodeStartEvent retainedEvent)
open ReferenceGeneratedCalendarEpisodeInitialLaw
  (ae_retained_episode_origin ae_retained_unique_episodeStart)

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeRetainedReindex

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] : MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

/-- The literal event that date `q` belongs to the actual episode starting at
`s` and is retained at its incoming PRE state. -/
def episodeDateEvent (s q : Fin p.T) : Set Omega :=
  episodeStartEvent rate rewards C_star C_h control0 s ∩
    retainedEvent rate rewards C_star C_h control0 s q

/-- One episode/date contribution. An absent current mark contributes zero;
the event itself includes both the actual start and the retained interval. -/
def episodeDateTerm (f : LogicalCell p rate → ℝ) (s q : Fin p.T) (w : Omega) : ℝ :=
  ((currentMark rate rewards C_star C_h control0 q w).elim 0 f) *
    (Set.indicator (episodeDateEvent rate rewards C_star C_h control0 s q)
      (fun _ => (1 : ℝ)) w)

private theorem sum_episodeDateIndicator
    (w : Omega) (q : Fin p.T) (e : LogicalCell p rate)
    (he : currentMark rate rewards C_star C_h control0 q w = some e)
    (hclear : e.before.overflow = false)
    (horigin : ∀ (q : Fin p.T) (e : LogicalCell p rate),
      currentMark rate rewards C_star C_h control0 q w = some e → e.before.overflow = false →
      ∃ (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate (terminalSource rate rewards C_star C_h control0 w) rewards C_star C_h).length)
        (_P : ReferenceActivePhysicalStep.Payload rate) (_A : RecordedQueueRun.RunState p.K),
        let s := (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate (terminalSource rate rewards C_star C_h control0 w) rewards C_star C_h)[rho.val].input.time
        w ∈ ReferenceGeneratedCalendarEpisodeSlowLaw.episodeStartEvent rate rewards C_star C_h control0 s ∧
        w ∈ ReferenceGeneratedCalendarEpisodeSlowLaw.retainedEvent rate rewards C_star C_h control0 s q)
    (hunique : ∀ (q : Fin p.T) (e : LogicalCell p rate),
      currentMark rate rewards C_star C_h control0 q w = some e → e.before.overflow = false →
      ∃! s : Fin p.T,
        w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
          w ∈ retainedEvent rate rewards C_star C_h control0 s q)
    :
    (∑ s : Fin p.T,
      Set.indicator
        (ReferenceGeneratedCalendarEpisodeSlowLaw.episodeStartEvent rate rewards C_star C_h control0 s ∩
          ReferenceGeneratedCalendarEpisodeSlowLaw.retainedEvent rate rewards C_star C_h control0 s q)
        (fun _ => (1 : ℝ)) w) = 1 := by
  obtain ⟨rho, P, A, hpair⟩ := horigin q e he hclear
  obtain ⟨hs, hret⟩ := hpair
  let s₀ := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate (terminalSource rate rewards C_star C_h control0 w) rewards C_star C_h)[rho.val].input.time
  have hpair₀ : w ∈ episodeStartEvent rate rewards C_star C_h control0 s₀ ∧
      w ∈ retainedEvent rate rewards C_star C_h control0 s₀ q := by
    simpa only [s₀] using And.intro hs hret
  obtain ⟨s₁, hpair₁, hunique₁⟩ := hunique q e he hclear
  have hs₁ : s₁ = s₀ := (hunique₁ s₀ hpair₀).symm
  have hone (s : Fin p.T) :
      w ∈ episodeDateEvent rate rewards C_star C_h control0 s q ↔ s = s₀ := by
    constructor
    · intro h
      change w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
        w ∈ retainedEvent rate rewards C_star C_h control0 s q at h
      exact (hunique₁ s h).trans hs₁
    · intro h
      subst s
      exact hpair₀
  have hterm (s : Fin p.T) :
      Set.indicator (episodeStartEvent rate rewards C_star C_h control0 s ∩
        retainedEvent rate rewards C_star C_h control0 s q)
        (fun _ => (1 : ℝ)) w = if s = s₀ then 1 else 0 := by
    by_cases hs : s = s₀
    · subst s
      have hmem₀ : w ∈ episodeStartEvent rate rewards C_star C_h control0 s₀ ∩
          retainedEvent rate rewards C_star C_h control0 s₀ q := hpair₀
      rw [Set.indicator_of_mem hmem₀]
      simp
    · have hnot : w ∉ episodeStartEvent rate rewards C_star C_h control0 s ∩
          retainedEvent rate rewards C_star C_h control0 s q := by
        intro h
        have h' : w ∈ episodeDateEvent rate rewards C_star C_h control0 s q := h
        exact hs ((hone s).mp h')
      rw [Set.indicator_of_notMem hnot]
      simp [hs]
  simp_rw [hterm]
  simp

private theorem sum_episodeDateIndicator_eq_zero
    (w : Omega) (q : Fin p.T) (e : LogicalCell p rate)
    (he : currentMark rate rewards C_star C_h control0 q w = some e)
    (hover : e.before.overflow = true)
    (hcoverage : ∀ (s q : Fin p.T) (w : Omega),
      w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
      s.val ≤ q.val → q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
      ∃ e : LogicalCell p rate,
        currentMark rate rewards C_star C_h control0 q w = some e)
    (hretained : ∀ (s q : Fin p.T) (e : LogicalCell p rate),
      currentMark rate rewards C_star C_h control0 q w = some e →
      (w ∈ retainedEvent rate rewards C_star C_h control0 s q ↔
        s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧
          e.before.overflow = false)) :
    (∑ s : Fin p.T,
      Set.indicator (episodeStartEvent rate rewards C_star C_h control0 s ∩
        retainedEvent rate rewards C_star C_h control0 s q) (fun _ => (1 : ℝ)) w) = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hmem : w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∩
      retainedEvent rate rewards C_star C_h control0 s q
  · rcases hmem with ⟨hs, hret⟩
    have hmem' : w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∩
        retainedEvent rate rewards C_star C_h control0 s q := ⟨hs, hret⟩
    have hretMem : w ∈ retainedEvent rate rewards C_star C_h control0 s q := hret
    change s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧
      (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
        q.castSucc (terminalSource rate rewards C_star C_h control0 w)).any
        (fun S => !S.overflow) = true at hret
    obtain ⟨hsq, hq, _hpre⟩ := hret
    obtain ⟨e', he'⟩ := hcoverage s q w hs hsq hq
    have heq : e' = e := Option.some.inj (he'.symm.trans he)
    have hclear := (hretained s q e' he').mp hretMem
    have hclear' : e.before.overflow = false := by simpa only [heq] using hclear.2.2
    simp only [Set.indicator_of_mem hmem']
    exfalso
    have hfalse : false = true := hclear'.symm.trans hover
    cases hfalse
  · simp [Set.indicator, hmem]

/-- Reindex the complete literal PRE-clear archive by the unique actual
episode-start/date pairs. This holds simultaneously for every real-valued
cell test and under the raw and every original fixed-ID terminal law. -/
theorem episodeDateSum_eq_retainedArchiveSum
    (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ f : LogicalCell p rate → ℝ,
      (∑ s : Fin p.T, ∑ q : Fin p.T,
        episodeDateTerm rate rewards C_star C_h control0 f s q w) =
      (((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.before.overflow = false)).map f).sum := by
  filter_upwards
    [ae_retained_episode_origin rate rewards C_star C_h control0 ids,
      ae_retained_unique_episodeStart rate rewards C_star C_h control0 ids,
      ReferenceGeneratedCalendarEpisodeSlowLaw.ae_retainedEvent_currentMark
        rate rewards C_star C_h control0 ids] with w horigin hunique hretained
  intro f
  let H := archive rate rewards C_star C_h control0 w
  let L := H.filter (fun e => e.before.overflow = false)
  let dates := L.map LogicalCell.time
  let g := fun q : Fin p.T =>
    (currentMark rate rewards C_star C_h control0 q w).elim 0
      (fun e => if e.before.overflow = false then f e else 0)
  have hdate (q : Fin p.T) :
      (∑ s : Fin p.T, episodeDateTerm rate rewards C_star C_h control0 f s q w) = g q := by
    cases hmark : currentMark rate rewards C_star C_h control0 q w with
    | none => simp [episodeDateTerm, hmark, g]
    | some e =>
      by_cases hclear : e.before.overflow = false
      · have horigin' (q' : Fin p.T) (e' : LogicalCell p rate)
          (he' : currentMark rate rewards C_star C_h control0 q' w = some e')
          (hc : e'.before.overflow = false) :
          ∃ (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate (terminalSource rate rewards C_star C_h control0 w) rewards C_star C_h).length)
            (P : ReferenceActivePhysicalStep.Payload rate) (A : RecordedQueueRun.RunState p.K),
            let s := (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate (terminalSource rate rewards C_star C_h control0 w) rewards C_star C_h)[rho.val].input.time
            w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
              w ∈ retainedEvent rate rewards C_star C_h control0 s q' := by
          obtain ⟨rho, P, A, _, _, _, _, _, hs, hr⟩ := horigin q' e' he' hc
          exact ⟨rho, P, A, hs, hr⟩
        have hsum := sum_episodeDateIndicator rate rewards C_star C_h control0 w q e hmark hclear
          horigin' hunique
        simp only [episodeDateTerm, episodeDateEvent, hmark]
        rw [← Finset.mul_sum, hsum]
        simp [g, hmark, hclear]
      · have hover : e.before.overflow = true := by
          cases hb : e.before.overflow with
          | false => exact False.elim (hclear hb)
          | true => rfl
        have hcoverage : ∀ (s q : Fin p.T) (w : Omega),
            w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
            s.val ≤ q.val → q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
            ∃ e : LogicalCell p rate,
              currentMark rate rewards C_star C_h control0 q w = some e := by
          intro s q w hs hsq hq
          obtain ⟨_, ⟨e', he', _⟩⟩ :=
            ReferenceGeneratedCalendarEpisodeSlowLaw.episodeStartEvent_unique_coverage
              rate rewards C_star C_h control0 s q w hs hsq hq
          exact ⟨e', he'⟩
        have hsum := sum_episodeDateIndicator_eq_zero rate rewards C_star C_h control0 w q e hmark hover
            hcoverage hretained
        simp only [episodeDateTerm, episodeDateEvent, hmark]
        rw [← Finset.mul_sum, hsum]
        simp [g, hmark, hover]
  have hn : dates.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).filter _).imp
        (fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h))
  have hvalues : ∀ e ∈ L, f e = g e.time := by
    intro e he
    obtain ⟨hem, hclear⟩ := List.mem_filter.mp he
    have hclear' : e.before.overflow = false := of_decide_eq_true hclear
    have hmark : currentMark rate rewards C_star C_h control0 e.time w = some e :=
      (ReferenceGeneratedCalendarEpisodeSlowLaw.currentMark_eq_some_iff
        rate rewards C_star C_h control0 e.time w e).mpr ⟨hem, rfl⟩
    simp [g, hmark, hclear']
  have hm : L.map f = dates.map g := by
    rw [List.map_map]
    exact List.map_congr_left hvalues
  have hsupport : ∀ q ∉ dates.toFinset, g q = 0 := by
    intro q hq
    dsimp only [g]
    cases hmark : currentMark rate rewards C_star C_h control0 q w with
    | none => simp
    | some e =>
      by_cases hc : e.before.overflow = false
      · have he := (ReferenceGeneratedCalendarEpisodeSlowLaw.currentMark_eq_some_iff
          rate rewards C_star C_h control0 q w e).mp hmark
        have hmem : e ∈ L := List.mem_filter.mpr ⟨he.1, decide_eq_true hc⟩
        have hqmem : q ∈ dates := by
          exact List.mem_map.mpr ⟨e, hmem, he.2⟩
        exact (hq (List.mem_toFinset.mpr hqmem)).elim
      · simp [hc]
  have hsumArchive : (L.map f).sum = ∑ q : Fin p.T, g q := by
    rw [hm, ← List.sum_toFinset g hn]
    apply Finset.sum_subset (Finset.subset_univ dates.toFinset)
    intro q hq hnot
    exact hsupport q hnot
  calc
    _ = ∑ q : Fin p.T, g q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact hdate q
    _ = (L.map f).sum := hsumArchive.symm

/-- Measurability of the literal actual start/date gate. -/
theorem measurableSet_episodeDateEvent (s q : Fin p.T) :
    MeasurableSet (episodeDateEvent rate rewards C_star C_h control0 s q) := by
  exact (ReferenceGeneratedCalendarEpisodeInitialLaw.measurableSet_episodeStartEvent
      rate rewards C_star C_h control0 s).inter
    (ReferenceGeneratedCalendarEpisodeSlowLaw.measurableSet_retainedEvent
      rate rewards C_star C_h control0 s q)

private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hsum : Measurable (fun o : Option A => Equiv.optionEquivSumPUnit A o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

/-- A measurable continuous-cell test gives measurable actual episode/date
terms. The whole logical-cell carrier retains its original Borel factors. -/
theorem measurable_episodeDateTerm (f : LogicalCell p rate → ℝ)
    (hf : Measurable f) (s q : Fin p.T) :
    Measurable (episodeDateTerm rate rewards C_star C_h control0 f s q) := by
  unfold episodeDateTerm
  exact ((measurable_option_elim f hf 0).comp
      (ReferenceGeneratedCalendarEpisodeSlowLaw.measurable_currentMark
        rate rewards C_star C_h control0 q)).mul
    (measurable_const.indicator
      (measurableSet_episodeDateEvent rate rewards C_star C_h control0 s q))

/-- Uniform bound for one real-valued actual episode/date test term. -/
theorem episodeDateTerm_abs_le (f : LogicalCell p rate → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ e, |f e| ≤ B)
    (s q : Fin p.T) (w : Omega) :
    |episodeDateTerm rate rewards C_star C_h control0 f s q w| ≤ B := by
  have hcoef :
      |(currentMark rate rewards C_star C_h control0 q w).elim 0 f| ≤ B := by
    cases h : currentMark rate rewards C_star C_h control0 q w with
    | none => simpa [h] using hB
    | some e => simpa [h] using hbound e
  have hind :
      |Set.indicator (episodeDateEvent rate rewards C_star C_h control0 s q)
        (fun _ => (1 : ℝ)) w| ≤ 1 := by
    by_cases h : w ∈ episodeDateEvent rate rewards C_star C_h control0 s q
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  unfold episodeDateTerm
  calc
    _ = |(currentMark rate rewards C_star C_h control0 q w).elim 0 f| *
        |Set.indicator (episodeDateEvent rate rewards C_star C_h control0 s q)
          (fun _ => (1 : ℝ)) w| := abs_mul _ _
    _ ≤ B * 1 := mul_le_mul hcoef hind (abs_nonneg _) hB
    _ = B := mul_one B

/-- Every actual episode/date term is integrable under the raw original law
and under each original fixed-ID law, for a visible bounded measurable test. -/
theorem integrable_episodeDateTerm (ids : Option (CompletePublicTable.IDArray p))
    (f : LogicalCell p rate → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hbound : ∀ e, |f e| ≤ B) (s q : Fin p.T) :
    Integrable (episodeDateTerm rate rewards C_star C_h control0 f s q)
      (ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  cases ids <;> dsimp only [Option.elim] <;>
    apply Integrable.of_bound
      (measurable_episodeDateTerm rate rewards C_star C_h control0 f hf s q).aestronglyMeasurable
      B <;>
    exact Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using
        episodeDateTerm_abs_le rate rewards C_star C_h control0 f B hB hbound s q w

/-- Exact signed integral decomposition of the retained archive sum into
actual episode/date terms, under the raw law and every original fixed-ID law.
The bound is only test regularity; no stochastic episode law is used. -/
theorem integral_retainedArchiveSum_eq_episodeDateIntegrals
    (ids : Option (CompletePublicTable.IDArray p))
    (f : LogicalCell p rate → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Measurable f) (hbound : ∀ e, |f e| ≤ B) :
    (∫ w, (((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.before.overflow = false)).map f).sum
      ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) =
      ∑ s : Fin p.T, ∑ q : Fin p.T,
        ∫ w, episodeDateTerm rate rewards C_star C_h control0 f s q w
          ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
            (fixedIDTerminalLaw rate rewards C_star C_h control0) := by
  let μ := ids.elim (terminalLaw rate rewards C_star C_h control0)
    (fixedIDTerminalLaw rate rewards C_star C_h control0)
  have hae := episodeDateSum_eq_retainedArchiveSum rate rewards C_star C_h control0 ids
  have hae' : ∀ᵐ w ∂μ,
      (∑ s : Fin p.T, ∑ q : Fin p.T,
        episodeDateTerm rate rewards C_star C_h control0 f s q w) =
        (((archive rate rewards C_star C_h control0 w).filter
          (fun e => e.before.overflow = false)).map f).sum := by
    simpa only [μ] using (hae.mono fun w hw => hw f)
  have hfun :
      (fun w => (((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.before.overflow = false)).map f).sum) =ᵐ[μ]
      (fun w => ∑ s : Fin p.T, ∑ q : Fin p.T,
        episodeDateTerm rate rewards C_star C_h control0 f s q w) := by
    filter_upwards [hae'] with w hw
    exact hw.symm
  have hterm (s q : Fin p.T) :
      Integrable (episodeDateTerm rate rewards C_star C_h control0 f s q) μ :=
    integrable_episodeDateTerm rate rewards C_star C_h control0 ids f B hB hf hbound s q
  have hinner (s : Fin p.T) :
      Integrable (fun w => ∑ q : Fin p.T,
        episodeDateTerm rate rewards C_star C_h control0 f s q w) μ := by
    simpa only [← Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun q _ => hterm s q))
  calc
    _ = ∫ w, ∑ s : Fin p.T, ∑ q : Fin p.T,
          episodeDateTerm rate rewards C_star C_h control0 f s q w ∂μ :=
      integral_congr_ae hfun
    _ = ∑ s : Fin p.T, ∫ w, ∑ q : Fin p.T,
          episodeDateTerm rate rewards C_star C_h control0 f s q w ∂μ := by
      rw [integral_finsetSum Finset.univ (fun s _ => hinner s)]
    _ = ∑ s : Fin p.T, ∑ q : Fin p.T,
          ∫ w, episodeDateTerm rate rewards C_star C_h control0 f s q w ∂μ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_finsetSum Finset.univ (fun q _ => hterm s q)]

/-- Comparator reward minus the accepted stopped-cell auxiliary reward. -/
public def retainedSignedCellGap
    (S : ProductSetLaw.ProductSet p.K p.m) (e : LogicalCell p rate) : ℝ :=
  (∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
    ReferenceInitialStoppedCalendar.cellReward rate rewards e

private theorem comparatorReward_bounds (S : ProductSetLaw.ProductSet p.K p.m)
    (q : Fin p.T) :
    0 ≤ ∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ) ∧
      (∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ)) ≤ p.m := by
  have hb (i : Fin p.K) :
      0 ≤ ((rewards q i).val : ℝ) / (D p : ℝ) ∧
        ((rewards q i).val : ℝ) / (D p : ℝ) ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (D_pos p))).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards q i).isLt
  refine ⟨Finset.sum_nonneg (fun i _ => (hb i).1), ?_⟩
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
    (Finset.mem_powersetCard.mp S.property).2] using
      Finset.sum_le_sum (fun i (_hi : i ∈ S.val) => (hb i).2)

private theorem retainedSignedCellGap_abs_le
    (S : ProductSetLaw.ProductSet p.K p.m) (e : LogicalCell p rate) :
    |retainedSignedCellGap rate rewards S e| ≤ p.m := by
  have hc := comparatorReward_bounds rewards S e.time
  have hr := ReferenceExhaustiveGeneratedCalendarSourceLaw.cellReward_bounds rate rewards e
  unfold retainedSignedCellGap
  exact abs_le.mpr ⟨by linarith only [hc.1, hr.2], by linarith only [hc.2, hr.1]⟩

private theorem measurable_retainedSignedCellGap
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (retainedSignedCellGap rate rewards S) := by
  let mark : LogicalCell p rate → Fin p.T × (SlowSet p × Fin p.K) :=
    fun e => (e.time, (e.slowSet, e.fastArm))
  have hm : Measurable mark :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time.prodMk
      (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.prodMk
        ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_fastArm)
  let F : Fin p.T × (SlowSet p × Fin p.K) → ℝ := fun x =>
    (∑ i ∈ S.val, ((rewards x.1 i).val : ℝ) / (D p : ℝ)) -
      ((∑ i ∈ x.2.1.val, ((rewards x.1 i).val : ℝ) / (D p : ℝ)) +
        ((rewards x.1 x.2.2).val : ℝ) / (D p : ℝ))
  have hF : Measurable F := measurable_of_countable F
  have h := hF.comp hm
  convert h using 1
  funext e
  simp only [Function.comp_apply, mark, retainedSignedCellGap,
    ReferenceInitialStoppedCalendar.cellReward]
  rfl

/-- The exact accepted signed retained gap is the integral of its actual
episode/date decomposition under either original terminal law. Its established
measurability, integrability, and uniform archive bound are returned with the
decomposition. -/
theorem retainedSignedGap_episodeDateIntegral
    (ids : Option (CompletePublicTable.IDArray p))
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (ReferenceGeneratedCalendarOverflowTail.retainedSignedGap
      rate rewards C_star C_h control0 S) ∧
    Integrable (ReferenceGeneratedCalendarOverflowTail.retainedSignedGap
      rate rewards C_star C_h control0 S)
      (ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) ∧
    (∀ w, |ReferenceGeneratedCalendarOverflowTail.retainedSignedGap
      rate rewards C_star C_h control0 S w| ≤ (p.m : ℝ) * p.T) ∧
    (∫ w, ReferenceGeneratedCalendarOverflowTail.retainedSignedGap
        rate rewards C_star C_h control0 S w
      ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) =
      ∑ s : Fin p.T, ∑ q : Fin p.T,
        ∫ w, episodeDateTerm rate rewards C_star C_h control0
          (retainedSignedCellGap rate rewards S) s q w
          ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
            (fixedIDTerminalLaw rate rewards C_star C_h control0) := by
  refine ⟨ReferenceGeneratedCalendarOverflowTail.measurable_retainedSignedGap
      rate rewards C_star C_h control0 S,
    ReferenceGeneratedCalendarOverflowTail.integrable_retainedSignedGap
      rate rewards C_star C_h control0 ids S,
    ?_, ?_⟩
  · exact ReferenceGeneratedCalendarOverflowTail.retainedSignedGap_abs_le
      rate rewards C_star C_h control0 S
  · have h := integral_retainedArchiveSum_eq_episodeDateIntegrals rate rewards C_star C_h
      control0 ids (retainedSignedCellGap rate rewards S) (p.m : ℝ) (Nat.cast_nonneg _)
      (measurable_retainedSignedCellGap rate rewards S)
      (fun e => retainedSignedCellGap_abs_le rate rewards S e)
    change (∫ w, (((archive rate rewards C_star C_h control0 w).filter
        (fun e => e.before.overflow = false)).map
          (retainedSignedCellGap rate rewards S)).sum
      ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) = _
    exact h

private theorem retainedMarginalCellGap_abs_le
    (S : ProductSetLaw.ProductSet p.K p.m) (e : LogicalCell p rate) :
    |ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
      rate rewards S e| ≤ p.m := by
  let r := fun i : Fin p.K => ((rewards e.time i).val : ℝ) / (D p : ℝ)
  let theta := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.before)
  have hr (i : Fin p.K) : 0 ≤ r i ∧ r i ≤ 1 :=
    ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards e.time i
  have ht (i : Fin p.K) : 0 ≤ theta i :=
    (RecordedMarginalGrowth.state_theta_pos Q e.before i
      (by have hm := p.two_le_m; omega) p.m_lt_K).le
  have hc : 0 ≤ ∑ i ∈ S.val, r i ∧ (∑ i ∈ S.val, r i) ≤ p.m := by
    refine ⟨Finset.sum_nonneg (fun i _ => (hr i).1), ?_⟩
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      (Finset.mem_powersetCard.mp S.property).2] using
        Finset.sum_le_sum (fun i (_hi : i ∈ S.val) => (hr i).2)
  have hw : 0 ≤ ∑ i : Fin p.K, theta i * r i ∧
      (∑ i : Fin p.K, theta i * r i) ≤ p.m := by
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (ht i) (hr i).1), ?_⟩
    calc
      _ ≤ ∑ i : Fin p.K, theta i :=
        Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (ht i) (hr i).2)
      _ = _ := RecordedMarginalGrowth.state_sum_theta_eq_m Q e.before
        (by have hm := p.two_le_m; omega) p.m_lt_K
  unfold ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
  simp_rw [mul_div_assoc]
  exact abs_le.mpr ⟨by linarith only [hc.1, hw.2], by linarith only [hc.2, hw.1]⟩

private theorem measurable_retainedMarginalCellGap
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
      rate rewards S) := by
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

/-- Exact integral decomposition for the accepted PRE-clear current-marginal
gap, with the original law's existing regularity and bound. -/
theorem retainedMarginalGap_episodeDateIntegral
    (ids : Option (CompletePublicTable.IDArray p))
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap
      rate rewards C_star C_h control0 S) ∧
    Integrable (ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap
      rate rewards C_star C_h control0 S)
      (ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) ∧
    (∀ w, |ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap
      rate rewards C_star C_h control0 S w| ≤ (p.m : ℝ) * p.T) ∧
    (∫ w, ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap
        rate rewards C_star C_h control0 S w
      ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) =
      ∑ s : Fin p.T, ∑ q : Fin p.T,
        ∫ w, episodeDateTerm rate rewards C_star C_h control0
          (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap rate rewards S)
          s q w
          ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
            (fixedIDTerminalLaw rate rewards C_star C_h control0) := by
  refine ⟨ReferenceGeneratedCalendarRetainedMarginalBridge.measurable_retainedMarginalGap
      rate rewards C_star C_h control0 S,
    ReferenceGeneratedCalendarRetainedMarginalBridge.integrable_retainedMarginalGap
      rate rewards C_star C_h control0 ids S,
    ?_, ?_⟩
  · exact ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap_abs_le
      rate rewards C_star C_h control0 S
  · have h := integral_retainedArchiveSum_eq_episodeDateIntegrals rate rewards C_star C_h
      control0 ids (ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap
        rate rewards S) (p.m : ℝ) (Nat.cast_nonneg _)
      (measurable_retainedMarginalCellGap rate rewards S)
      (fun e => retainedMarginalCellGap_abs_le rate rewards S e)
    simpa only [ReferenceGeneratedCalendarRetainedMarginalBridge.retainedMarginalGap,
      ReferenceGeneratedCalendarRetainedMarginalBridge.cellMarginalGap, archive] using h

end Bandits.Support.ReferenceGeneratedCalendarEpisodeRetainedReindex

end
