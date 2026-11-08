/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowLaw
public import Bandits.Support.RecordedQuantizedEstimateReplay

/-!
# Source quantized episode histories on the generated calendar

Sources: ZIP4 `04_slow_fast_learner.tex:140-215,329-390` and
`06_interruptions.tex:391-426`.

The history retains the accepted strict start history and exactly the past
normalized floor estimates. No recorder label is recovered from these vectors.
The results below concern deterministic replay and transport of observations;
they do not assert a conditional slow-set law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeSlowLaw
open RecordedQuantizedEstimateReplay
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport

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
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The carrier of the single accepted start history and source estimates. -/
abbrev History (s q : Fin p.T) :=
  (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p)

omit rewards C_star C_h control0 in
/-- The source estimate of a cell, including disabled and incoming-stop gates. -/
def sourceCellEstimate (e : LogicalCell p rate) : Estimate p :=
  vectorCoarsening (Q).n (cellEstimate rate e)

omit rewards C_star C_h control0 in
theorem measurable_sourceCellEstimate : Measurable (sourceCellEstimate rate) :=
  (vectorCoarsening_measurable (Q).n).comp (measurable_cellEstimate rate)

omit rewards C_star C_h control0 in
theorem sourceCellEstimate_eq_rawEstimate (e : LogicalCell p rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c)
    (i : Fin p.K) :
    sourceCellEstimate rate e i = RecordedRoundMoments.rawEstimate Q e.before c i := by
  rw [rawEstimate_eq_sourceCoarsening]
  unfold sourceCellEstimate vectorCoarsening cellEstimate
  rw [hc]
  rfl

omit rewards C_star C_h control0 in
/-- Absence has zero source estimate and supplies no artificial numerical state. -/
def sourceOptionalEstimate (e : Option (LogicalCell p rate)) : Estimate p :=
  vectorCoarsening (Q).n (optionalEstimate rate e)

omit rewards C_star C_h control0 in
theorem sourceOptionalEstimate_none : sourceOptionalEstimate rate none = 0 := by
  funext i
  simp only [sourceOptionalEstimate, vectorCoarsening, scalarCoarsening,
    optionalEstimate, Pi.zero_apply, mul_zero, Nat.floor_zero, Nat.cast_zero, zero_div]

omit rewards C_star C_h control0 in
theorem sourceOptionalEstimate_some (e : LogicalCell p rate) :
    sourceOptionalEstimate rate (some e) = sourceCellEstimate rate e := rfl

omit rewards C_star C_h control0 in
theorem measurable_sourceOptionalEstimate : Measurable (sourceOptionalEstimate rate) :=
  (vectorCoarsening_measurable (Q).n).comp (measurable_optionalEstimate rate)

/-- The normalized floor on the same actual per-date observer. -/
def sourceEstimateAt (q : Fin p.T) (w : Omega) : Estimate p :=
  sourceOptionalEstimate rate (currentMark rate rewards C_star C_h control0 q w)

theorem sourceEstimateAt_eq_coarsening (q : Fin p.T) (w : Omega) :
    sourceEstimateAt rate rewards C_star C_h control0 q w =
      vectorCoarsening (Q).n (estimateAt rate rewards C_star C_h control0 q w) := rfl

theorem measurable_sourceEstimateAt (q : Fin p.T) :
    Measurable (sourceEstimateAt rate rewards C_star C_h control0 q) :=
  (measurable_sourceOptionalEstimate rate).comp
    (measurable_currentMark rate rewards C_star C_h control0 q)

omit rewards C_star C_h control0 in
/-- Borel coarsening of the finer accepted observer, without changing its seed. -/
def historyCoarsening (s q : Fin p.T) (h : History rate s q) : History rate s q :=
  (h.1, fun v => vectorCoarsening (Q).n (h.2 v))

omit rewards C_star C_h control0 in
theorem measurable_historyCoarsening (s q : Fin p.T) :
    Measurable (historyCoarsening rate s q) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr fun v =>
    (vectorCoarsening_measurable (Q).n).comp ((measurable_pi_apply v).comp measurable_snd))

/-- Exactly H_s and the source estimates at s ≤ v < q. -/
def sourceEstimateHistory (s q : Fin p.T) (w : Omega) : History rate s q :=
  (startHistory rate rewards C_star C_h control0 s w,
    fun v => sourceEstimateAt rate rewards C_star C_h control0 v.val w)

theorem sourceEstimateHistory_eq_coarsening (s q : Fin p.T) (w : Omega) :
    sourceEstimateHistory rate rewards C_star C_h control0 s q w =
      historyCoarsening rate s q (estimateHistory rate rewards C_star C_h control0 s q w) := rfl

theorem measurable_sourceEstimateHistory (s q : Fin p.T) :
    Measurable (sourceEstimateHistory rate rewards C_star C_h control0 s q) :=
  (measurable_historyCoarsening rate s q).comp
    (measurable_estimateHistory rate rewards C_star C_h control0 s q)

omit rate rewards C_star C_h control0 in
/-- Normalized flooring preserves the integer code, even when the input is zero. -/
theorem floor_scalarCoarsening (n : ℕ) (hn : 0 < n) (x : ℝ) :
    Nat.floor ((n : ℝ) * scalarCoarsening n x) = Nat.floor ((n : ℝ) * x) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold scalarCoarsening
  rw [show (n : ℝ) * ((Nat.floor ((n : ℝ) * x) : ℝ) / (n : ℝ)) =
    (Nat.floor ((n : ℝ) * x) : ℝ) by field_simp]
  exact Nat.floor_natCast _

omit rewards C_star C_h control0 in
theorem estimateRecord_coarsening (S : RecordedQueueRun.RunState p.K)
    (enabled : Bool) (x : Estimate p) :
    estimateRecord rate S enabled (vectorCoarsening (Q).n x) =
      estimateRecord rate S enabled x := by
  funext i
  simp only [estimateRecord, vectorCoarsening, floor_scalarCoarsening (Q).n (Q).n_pos]

omit rewards C_star C_h control0 in
theorem estimateStep_coarsening (S : RecordedQueueRun.RunState p.K)
    (enabled : Bool) (x : Estimate p) :
    estimateStep rate S enabled (vectorCoarsening (Q).n x) =
      estimateStep rate S enabled x := by
  unfold estimateStep
  rw [estimateRecord_coarsening]

omit rewards C_star C_h control0 in
theorem stepFromEstimate_eq_estimateStep (S : RecordedQueueRun.RunState p.K)
    (enabled : Bool) (x : Estimate p) :
    stepFromEstimate Q S enabled x = estimateStep rate S enabled x := rfl

omit control0 in
/-- The actual chronological fold consumes only source vectors and its strict seed. -/
def sourceReplayPrefix (s q : Fin p.T) (h : History rate s q)
    (n : ℕ) (hn : n ≤ q.val - s.val) : Option (RecordedQueueRun.RunState p.K) :=
  replayPrefix rate rewards C_star C_h s q h n hn

omit control0 in
/-- Finite induction joins the coarsened sequence to the accepted chronological
fold at every prefix, with the same indices and the same varying strict seed. -/
theorem sourceReplayPrefix_coarsening (s q : Fin p.T) (h : History rate s q)
    (n : ℕ) (hn : n ≤ q.val - s.val) :
    sourceReplayPrefix rate rewards C_star C_h s q (historyCoarsening rate s q h) n hn =
      replayPrefix rate rewards C_star C_h s q h n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change replayPrefix rate rewards C_star C_h s q (historyCoarsening rate s q h) (n + 1) hn = _
    have hi := ih (by omega : n ≤ q.val - s.val)
    change replayPrefix rate rewards C_star C_h s q (historyCoarsening rate s q h) n _ = _ at hi
    rw [replayPrefix_succ, replayPrefix_succ, hi]
    apply congrArg (fun f => (replayPrefix rate rewards C_star C_h s q h n (by omega)).map f)
    funext S
    exact estimateStep_coarsening rate S true _

omit control0 in
/-- Complete numerical PRE, including records, from the source estimate history. -/
def sourceEpisodeReplay (s q : Fin p.T) (h : History rate s q) :
    Option (RecordedQueueRun.RunState p.K) :=
  sourceReplayPrefix rate rewards C_star C_h s q h (q.val - s.val) le_rfl

omit control0 in
theorem measurable_sourceEpisodeReplay (s q : Fin p.T) :
    Measurable (sourceEpisodeReplay rate rewards C_star C_h s q) :=
  measurable_episodeReplay rate rewards C_star C_h s q

theorem sourceEpisodeReplay_actual_eq_finer (s q : Fin p.T) (w : Omega) :
    sourceEpisodeReplay rate rewards C_star C_h s q
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w) =
    episodeReplay rate rewards C_star C_h s q
      (estimateHistory rate rewards C_star C_h control0 s q w) :=
  sourceReplayPrefix_coarsening rate rewards C_star C_h s q
    (estimateHistory rate rewards C_star C_h control0 s q w) (q.val - s.val) le_rfl

/-- Both original terminal laws, without a numerical truth or coverage input. -/
theorem ae_sourceEpisodeReplay (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        s.val ≤ q.val → q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
        sourceEpisodeReplay rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) =
        ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) := by
  filter_upwards [ae_episodeReplay rate rewards C_star C_h control0 ids] with w hw
  intro s q hs hsq hq
  rw [sourceEpisodeReplay_actual_eq_finer]
  exact hw s q hs hsq hq

omit rate rewards C_star C_h control0 in
theorem replayFromEstimateCodes_eq_foldl {K : ℕ} (params : RecordedQueueRun.Parameters)
    (S : RecordedQueueRun.RunState K) (codes : List (Bool × (Fin K → ℕ))) :
    replayFromEstimateCodes params S codes =
      codes.foldl (fun state c => stepFromArrivalCode params state c.1 c.2) S := by
  induction codes generalizing S with
  | nil => rfl
  | cons c codes ih => exact ih _

omit control0 in
/-- The fixed finite-sequence replay really consumes the same chronological
indices and seed as the history fold. This is an equality of complete states. -/
theorem sourceReplayPrefix_eq_finiteEstimateReplay (s q : Fin p.T)
    (h : History rate s q) (n : ℕ) (hn : n ≤ q.val - s.val) :
    sourceReplayPrefix rate rewards C_star C_h s q h n hn =
      (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
        s.castSucc h.1.1).map (fun S => finiteEstimateReplay Q S (fun _ : Fin n => true)
          (fun i => h.2 ⟨⟨s.val + i.val, by have := i.isLt; omega⟩,
            by change s.val ≤ s.val + i.val; omega,
            by change s.val + i.val < q.val; have := i.isLt; omega⟩)) := by
  unfold sourceReplayPrefix replayPrefix finiteEstimateReplay
  simp_rw [replayFromEstimateCodes_eq_foldl]
  simp only [List.ofFn_eq_map, List.foldl_map]
  cases hs : ReferencePostInvocationNoncallGeometry.prefixNumerical
      rate rewards C_star C_h s.castSucc h.1.1 with
  | none =>
    simp only [Option.map_none]
    exact List.foldl_fixed' (fun _ => rfl) _
  | some S =>
    simp only [Option.map_some]
    apply List.foldl_hom some
    intro state i
    rfl

omit rate rewards C_star C_h control0 in
/-- Joint measurability includes a varying seed and the entire enabled schedule.
Only the integer state and Boolean schedule have countable carriers. -/
theorem measurable_finiteEstimateReplay_joint {K n : ℕ} (params : RecordedQueueRun.Parameters) :
    Measurable (fun v : (RecordedQueueRun.RunState K × (Fin n → Bool)) ×
        (Fin n → Fin K → ℝ) => finiteEstimateReplay params v.1.1 v.1.2 v.2) := by
  apply measurable_from_prod_countable_right
  intro v
  exact finiteEstimateReplay_measurable params v.1 v.2

omit rewards C_star C_h control0 in
/-- Discard precisely the later source estimates. -/
def historyPrefix (s q r : Fin p.T) (hqr : q.val ≤ r.val)
    (h : History rate s r) : History rate s q :=
  (h.1, fun v => h.2 ⟨v.val, v.property.1, v.property.2.trans_le hqr⟩)

omit rewards C_star C_h control0 in
theorem measurable_historyPrefix (s q r : Fin p.T) (hqr : q.val ≤ r.val) :
    Measurable (historyPrefix rate s q r hqr) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr fun v =>
    (measurable_pi_apply (⟨v.val, v.property.1,
      v.property.2.trans_le hqr⟩ : EstimateDates s r)).comp measurable_snd)

theorem historyPrefix_sourceEstimateHistory (s q r : Fin p.T) (hqr : q.val ≤ r.val)
    (w : Omega) :
    historyPrefix rate s q r hqr (sourceEstimateHistory rate rewards C_star C_h control0 s r w) =
      sourceEstimateHistory rate rewards C_star C_h control0 s q w := rfl

/-- A single source-history prefix determines every earlier numerical PRE. -/
theorem ae_sourceEpisodeReplay_prefix (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q r : Fin p.T) (hqr : q.val ≤ r.val),
        w ∈ episodeStartEvent rate rewards C_star C_h control0 s → s.val ≤ q.val →
        r.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
        sourceEpisodeReplay rate rewards C_star C_h s q
          (historyPrefix rate s q r hqr (sourceEstimateHistory rate rewards C_star C_h control0 s r w)) =
        ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) := by
  filter_upwards [ae_sourceEpisodeReplay rate rewards C_star C_h control0 ids] with w hw
  intro s q r hqr hs hsq hr
  rw [historyPrefix_sourceEstimateHistory]
  exact hw s q hs hsq (by omega)

/-- The accepted fixed-sequence replay consumes the actual normalized source
estimates, in exact chronological order, from the actual strict-prefix seed. -/
theorem ae_sourceFiniteEstimateReplay (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        s.val ≤ q.val → q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
        (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
          (startHistory rate rewards C_star C_h control0 s w).1).map
            (fun S => finiteEstimateReplay Q S (fun _ : Fin (q.val - s.val) => true)
              (fun i => sourceEstimateAt rate rewards C_star C_h control0
                ⟨s.val + i.val, by have := i.isLt; omega⟩ w)) =
        ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) := by
  filter_upwards [ae_sourceEpisodeReplay rate rewards C_star C_h control0 ids] with w hw
  intro s q hs hsq hq
  have hbridge := sourceReplayPrefix_eq_finiteEstimateReplay rate rewards C_star C_h s q
    (sourceEstimateHistory rate rewards C_star C_h control0 s q w) (q.val - s.val) le_rfl
  exact hbridge.symm.trans (hw s q hs hsq hq)

omit rewards C_star C_h control0 in
/-- Append the current estimate and preserve the sole original start history. -/
def historySuccessor (s q r : Fin p.T) (hqr : r.val = q.val + 1)
    (v : History rate s q × Estimate p) : History rate s r :=
  (v.1.1, fun t => if ht : t.val = q then v.2 else
    v.1.2 ⟨t.val, t.property.1, by
      have := t.property.2
      have hne : t.val.val ≠ q.val := fun h => ht (Fin.ext h)
      omega⟩)

omit rewards C_star C_h control0 in
theorem measurable_historySuccessor (s q r : Fin p.T) (hqr : r.val = q.val + 1) :
    Measurable (historySuccessor rate s q r hqr) := by
  apply measurable_fst.fst.prodMk
  apply measurable_pi_iff.mpr
  intro t
  by_cases ht : t.val = q
  · simpa only [historySuccessor, ht, dite_true] using
      (measurable_snd : Measurable (Prod.snd : History rate s q × Estimate p → Estimate p))
  · simp only [ht, dite_false]
    exact ((measurable_pi_apply (⟨t.val, t.property.1, by
        have := t.property.2
        have hne : t.val.val ≠ q.val := fun h => ht (Fin.ext h)
        omega⟩ : EstimateDates s q)).comp measurable_fst.snd)

theorem historySuccessor_sourceEstimateHistory (s q r : Fin p.T)
    (hqr : r.val = q.val + 1) (w : Omega) :
    historySuccessor rate s q r hqr
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w,
        sourceEstimateAt rate rewards C_star C_h control0 q w) =
      sourceEstimateHistory rate rewards C_star C_h control0 s r w := by
  apply Prod.ext
  · rfl
  · funext t
    by_cases ht : t.val = q
    · simp only [historySuccessor, ht, dite_true, sourceEstimateHistory]
    · simp only [historySuccessor, ht, dite_false, sourceEstimateHistory]

/-- Exactly the sigma field generated by the source estimates and H_s. -/
abbrev sourceHistorySpace (s q : Fin p.T) : MeasurableSpace Omega :=
  MeasurableSpace.comap (sourceEstimateHistory rate rewards C_star C_h control0 s q) inferInstance

theorem sourceHistorySpace_le_finer (s q : Fin p.T) :
    sourceHistorySpace rate rewards C_star C_h control0 s q ≤
      estimateHistorySpace rate rewards C_star C_h control0 s q :=
  MeasurableSpace.comap_le_comap_of_eq_comp (historyCoarsening rate s q)
    (measurable_historyCoarsening rate s q) rfl

theorem sourceHistorySpace_mono (s q r : Fin p.T) (hqr : q.val ≤ r.val) :
    sourceHistorySpace rate rewards C_star C_h control0 s q ≤
      sourceHistorySpace rate rewards C_star C_h control0 s r :=
  MeasurableSpace.comap_le_comap_of_eq_comp (historyPrefix rate s q r hqr)
    (measurable_historyPrefix rate s q r hqr) rfl

theorem measurable_sourceEpisodeReplay_history (s q : Fin p.T) :
    Measurable[sourceHistorySpace rate rewards C_star C_h control0 s q]
      (fun w => sourceEpisodeReplay rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w)) :=
  (measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp
    (comap_measurable (sourceEstimateHistory rate rewards C_star C_h control0 s q))

omit control0 in
/-- The fixed anchor is read from the same optional strict-prefix seed. -/
def sourceEpisodeMass (s q : Fin p.T) (h : History rate s q) (U : SlowSet p) : ℝ≥0∞ :=
  match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc h.1.1,
      sourceEpisodeReplay rate rewards C_star C_h s q h with
  | some A, some S => RecordedSlowRefresh.recordedSlowPMF p Q S
      (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U
  | _, _ => 0

omit control0 in
theorem measurable_sourceEpisodeMass (s q : Fin p.T) (U : SlowSet p) :
    Measurable (fun h => sourceEpisodeMass rate rewards C_star C_h s q h U) :=
  measurable_episodeMass rate rewards C_star C_h s q U

theorem sourceEpisodeMass_actual_eq_finer (s q : Fin p.T) (w : Omega) (U : SlowSet p) :
    sourceEpisodeMass rate rewards C_star C_h s q
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U =
    episodeMass rate rewards C_star C_h s q
      (estimateHistory rate rewards C_star C_h control0 s q w) U := by
  unfold sourceEpisodeMass episodeMass
  rw [sourceEpisodeReplay_actual_eq_finer]
  rfl

omit control0 in
/-- The incoming-clear gate keeps the first detecting POST update. -/
def sourceHistoryRetained (s q : Fin p.T) : Set (History rate s q) :=
  {h | s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧
    (sourceEpisodeReplay rate rewards C_star C_h s q h).any (fun S => !S.overflow) = true}

omit control0 in
theorem measurableSet_sourceHistoryRetained (s q : Fin p.T) :
    MeasurableSet (sourceHistoryRetained rate rewards C_star C_h s q) :=
  measurableSet_historyRetained rate rewards C_star C_h s q

theorem ae_retainedEvent_sourceHistory (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        (w ∈ retainedEvent rate rewards C_star C_h control0 s q ↔
          sourceEstimateHistory rate rewards C_star C_h control0 s q w ∈
            sourceHistoryRetained rate rewards C_star C_h s q) := by
  filter_upwards [ae_retainedEvent_history rate rewards C_star C_h control0 ids] with w hw
  intro s q hs
  rw [hw s q hs]
  simp only [historyRetained, sourceHistoryRetained, Set.mem_ofPred_eq,
    sourceEpisodeReplay_actual_eq_finer]

open ReferenceOriginalCalendarEpisodeChronology in
/-- One actual source, birth, payload and clear seed work for every U. -/
theorem ae_sourceEpisodeMass_actual (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        w ∈ retainedEvent rate rewards C_star C_h control0 s q →
        ∃ (e : LogicalCell p rate)
          (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h).length)
          (P : ReferenceActivePhysicalStep.Payload rate) (A : RecordedQueueRun.RunState p.K),
          currentMark rate rewards C_star C_h control0 q w = some e ∧
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[rho.val].input.time = s ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[rho.val] P ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
            (startHistory rate rewards C_star C_h control0 s w).1 = some A ∧
          A.overflow = false ∧ P.anchor = RecordedQueueRun.scoreWeight Q A ∧
          ∀ U : SlowSet p, sourceEpisodeMass rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U =
            RecordedSlowRefresh.recordedSlowPMF p Q e.before P.anchor P.anchor_pos U := by
  filter_upwards [ae_episodeMass_actual rate rewards C_star C_h control0 ids] with w hw
  intro s q hs hret
  obtain ⟨e, rho, P, A, he, ht, hb, hA, hc, ha, hm⟩ := hw s q hs hret
  refine ⟨e, rho, P, A, he, ht, hb, hA, hc, ha, ?_⟩
  intro U
  rw [sourceEpisodeMass_actual_eq_finer]
  exact hm U

/-- The source vector is identified with the accepted estimate at the actual
original word entry. Existence and the numerical-coordinate match are proved
from the marked path, rather than supplied by the caller. -/
theorem ae_sourceEstimateAt_original_input (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (q : Fin p.T) (e : LogicalCell p rate),
        currentMark rate rewards C_star C_h control0 q w = some e →
        ∃ hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate (Z w) rewards C_star C_h = some active,
        let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h (Z w) hl
        ∃ hi : e.time.val - ReferenceCompletePhysicalHistory.physicalStart rate (Z w) rewards C_star C_h < W.length,
          e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
            W[e.time.val - ReferenceCompletePhysicalHistory.physicalStart rate (Z w) rewards C_star C_h] ∧
          sourceEstimateAt rate rewards C_star C_h control0 q w =
            sourceEstimate Q e.before
              W[e.time.val - ReferenceCompletePhysicalHistory.physicalStart rate (Z w) rewards C_star C_h] := by
  filter_upwards [ReferenceExhaustiveGeneratedCalendarSourceLaw.ae_terminal_marked_path
    rate rewards C_star C_h control0 ids] with w hw
  intro q e he
  obtain ⟨hem, _⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he
  rcases hw.2.2 with hn | ⟨hl, hdata⟩
  · have hnil : archive rate rewards C_star C_h control0 w = [] := hn.2
    rw [hnil] at hem
    exact (List.not_mem_nil hem).elim
  · obtain ⟨_, _, _, hi, _, hnum, _⟩ := hdata e hem
    refine ⟨hl, hi, hnum, ?_⟩
    funext i
    unfold sourceEstimateAt
    rw [he, sourceOptionalEstimate_some]
    exact sourceCellEstimate_eq_rawEstimate rate e _ hnum i

/-- Complete UPDATE, arrivals and all-arm service consume the actual source
estimate. Incoming overflow remains absorbing and the first crossing is kept. -/
theorem ae_source_estimate_numerical_update (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (q : Fin p.T) (e : LogicalCell p rate),
        currentMark rate rewards C_star C_h control0 q w = some e →
          e.numerical.1 = true ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) =
            some e.before ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.succ (Z w) =
            some e.after ∧
          e.arrivals = acceptedRecordFromEstimate Q e.before true
            (sourceEstimateAt rate rewards C_star C_h control0 q w) ∧
          e.after = stepFromEstimate Q e.before true
            (sourceEstimateAt rate rewards C_star C_h control0 q w) ∧
          e.service = (fun i => RecordedQueueRun.recordService (4 * (Q).n)
            (e.before.registers i) (acceptedRecordFromEstimate Q e.before true
              (sourceEstimateAt rate rewards C_star C_h control0 q w) i)) := by
  filter_upwards [ae_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hw
  intro q e he
  obtain ⟨hen, hb, ha, hr, hs, hv⟩ := hw q e he
  have hrec : acceptedRecordFromEstimate Q e.before true
      (sourceEstimateAt rate rewards C_star C_h control0 q w) =
      estimateRecord rate e.before true (estimateAt rate rewards C_star C_h control0 q w) := by
    change estimateRecord rate e.before true (sourceEstimateAt rate rewards C_star C_h control0 q w) = _
    rw [sourceEstimateAt_eq_coarsening, estimateRecord_coarsening]
  refine ⟨hen, hb, ha, hr.trans hrec.symm, ?_, ?_⟩
  · rw [stepFromEstimate_eq_estimateStep, sourceEstimateAt_eq_coarsening, estimateStep_coarsening]
    exact hs
  · rw [hrec]
    exact hv

theorem measurable_sourceEpisodeMass_history (s q : Fin p.T) (U : SlowSet p) :
    Measurable[sourceHistorySpace rate rewards C_star C_h control0 s q]
      (fun w => sourceEpisodeMass rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) U) :=
  (measurable_sourceEpisodeMass rate rewards C_star C_h s q U).comp
    (comap_measurable (sourceEstimateHistory rate rewards C_star C_h control0 s q))

theorem measurableSet_sourceHistoryRetained_history (s q : Fin p.T) :
    MeasurableSet[sourceHistorySpace rate rewards C_star C_h control0 s q]
      ((sourceEstimateHistory rate rewards C_star C_h control0 s q) ⁻¹'
        sourceHistoryRetained rate rewards C_star C_h s q) :=
  (measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage
    (comap_measurable (sourceEstimateHistory rate rewards C_star C_h control0 s q))

theorem measurableSet_episodeStartEvent_sourceHistory (s q : Fin p.T) :
    MeasurableSet[sourceHistorySpace rate rewards C_star C_h control0 s q]
      (episodeStartEvent rate rewards C_star C_h control0 s) := by
  rw [episodeStartEvent_eq_history_preimage]
  exact ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage measurable_fst).preimage
    (measurable_fst.comp (comap_measurable (sourceEstimateHistory rate rewards C_star C_h control0 s q)))

omit rewards C_star C_h control0 in
private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (fun L : List A => L[k]?) := by
  have htag : Measurable (fun L : List A =>
      ReferenceActiveHorizonMeasurability.listObservationAt L k) :=
    (measurable_pi_apply k).comp
      ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.snd
  have hdecode : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_fun_sum measurable_const
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hdecode.comp htag using 1
  funext L
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationAt]
  cases L[k]? <;> rfl

omit rewards C_star C_h control0 in
private theorem measurable_find_time (q : Fin p.T) :
    Measurable (fun H : List (LogicalCell p rate) => H.find? (fun e => e.time == q)) := by
  have ht : Measurable (fun H : List (LogicalCell p rate) => H.map LogicalCell.time) :=
    ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id _
      measurable_logicalCell_time
  have hn : Measurable (fun H : List (LogicalCell p rate) =>
      (H.map LogicalCell.time).findIdx (fun t => t == q)) :=
    (measurable_of_countable (fun L : List (Fin p.T) => L.findIdx (fun t => t == q))).comp ht
  have hg : Measurable (fun nH : ℕ × List (LogicalCell p rate) => nH.2[nH.1]?) :=
    measurable_from_prod_countable_right (fun n => measurable_list_getElem? n)
  convert hg.comp (hn.prodMk measurable_id) using 1
  funext H
  simp only [Function.comp_apply, List.find?_eq_getElem?_findIdx, List.findIdx_map, id_eq]
  rfl

omit rate rewards C_star C_h control0 in
private theorem measurable_list_take {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (fun L : List A => L.take n) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)
  apply measurable_comap_iff.mpr
  change Measurable (fun L : List A => ((L.take n).length,
    fun j => ReferenceActiveHorizonMeasurability.listObservationAt (L.take n) j))
  simp only [List.length_take]
  apply ((measurable_of_countable (fun k : ℕ => min n k)).comp hc.fst).prodMk
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < n
  · simpa only [Function.comp_def, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
      ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take, hj, ite_true] using
        (measurable_pi_apply j).comp hc.snd
  · have heq : (fun L : List A => ReferenceActiveHorizonMeasurability.listObservationAt (L.take n) j) =
        fun _ => (Sum.inl () : Unit ⊕ A) := by
      funext L
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take, hj, ite_false]
    rw [heq]
    exact measurable_const

omit rewards C_star C_h control0 in
private theorem chronological_filter_eq_take (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val)) (n : ℕ) :
    H.filter (fun e => e.time.val < n) = H.take (H.filter (fun e => e.time.val < n)).length := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    obtain ⟨heH, hH⟩ := List.pairwise_cons.mp hH
    by_cases he : e.time.val < n
    · simp only [List.filter_cons, decide_eq_true he, ite_true, List.length_cons, List.take_succ_cons]
      exact congrArg (List.cons e) (ih hH)
    · have hf : H.filter (fun e => e.time.val < n) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        have ht := heH c hc
        simpa only [decide_eq_true_eq] using (show ¬ c.time.val < n by omega)
      simp only [List.filter_cons, decide_eq_false he, Bool.false_eq_true, ite_false,
        hf, List.length_nil, List.take_zero]

omit rewards C_star C_h control0 in
private theorem measurable_chronological_filter {X : Type*} [MeasurableSpace X]
    (H : X → List (LogicalCell p rate)) (hH : Measurable H)
    (hchron : ∀ x, (H x).Pairwise (fun e f => e.time.val < f.time.val)) (n : ℕ) :
    Measurable (fun x => (H x).filter (fun e => e.time.val < n)) := by
  have ht : Measurable (fun x => (H x).map LogicalCell.time) :=
    ReferenceActiveHorizonMeasurability.measurable_list_map H hH _ measurable_logicalCell_time
  have hc : Measurable (fun x => (((H x).map LogicalCell.time).filter
      (fun t => t.val < n)).length) :=
    (measurable_of_countable (fun L : List (Fin p.T) => (L.filter (fun t : Fin p.T => t.val < n)).length)).comp ht
  have htake : Measurable (fun v : ℕ × List (LogicalCell p rate) => v.2.take v.1) :=
    measurable_from_prod_countable_right (fun k => measurable_list_take k)
  convert htake.comp (hc.prodMk hH) using 1
  funext x
  rw [chronological_filter_eq_take rate (H x) (hchron x) n]
  simp only [List.filter_map, List.length_map, Function.comp_apply]
  rfl

omit rewards C_star C_h control0 in
private theorem filter_time_filter (H : List (LogicalCell p rate)) (a b : ℕ) (hab : a ≤ b) :
    (H.filter (fun e => e.time.val < b)).filter (fun e => e.time.val < a) =
      H.filter (fun e => e.time.val < a) := by
  rw [List.filter_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h, h.trans_le hab⟩⟩

omit rewards C_star C_h control0 in
private theorem find_time_filter (H : List (LogicalCell p rate)) (q : Fin p.T)
    (n : ℕ) (hq : q.val < n) :
    (H.filter (fun e => e.time.val < n)).find? (fun e => e.time == q) =
      H.find? (fun e => e.time == q) := by
  rw [List.find?_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact ⟨And.right, fun h => ⟨h ▸ hq, h⟩⟩

/-- A joint test sees the current estimate and mark separately from E_q. -/
def terminalSourceJoint (s q : Fin p.T) (w : Omega) :
    History rate s q × (Estimate p × Option (LogicalCell p rate)) :=
  (sourceEstimateHistory rate rewards C_star C_h control0 s q w,
    (sourceEstimateAt rate rewards C_star C_h control0 q w,
      currentMark rate rewards C_star C_h control0 q w))

theorem measurable_terminalSourceJoint (s q : Fin p.T) :
    Measurable (terminalSourceJoint rate rewards C_star C_h control0 s q) :=
  (measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q).prodMk
    ((measurable_sourceEstimateAt rate rewards C_star C_h control0 q).prodMk
      (measurable_currentMark rate rewards C_star C_h control0 q))

section CalendarTransport

open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarLivePayoff
open ReferenceGeneratedCalendarLaterRenewalSlowInitialization

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0

/-- Read the SAME history schema from a finite actual calendar prefix. -/
def calendarSourceHistory (s q : Fin p.T) (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) : History rate s q :=
  ((sourcePrefix control0 s.val (current k hk w),
    (stored k hk w).2.filter (fun e => e.time.val < s.val)),
    fun v => sourceOptionalEstimate rate ((stored k hk w).2.find? (fun e => e.time == v.val)))

/-- Current output is observable by a test; it is not added to the history. -/
def calendarSourceJoint (s q : Fin p.T) (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) : History rate s q × (Estimate p × Option (LogicalCell p rate)) :=
  (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk w,
    (sourceOptionalEstimate rate ((stored k hk w).2.find? (fun e => e.time == q)),
      (stored k hk w).2.find? (fun e => e.time == q)))

theorem measurable_calendarSourceHistory (s q : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk) := by
  have hH := (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk).snd.snd
  exact (((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).comp
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk)).prodMk
    (measurable_chronological_filter rate _ hH (fun w =>
      (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w).1) s.val)).prodMk
    (measurable_pi_iff.mpr fun v => (measurable_sourceOptionalEstimate rate).comp
      ((measurable_find_time rate v.val).comp hH))

theorem measurable_calendarSourceJoint (s q : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q k hk) := by
  have hm := (measurable_find_time rate q).comp
    (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk).snd.snd
  exact (measurable_calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk).prodMk
    (((measurable_sourceOptionalEstimate rate).comp hm).prodMk hm)

/-- Seed, every history date, and current mark match on one literal ancestor. -/
theorem calendarSourceJoint_ancestor (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j ≤ k) (hq : q.val < t0.val + 1 + j) :
    calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q k hk w =
      calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega)
        (ancestor k j hj w) := by
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0
    b0 u0 t0 k hk w j hj).2.1
  change sourcePrefix control0 (t0.val + 1 + j) (current k hk w) =
    sourcePrefix control0 (t0.val + 1 + j) (current j (by omega) (ancestor k j hj w)) at hp
  have hs := congrArg (sourcePrefix control0 s.val) hp
  simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _
    (by omega : s.val ≤ t0.val + 1 + j)] at hs
  have hH := calendar_archiveBefore_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj
  have hstart := congrArg (fun H : List (LogicalCell p rate) =>
    H.filter (fun e => e.time.val < s.val)) hH
  rw [filter_time_filter rate _ _ _ (by omega)] at hstart
  have hfind (v : Fin p.T) (hv : v.val < t0.val + 1 + j) :
      (stored k hk w).2.find? (fun e => e.time == v) =
        (stored j (by omega) (ancestor k j hj w)).2.find? (fun e => e.time == v) := by
    have h := congrArg (fun H : List (LogicalCell p rate) => H.find? (fun e => e.time == v)) hH
    rw [find_time_filter rate _ v _ hv] at h
    exact h
  unfold calendarSourceJoint calendarSourceHistory
  rw [hs, hstart, hfind q hq]
  congr 2
  funext v
  rw [hfind v.val (v.property.2.trans hq)]

/-- Arbitrary joint nonnegative tests pull back through every real ancestor,
including the root, with its original unnormalized measure. -/
theorem calendarLaw_source_joint_test (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (j : ℕ) (hj : j ≤ k)
    (hq : q.val < t0.val + 1 + j)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q k hk w)
      ∂law k hk) =
    ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega) w)
      ∂law j (by omega) := by
  have hm := hF.comp (measurable_calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega))
  calc
    _ = ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega)
        (ancestor k j hj w)) ∂law k hk :=
      lintegral_congr (fun w => congrArg F
        (calendarSourceJoint_ancestor rate rewards C_star C_h control0 b0 u0 t0 s q hsq k hk w j hj hq))
    _ = _ := by
      have hx := measurable_calendarAncestor rate rewards C_star C_h b0 u0 t0 k j hj
      have he := lintegral_map (μ := law k hk) hm hx
      rw [calendarLaw_map_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk j hj] at he
      simpa only [Function.comp_def] using he.symm

/-- The joint identity retains the complete original lift on that SAME ancestor. -/
theorem calendarSourceJoint_ancestor_original (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (j : ℕ) (hj : j ≤ k) (hq : q.val < t0.val + 1 + j) :
    (original k w, calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q k hk w) =
      (original j (ancestor k j hj w),
        calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega)
          (ancestor k j hj w)) :=
  Prod.ext (calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k j hj w).symm
    (calendarSourceJoint_ancestor rate rewards C_star C_h control0 b0 u0 t0 s q hsq k hk w j hj hq)

/-- The same transport after normalizing only the original ID atom. -/
theorem calendarLaw_source_joint_test_fixedID (ids : CompletePublicTable.IDArray p)
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (j : ℕ) (hj : j ≤ k)
    (hq : q.val < t0.val + 1 + j)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q k hk w)
      ∂(CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (law k hk).restrict ((current k hk) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids)) =
    ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega) w)
      ∂(CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (law j (by omega)).restrict
          ((current j (by omega)) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  let E : Set (History rate s q × (Estimate p × Option (LogicalCell p rate))) :=
    {x | x.1.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  have hE : MeasurableSet E :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst.fst.fst
  have htest := calendarLaw_source_joint_test rate rewards C_star C_h control0 b0 u0 t0
    s q hsq k hk j hj hq (E.indicator F) (hF.indicator hE)
  have hAk := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk)
  have hAj := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 j (by omega))
  rw [lintegral_smul_measure, lintegral_smul_measure]
  apply congrArg (fun a : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {ids})⁻¹ * a)
  rw [← lintegral_indicator hAk, ← lintegral_indicator hAj]
  convert htest using 1 <;> apply lintegral_congr <;> intro w <;> rfl

/-- The strict history at the current step is already the PRE history. -/
theorem calendarSourceHistory_step (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (v : AssignmentParameterFibreKernel.AssignmentVector p) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q (k + 1) (by omega) (w, v) =
      calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w := by
  dsimp only
  have hp := (calendarObservation_step_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w v).2
  change sourcePrefix control0 (t0.val + 1 + k) (current (k + 1) (by omega) (w, v)) =
    sourcePrefix control0 (t0.val + 1 + k) (current k hk.le w) at hp
  have hsource := congrArg (sourcePrefix control0 s.val) hp
  simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ hs] at hsource
  have hH := calendar_archiveBefore_ancestor rate rewards C_star C_h control0 b0 u0 t0
    (k + 1) (by omega) (w, v) k (by omega)
  have ha : ancestor (k + 1) k (by omega) (w, v) = w :=
    (calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k k le_rfl (w, v)).trans
      (calendarAncestor_self rate rewards C_star C_h b0 u0 t0 k w)
  rw [ha] at hH
  have hstart := congrArg (fun H : List (LogicalCell p rate) => H.filter (fun e => e.time.val < s.val)) hH
  rw [filter_time_filter rate _ _ _ hs] at hstart
  unfold calendarSourceHistory
  rw [hsource, hstart]
  congr 1
  funext t
  have hfind := congrArg (fun H : List (LogicalCell p rate) => H.find? (fun e => e.time == t.val)) hH
  rw [find_time_filter rate _ t.val _ t.property.2] at hfind
  rw [hfind]

/-- Literal local one-step joint readout for the terminal refresh consumer. -/
def calendarStepSourceJoint (s : Fin p.T) (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (wv : Sample k × AssignmentParameterFibreKernel.AssignmentVector p) :
    History rate s ⟨t0.val + 1 + k, hk⟩ × (Estimate p × Option (LogicalCell p rate)) :=
  (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s ⟨t0.val + 1 + k, hk⟩ k hk.le wv.1,
    (sourceOptionalEstimate rate
      (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2),
      calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2))

theorem calendarSourceJoint_step (s : Fin p.T) (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (hs : s.val ≤ t0.val + 1 + k)
    (wv : Sample k × AssignmentParameterFibreKernel.AssignmentVector p) :
    calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s ⟨t0.val + 1 + k, hk⟩
      (k + 1) (by omega) wv =
      calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s k hk wv := by
  have hm := calendar_find_time_ancestor rate rewards C_star C_h control0 b0 u0 t0
    (k + 1) (by omega) wv k (by omega)
  dsimp only at hm
  have ha := calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) wv
  rw [ha] at hm
  unfold calendarSourceJoint calendarStepSourceJoint
  rw [calendarSourceHistory_step rate rewards C_star C_h control0 b0 u0 t0 s k hk hs, hm]

theorem measurable_calendarStepSourceJoint (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) :
    Measurable (calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s k hk) := by
  have hm := measurable_calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk
  exact ((measurable_calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0
    s ⟨t0.val + 1 + k, hk⟩ k hk.le).comp measurable_fst).prodMk
      (((measurable_sourceOptionalEstimate rate).comp hm).prodMk hm)

/-- The terminal generated payload is precisely the same history/mark observer. -/
theorem terminalSourceJoint_generated (s q : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b0 u0 t0)) :
    terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩ =
      calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q
        (p.T - (t0.val + 1)) (by omega) w := rfl

/-- Joint terminal tests reach any processed ancestor, under the raw or any
original fixed-ID component law. There is no component-mass normalization. -/
theorem generated_component_source_joint_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val) (j : ℕ)
    (hj : j ≤ p.T - (t0.val + 1)) (hq : q.val < t0.val + 1 + j)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q j (by omega) w)
      ∂ids.elim (law j (by omega)) (fun id =>
        (CompletePublicTable.idArrayMeasure p {id})⁻¹ • (law j (by omega)).restrict
          ((current j (by omega)) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection id)) := by
  cases ids with
  | none =>
    exact calendarLaw_source_joint_test rate rewards C_star C_h control0 b0 u0 t0
      s q hsq _ (by omega) j hj hq F hF
  | some id =>
    exact calendarLaw_source_joint_test_fixedID rate rewards C_star C_h control0 b0 u0 t0
      id s q hsq _ (by omega) j hj hq F hF

/-- ROOT transport, including histories which began strictly before ROOT. -/
theorem generated_component_source_joint_root_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val) (hqt : q.val ≤ t0.val)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s q 0 (by omega) w)
      ∂ids.elim (law 0 (by omega)) (fun id =>
        (CompletePublicTable.idArrayMeasure p {id})⁻¹ • (law 0 (by omega)).restrict
          ((current 0 (by omega)) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection id)) :=
  generated_component_source_joint_test rate rewards C_star C_h control0 b0 u0 t0
    ids s q hsq 0 (Nat.zero_le _) (by omega) F hF

/-- Later-ancestor transport ends at the actual step, with E read at PRE. -/
theorem generated_component_source_joint_step_test (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (j : ℕ) (hj : t0.val + 1 + j < p.T) (hs : s.val ≤ t0.val + 1 + j)
    (F : History rate s ⟨t0.val + 1 + j, hj⟩ × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s ⟨t0.val + 1 + j, hj⟩
        ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∫⁻ wv, F (calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s j hj wv)
      ∂ids.elim (law (j + 1) (by omega)) (fun id =>
        (CompletePublicTable.idArrayMeasure p {id})⁻¹ • (law (j + 1) (by omega)).restrict
          ((current (j + 1) (by omega)) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection id)) := by
  have h := generated_component_source_joint_test rate rewards C_star C_h control0 b0 u0 t0
    ids s ⟨t0.val + 1 + j, hj⟩ hs (j + 1) (by omega) (by dsimp only; omega) F hF
  exact h.trans (lintegral_congr (fun wv : Sample j × AssignmentParameterFibreKernel.AssignmentVector p =>
    congrArg F (calendarSourceJoint_step rate rewards C_star C_h control0 b0 u0 t0 s j hj hs wv)))

/-- ROOT's mark is its original native cell, with its whole UPDATE. -/
def calendarRootSourceJoint (s : Fin p.T) (w : Sample 0) :
    History rate s t0 × (Estimate p × Option (LogicalCell p rate)) :=
  (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w,
    (sourceCellEstimate rate (calendarRootCell rate rewards C_star C_h control0 b0 u0 t0 w),
      some (calendarRootCell rate rewards C_star C_h control0 b0 u0 t0 w)))

theorem calendarSourceJoint_root (s : Fin p.T) (w : Sample 0) :
    calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) w =
      calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s w := by
  let e := calendarRootCell rate rewards C_star C_h control0 b0 u0 t0 w
  have ht : e.time = t0 := by
    cases b0 <;> exact ReferenceFirstNextInstallationCellFactors.actualFirstCell_time
      rate rewards C_star C_h control0 t0 _ _
  have hstored := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).2.1
  have hpair := (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).1
  change (stored 0 (by omega) w).2.Pairwise (fun e f => e.time.val < f.time.val) at hpair
  rw [hstored] at hpair
  have hnone : (calendarNativePrelist rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) w).find?
      (fun f => f.time == t0) = none := by
    apply List.find?_eq_none.mpr
    intro f hf
    have hlt := (List.pairwise_append.mp hpair).2.2 f hf e (List.mem_singleton_self _)
    have hne : f.time ≠ t0 := by
      intro he
      change f.time.val < e.time.val at hlt
      rw [he, ht] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
    intro he
    exact hne (beq_iff_eq.mp he)
  have hmark : (stored 0 (by omega) w).2.find? (fun f => f.time == t0) = some e := by
    rw [hstored, List.find?_append, hnone]
    change [e].find? (fun f => f.time == t0) = some e
    simp only [List.find?_cons, ht, beq_self_eq_true]
  unfold calendarSourceJoint calendarRootSourceJoint
  rw [hmark]
  rfl

theorem measurable_calendarRootSourceJoint (s : Fin p.T) :
    Measurable (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s) := by
  have he : calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s =
      calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega) :=
    funext (fun w => (calendarSourceJoint_root rate rewards C_star C_h control0 b0 u0 t0 s w).symm)
  rw [he]
  exact measurable_calendarSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega)

/-- The actual ROOT native-cell pullback under both original component laws. -/
theorem generated_component_source_joint_native_root_test (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (hs : s.val ≤ t0.val)
    (F : History rate s t0 × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∫⁻ w, F (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s w)
      ∂ids.elim (law 0 (by omega)) (fun id =>
        (CompletePublicTable.idArrayMeasure p {id})⁻¹ • (law 0 (by omega)).restrict
          ((current 0 (by omega)) ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection id)) := by
  have h := generated_component_source_joint_root_test rate rewards C_star C_h control0 b0 u0 t0
    ids s t0 hs le_rfl F hF
  exact h.trans (lintegral_congr (fun w => congrArg F
    (calendarSourceJoint_root rate rewards C_star C_h control0 b0 u0 t0 s w)))

end CalendarTransport

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

/-- The exhaustive component weights are kept, also after original-ID localization. -/
theorem terminalLaw_source_joint_components (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) =
    ∑' i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p,
      ∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨i, w⟩)
        ∂ids.elim
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i)
          (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
            rate rewards C_star C_h control0 id i) := by
  have hm := hF.comp (measurable_terminalSourceJoint rate rewards C_star C_h control0 s q)
  cases ids with
  | none =>
    rw [Option.elim_none, ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw, lintegral_sum_measure]
    apply tsum_congr
    intro i
    simpa only [Option.elim_none, Function.comp_def] using lintegral_map hm (measurable_sigma_mk i)
  | some id =>
    rw [Option.elim_some, ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw, lintegral_sum_measure]
    apply tsum_congr
    intro i
    simpa only [Option.elim_some, Function.comp_def] using lintegral_map hm (measurable_sigma_mk i)

/-- Full raw/fixed-ID terminal joint pullback: each generated component uses
its ROOT or actual later ancestor. No-call and stopped components retain their
original full payloads and weights, without any future-call restriction. -/
theorem terminalLaw_source_joint_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) =
    ∑' i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p,
      match i with
      | .generated b u t =>
        ∫⁻ w, F (calendarSourceJoint rate rewards C_star C_h control0 b u t s q
          (q.val - t.val) (by have := q.isLt; omega) w)
          ∂ids.elim
            (ReferenceGeneratedRankCalendarFoundation.calendarLaw rate rewards C_star C_h control0 b u t
              (q.val - t.val) (by have := q.isLt; omega))
            (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
              (ReferenceGeneratedRankCalendarFoundation.calendarLaw rate rewards C_star C_h control0 b u t
                (q.val - t.val) (by have := q.isLt; omega)).restrict
                ((ReferenceGeneratedCalendarResidualBlock.calendarCurrentSource rate rewards C_star C_h control0 b u t
                  (q.val - t.val) (by have := q.isLt; omega)) ⁻¹'
                    ReferenceFixedIDSourceSection.fixedIDSourceSection id))
      | i =>
        ∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨i, w⟩)
          ∂ids.elim
            (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i)
            (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
              rate rewards C_star C_h control0 id i) := by
  rw [terminalLaw_source_joint_components rate rewards C_star C_h control0 ids s q F hF]
  apply tsum_congr
  intro i
  cases i with
  | noCall => rfl
  | stopped u t => rfl
  | generated b u t =>
    exact generated_component_source_joint_test rate rewards C_star C_h control0 b u t ids s q hsq
      (q.val - t.val) (by have := q.isLt; omega) (by omega) F hF

end Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport
