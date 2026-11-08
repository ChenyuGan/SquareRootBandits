/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarRetainedFastCore
import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore

/-!
# Later noncall FAST tests on the original calendar measure

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

The history is the accepted strict source history and past estimates. The
current native recorder and FAST draw are integrated jointly. No distribution
of the incoming slow set is assumed, and only numerical PRE is tested for
overflow. The original whole-vector extension is retained until its integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationGeneratedAlignment
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarLaterRenewalSlowInitialization
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarNoncallRoundLaw
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceOriginalCalendarEpisodeChronology
open ReferencePostInvocationSupportedDisintegration (Innovation innovationLaw)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix actualRecord)
open ReferenceCompletePhysicalHistory (completeSuffixRecords)
open RecordedQueueRun (scoreWeight)
open CanonicalFastSampling (FastArm)

namespace Bandits.Support.ReferenceGeneratedCalendarLaterNoncallFast

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton
  ReferenceRankInstallationRecorderFoundation.optionSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "cell" => calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0
local notation "hist" => calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0
local notation "fastTest" => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h

/-- Pointwise source witnesses on the finite one-round carrier. The same
strict seed supplies the operative selected anchor; this is not a terminal
almost-everywhere specialization. -/
private theorem retained_source_data (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hstart : (hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w ∈
      sourceHistoryRetained rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := hist s q k hk.le w
    ∃ (A S : RecordedQueueRun.RunState p.K) (r : Record rate)
      (c : RecordedQueueRun.RoundInput p.K) (v : ReferenceActivePhysicalStep.Selection r.input),
      prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 = some A ∧
      sourceEpisodeReplay rate rewards C_star C_h s q h = some S ∧
      prefixNumerical rate rewards C_star C_h q.castSucc (current k hk.le w) = some S ∧
      S.overflow = false ∧ A.overflow = false ∧
      actualRecord rate rewards C_star C_h q (current k hk.le w) = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧ c.enabled = true ∧
      r.output.preparation.coordinator.selection = some v ∧
      v.view.payload.anchor = scoreWeight Q A := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := current k hk.le w
  let h := hist s q k hk.le w
  obtain ⟨_hsq, hq, hclear⟩ := hret
  have hrep := ReferenceGeneratedCalendarEpisodeTransitionCore.calendarSourceHistory_replay
    rate rewards C_star C_h control0 b0 u0 t0 s q hs k hk.le le_rfl w hstart hq
  have hclearZ : (prefixNumerical rate rewards C_star C_h q.castSucc z).any
      (fun S => !S.overflow) = true := by rw [← hrep]; exact hclear
  obtain ⟨S, hS⟩ := calendarNoncall_numerical_present rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have hSz : prefixNumerical rate rewards C_star C_h q.castSucc z = some S :=
    (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).symm.trans hS
  have hSc : S.overflow = false := by
    simpa only [hSz, Option.any_some, Bool.not_eq_true'] using hclearZ
  have hstartZ : z ∈ sourceStartEvent rate rewards C_star C_h s :=
    (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s z).mpr hstart
  obtain ⟨rho0, ht0, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z hstartZ
  have hcover0 : EpisodeCovers (completeSuffixRecords rate z rewards C_star C_h)[rho0.val] q :=
    ⟨hb0, ht0 ▸ hs, ht0 ▸ hq⟩
  have hen := (nominalEnabled_iff_unique_episode rate rewards C_star C_h z q).mpr
    ⟨rho0, hcover0, fun other ho => complete_episode_interval_at_most_one
      rate rewards C_star C_h z q other rho0 ho hcover0⟩
  obtain ⟨rho, P, r, c, v, hr, hc, hcen, hcover, huniq, hb, _hPuniq,
    _hbefore, hv, ha, _hrates, _hgrid, _hclock⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z q hen
  have hrho : rho0 = rho := huniq rho0 hcover0
  have ht : (completeSuffixRecords rate z rewards C_star C_h)[rho.val].input.time = s := by
    simpa only [hrho] using ht0
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover
    rate rewards C_star C_h control0 z q rho P hcover hb hclearZ
  rw [ht] at hA
  exact ⟨A, S, r, c, v, hA, hrep.trans hSz, hSz, hSc, hAc, hr, hc, hcen,
    hv, ha.trans hanchor⟩

/-- The actual retained noncall is present and has the literal incoming U
and the replayed numerical PRE. Enabled bottom/zero updates remain present. -/
private theorem retained_noncall_cell (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hc : callFlag k (by omega) w = false)
    (hstart : (hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w ∈
      sourceHistoryRetained rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩) :
    ∃ e : LogicalCell p rate, cell k hk w = some e ∧
      e.slowSet = (stored k hk.le w).1 ∧
      sourceEpisodeReplay rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩
        (hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w) = some e.before ∧ e.before.overflow = false := by
  obtain ⟨A, S, r, c, v, _hA, hrep, hS, hSc, _hAc, hr, hinput, hen, _hv, _ha⟩ :=
    retained_source_data rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w hstart hret
  have hp := calendarObservation_noncall_presence rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
  change (cell k hk w).isSome =
    ((actualRecord rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      (current k hk.le w)).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any
        RecordedQueueRun.RoundInput.enabled at hp
  rw [hr, Option.bind_some, hinput, Option.any_some, hen] at hp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hp
  have hclear : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w).2 = true := by
    change ((observe k hk.le w).2.val.2.2.1).any (fun S => !S.overflow) = true
    rw [calendarObservation_numerical]
    change (prefixNumerical rate rewards C_star C_h (⟨t0.val + 1 + k, hk⟩ : Fin p.T).castSucc
      (current k hk.le w)).any (fun S => !S.overflow) = true
    rw [hS, Option.any_some, hSc]
    rfl
  let v0 : Vector := ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)
  obtain ⟨hU, _hprePath, _hpostPath⟩ := calendarObservation_noncall_clear_cell
    rate rewards C_star C_h control0 b0 u0 t0 k hk w v0 hc hclear e he
  obtain ⟨_record, _input, _hrecord, _hinput, _henabled, _htime, _hphysical,
      _hnumerical, hpre, _hstep, _harrivals, _hservice, _hstored, _hpost⟩ :=
    calendarNoncallCell_actualInput rate rewards C_star C_h control0 b0 u0 t0 k hk w v0 hc e he
  have heS : e.before = S := Option.some.inj
    (hpre.trans ((calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).trans hS))
  exact ⟨e, he, hU, by rw [heS]; exact hrep, by rw [heS]; exact hSc⟩

omit rate rewards C_star C_h control0 b0 u0 t0 in
/-- A present collection call and its operative selection use the same OLD
payload. This joins readouts of one record, without a sampler-law premise. -/
private theorem collection_selection_payload {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate)
    (args : (P : ReferenceActivePhysicalStep.Payload rate) × ReferenceActivePhysicalStep.Ledger rate ×
      CoordinatorPhaseClock.StartRoundResult p × (FastArm P.slowSet → ℝ))
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r = some args)
    (v : ReferenceActivePhysicalStep.Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v) : v.view.payload = args.1 := by
  rcases args with ⟨P, ledger, started, weights⟩
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hc
  split at hc
  next =>
    cases hdispatch : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hdispatch] at hc <;> contradiction
    | collection old oldLedger clock cutoff outcome =>
      cases outcome <;> simp only [hdispatch] at hc
      all_goals try contradiction
      case continuing core snapshot boundary checked =>
        cases Option.some.inj hc
        simp only [hdispatch, ReferenceActivePhysicalStep.DispatchCut.selection] at hv
        cases Option.some.inj hv
        rfl
    | live a b base outcome =>
      cases outcome <;> simp only [hdispatch] at hc
      all_goals try contradiction
      case cutoffChosen dispatched hs newLedger hi he hd hclock hp hn arm =>
        split at hc
        next =>
          cases Option.some.inj hc
          simp only [hdispatch, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt] at hv
          cases Option.some.inj hv
          rfl
        next => contradiction
    | invalidCollectionCutoff => simp only [hdispatch] at hc; contradiction
    | dagger => simp only [hdispatch] at hc; contradiction
  next => contradiction

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem fastPMF_congr (a w a' w' : Fin p.K → ℝ)
    (ha : ∀ j, 0 < a j) (hw : ∀ j, 0 < w j)
    (ha' : ∀ j, 0 < a' j) (hw' : ∀ j, 0 < w' j)
    (haa : a = a') (hww : w = w') (U : SlowSet p) :
    ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate a w ha hw U =
      ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate a' w' ha' hw' U := by
  subst a'
  subst w'
  rfl

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem qGammaPMF_congr (a w a' w' : Fin p.K → ℝ)
    (ha : ∀ j, 0 < a j) (hw : ∀ j, 0 < w j)
    (ha' : ∀ j, 0 < a' j) (hw' : ∀ j, 0 < w' j)
    (hlo : ∀ j, a j ≤ w j) (hhi : ∀ j, w j ≤ 2 * a j)
    (hlo' : ∀ j, a' j ≤ w' j) (hhi' : ∀ j, w' j ≤ 2 * a' j)
    (haa : a = a') (hww : w = w') (U : SlowSet p) :
    CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap a w ha hw hlo hhi U =
      CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        a' w' ha' hw' hlo' hhi' U := by
  subst a'
  subst w'
  rfl

/-- Evaluate the whole current innovation on an actual retained noncall.
LIVE/COLLECTION, presence, clear PRE, strict seed and operative anchor are
produced inside this proof. The incoming set has no stipulated law. -/
private theorem retained_noncall_fast_refill (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hc : callFlag k (by omega) w = false)
    (hstart : (hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w ∈
      sourceHistoryRetained rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k
    (∫⁻ x, (cell k hk (fill (w, x))).elim 0
      (fun e => Phi (hist s q k hk.le (fill (w, x)), (e.slowSet, e.fastArm)))
      ∂innovationLaw (p := p)) =
      fastTest s q Phi (hist s q k hk.le w) (stored k hk.le w).1 := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  obtain ⟨A, S, r, c, v, hA, hrep, _hS, hSc, _hAc, hr, hinput, hen, hv, ha⟩ :=
    retained_source_data rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w hstart hret
  obtain ⟨e, he, hU, hpre, heclear⟩ :=
    retained_noncall_cell rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w hc hstart hret
  have heS : e.before = S := Option.some.inj (hpre.symm.trans hrep)
  rw [ReferenceGeneratedCalendarRetainedFastCore.historyFastTest, hA, hrep]
  by_cases hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
  · let zz : ContinuingLiveSource rate rewards C_star C_h q := ⟨current k hk.le w, hl⟩
    have he0 := he
    unfold calendarNoncallCell noncallDateCell at he0
    rw [dite_eq_left hl] at he0
    have heq : continuingLogicalCell rate rewards C_star C_h q zz
        (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k w).1.2 = e := Option.some.inj he0
    have hbefore : continuingBefore rate rewards C_star C_h q zz = S :=
      (congrArg LogicalCell.before heq).trans heS
    have hclear : (continuingBefore rate rewards C_star C_h q zz).overflow = false := by
      rw [hbefore]; exact hSc
    have hrEq : r = continuingRecord rate rewards C_star C_h q zz :=
      Option.some.inj (hr.symm.trans (continuingSourceCell_spec rate rewards C_star C_h q zz).1)
    subst r
    have hvEq : v = (continuingSourceCell rate rewards C_star C_h q zz).selected :=
      Option.some.inj (hv.symm.trans (continuingSourceCell rate rewards C_star C_h q zz).selection_actual)
    have hanchor : (continuingSourceCell rate rewards C_star C_h q zz).selected.view.payload.anchor =
        scoreWeight Q A := by rw [← hvEq]; exact ha
    have hslow : (continuingSourceCell rate rewards C_star C_h q zz).selected.view.payload.slowSet =
        (stored k hk.le w).1 := by
      have hu := (congrArg LogicalCell.slowSet heq).trans hU
      simpa only [continuingLogicalCell, appendLogicalCell, hclear, Bool.false_eq_true, ite_false] using hu
    have hf := ReferenceGeneratedCalendarRetainedFastCore.calendar_live_fast_refill_test
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w hl hclear Phi
    dsimp only at hf
    have hpmf := fastPMF_congr rate _ _ _ _
      (continuingSourceCell rate rewards C_star C_h q zz).selected.view.payload.anchor_pos
      (RecordedSlowRefresh.scoreWeight_pos Q _) (RecordedSlowRefresh.scoreWeight_pos Q A)
      (RecordedSlowRefresh.scoreWeight_pos Q S) hanchor (congrArg (scoreWeight Q) hbefore)
      (continuingSourceCell rate rewards C_star C_h q zz).selected.view.payload.slowSet
    rw [hpmf, hslow] at hf
    change _ = ∑ j : FastArm (stored k hk.le w).1,
      Phi (hist s q k hk.le w, ((stored k hk.le w).1, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (scoreWeight Q A)
          (scoreWeight Q S) (RecordedSlowRefresh.scoreWeight_pos Q A)
          (RecordedSlowRefresh.scoreWeight_pos Q S) (stored k hk.le w).1 j
    refine Eq.trans ?_ hf
    apply lintegral_congr
    intro x
    cases cell k hk (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k (w, x)) <;> rfl
  · have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    let zz : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    have hrEq : r = collectionRecord rate rewards C_star C_h q zz :=
      Option.some.inj (hr.symm.trans (collectionRecord_spec rate rewards C_star C_h q zz).1)
    subst r
    have hcEq : c = collectionInput rate rewards C_star C_h q zz :=
      Option.some.inj (hinput.symm.trans (Option.some_get _).symm)
    have henabled : (collectionInput rate rewards C_star C_h q zz).enabled = true := hcEq ▸ hen
    have he0 := he
    unfold calendarNoncallCell noncallDateCell at he0
    rw [dite_eq_right hl, dite_eq_left hcol, laterCollectionCell?, henabled, ite_eq_left rfl] at he0
    have heq : laterCollectionCell rate rewards C_star C_h q zz (stored k hk.le w).1
        (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k w).1.2 = e := Option.some.inj he0
    have hbefore : collectionBefore rate rewards C_star C_h q zz = S :=
      (congrArg LogicalCell.before heq).trans heS
    have hclear : (collectionBefore rate rewards C_star C_h q zz).overflow = false := by
      rw [hbefore]; exact hSc
    have hpay := collection_selection_payload (collectionRecord rate rewards C_star C_h q zz)
      (collectionArguments rate rewards C_star C_h q zz)
      (collectionArguments_spec rate rewards C_star C_h q zz) v hv
    have hanchor : (collectionArguments rate rewards C_star C_h q zz).1.anchor = scoreWeight Q A :=
      (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.anchor) hpay).symm.trans ha
    have hf := ReferenceGeneratedCalendarRetainedFastCore.calendar_collection_fast_refill_test
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w hl hcol henabled hclear Phi
    dsimp only at hf
    obtain ⟨_hOldPayload, hlo, hhi, hfast⟩ := calendarCollection_fastLaw
      rate rewards C_star C_h control0 b0 u0 t0 k hk w hcol henabled hclear
    have hlo' (j : Fin p.K) : scoreWeight Q A j ≤ scoreWeight Q S j := by
      rw [← hbefore, ← hanchor]
      exact hlo j
    have hhi' (j : Fin p.K) : scoreWeight Q S j ≤ 2 * scoreWeight Q A j := by
      rw [← hbefore, ← hanchor]
      exact hhi j
    have hpmf : ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate
        (collectionArguments rate rewards C_star C_h q zz).1.anchor
        (scoreWeight Q (collectionBefore rate rewards C_star C_h q zz))
        (collectionArguments rate rewards C_star C_h q zz).1.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) (stored k hk.le w).1 =
        ReferenceGeneratedCalendarRetainedFastCore.numericalFastPMF rate A S (stored k hk.le w).1 := by
      rw [ReferenceGeneratedCalendarRetainedFastCore.numericalFastPMF_eq_qGamma rate A S hlo' hhi']
      calc
        _ = CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
            (collectionArguments rate rewards C_star C_h q zz).1.anchor
            (scoreWeight Q (collectionBefore rate rewards C_star C_h q zz))
            (collectionArguments rate rewards C_star C_h q zz).1.anchor_pos
            (RecordedSlowRefresh.scoreWeight_pos Q _) hlo hhi (stored k hk.le w).1 := by
          ext j
          rw [ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply,
            CanonicalFastSampling.qGammaPMF_apply, hfast]
        _ = _ := qGammaPMF_congr rate _ _ _ _
          (collectionArguments rate rewards C_star C_h q zz).1.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) (RecordedSlowRefresh.scoreWeight_pos Q A)
          (RecordedSlowRefresh.scoreWeight_pos Q S) hlo hhi hlo' hhi'
          hanchor (congrArg (scoreWeight Q) hbefore) (stored k hk.le w).1
    rw [hpmf] at hf
    change _ = ∑ j : FastArm (stored k hk.le w).1,
      Phi (hist s q k hk.le w, ((stored k hk.le w).1, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (scoreWeight Q A)
          (scoreWeight Q S) (RecordedSlowRefresh.scoreWeight_pos Q A)
          (RecordedSlowRefresh.scoreWeight_pos Q S) (stored k hk.le w).1 j
    refine Eq.trans ?_ hf
    apply lintegral_congr
    intro x
    cases cell k hk (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k (w, x)) <;> rfl

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem measurable_optional_test {X : Type*} [MeasurableSpace X]
    (f : X × LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun v : X × Option (LogicalCell p rate) =>
      v.2.elim 0 (fun e => f (v.1, e))) := by
  have h := ((hf.comp measurable_swap).sumElim
    (measurable_const : Measurable (fun _ : PUnit × X => (0 : ℝ≥0∞)))).comp
      (MeasurableEquiv.sumProdDistrib (LogicalCell p rate) PUnit X).measurable_toFun
  have hp := h.comp (((comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))).comp
    measurable_snd).prodMk measurable_fst)
  convert hp using 1
  funext v
  rcases v with ⟨x, e⟩
  cases e <;> rfl

/-- Transport arbitrary accepted-history/optional-cell tests through the
actual whole-vector extension and the whole current innovation. -/
private theorem noncall_history_innovation_test (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (F : History rate s ⟨t0.val + 1 + k, hk⟩ × Option (LogicalCell p rate) → ℝ≥0∞)
    (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k
    (∫⁻ wv : Sample (k + 1), if callFlag k (by omega) wv.1 = false then
      F (hist s q k hk.le wv.1,
        calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2)
      else 0 ∂law (k + 1) (by omega)) =
    ∫⁻ w, if callFlag k (by omega) w = false then
      ∫⁻ x, F (hist s q k hk.le w, cell k hk (fill (w, x))) ∂innovationLaw (p := p)
      else 0 ∂(law k hk.le).map
        (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then
      F (hist s q k hk.le wv.1,
        calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2) else 0
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have ht : Measurable test := (hF.comp
    (((measurable_calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le).comp
      measurable_fst).prodMk
      (measurable_calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk))).ite
        (hgate.preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v)
    ∂calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  by_cases hc : callFlag k (by omega) w = false
  · rw [ite_eq_left hc]
    apply lintegral_congr
    intro x
    have hc' : callFlag k (by omega) (fill (w, x)) = false :=
      (calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w x).trans hc
    have hn : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (current k hk.le (fill (w, x))) = none := by
      apply Option.not_isSome_iff_eq_none.mp
      change ¬ callFlag k (by omega) (fill (w, x)) = true
      rw [hc']
      exact Bool.false_ne_true
    rw [calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk _ hn,
      lintegral_dirac]
    dsimp only [test]
    rw [ite_eq_left hc', calendarStepCell, dite_eq_right (by rw [hc']; exact Bool.false_ne_true)]
    rw [ReferenceGeneratedCalendarRetainedFastCore.calendarSourceHistory_fillInnovation
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w x]
    rfl
  · rw [ite_eq_right hc]
    have hz (x : Innovation p) (v : Vector) : test (fill (w, x), v) = 0 := by
      dsimp only [test]
      rw [calendarCallFlag_fillInnovation, ite_eq_right hc]
    simp_rw [hz, lintegral_zero]

include control0 in
private theorem measurable_retained_optional_test (s q : Fin p.T)
    (F : History rate s q × LogicalCell p rate → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun he : History rate s q × Option (LogicalCell p rate) =>
      if he.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        he.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        he.2.elim 0 (fun e => F (he.1, e)) else 0) :=
  (measurable_optional_test rate F hF).ite
    (((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage
      measurable_fst.fst.fst).inter
      ((measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage measurable_fst))
    measurable_const

/-- Pointwise innovation equality on the retained incoming sample. -/
private theorem retained_noncall_refill_eq (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hc : callFlag k (by omega) w = false)
    (hstart : (hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : hist s ⟨t0.val + 1 + k, hk⟩ k hk.le w ∈
      sourceHistoryRetained rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := hist s q k hk.le
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k
    (∫⁻ x, (cell k hk (fill (w, x))).elim 0
      (fun e => Phi (h w, (e.slowSet, e.fastArm))) ∂innovationLaw (p := p)) =
    ∫⁻ x, (cell k hk (fill (w, x))).elim 0
      (fun e => fastTest s q Phi (h w) e.slowSet) ∂innovationLaw (p := p) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let h := hist s q k hk.le
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k
  have hhistory (x : Innovation p) : h (fill (w, x)) = h w :=
    ReferenceGeneratedCalendarRetainedFastCore.calendarSourceHistory_fillInnovation
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w x
  have hi := retained_noncall_fast_refill rate rewards C_star C_h control0 b0 u0 t0
    s k hk hs w hc hstart hret Phi
  have hleft : (∫⁻ x, (cell k hk (fill (w, x))).elim 0
      (fun e => Phi (h w, (e.slowSet, e.fastArm))) ∂innovationLaw (p := p)) =
      fastTest s q Phi (h w) (stored k hk.le w).1 := by
    refine Eq.trans ?_ hi
    apply lintegral_congr
    intro x
    change ((cell k hk (fill (w, x))).elim 0
      (fun e => Phi (h w, (e.slowSet, e.fastArm)))) =
        (cell k hk (fill (w, x))).elim 0
          (fun e => Phi (h (fill (w, x)), (e.slowSet, e.fastArm)))
    rw [hhistory]
  have hright : (∫⁻ x, (cell k hk (fill (w, x))).elim 0
      (fun e => fastTest s q Phi (h w) e.slowSet) ∂innovationLaw (p := p)) =
      fastTest s q Phi (h w) (stored k hk.le w).1 := by
    have heq (x : Innovation p) : (cell k hk (fill (w, x))).elim 0
        (fun e => fastTest s q Phi (h w) e.slowSet) =
        fastTest s q Phi (h w) (stored k hk.le w).1 := by
      have hc' : callFlag k (by omega) (fill (w, x)) = false :=
        (calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w x).trans hc
      have hstart' : (h (fill (w, x))).1.1 ∈ sourceStartEvent rate rewards C_star C_h s := by
        rw [hhistory]; exact hstart
      have hret' : h (fill (w, x)) ∈ sourceHistoryRetained rate rewards C_star C_h s q := by
        rw [hhistory]; exact hret
      obtain ⟨e, he, hseed, _hpre, _hclear⟩ := retained_noncall_cell
        rate rewards C_star C_h control0 b0 u0 t0 s k hk hs (fill (w, x)) hc' hstart' hret'
      have hu := congrArg (fun v : BootstrapPrivateRoundStreams.SourceInput p ×
          (SlowSet p × List (LogicalCell p rate)) => v.2.1)
        (calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k hk.le le_rfl (w, x))
      rw [he, Option.elim_some, hseed]
      exact congrArg (fastTest s q Phi (h w)) hu
    simp_rw [heq]
    rw [lintegral_const, measure_univ, mul_one]
  exact hleft.trans hright.symm

/-- Raw unnormalized later noncall equality. The source opportunity and
retention gates produce every native-law input internally. -/
theorem calendarLaw_later_noncall_fast_test_raw (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := hist s q k hk.le
    let c := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk
    (∫⁻ wv : Sample (k + 1),
      if callFlag k (by omega) wv.1 = false ∧
        (h wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        (c wv.1 wv.2).elim 0 (fun e => Phi (h wv.1, (e.slowSet, e.fastArm))) else 0
        ∂law (k + 1) (by omega)) =
    ∫⁻ wv : Sample (k + 1),
      if callFlag k (by omega) wv.1 = false ∧
        (h wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        (c wv.1 wv.2).elim 0 (fun e => fastTest s q Phi (h wv.1) e.slowSet) else 0
        ∂law (k + 1) (by omega) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let h := hist s q k hk.le
  let c := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
    (by change t0.val < t0.val + 1 + k; omega) k
  let G : Set (History rate s q) :=
    {h | h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q}
  let actual : History rate s q × Option (LogicalCell p rate) → ℝ≥0∞ := fun he =>
    if he.1 ∈ G then he.2.elim 0 (fun e => Phi (he.1, (e.slowSet, e.fastArm))) else 0
  let mean : History rate s q × Option (LogicalCell p rate) → ℝ≥0∞ := fun he =>
    if he.1 ∈ G then he.2.elim 0 (fun e => fastTest s q Phi he.1 e.slowSet) else 0
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.mono le_rfl le_top
  have hactual : Measurable actual := measurable_retained_optional_test rate rewards C_star C_h control0
    s q (fun he => Phi (he.1, (he.2.slowSet, he.2.fastArm)))
      (hPhi.comp (measurable_fst.prodMk ((hU.comp measurable_snd).prodMk
        (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_fastArm.comp measurable_snd))))
  have hmean : Measurable mean := measurable_retained_optional_test rate rewards C_star C_h control0
    s q (fun he => fastTest s q Phi he.1 he.2.slowSet)
      ((ReferenceGeneratedCalendarRetainedFastCore.measurable_historyFastTest rate rewards C_star C_h
        s q Phi hPhi).comp (f := fun he : History rate s q × LogicalCell p rate =>
          (he.1, he.2.slowSet)) (measurable_fst.prodMk (hU.comp measurable_snd)))
  have ha := noncall_history_innovation_test rate rewards C_star C_h control0 b0 u0 t0
    s k hk hs actual hactual
  have hm := noncall_history_innovation_test rate rewards C_star C_h control0 b0 u0 t0
    s k hk hs mean hmean
  have hinter :
      (∫⁻ w, if callFlag k (by omega) w = false then
        ∫⁻ x, actual (h w, cell k hk (fill (w, x))) ∂innovationLaw (p := p) else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k)) =
      ∫⁻ w, if callFlag k (by omega) w = false then
        ∫⁻ x, mean (h w, cell k hk (fill (w, x))) ∂innovationLaw (p := p) else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k) := by
    apply lintegral_congr
    intro w
    by_cases hc : callFlag k (by omega) w = false
    · rw [ite_eq_left hc, ite_eq_left hc]
      by_cases hg : h w ∈ G
      · have hlocal := retained_noncall_refill_eq rate rewards C_star C_h control0 b0 u0 t0
          s k hk hs w hc hg.1 hg.2 Phi
        simpa only [actual, mean, ite_eq_left hg] using hlocal
      · have hzA (x : Innovation p) : actual (h w, cell k hk (fill (w, x))) = 0 :=
          ite_eq_right hg
        have hzM (x : Innovation p) : mean (h w, cell k hk (fill (w, x))) = 0 :=
          ite_eq_right hg
        simp only [hzA, hzM, lintegral_zero]
    · simp only [ite_eq_right hc]
  calc
    _ = ∫⁻ wv : Sample (k + 1), if callFlag k (by omega) wv.1 = false then
        actual (h wv.1, c wv.1 wv.2) else 0 ∂law (k + 1) (by omega) := by
      apply lintegral_congr
      intro wv
      change Sample k × Vector at wv
      change (if callFlag k (by omega) wv.1 = false ∧ h wv.1 ∈ G then
        (c wv.1 wv.2).elim 0 (fun e => Phi (h wv.1, (e.slowSet, e.fastArm))) else 0) = _
      exact ite_and (callFlag k (by omega) wv.1 = false) (h wv.1 ∈ G) _ _
    _ = _ := ha
    _ = _ := hinter
    _ = ∫⁻ wv : Sample (k + 1), if callFlag k (by omega) wv.1 = false then
        mean (h wv.1, c wv.1 wv.2) else 0 ∂law (k + 1) (by omega) := hm.symm
    _ = _ := by
      apply lintegral_congr
      intro wv
      change Sample k × Vector at wv
      change (if callFlag k (by omega) wv.1 = false then
        if h wv.1 ∈ G then (c wv.1 wv.2).elim 0
          (fun e => fastTest s q Phi (h wv.1) e.slowSet) else 0 else 0) = _
      exact (ite_and (callFlag k (by omega) wv.1 = false) (h wv.1 ∈ G) _ _).symm

omit control0 b0 u0 t0 in
private theorem historyFastTest_indicator (ids : CompletePublicTable.IDArray p) (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) :
    fastTest s q
      ({x : History rate s q × (SlowSet p × Fin p.K) |
        x.1.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}.indicator Phi) h U =
      if h.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids then fastTest s q Phi h U else 0 := by
  by_cases hi : h.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  · simp only [ReferenceGeneratedCalendarRetainedFastCore.historyFastTest,
      Set.indicator_apply, Set.mem_ofPred_eq, hi, ite_true]
  · cases hA : prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 <;>
      cases hS : sourceEpisodeReplay rate rewards C_star C_h s q h <;>
      simp [ReferenceGeneratedCalendarRetainedFastCore.historyFastTest, hA, hS, hi]

/-- Later NONCALL FAST evaluation under the raw calendar law and EVERY
original fixed-ID law. Only the original ID-atom inverse rescales the measure;
the generated component, retained event and current row remain unnormalized.
The gates concern incoming PRE, so the first detecting overflow update stays.
-/
theorem calendarLaw_later_noncall_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (b0 : Bool) (u0 t0 s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le
    let c := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk
    let gamma := ids.elim
      (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
      (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
        (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)).restrict
          ((calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) ⁻¹'
            ReferenceFixedIDSourceSection.fixedIDSourceSection id))
    (∫⁻ wv : CalendarSample rate rewards C_star C_h b0 u0 t0 (k + 1),
      if calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = false ∧
        (h wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        (c wv.1 wv.2).elim 0 (fun e => Phi (h wv.1, (e.slowSet, e.fastArm))) else 0 ∂gamma) =
    ∫⁻ wv : CalendarSample rate rewards C_star C_h b0 u0 t0 (k + 1),
      if calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = false ∧
        (h wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        (c wv.1 wv.2).elim 0 (fun e => fastTest s q Phi (h wv.1) e.slowSet) else 0 ∂gamma := by
  dsimp only
  cases ids with
  | none =>
    exact calendarLaw_later_noncall_fast_test_raw
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs Phi hPhi
  | some ids =>
    dsimp only [Option.elim_some]
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le
    let c := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk
    let E : Set (History rate s q × (SlowSet p × Fin p.K)) :=
      {x | x.1.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
    have hE : MeasurableSet E :=
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst.fst.fst
    let mu : Measure (CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :=
      calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)
    let sectionID : Set (CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :=
      {wv | calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv ∈
        ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
    let gate : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → Prop := fun wv =>
      calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = false ∧
        (h wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q
    let actual (Psi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) :
        CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → ℝ≥0∞ := fun wv =>
      if gate wv then (c wv.1 wv.2).elim 0 (fun e => Psi (h wv.1, (e.slowSet, e.fastArm))) else 0
    let mean (Psi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) :
        CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → ℝ≥0∞ := fun wv =>
      if gate wv then (c wv.1 wv.2).elim 0 (fun e => fastTest s q Psi (h wv.1) e.slowSet) else 0
    change (∫⁻ wv, actual Phi wv ∂(CompletePublicTable.idArrayMeasure p {ids})⁻¹ • mu.restrict sectionID) =
      ∫⁻ wv, mean Phi wv ∂(CompletePublicTable.idArrayMeasure p {ids})⁻¹ • mu.restrict sectionID
    have hraw : (∫⁻ wv, actual (E.indicator Phi) wv ∂mu) =
        ∫⁻ wv, mean (E.indicator Phi) wv ∂mu :=
      calendarLaw_later_noncall_fast_test_raw rate rewards C_star C_h control0
        b0 u0 t0 s k hk hs (E.indicator Phi) (hPhi.indicator hE)
    have hID (wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :
        wv ∈ sectionID ↔ (h wv.1).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
      have heq := congrArg (fun H : History rate s q => H.1.1.1.1)
        (calendarSourceHistory_step rate rewards C_star C_h control0 b0 u0 t0 s k hk hs wv.1 wv.2)
      change _ = ids ↔ _ = ids
      change (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv).1.1 =
        (h wv.1).1.1.1.1 at heq
      rw [heq]
    have hsection : MeasurableSet sectionID :=
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
        (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
    have hactual : sectionID.indicator (actual Phi) = actual (E.indicator Phi) := by
      funext wv
      by_cases hid : (h wv.1).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids
      · have hwid := (hID wv).mpr hid
        rw [Set.indicator_of_mem hwid]
        by_cases hg : gate wv
        · simp only [actual, ite_eq_left hg]
          cases c wv.1 wv.2 <;> simp [E, hid]
        · simp only [actual, ite_eq_right hg]
      · have hwid := mt (hID wv).mp hid
        rw [Set.indicator_of_notMem hwid]
        by_cases hg : gate wv
        · simp only [actual, ite_eq_left hg]
          cases c wv.1 wv.2 <;> simp [E, hid]
        · simp only [actual, ite_eq_right hg]
    have hmean : mean (E.indicator Phi) = sectionID.indicator (mean Phi) := by
      funext wv
      by_cases hid : (h wv.1).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids
      · have hwid := (hID wv).mpr hid
        rw [Set.indicator_of_mem hwid]
        by_cases hg : gate wv
        · simp only [mean, ite_eq_left hg]
          cases c wv.1 wv.2 <;>
            simp only [Option.elim_none, Option.elim_some, E, historyFastTest_indicator, ite_eq_left hid]
        · simp only [mean, ite_eq_right hg]
      · have hwid := mt (hID wv).mp hid
        rw [Set.indicator_of_notMem hwid]
        by_cases hg : gate wv
        · simp only [mean, ite_eq_left hg]
          cases c wv.1 wv.2 <;>
            simp only [Option.elim_none, Option.elim_some, E, historyFastTest_indicator, ite_eq_right hid]
        · simp only [mean, ite_eq_right hg]
    rw [lintegral_smul_measure, lintegral_smul_measure]
    apply congrArg (fun a : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {ids})⁻¹ * a)
    rw [← lintegral_indicator hsection, ← lintegral_indicator hsection, hactual, ← hmean]
    exact hraw

end Bandits.Support.ReferenceGeneratedCalendarLaterNoncallFast
