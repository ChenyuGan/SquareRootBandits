/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverNoGateStopMask

/-!
# Adaptation of the actual stopped first handover

The observation and support charge in this module are read from the original
physical source and the literal first-handover calendar.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveStoppedHandoverAdaptation

variable {p : ConstructorDimensions.Parameters}
local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p

/-- The source's literal binary handover observation, including the actual
selection and the incoming stage of the selected follower. -/
def X_H (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : ℕ) (z : Source) : Bool :=
  if hk : k < p.T then
    decide (i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h k z ∧
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            ⟨k, hk⟩ z = some r ∧
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r = some selected ∧
          ((ReferenceFirstLiveHandoverBoundaryFactorization.Before rate r i ∧
              ReferenceFirstLiveHandoverBoundaryFactorization.V_before
                rate rewards C_star C_h i ⟨k, hk⟩ z) ∨
            (ReferenceFirstLiveHandoverBoundaryFactorization.After rate r selected i ∧
              ReferenceFirstLiveHandoverBoundaryFactorization.V_after
                rate rewards C_star C_h i ⟨k, hk⟩ z)))
  else false

/-- The deterministic number of positive integer-grid arms in the original
reward row; the terminal branch is zero. -/
def g_H (_rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (_C_star _C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (_z : Source) : ℝ :=
  if hk : k < p.T then
    ((Finset.univ.filter fun a : Fin p.K => 0 < (rewards ⟨k, hk⟩ a).val).card : ℝ)
  else 0

/-- The stopped first-handover support charge, with no analytical cap. -/
def G_H (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source) : ℝ :=
  ∑ v ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
    rate rewards C_star C_h z,
      g_H rate rewards C_star C_h control0 (v - 1) z

private theorem crossing_of_window_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source)
    (hwindow : 0 < (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hl] at hwindow
      simp at hwindow
  | some active =>
      apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp
      simp [hl]

private theorem actual_window_state_facts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source)
    (j : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    ReferenceFirstLiveConfirmationHistory.FirstLiveState
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z)[j.val].input.state) ∧
      ∀ i, ∃ state : ReferencePrelaunchFollower.State p rate.eta,
          ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
            (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z)[j.val].input.state.followers i = .ordinary state memory ∧
            (state.status = ActiveRoundActions.FollowerStatus.unoccupied → state.lastDown = none) := by
  classical
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z
    (by have hj := j.isLt; omega)
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hcross
  let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
  let count := p.T - s
  have hs : s ≤ p.T := by
    simpa only [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hlaunch' := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hcross
  have hstate : ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross = initial := by
    apply Option.some.inj
    exact hlaunch'.symm.trans hlaunch
  let hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  let hactive := hcanonical.2.1
  let hfirst := hcanonical.1
  have hstartEq : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed := by
    dsimp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hactive' : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    rw [hstartEq]
    simpa only [initial] using hactive
  have hfirst' : initial.coordinator = .first := by
    simpa only [initial] using hfirst
  have hdecoder := ReferenceFirstLiveDownCompletionReadout.actual_corrected_decoder_seed
    rate z rewards C_star C_h hcross
  have hseedConfig : ∀ i, initial.followers i = .ordinary (seed.followers i) (seed.memory i) := by
    intro i
    simpa only [initial, seed, hstate] using seed.configuration i
  have hseedLastDown : ∀ i, (seed.followers i).lastDown = none := by
    intro i
    obtain ⟨st, mem, hst, hnone, _hunocc, _hwell, _hchron, _hstamp⟩ := hdecoder i
    have heq : st = seed.followers i := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hst.symm.trans (hseedConfig i))).1
    rw [← heq]
    exact hnone
  have hseedUnoccupied : ∀ i, (seed.followers i).status = .unoccupied := by
    intro i
    obtain ⟨st, mem, hst, _hnone, hunocc, _hwell, _hchron, _hstamp⟩ := hdecoder i
    have heq : st = seed.followers i := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hst.symm.trans (hseedConfig i))).1
    rw [← heq]
    exact hunocc
  let E := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hfollower := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hactive' hfirst' seed.followers seed.memory hseedConfig seed.S_zero seed.delta_zero
    seed.backlog_zero hseedLastDown hseedUnoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hlaunchAgain := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hcomplete : E.records = ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
      rate rewards C_star C_h z := by
    change E.records = ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunchAgain).symm
  have hwindow : W = ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords rate rewards C_star C_h z)
    rw [hcomplete]
  have hcount : E.records.length = count := by
    exact ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
  have hWle : W.length ≤ count := by
    calc
      W.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = count := hcount
  have hjW : j.val < W.length := by
    calc
      j.val < (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).length := j.isLt
      _ = W.length := by rw [hwindow]
  have hsafe := hfollower.1 j.val (Nat.le_of_lt hjW)
  obtain ⟨hprefix, hstates⟩ := hsafe
  have hjCount : j.val < count := by
    exact lt_of_lt_of_le hjW hWle
  have hspanJ : s + (j.val + 1) ≤ p.T := by omega
  let runRecord := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val hspanJ hactive
  have hrunRecord : E.records[j.val]'(by rw [hcount]; exact hjCount) = runRecord := by
    have h := ReferenceLocalReleaseGateChronology.run_record_at initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive count hspan
        ⟨j.val, hjCount⟩
    simpa only [E, runRecord] using h
  have hpre : W <+: E.records := List.takeWhile_prefix _
  have hrecordEqW : W[j.val] = runRecord := by
    exact (hpre.getElem hjW).trans hrunRecord
  have hrecordEq :
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[j.val] =
        runRecord := by
    simpa only [hwindow] using hrecordEqW
  have hinputState :
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[j.val].input.state =
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val
          hprefix hactive').finalState := by
    rw [hrecordEq]
    rfl
  have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hactive' hfirst' hcanonical.2.2 ⟨j.val, hjW⟩
  have hwindow' : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive').records =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z := by
    simpa only [W] using hwindow
  constructor
  · simpa only [hwindow'] using hcarried
  · intro i
    obtain ⟨state', memory', hfinal, _hdomain, _hbound, _hbuffer, _hstamps, hzero, _hnonzero⟩ := hstates i
    refine ⟨state', memory', ?_, ?_⟩
    · rw [hinputState]
      exact hfinal
    · intro hunoccupied
      exact (hzero hunoccupied).1

/-- Each actual supported first-live choice lies in exactly one incoming
handover stage for every still-pending follower. The dichotomy follows from
the computed first selection, carried ownership, and physical follower
chronology. -/
theorem actual_supported_stage_exhaustive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source) (d : ℕ)
    (hd : d ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
      rate rewards C_star C_h z)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h (d - 1) z) :
    ∃ j : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).length,
      ∃ selected : ReferenceActivePhysicalStep.Selection
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).get j).input,
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z).get j) = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧
        (ReferenceFirstLiveHandoverBoundaryFactorization.Before rate
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z).get j) i ∨
          ReferenceFirstLiveHandoverBoundaryFactorization.After rate
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z).get j) selected i) := by
  classical
  obtain ⟨j, hdate, hrecord, selected, hselected, _hpayload, hmissing, hphase,
      _next, _owned, _base, _hnext, _hnextPayload, _hupdate⟩ :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_provenance
      rate rewards C_star C_h z d hd
  let r := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z).get j
  have hdateSupport : r.input.time.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z := by
    simpa only [r] using hdate ▸ hd
  have htime : d - 1 = r.input.time.val := by
    dsimp [r] at hdate ⊢
    omega
  have hmissingEq : ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h r.input.time.val z =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r := by
    simpa only [r, List.get_eq_getElem] using
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_eq_window_missing
        rate rewards C_star C_h z j hdateSupport)
  have hi' : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h r.input.time.val z := by
    simpa only [htime] using hi
  have hiMissing : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r := by
    rw [← hmissingEq]
    exact hi'
  have hiPending : i ∈ selected.view.pendingAtChoice := by
    rw [hmissing] at hiMissing
    exact hiMissing
  have hselected' : ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r =
      some selected := by simpa only [r] using hselected
  have hstateFacts := actual_window_state_facts rate rewards C_star C_h z j
  have hstateFirstLive : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state := by
    simpa only [r, List.get_eq_getElem] using hstateFacts.1
  obtain ⟨state, memory, hconfig, hunoccupied⟩ := hstateFacts.2 i
  have hconfig' : r.input.state.followers i = .ordinary state memory := by
    simpa only [r, List.get_eq_getElem] using hconfig
  have hstage :
      ReferenceFirstLiveHandoverBoundaryFactorization.Before rate r i ∨
        ReferenceFirstLiveHandoverBoundaryFactorization.After rate r selected i := by
    cases hc : r.input.state.coordinator with
    | first =>
        have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers r.input.state := by
          simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hstateFirstLive
        exact Or.inl ⟨state, memory, hconfig', (hinitial i state memory hconfig').2⟩
    | live incoming owned base =>
        have hlive : ReferenceActiveDataOwnership.carriedOccupiedFields incoming.payload
            r.input.state ∧
            ∀ i s memory, r.input.state.followers i = .ordinary s memory →
              incoming.pendingAtChoice.Nonempty → s.status ≠ ActiveRoundActions.FollowerStatus.released := by
          simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hstateFirstLive
        have hphase' : selected.view.payload = incoming.payload ∧
            selected.view.pendingAtChoice = incoming.pendingAtChoice := by
          rw [hc] at hphase
          exact hphase
        have hincoming : i ∈ incoming.pendingAtChoice := by
          rw [← hphase'.2]
          exact hiPending
        by_cases hUnoccupied : state.status = ActiveRoundActions.FollowerStatus.unoccupied
        · exact Or.inl ⟨state, memory, hconfig', hunoccupied hUnoccupied⟩
        · have hlast : state.lastDown = some (selected.view.payload.downRecord i) := by
            have hfield := hlive.1 i
            rw [hconfig'] at hfield
            have hfield := hfield hUnoccupied
            rw [hphase'.1]
            exact hfield
          exact Or.inr ⟨state, memory, hconfig', hlast⟩
    | collection payload ledger proposal =>
        have hfalse : False := by
          simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hstateFirstLive
        exact hfalse.elim
    | dagger =>
        have hfalse : False := by
          rw [hc] at hphase
          exact hphase
        exact hfalse.elim
  exact ⟨j, selected, hselected', hiPending, hstage⟩

/-- The two incoming stages are disjoint because one state cannot have both
no accepted DOWN word and the selected accepted DOWN word. -/
theorem actual_supported_stage_disjoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (i : Fin (p.m - 1)) :
    ¬(ReferenceFirstLiveHandoverBoundaryFactorization.Before rate r i ∧
      ReferenceFirstLiveHandoverBoundaryFactorization.After rate r selected i) := by
  rintro ⟨⟨before, beforeMemory, hbefore, hnone⟩,
    ⟨after, afterMemory, hafter, hsome⟩⟩
  have hstates := hbefore.symm.trans hafter
  have hstateEq := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hstates).1
  subst after
  rw [hnone] at hsome
  cases hsome

/-- On an actual source round, `X_H` is precisely its literal pending/stage
formula. -/
theorem X_H_eq_decide (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : Fin p.T) (z : Source) :
    X_H rate rewards C_star C_h control0 i k.val z =
      decide (i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h k.val z ∧
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h k z = some r ∧
            ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r = some selected ∧
            ((ReferenceFirstLiveHandoverBoundaryFactorization.Before rate r i ∧
                ReferenceFirstLiveHandoverBoundaryFactorization.V_before
                  rate rewards C_star C_h i k z) ∨
              (ReferenceFirstLiveHandoverBoundaryFactorization.After rate r selected i ∧
                ReferenceFirstLiveHandoverBoundaryFactorization.V_after
                  rate rewards C_star C_h i k z))) := by
  simp [X_H]

/-- The handover observation is false away from the actual pending set. -/
theorem X_H_false_of_not_pending (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : ℕ) (z : Source)
    (h : i ∉ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h k z) :
    X_H rate rewards C_star C_h control0 i k z = false := by
  by_cases hk : k < p.T
  · simp [X_H, hk, h]
  · simp [X_H, hk]

/-- There is no handover observation at or beyond the physical horizon. -/
theorem X_H_false_of_not_lt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : ℕ) (z : Source) (hk : ¬ k < p.T) :
    X_H rate rewards C_star C_h control0 i k z = false := by
  simp [X_H, hk]

/-- The deterministic support weight has its positive-grid cardinal formula
on source rounds. -/
theorem g_H_eq_card (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin p.T) (z : Source) :
    g_H rate rewards C_star C_h control0 k.val z =
      ((Finset.univ.filter fun a : Fin p.K => 0 < (rewards k a).val).card : ℝ) := by
  simp [g_H]

/-- The deterministic support weight vanishes at and after the horizon. -/
theorem g_H_eq_zero_of_not_lt (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (z : Source) (hk : ¬ k < p.T) :
    g_H rate rewards C_star C_h control0 k z = 0 := by
  simp [g_H, hk]

/-- The stopped support weight is deterministic before each source round. -/
theorem g_H_preRound_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (k + 1)]
      (fun z : Source => g_H rate rewards C_star C_h control0 k z) := by
  by_cases hk : k < p.T
  · simp [g_H, hk]
    exact stronglyMeasurable_const
  · simp [g_H, hk]
    exact stronglyMeasurable_const

/-- The waiting-process observation is the literal real-valued encoding of
the actual binary handover observation. -/
theorem observation_eq_X_H
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : ℕ) :
    PhaseServiceWaiting.observation
      (X_H rate rewards C_star C_h control0) i k =
        fun z : Source => if X_H rate rewards C_star C_h control0 i k z then 1 else 0 := rfl

/-- The stopped charge unfolds to the source-date sum. -/
theorem G_H_eq_sum (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source) :
    G_H rate rewards C_star C_h control0 z =
      ∑ v ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
        rate rewards C_star C_h z,
        g_H rate rewards C_star C_h control0 (v - 1) z := rfl

/-- Summing the total-charge process over the actual pending calendar gives
exactly the source's uncapped handover support charge. -/
theorem totalCharge_eq_G_H
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source) :
    PhaseServiceWaiting.totalCharge
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat rate rewards C_star C_h)
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h)
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h)
      (g_H rate rewards C_star C_h control0) p.T z =
        G_H rate rewards C_star C_h control0 z := by
  classical
  let S := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z
  have hactive (t : ℕ) (ht : t < p.T) :
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z ≤ t + 1 ∧
        t + 1 < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z ∧
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat rate rewards C_star C_h t z).Nonempty) ↔
      t + 1 ∈ S := by
    have hpend :
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t z).Nonempty ↔ t + 1 ∈ S := by
      simpa [S] using
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
          rate rewards C_star C_h z t)
    have hcal : t + 1 ∈ S ↔
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z ≤ t + 1 ∧
          t + 1 < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z := by
      change t + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
          rate rewards C_star C_h z ↔
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z ≤ t + 1 ∧
          t + 1 < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z
      rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_eq_interval]
      simp only [Finset.mem_Ico]
    rw [hpend]
    constructor
    · rintro ⟨_, _, hmem⟩
      exact hmem
    · intro hmem
      exact ⟨(hcal.mp hmem).1, (hcal.mp hmem).2, hmem⟩
  have hterm (t : ℕ) (ht : t < p.T) :
      PhaseServiceWaiting.A
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat rate rewards C_star C_h)
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h)
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h)
        (g_H rate rewards C_star C_h control0) t z =
      if t + 1 ∈ S then g_H rate rewards C_star C_h control0 t z else 0 := by
    by_cases h : ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma
          rate rewards C_star C_h z ≤ t + 1 ∧
        t + 1 < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z ∧
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t z).Nonempty
    · have hs : t + 1 ∈ S := hactive t ht |>.mp h
      simp [PhaseServiceWaiting.A, h, hs]
    · have hs : t + 1 ∉ S := fun hs => h ((hactive t ht).mpr hs)
      simp [PhaseServiceWaiting.A, h, hs]
  unfold PhaseServiceWaiting.totalCharge
  rw [G_H]
  have hleft :
      (∑ t ∈ Finset.range p.T,
        PhaseServiceWaiting.A
          (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat rate rewards C_star C_h)
          (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h)
          (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h)
          (g_H rate rewards C_star C_h control0) t z) =
        ∑ t ∈ Finset.range p.T,
          if t + 1 ∈ S then g_H rate rewards C_star C_h control0 t z else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hterm t (Finset.mem_range.mp ht)
  rw [hleft, ← Finset.sum_filter]
  apply Finset.sum_bij (fun t _ => t + 1)
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu htu
    omega
  · intro v hv
    have hbounds := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_bounds
      rate rewards C_star C_h z v hv
    have hvpos : 0 < v := by omega
    have hvle : v ≤ p.T := hbounds.2
    have hvlt : v - 1 < p.T := by omega
    refine ⟨v - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvlt, ?_⟩, ?_⟩
    · have hdate : (v - 1) + 1 = v := by omega
      simpa [S, hdate] using hv
    · omega
  · intro t ht
    have hindex : (t + 1) - 1 = t := by omega
    rw [hindex]

section Adaptation

open ReferenceFirstLiveSourceStoppedHandoverEndpoint
open ReferenceFirstLiveHandoverBoundaryFactorization
open ReferenceFirstLiveSourceStoppedReleaseEndpoint (firstExcluded physicalStart)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "H" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

private theorem actualRecord_time (t : Fin p.T) (z : Source)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have heq := Option.some.inj (hr.symm.trans
      (ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2))
    subst r
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem window_selection_stage (z : Source)
    (j : Fin (window rate rewards C_star C_h z).length) (i : Fin (p.m - 1)) :
    let r := (window rate rewards C_star C_h z).get j
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      actualSelection rate r = some selected ∧
      (Before rate r i ∨ After rate r selected i) := by
  let r := (window rate rewards C_star C_h z).get j
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z (by have := j.isLt; omega)
  have hprov := source_window_provenance rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨_, installed, firstSelected, _, _, _, _, _, hrows⟩
  · have := j.isLt
    omega
  obtain ⟨selected, hselected, _hp, hphase, _hrest⟩ := hrows j
  have hstateFacts := actual_window_state_facts rate rewards C_star C_h z j
  have hfirst : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state := by
    simpa only [r, List.get_eq_getElem] using hstateFacts.1
  obtain ⟨state, memory, hconfig, hunoccupied⟩ := hstateFacts.2 i
  have hcfig : r.input.state.followers i = .ordinary state memory := by
    simpa only [r, List.get_eq_getElem] using hconfig
  refine ⟨selected, hselected, ?_⟩
  cases hc : r.input.state.coordinator with
  | first =>
      have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers r.input.state := by
        simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hfirst
      exact Or.inl ⟨state, memory, hcfig, (hinitial i state memory hcfig).2⟩
  | live incoming owned base =>
      have hcarried : ReferenceActiveDataOwnership.carriedOccupiedFields incoming.payload
          r.input.state ∧
          ∀ i s memory, r.input.state.followers i = .ordinary s memory →
            incoming.pendingAtChoice.Nonempty → s.status ≠ ActiveRoundActions.FollowerStatus.released := by
        simpa only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] using hfirst
      have hpayload : selected.view.payload = incoming.payload ∧
          selected.view.pendingAtChoice = incoming.pendingAtChoice := by
        rw [hc] at hphase
        exact hphase
      by_cases hu : state.status = ActiveRoundActions.FollowerStatus.unoccupied
      · exact Or.inl ⟨state, memory, hcfig, hunoccupied hu⟩
      · apply Or.inr
        refine ⟨state, memory, hcfig, ?_⟩
        have hfield := hcarried.1 i
        rw [hcfig] at hfield
        rw [hpayload.1]
        exact hfield hu
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hfirst
  | dagger =>
      rw [hc] at hphase
      exact hphase.elim

private theorem pending_of_actual_window (t : Fin p.T) (z : Source)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input) (i : Fin (p.m - 1))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hw : r ∈ window rate rewards C_star C_h z)
    (hselected : actualSelection rate r = some selected)
    (hi : i ∈ selected.view.pendingAtChoice)
    (hstop : t.val + 1 < firstExcluded rate rewards C_star C_h z) :
    i ∈ pendingNat rate rewards C_star C_h t.val z := by
  have ht := actualRecord_time rate rewards C_star C_h t z r hr
  have hm : missing rate r = selected.view.pendingAtChoice := by
    unfold missing
    rw [hselected]
    rfl
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hw
  have hd : t.val + 1 ∈ supportDates rate rewards C_star C_h z := by
    apply (supportDates_mem_iff rate rewards C_star C_h z _).mpr
    refine ⟨⟨j, hj⟩, ?_, ?_, hstop⟩
    · rw [hje, ht]
    · rw [hje, hm]
      exact ⟨i, hi⟩
  rw [pendingNat_eq_actual_missing_on_support rate rewards C_star C_h z t.val t.isLt hd, hr]
  change i ∈ missing rate r
  rw [hm]
  exact hi

/-- The literal pending event is the finite union of the two actual incoming
stages, stopped by the original strict-past endpoint. -/
theorem pendingNat_mem_iff_stopped_sections (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    i ∈ pendingNat rate rewards C_star C_h t.val z ↔
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_before rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z) ∨
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_after rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z) := by
  constructor
  · intro hi
    have hd := (pendingNat_nonempty_iff rate rewards C_star C_h z t.val).mp ⟨i, hi⟩
    obtain ⟨j, hdate, _hm, hstop⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hd
    let r := (window rate rewards C_star C_h z).get j
    have ht : r.input.time = t := by
      apply Fin.ext
      dsimp only [r, List.get_eq_getElem]
      omega
    obtain ⟨selected, hselected, hstage⟩ := window_selection_stage rate rewards C_star C_h z j i
    have hpending : pendingNat rate rewards C_star C_h t.val z = missing rate r := by
      have h := pendingNat_eq_window_missing rate rewards C_star C_h z j (by simpa [hdate] using hd)
      change pendingNat rate rewards C_star C_h r.input.time.val z = missing rate r at h
      rw [ht] at h
      exact h
    have hi' : i ∈ selected.view.pendingAtChoice := by
      rw [hpending, missing, hselected] at hi
      exact hi
    have hcal := source_window_record_calendar rate rewards C_star C_h z j
    have hs : physicalStart rate rewards C_star C_h z ≤ t.val := by
      have hc := hcal.1
      change r.input.time.val = physicalStart rate rewards C_star C_h z + j.val at hc
      rw [ht] at hc
      omega
    let s : Fin (t.val + 1) := ⟨physicalStart rate rewards C_star C_h z, by omega⟩
    let q := ActualInitializationPhysicalStep.selectedRowIndex p z
    have hcross : crossed rate rewards C_star C_h z :=
      crossing_of_window_nonempty rate rewards C_star C_h z (by have := j.isLt; omega)
    have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
      have hrec : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          r.input.time z = some r := hcal.2
      rw [ht] at hrec
      exact hrec
    have hw : r ∈ firstWindow rate rewards C_star C_h z := List.get_mem _ _
    rcases hstage with hb | ha
    · exact Or.inl ⟨⟨q, s, rfl, hcross, rfl, hs, r, selected, hr, hw, hselected, hi', hb⟩, hstop⟩
    · exact Or.inr ⟨⟨q, s, rfl, hcross, rfl, hs, r, selected, hr, hw, hselected, hi', ha⟩, hstop⟩
  · rintro (⟨⟨q, s, he⟩, hstop⟩ | ⟨⟨q, s, he⟩, hstop⟩)
    · obtain ⟨r, selected, hr, hw, hselected, hi, _hb⟩ := he.2.2.2.2
      exact pending_of_actual_window rate rewards C_star C_h t z r selected i hr hw hselected hi hstop
    · obtain ⟨r, selected, hr, hw, hselected, hi, _ha⟩ := he.2.2.2.2
      exact pending_of_actual_window rate rewards C_star C_h t z r selected i hr hw hselected hi hstop

/-- Actual stopped pending membership is predictable on the original source. -/
theorem pendingNat_preRound_measurableSet (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    MeasurableSet[H (k + 1)] {z : Source | i ∈ pendingNat rate rewards C_star C_h k z} := by
  have hb := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_before_stopped_union
    rate rewards C_star C_h control0 ⟨k, hk⟩ i
  have ha := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_after_stopped_union
    rate rewards C_star C_h control0 ⟨k, hk⟩ i
  convert hb.union ha using 1
  ext z
  exact pendingNat_mem_iff_stopped_sections rate rewards C_star C_h ⟨k, hk⟩ i z

/-- A supported source date is a finite union of predictable pending events. -/
theorem supportDates_preRound_measurableSet (t : Fin p.T) :
    MeasurableSet[H (t.val + 1)]
      {z : Source | t.val + 1 ∈ supportDates rate rewards C_star C_h z} := by
  have hm := MeasurableSet.iUnion fun i : Fin (p.m - 1) =>
    pendingNat_preRound_measurableSet rate rewards C_star C_h control0 i t.val t.isLt
  convert hm using 1
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact (pendingNat_nonempty_iff rate rewards C_star C_h z t.val).symm

/-- For a nonterminal date, the actual start has occurred exactly when
some supported one-based round no later than that date exists. -/
theorem handover_sigma_le_iff (z : Source) (v : ℕ) (hv : v ≤ p.T) :
    sigma rate rewards C_star C_h z ≤ v ↔
      ∃ u : Fin p.T, u.val + 1 ≤ v ∧
        u.val + 1 ∈ supportDates rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := actual_handover_interval rate rewards C_star C_h z
  constructor
  · intro hstart
    have hne : (supportDates rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (empty_support_endpoints rate rewards C_star C_h z hempty).1
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨sigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = sigma rate rewards C_star C_h z := by dsimp [u]; omega
    refine ⟨u, by omega, ?_⟩
    rw [hinterval, Finset.mem_Ico, hu]
    omega
  · rintro ⟨u, hu, hmem⟩
    rw [hinterval, Finset.mem_Ico] at hmem
    omega

/-- The actual first excluded endpoint has occurred exactly when an earlier
supported round exists and the current one-based date is unsupported. -/
theorem handover_theta_le_iff (z : Source) (v : ℕ) (hv : v ≤ p.T) :
    theta rate rewards C_star C_h z ≤ v ↔
      (∃ u : Fin p.T, u.val + 1 < v ∧
        u.val + 1 ∈ supportDates rate rewards C_star C_h z) ∧
      v ∉ supportDates rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := actual_handover_interval rate rewards C_star C_h z
  constructor
  · intro hend
    have hne : (supportDates rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (empty_support_endpoints rate rewards C_star C_h z hempty).2
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨sigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = sigma rate rewards C_star C_h z := by dsimp [u]; omega
    constructor
    · refine ⟨u, by omega, ?_⟩
      rw [hinterval, Finset.mem_Ico, hu]
      omega
    · rw [hinterval, Finset.mem_Ico]
      omega
  · rintro ⟨⟨u, hu, hmem⟩, hnot⟩
    rw [hinterval, Finset.mem_Ico] at hmem hnot
    omega

private theorem supported_before_measurable
    (v : ℕ) (strict : Bool) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v]
      {z : Source | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ supportDates rate rewards C_star C_h z} := by
  let : MeasurableSpace (Source) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v
  have heq : {z : Source | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ supportDates rate rewards C_star C_h z} =
      ⋃ u : Fin p.T, if (if strict then u.val + 1 < v else u.val + 1 ≤ v) then
        {z : Source | u.val + 1 ∈ supportDates rate rewards C_star C_h z} else ∅ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, hm⟩
      refine ⟨u, ?_⟩
      rw [ite_eq_left hu]
      exact hm
    · rintro ⟨u, hu⟩
      by_cases h : if strict then u.val + 1 < v else u.val + 1 ≤ v
      · rw [ite_eq_left h] at hu
        exact ⟨u, h, hu⟩
      · rw [ite_eq_right h] at hu
        exact hu.elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : if strict then u.val + 1 < v else u.val + 1 ≤ v
  · rw [ite_eq_left hu]
    have hle : u.val + 1 ≤ v := by
      cases strict with
      | false => exact hu
      | true => exact Nat.le_of_lt hu
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono hle _
      (supportDates_preRound_measurableSet rate rewards C_star C_h control0 u)
  · rw [ite_eq_right hu]
    exact MeasurableSet.empty

/-- The endpoint module's actual start is a stopping time for the original
source-prefix filtration, including empty and terminal handover phases. -/
theorem sigma_preRound_stopping :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (sigma rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : Source | sigma rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hlow := (actual_handover_interval rate rewards C_star C_h z).2.1
      omega
    rw [heq]
    exact @MeasurableSet.empty (Source)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · have heq : {z : Source | sigma rate rewards C_star C_h z ≤ v} =
        {z : Source | ∃ u : Fin p.T, u.val + 1 ≤ v ∧
          u.val + 1 ∈ supportDates rate rewards C_star C_h z} := by
      ext z
      exact handover_sigma_le_iff rate rewards C_star C_h z v hv
    rw [heq]
    exact supported_before_measurable rate rewards C_star C_h control0 v false
  · have heq : {z : Source | sigma rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨_, _, horder, hhigh⟩ := actual_handover_interval rate rewards C_star C_h z
      omega
    rw [heq]
    exact MeasurableSet.univ

/-- The actual first excluded handover endpoint is a stopping time on every
natural index, including the empty-support and terminal sentinels. -/
theorem theta_preRound_stopping :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (theta rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : Source | theta rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      obtain ⟨_, hlow, horder, _⟩ := actual_handover_interval rate rewards C_star C_h z
      omega
    rw [heq]
    exact @MeasurableSet.empty (Source)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · let current : Fin p.T := ⟨v - 1, by omega⟩
    have hcurrent : current.val + 1 = v := by dsimp [current]; omega
    have heq : {z : Source | theta rate rewards C_star C_h z ≤ v} =
        {z : Source | ∃ u : Fin p.T, u.val + 1 < v ∧
          u.val + 1 ∈ supportDates rate rewards C_star C_h z} ∩
        {z : Source | v ∈ supportDates rate rewards C_star C_h z}ᶜ := by
      ext z
      exact handover_theta_le_iff rate rewards C_star C_h z v hv
    rw [heq]
    have hm := supportDates_preRound_measurableSet rate rewards C_star C_h control0 current
    rw [hcurrent] at hm
    exact (supported_before_measurable rate rewards C_star C_h control0 v true).inter hm.compl
  · have heq : {z : Source | theta rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hhigh := (actual_handover_interval rate rewards C_star C_h z).2.2.2
      omega
    rw [heq]
    exact MeasurableSet.univ


/-- The true event uses the same actual record in its pending section and
its physical service test. Acceptance in the present update stays in Before. -/
theorem X_H_true_iff_stopped_sections (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    X_H rate rewards C_star C_h control0 i t.val z = true ↔
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_before rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z ∧
        V_before rate rewards C_star C_h i t z) ∨
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_after rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z ∧
        V_after rate rewards C_star C_h i t z) := by
  rw [X_H_eq_decide]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hi, r, selected, hr, hselected, hstage⟩
    have hsections := (pendingNat_mem_iff_stopped_sections rate rewards C_star C_h t i z).mp hi
    rcases hstage with hb | ha
    · rcases hsections with ⟨he, hstop⟩ | ⟨⟨q, s, he⟩, hstop⟩
      · exact Or.inl ⟨he, hstop, hb.2⟩
      · obtain ⟨r', selected', hr', _hw, _hsel, _hi, hafter⟩ := he.2.2.2.2
        have heq : r' = r := Option.some.inj (hr'.symm.trans hr)
        subst r'
        exact (actual_supported_stage_disjoint rate r selected' i ⟨hb.1, hafter⟩).elim
    · rcases hsections with ⟨⟨q, s, he⟩, hstop⟩ | ⟨he, hstop⟩
      · obtain ⟨r', selected', hr', _hw, _hsel, _hi, hbefore⟩ := he.2.2.2.2
        have heq : r' = r := Option.some.inj (hr'.symm.trans hr)
        subst r'
        exact (actual_supported_stage_disjoint rate r selected i ⟨hbefore, ha.1⟩).elim
      · exact Or.inr ⟨he, hstop, ha.2⟩
  · rintro (⟨⟨q, s, he⟩, hstop, hv⟩ | ⟨⟨q, s, he⟩, hstop, hv⟩)
    · obtain ⟨r, selected, hr, hw, hselected, hi, hb⟩ := he.2.2.2.2
      exact ⟨pending_of_actual_window rate rewards C_star C_h t z r selected i
        hr hw hselected hi hstop, r, selected, hr, hselected, Or.inl ⟨hb, hv⟩⟩
    · obtain ⟨r, selected, hr, hw, hselected, hi, ha⟩ := he.2.2.2.2
      exact ⟨pending_of_actual_window rate rewards C_star C_h t z r selected i
        hr hw hselected hi hstop, r, selected, hr, hselected, Or.inr ⟨ha, hv⟩⟩

/-- Restoring the complete original current control identifies the service
branches with F's original B tests; no discrete replacement of a row is used. -/
theorem X_H_true_iff_stopped_B (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    X_H rate rewards C_star C_h control0 i t.val z = true ↔
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_before rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z ∧
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B_before rate rewards C_star C_h i t) ∨
      ((∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ E_after rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z ∧
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B_after rate rewards C_star C_h i t) := by
  rw [X_H_true_iff_stopped_sections]
  have hb : ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
      ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B_before rate rewards C_star C_h i t) ↔
      V_before rate rewards C_star C_h i t z := by
    change V_before rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        (ReferenceSourceCurrentControlFreshness.u_t p t z)) ↔ _
    rw [before_current_restoration control0 t z,
      ← V_before_sourcePrefix_successor rate rewards C_star C_h control0 i t z]
  have ha : ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
      ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B_after rate rewards C_star C_h i t) ↔
      V_after rate rewards C_star C_h i t z := by
    change V_after rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        (ReferenceSourceCurrentControlFreshness.u_t p t z)) ↔ _
    rw [before_current_restoration control0 t z,
      ← V_after_sourcePrefix_successor rate rewards C_star C_h control0 i t z]
  rw [hb, ha]

private theorem measurableSet_of_indicator {m : MeasurableSpace Source} (V : Source → Prop)
    (h : StronglyMeasurable[m] (fun z => if V z then (1 : ℝ) else 0)) :
    MeasurableSet[m] {z | V z} := by
  have h1 : StronglyMeasurable[m] (fun _ : Source => (1 : ℝ)) := stronglyMeasurable_const
  convert h.measurableSet_eq_fun h1 using 1
  ext z
  by_cases hv : V z <;> simp [hv]

/-- The actual stopped binary observation is observable by round end in the
original source-prefix filtration, without an adaptation premise. -/
theorem observation_roundEnd_stronglyMeasurable (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[H (k + 2)]
      (PhaseServiceWaiting.observation (X_H rate rewards C_star C_h control0) i k) := by
  let t : Fin p.T := ⟨k, hk⟩
  have hb := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_before_stopped_union
    rate rewards C_star C_h control0 t i
  have ha := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_after_stopped_union
    rate rewards C_star C_h control0 t i
  have hle : t.val + 1 ≤ k + 2 := by dsimp only [t]; omega
  have hb' := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono hle _ hb
  have ha' := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono hle _ ha
  have hvb := measurableSet_of_indicator
    (V_before rate rewards C_star C_h i t)
    (V_before_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t)
  have hva := measurableSet_of_indicator
    (V_after rate rewards C_star C_h i t)
    (V_after_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t)
  have hx : MeasurableSet[H (k + 2)]
      {z : Source | X_H rate rewards C_star C_h control0 i k z = true} := by
    convert (hb'.inter hvb).union (ha'.inter hva) using 1
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    simpa only [and_assoc] using X_H_true_iff_stopped_sections rate rewards C_star C_h control0 t i z
  rw [observation_eq_X_H]
  exact StronglyMeasurable.ite hx stronglyMeasurable_const stronglyMeasurable_const

end Adaptation

end Bandits.Support.ReferenceFirstLiveStoppedHandoverAdaptation

end
