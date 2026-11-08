/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination
public import Bandits.Support.ReferenceGeneratedCalendarRoundLaw

/-!
# Episode chronology on the original physical calendar

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
The statements below concern the same original physical records. Logical
numerical prefixes retain their own first-overflow cut.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceOriginalCalendarEpisodeChronology

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence ReferenceCompleteEpisodeAnchorOrigin
open CoordinatorRoundDispatch

variable {p : ConstructorDimensions.Parameters}

/-- The observation-free episode-origin test on the incoming original state.
A corrected assignment before the old freeze boundary does not pass this test. -/
def IsEpisodeStartBeforeChoice {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) : Prop :=
  match r.input.state.coordinator with
  | .first => True
  | .collection _ ledger _ =>
      ledger.pending = ∅ ∧ ledger.freezeAt ≤ r.input.time.val + 1
  | _ => False

private theorem chosen_collection_pending_empty
    (x : CollectionInput p) (core : CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction) :
    x.ledger.pending = ∅ := by
  classical
  by_contra hn
  have hut : x.cutoffIndex.val ≤ x.time.val := by
    have ht := core.clock_start_time_valid
    simp only [CoordinatorPhaseClock.startRoundTimeValid, core.clock_sigma_eq,
      core.clock_cutoff_eq] at ht
    exact ht.2
  have hp := CoordinatorPhaseClock.startRound_collection_pending p x.etaReal x.time
    x.payload.sigma x.cutoffIndex x.clock x.ledger.pending
    core.clock_parameter_valid core.clock_registers_valid core.clock_sigma_eq
    core.clock_cutoff_eq hut hn
  have he := Except.ok.inj (hs.symm.trans hp)
  rw [he] at hi
  cases hi

/-- On every actual original record, the before-choice incoming-state test is
exactly the first/renewal installation test. All success facts come from the
accepted actual phase-exhaustion theorem. -/
theorem complete_episode_birth_iff_before_choice
    (rate : ReferenceActivePhysicalStep.RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    IsEpisodeAnchorBirth r ↔ IsEpisodeStartBeforeChoice r := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  change IsEpisodeAnchorBirth r ↔ IsEpisodeStartBeforeChoice r
  have he := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 k
  have hsel : r.output.preparation.coordinator.selection ≠ none := he.2.1
  have hactual : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  cases hc : r.input.state.coordinator with
  | first =>
      have hd : r.output.preparation.coordinator =
          .first (dispatchFirst (firstInput r.input)) := by
        rw [hactual, dispatch_first r.input hc]
      cases ho : dispatchFirst (firstInput r.input) <;> rw [ho] at hd
      all_goals try { simp only [hd, DispatchCut.selection, ne_eq, not_true_eq_false] at hsel }
      simp only [IsEpisodeAnchorBirth, hd, IsEpisodeStartBeforeChoice, hc]
  | live a b c =>
      have hd : r.output.preparation.coordinator =
          .live a b c (dispatchLive (liveInput r.input a b c)) := by
        rw [hactual]
        simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      simp only [IsEpisodeAnchorBirth, hd, IsEpisodeStartBeforeChoice, hc]
  | dagger =>
      exact (he.1 hc).elim
  | collection P ledger saved =>
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock P ledger saved cutoff
        let x := collectionInput r.input P ledger clock cutoff
        have hd : r.output.preparation.coordinator =
            .collection P ledger clock cutoff (dispatchCollection x) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
          rfl
        cases ho : dispatchCollection x <;> rw [ho] at hd
        all_goals try { simp only [hd, DispatchCut.selection, ne_eq, not_true_eq_false] at hsel }
        case continuing core prepared boundary checked =>
          have hn := prepared.inputsValid.pending_nonempty
          change ledger.pending.Nonempty at hn
          simp only [IsEpisodeAnchorBirth, hd, IsEpisodeStartBeforeChoice, hc]
          constructor
          · exact False.elim
          · intro h
            exact Finset.nonempty_iff_ne_empty.mp hn h.1
        case laterChosen core consistent started hs instruction hi output hlocal clockData installed selected =>
          have hp := chosen_collection_pending_empty x core started hs instruction hi
          have hiData := CoordinatorPhaseClock.startRound_assignment_effect p x.etaReal x.time
            x.clock x.ledger.pending started instruction core.clock_parameter_valid
            core.clock_registers_valid core.clock_start_time_valid hs hi
          have hk : instruction.kind =
              CoordinatorPhaseClock.classifyAssignmentStart (some P.sigma) r.input.time ledger.freezeAt := by
            simpa only [x, collectionInput, clock, collectionClock, hiData.1] using hiData.2.1
          simp only [IsEpisodeAnchorBirth, hd, IsEpisodeStartBeforeChoice, hc]
          change ledger.pending = ∅ at hp
          rw [hk, hp]
          simp only [CoordinatorPhaseClock.classifyAssignmentStart, FollowerCutoffScan.calendarRound,
            true_and]
          by_cases h : ledger.freezeAt ≤ r.input.time.val + 1 <;> simp [h]
      · have hd : r.output.preparation.coordinator = .invalidCollectionCutoff := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_right hcut]
        simp only [hd, DispatchCut.selection, ne_eq, not_true_eq_false] at hsel

private theorem complete_record_clockAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.state ∧
      ReferenceCoordinatorClockDomains.clockAt
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val + 1)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].output.next := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hactive : active =
          ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc :=
        Option.some.inj (hlaunch.symm.trans hcanonical)
      subst active
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          hlaunch)
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          initial := by
        have hfirst : initial.coordinator = .first := seed.coordinatorFirst
        simp [ReferenceCoordinatorClockDomains.clockAt, initial, hfirst]
      have hruns := ReferenceRunClockPreservation.run_clockAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          hlaunch) hseed
      have hmem :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val] ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      have hrecord := hruns.2.2.2
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] hmem
      exact ⟨hrecord.1, hrecord.2.1⟩


private theorem storedPayload_ne_none_of_phase
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (c : CoordinatorConfiguration p rate) (hf : c ≠ .first) (hd : c ≠ .dagger) :
    storedPayload c ≠ none := by
  cases c <;> simp_all [storedPayload]

/-- A successful actual installation stores that same whole payload through
POST, including its original start and all immutable assignment fields. -/
private theorem complete_installation_stored_payload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hb : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] P) :
    storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.next.coordinator = some P := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  change InstallationBirth r P at hb
  change storedPayload r.output.next.coordinator = some P
  have he := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 k
  have hsel : r.output.preparation.coordinator.selection ≠ none := he.2.1
  have hnon : storedPayload r.output.next.coordinator ≠ none :=
    storedPayload_ne_none_of_phase _ he.2.2.2.1 he.2.2.2.2
  have hn : r.output.next.coordinator = r.output.coordinator.configuration := by
    rw [r.output_eq]
    rfl
  have ho : r.output.coordinator = r.output.preparation.observeCoordinator := by
    rw [r.output_eq]
    rfl
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp only [InstallationBirth, hc] at hb
      case chosen installed selected =>
        rcases hb with ⟨rfl, _⟩
        have hframe := livePostChoice_payload_frame r.output.preparation installed.registers
          installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
        have hout : storedPayload r.output.next.coordinator = none ∨
            storedPayload r.output.next.coordinator = some installed.registers.payload := by
          rw [hn, ho]
          unfold PreparedRound.observeCoordinator
          rw [dite_eq_right hsel, hc]
          exact hframe
        exact hout.resolve_left hnon
  | live a b c outcome => simp only [InstallationBirth, hc] at hb
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [InstallationBirth, hc] at hb
      case laterChosen core consistent started hs instruction hi output hlocal clockData installed selected =>
        rcases hb with ⟨rfl, _⟩
        have hframe := livePostChoice_payload_frame r.output.preparation installed.registers
          installed.ownedRegisters installed.retainedBaseScore started
        have hout : storedPayload r.output.next.coordinator = none ∨
            storedPayload r.output.next.coordinator = some installed.registers.payload := by
          rw [hn, ho]
          unfold PreparedRound.observeCoordinator
          rw [dite_eq_right hsel, hc]
          exact hframe
        exact hout.resolve_left hnon
  | invalidCollectionCutoff => simp only [InstallationBirth, hc] at hb
  | dagger => simp only [InstallationBirth, hc] at hb

/-- Later original stored assignments cannot predate an earlier installation.
This follows actual adjacent states and the actual payload transition; equality
of numerical anchors plays no role. -/
private theorem complete_earlier_birth_le_stored_sigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ (b k : Fin R.length) (P Q : Payload rate), b.val < k.val →
      InstallationBirth R[b.val] P → storedPayload R[k.val].input.state.coordinator = some Q →
      P.sigma.val ≤ Q.sigma.val := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hall : ∀ n (hn : n < R.length) (b : Fin R.length) (P Q : Payload rate),
      b.val < n → InstallationBirth R[b.val] P →
      storedPayload (R[n]'hn).input.state.coordinator = some Q → P.sigma.val ≤ Q.sigma.val := by
    intro n
    induction n with
    | zero => intro hn b P Q h; omega
    | succ n ih =>
        intro hn b P Q hbk hb hQ
        have hn0 : n < R.length := by omega
        have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z n hn
        have hQnext : storedPayload (R[n]'hn0).output.next.coordinator = some Q := by
          rw [← hadj]
          exact hQ
        by_cases heq : b.val = n
        · have hb' : InstallationBirth (R[n]'hn0) P := by simpa only [heq] using hb
          have hP := complete_installation_stored_payload rate rewards C_star C_h z ⟨n, hn0⟩ P hb'
          have hpq : P = Q := Option.some.inj (hP.symm.trans hQnext)
          exact Nat.le_of_eq (congrArg (fun X : Payload rate => X.sigma.val) hpq)
        · have hbn : b.val < n := by omega
          have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification
            (R[n]'hn0).input
          have he : ReferenceAssignmentPayloadChronology.actualStepRecord (R[n]'hn0).input = R[n] := by
            have hout := (R[n]'hn0).output_eq
            cases hr : R[n]'hn0 with
            | mk input output houtput =>
                cases houtput
                rfl
          have hstep : (ReferenceActivePhysicalStep.step (R[n]'hn0).input).next =
              (R[n]'hn0).output.next := congrArg (fun o => o.next) (R[n]'hn0).output_eq.symm
          rw [hstep] at hclass
          rcases hclass with hnone | ⟨old, hold, hpost⟩ | ⟨fresh, hfresh, hpost⟩
          · rw [hQnext] at hnone
            cases hnone
          · have hsame : old = Q := Option.some.inj (hpost.symm.trans hQnext)
            subst old
            exact ih hn0 b P Q hbn hb hold
          · have hsame : fresh = Q := Option.some.inj (hpost.symm.trans hQnext)
            subst fresh
            rw [he] at hfresh
            have htP := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] P hb
            have htQ := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[n] Q hfresh
            rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
              rate rewards C_star C_h z b] at htP
            rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
              rate rewards C_star C_h z ⟨n, hn0⟩] at htQ
            dsimp only at htQ
            omega
  intro b k P Q hbk hb hQ
  exact hall k.val k.isLt b P Q hbk hb hQ

/-- The clipped one-based grid endpoint is monotone in the physical start. -/
private theorem gridBoundary_mono (rate : ReferenceActivePhysicalStep.RateInput p)
    (s t : Fin p.T) (hst : s.val ≤ t.val) :
    FollowerCutoffScan.gridBoundary p rate.eta.val s ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val t := by
  unfold FollowerCutoffScan.gridBoundary
  apply min_le_min_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.add_le_add_right hst 1)) 1

/-- A later first/renewal origin begins only after every earlier installation's
old episode endpoint. This is interval separation, stronger than distinct
installation timestamps. -/
private theorem complete_episode_birth_separation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (P : Payload rate)
    (hbk : b.val < k.val)
    (hb : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P)
    (hk : IsEpisodeAnchorBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]) :
    FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time.val + 1 := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have horigin := (complete_episode_birth_iff_before_choice rate rewards C_star C_h z k).mp hk
  have hclock := (complete_record_clockAt rate rewards C_star C_h z k).1
  change IsEpisodeStartBeforeChoice R[k.val] at horigin
  have hklen : k.val < R.length := k.isLt
  have hn : 0 < k.val := by omega
  have hprev : k.val - 1 + 1 < R.length := by omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (k.val - 1) hprev
  have he := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨k.val - 1, by omega⟩
  have hnotfirst : R[k.val].input.state.coordinator ≠ .first := by
    have hadj' : R[k.val].input.state = R[k.val - 1].output.next := by
      simpa only [Nat.sub_add_cancel hn] using hadj
    rw [hadj']
    exact he.2.2.2.1
  cases hc : R[k.val].input.state.coordinator with
  | first => exact (hnotfirst hc).elim
  | live a b c => simp only [IsEpisodeStartBeforeChoice, hc] at horigin
  | dagger => simp only [IsEpisodeStartBeforeChoice, hc] at horigin
  | collection Q ledger saved =>
      simp only [IsEpisodeStartBeforeChoice, hc] at horigin
      change ReferenceCoordinatorClockDomains.clockAt z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) R[k.val].input.time.val
        R[k.val].input.state at hclock
      simp only [ReferenceCoordinatorClockDomains.clockAt, hc] at hclock
      have hPQ := complete_earlier_birth_le_stored_sigma rate rewards C_star C_h z b k P Q
        hbk hb (by
          change storedPayload R[k.val].input.state.coordinator = some Q
          rw [hc]
          rfl)
      exact (gridBoundary_mono rate P.sigma Q.sigma hPQ).trans
        (hclock.2.2.2.2.2.1.symm.trans_le horigin.2)


/-- An episode birth determines one whole actual installation payload. -/
theorem episode_birth_payload_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) (hr : IsEpisodeAnchorBirth r) :
    ∃! P : Payload rate, InstallationBirth r P := by
  classical
  have make (P : Payload rate) (hb : InstallationBirth r P) :
      ∃! Q : Payload rate, InstallationBirth r Q :=
    ⟨P, hb, fun Q hQ => ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      r Q P hQ hb⟩
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp only [IsEpisodeAnchorBirth, hc] at hr
      case chosen installed selected =>
        exact make installed.registers.payload
          (ReferenceCompleteLiveComplementScoreSpan.first_installation_source r installed selected hc).1
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [IsEpisodeAnchorBirth, hc] at hr
      case laterChosen core consistent started hs instruction hi output hlocal clockData installed selected =>
        have hb := ReferenceLaterInstallationProvenance.record_laterChosen_birth r
        rw [hc] at hb
        exact make installed.registers.payload hb
  | live a b c outcome => simp only [IsEpisodeAnchorBirth, hc] at hr
  | invalidCollectionCutoff => simp only [IsEpisodeAnchorBirth, hc] at hr
  | dagger => simp only [IsEpisodeAnchorBirth, hc] at hr

/-- Any two original episode intervals covering the same calendar date have
the same record index. The proof uses renewal endpoint separation. -/
theorem complete_episode_interval_at_most_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (q : Fin p.T)
    (i j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hi : IsEpisodeAnchorBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val] ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[i.val].input.time.val ≤ q.val ∧
      q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[i.val].input.time)
    (hj : IsEpisodeAnchorBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val] ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val].input.time.val ≤ q.val ∧
      q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val].input.time) :
    i = j := by
  have excludes (a b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
      (ha : IsEpisodeAnchorBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val])
      (hb : IsEpisodeAnchorBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val])
      (hab : a.val < b.val) :
      FollowerCutoffScan.gridBoundary p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val].input.time ≤
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time.val + 1 := by
    obtain ⟨P, hP, _⟩ := episode_birth_payload_unique _ ha
    have ht : P.sigma = (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val].input.time :=
      Fin.ext (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ P hP)
    simpa only [ht] using complete_episode_birth_separation rate rewards C_star C_h z a b P hab hP hb
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := excludes i j hi.1 hj.1 hlt
    omega
  · have h := excludes j i hj.1 hi.1 hgt
    omega

private theorem complete_selected_payload_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length,
      b.val ≤ k.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] selected.view.payload := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have span : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
        span seed.activeAtStart
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] ∈ execution.records := by
        rw [← hrun]
        exact List.getElem_mem k.isLt
      obtain ⟨birth, hbirthMem, hbirth, htime, hbefore⟩ :=
        ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (p.T - start) span seed.activeAtStart seed.coordinatorFirst
          _ selected hmem hselected
      rw [← hrun] at hbirthMem
      obtain ⟨b, hb, hrecord⟩ := List.mem_iff_getElem.mp hbirthMem
      subst birth
      refine ⟨⟨b, hb⟩, ?_, hbirth⟩
      have hbtime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source ⟨b, hb⟩
      have hktime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source k
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b].input.time.val = start + b at hbtime
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val = start + k.val at hktime
      change b ≤ k.val
      exact Nat.le_of_add_le_add_left
        (hbtime.symm.trans_le (htime.trans_le (hbefore.trans_eq hktime)))


private theorem selectionAt_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (P : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (arm : ArmSelection P started time weights x.row) (v : Selection x)
    (hv : selectionAt x P started time weights arm = some v) : v.view.payload = P := by
  classical
  unfold selectionAt at hv
  split at hv
  · exact (congrArg (fun w : Selection x => w.view.payload) (Option.some.inj hv)).symm
  · cases hv

private theorem installation_selected_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) (P : Payload rate)
    (hb : InstallationBirth r P) (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v) : v.view.payload = P := by
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp only [InstallationBirth, hc] at hb
      case chosen installed arm =>
        rcases hb with ⟨rfl, _⟩
        simp only [hc, DispatchCut.selection] at hv
        exact selectionAt_payload _ _ _ _ _ _ _ hv
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [InstallationBirth, hc] at hb
      case laterChosen core consistent started hs instruction hi output hlocal clockData installed arm =>
        rcases hb with ⟨rfl, _⟩
        simp only [hc, DispatchCut.selection] at hv
        exact selectionAt_payload _ _ _ _ _ _ _ hv
  | live a b c outcome => simp only [InstallationBirth, hc] at hb
  | invalidCollectionCutoff => simp only [InstallationBirth, hc] at hb
  | dagger => simp only [InstallationBirth, hc] at hb

/-- Every actual successful choice retains its own whole selected payload
through POST; phase success is derived internally. -/
private theorem complete_selected_post_payload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v) :
    storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.next.coordinator = some v.view.payload := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  change storedPayload r.output.next.coordinator = some v.view.payload
  have he := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 k
  have hn := storedPayload_ne_none_of_phase r.output.next.coordinator he.2.2.2.1 he.2.2.2.2
  have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification r.input
  have hr : ReferenceAssignmentPayloadChronology.actualStepRecord r.input = r := by
    cases r with
    | mk input output houtput => cases houtput; rfl
  have hout : (ReferenceActivePhysicalStep.step r.input).next = r.output.next :=
    congrArg (fun o => o.next) r.output_eq.symm
  rw [hout] at hclass
  rcases hclass with hnone | ⟨old, hold, hpost⟩ | ⟨fresh, hfresh, hpost⟩
  · exact (hn hnone).elim
  · rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth r v hv with hs | hb
    · have hsame := Option.some.inj (hold.symm.trans hs)
      exact hsame ▸ hpost
    · exact complete_installation_stored_payload rate rewards C_star C_h z k _ hb
  · rw [hr] at hfresh
    have hsame := installation_selected_payload r fresh hfresh v hv
    exact hsame.symm ▸ hpost

private theorem complete_live_selected_before_grid
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨a, q, base, started, _hinstalled, valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      (rate := rate) rewards C_star C_h z k v hv hlive
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpost, _hout, hnext, _⟩
  have hnLive : ∃ (a' : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q' : CoordinatorLiveServiceFinish.OwnedRegisters a') (base' : Fin (p.m - 1) → ℕ),
      r.output.next.coordinator = .live a' q' base' := by
    rw [hnext, hpost]
    exact ⟨_, _, _, rfl⟩
  obtain ⟨a', q', base', hn⟩ := hnLive
  have hp := complete_selected_post_payload rate rewards C_star C_h z k v hv
  change storedPayload r.output.next.coordinator = some v.view.payload at hp
  rw [hn] at hp
  have hP : a'.payload = v.view.payload := Option.some.inj hp
  have hclock := (complete_record_clockAt rate rewards C_star C_h z k).2
  change ReferenceCoordinatorClockDomains.clockAt z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) (r.input.time.val + 1) r.output.next at hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hn] at hclock
  rcases hclock with ⟨_, hvalid, hsigma, _, hgrid, _, hbefore, _⟩
  have hg : a'.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val a'.payload.sigma := by
    rw [hgrid, hvalid.1, hsigma]
    rfl
  rw [hg, hP] at hbefore
  exact hbefore


private theorem complete_collection_call_grid
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate) (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (hcall : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] =
      some ⟨P, ledger, started, weights⟩) :
    started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  change ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r = _ at hcall
  have hactual : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  have hclock := (complete_record_clockAt rate rewards C_star C_h z k).1
  change ReferenceCoordinatorClockDomains.clockAt z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) r.input.time.val r.input.state at hclock
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hcall
  split at hcall
  next hfollowers =>
    cases hc : r.input.state.coordinator with
    | first =>
        have hd : r.output.preparation.coordinator = .first (dispatchFirst (firstInput r.input)) := by
          rw [hactual, dispatch_first r.input hc]
        cases ho : dispatchFirst (firstInput r.input) <;> simp only [hd, ho] at hcall
        all_goals contradiction
    | dagger =>
        have hd : r.output.preparation.coordinator = .dagger := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hc]
        simp only [hd] at hcall
        contradiction
    | live a b base =>
        have hd : r.output.preparation.coordinator = .live a b base (dispatchLive (liveInput r.input a b base)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
          rfl
        cases ho : dispatchLive (liveInput r.input a b base) <;> simp only [hd, ho] at hcall
        all_goals try contradiction
        case cutoffChosen dispatched hs newLedger hinit heq hdomain hcut hpending hno arm =>
          split at hcall
          next hpos =>
            cases Option.some.inj hcall
            simp only [ReferenceCoordinatorClockDomains.clockAt, hc] at hclock
            rcases hclock with ⟨_, hvalid, hsigma, _, _, _, _, _⟩
            rw [hcut]
            change a.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val a.payload.sigma
            rw [hvalid.1, hsigma]
            rfl
          next => contradiction
    | collection old oldLedger saved =>
        by_cases hcut : 1 ≤ oldLedger.cutoff ∧ oldLedger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨oldLedger.cutoff - 1, by omega⟩
          let clock := collectionClock old oldLedger saved cutoff
          let x := collectionInput r.input old oldLedger clock cutoff
          have hd : r.output.preparation.coordinator =
              .collection old oldLedger clock cutoff (dispatchCollection x) := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
            rfl
          cases ho : dispatchCollection x <;> simp only [hd, ho] at hcall
          all_goals try contradiction
          case continuing core snapshot boundary checked =>
            cases Option.some.inj hcall
            rw [snapshot.clockStarted_frame.1]
            have hvalid := core.clock_registers_valid
            have hsigma := core.clock_sigma_eq
            change CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock at hvalid
            change clock.sigma = some P.sigma at hsigma
            change clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma
            rw [hvalid.1, hsigma]
            rfl
        · have hd : r.output.preparation.coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_right hcut]
          simp only [hd] at hcall
          contradiction
  next => contradiction

/-- Every actual raw cell uses the same selected payload, its canonical
all-arm rates, and its operative clipped grid endpoint. The Boolean identity
is valid on disabled dates as well as enabled zero-arrival dates. -/
theorem complete_cell_geometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (v : Selection R[k.val].input) (b : Fin R.length),
      R[k.val].output.preparation.coordinator.selection = some v ∧
      b.val ≤ k.val ∧ InstallationBirth R[b.val] v.view.payload ∧
      c.rate = v.view.payload.rate ∧
      (c.enabled = true ↔ R[k.val].input.time.val + 1 <
        FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]
  cases hd : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some d =>
    have hcd : c = d := by
      have h := hc
      change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or _ = some c at h
      rw [hd] at h
      exact (Option.some.inj h).symm
    subst d
    have hlive := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain 0 r).mp (by rw [hd]; rfl)
    obtain ⟨hen, v, hv, _, hrate, _⟩ := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hd
    obtain ⟨v', hv', _, hactive, _⟩ := hlive
    have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    obtain ⟨b, hbk, hb⟩ := complete_selected_payload_birth rate rewards C_star C_h z k v hv
    refine ⟨v, b, hv, hbk, hb, hrate, ?_⟩
    have hbefore := complete_live_selected_before_grid rate rewards C_star C_h z k v hv hactive
    exact ⟨fun _ => hbefore, fun _ => hen⟩
  | none =>
    have hd : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
      have h := hc
      change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r) = some c at h
      rw [hd] at h
      exact h
    obtain ⟨P, ledger, started, weights, out, hcall, htail, _hrun, _hen, hflag, hrate, _⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hd
    have hgrid := complete_collection_call_grid rate rewards C_star C_h z k P ledger started weights hcall
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp
      ((ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h z).1 k).2.1
    have hselected := complete_selected_post_payload rate rewards C_star C_h z k v hv
    have hframe := collectionPostChoice_payload_frame r.output.preparation P ledger started weights
    have hn : r.output.next.coordinator = r.output.coordinator.configuration := by rw [r.output_eq]; rfl
    have hdiag : r.output.coordinator = collectionPostChoice r.output.preparation P ledger started weights := htail
    have hout : storedPayload r.output.next.coordinator = none ∨
        storedPayload r.output.next.coordinator = some P := by
      rw [hn, hdiag]
      exact hframe
    have hP : v.view.payload = P := by
      rcases hout with hnone | hP
      · rw [hselected] at hnone
        cases hnone
      · exact Option.some.inj (hselected.symm.trans hP)
    obtain ⟨b, hbk, hb⟩ := complete_selected_payload_birth rate rewards C_star C_h z k v hv
    refine ⟨v, b, hv, hbk, hb, hrate.trans (congrArg (fun X : Payload rate => X.rate) hP).symm, ?_⟩
    rw [hflag, hgrid, hP, decide_eq_true_eq]


/-- Literal one-based episode membership, including the final round when the
endpoint is clipped at `T+1`. -/
def EpisodeCovers {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) (q : Fin p.T) : Prop :=
  IsEpisodeAnchorBirth r ∧ r.input.time.val ≤ q.val ∧
    q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val r.input.time

private theorem complete_cell_present
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ∃ c, ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hp := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z k).2
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some c => exact ⟨c, by change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or _ = _; rw [hl]; rfl⟩
  | none =>
      rcases hp with hp | ⟨c, hc⟩
      · have hs := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain 0 r).mpr hp
        rw [hl] at hs
        cases hs
      · exact ⟨c, by change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or _ = _; rw [hl]; exact hc⟩

/-- Actual installation provenance, obtained from the same complete original
word's restoration theorem without a supplied origin or correctness premise. -/
private theorem complete_installation_episode_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (P : Payload rate)
    (hb : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (rho : Fin R.length) (P_rho : Payload rate), rho.val ≤ b.val ∧
      InstallationBirth R[rho.val] P_rho ∧ IsEpisodeAnchorBirth R[rho.val] ∧
      P.anchor = P_rho.anchor ∧ R[rho.val].input.time = P_rho.sigma ∧
      P_rho.sigma.val ≤ P.sigma.val ∧
      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
        FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
  obtain ⟨hc, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z b
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate z rewards C_star C_h hc
  have hr := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z
  rw [hlaunch] at hr
  obtain ⟨L, _, _, _, _, hbirths, _⟩ := hr
  obtain ⟨rho, P_rho, hle, hbirth, hepisode, _, _, hanchor, _, htime, hstart, hgrid, _⟩ := hbirths b P hb
  exact ⟨rho, P_rho, hle, hbirth, hepisode, hanchor, htime, hstart, hgrid⟩

/-- Every enabled raw cell has a real original episode origin, the SAME
selected anchor, canonical all-arm recording rates and operative endpoint. -/
private theorem complete_enabled_cell_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c)
    (hen : c.enabled = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (rho : Fin R.length) (P_rho : Payload rate) (v : Selection R[k.val].input),
      InstallationBirth R[rho.val] P_rho ∧ EpisodeCovers R[rho.val] R[k.val].input.time ∧
      R[k.val].output.preparation.coordinator.selection = some v ∧
      v.view.payload.anchor = P_rho.anchor ∧
      (∀ i, c.rate i = CanonicalRecordingRates.xi p rate.eta.val P_rho.anchor i) ∧
      FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma =
        FollowerCutoffScan.gridBoundary p rate.eta.val R[rho.val].input.time := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨v, b, hv, hbk, hb, hrate, hflag⟩ := complete_cell_geometry rate rewards C_star C_h z k c hc
  obtain ⟨rho, P_rho, hrb, hroot, hepisode, hanchor, htime, _hstart, hgrid⟩ :=
    complete_installation_episode_origin rate rewards C_star C_h z b v.view.payload hb
  have hrk : rho.val ≤ k.val := hrb.trans hbk
  have htroot := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  have htcurrent := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k
  have hbefore := hflag.mp hen
  refine ⟨rho, P_rho, v, hroot, ⟨hepisode, ?_, ?_⟩, hv, hanchor, ?_, ?_⟩
  · omega
  · rw [htime, hgrid]
    exact hbefore
  · intro i
    rw [hrate, AssignmentStartPayload.Input.rate_eq_canonical, hanchor]
  · rw [htime, hgrid]

/-- An original episode interval forces enablement of every actual raw cell
on that interval. This includes retained collection with zero arrivals. -/
private theorem complete_cell_enabled_of_episode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rho k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c)
    (hcover : EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[rho.val]
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time) :
    c.enabled = true := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨P, hb, _⟩ := episode_birth_payload_unique R[rho.val] hcover.1
  have htime : P.sigma = R[rho.val].input.time :=
    Fin.ext (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ P hb)
  obtain ⟨v, b, hv, _hbk, _hbv, _hrate, hflag⟩ := complete_cell_geometry rate rewards C_star C_h z k c hc
  apply hflag.mpr
  have hrootbound : R[k.val].input.time.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma := by
    rw [htime]
    exact hcover.2.2
  rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth R[k.val] v hv with hstored | hfresh
  · have ht1 := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
    have ht2 := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k
    have hle : rho.val ≤ k.val := by have h := hcover.2.1; omega
    by_cases heq : rho = k
    · subst rho
      have hP := installation_selected_payload R[k.val] P hb v hv
      rw [hP]
      exact hrootbound
    · have hlt : rho.val < k.val := by
        have hne : rho.val ≠ k.val := fun h => heq (Fin.ext h)
        omega
      have hPQ := complete_earlier_birth_le_stored_sigma rate rewards C_star C_h z rho k P v.view.payload hlt hb hstored
      exact hrootbound.trans_le (gridBoundary_mono rate P.sigma v.view.payload.sigma hPQ)
  · have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[k.val] v.view.payload hfresh
    have hbound := (FollowerCutoffScan.gridBoundary_bounds p rate.eta.val rate.eta.property rate.sourceCap v.view.payload.sigma).1
    simpa only [ht] using hbound

/-- The nominal original schedule is exactly the disjoint union of actual
first/renewal episode intervals. No future call or pre-overflow condition is
an input, and `q.val+1` is the source round. -/
theorem nominalEnabled_iff_unique_episode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T) :
    ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h q z = true ↔
      ∃! rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length,
        EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] q := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  constructor
  · intro hen
    unfold ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled at hen
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
    | none => simp only [hr, Option.bind_none, Option.any_none, Bool.false_eq_true] at hen
    | some r =>
      cases hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r with
      | none => simp only [hr, Option.bind_some, hc, Option.any_none, Bool.false_eq_true] at hen
      | some c =>
        have hcen : c.enabled = true := by simpa only [hr, Option.bind_some, hc, Option.any_some] using hen
        obtain ⟨k, _, hkr, _⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h q z r hr
        have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1
        obtain ⟨rho, P, v, _hb, hcover, _⟩ := complete_enabled_cell_origin rate rewards C_star C_h z k c (by rw [hkr]; exact hc) hcen
        rw [hkr, ht] at hcover
        refine ⟨rho, hcover, ?_⟩
        intro other hother
        exact complete_episode_interval_at_most_one rate rewards C_star C_h z q other rho hother hcover
  · rintro ⟨rho, hcover, _⟩
    have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
    have hs : s ≤ q.val := by
      have h := hcover.2.1
      rw [htime] at h
      exact (Nat.le_add_right _ _).trans h
    have hlen : R.length = p.T - s := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    let k : Fin R.length := ⟨q.val - s, by rw [hlen]; omega⟩
    have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some R[k.val] := by
      unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
      rw [ite_eq_left hs]
      exact List.getElem?_eq_getElem k.isLt
    have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z R[k.val] hr).2.2.1
    obtain ⟨c, hc⟩ := complete_cell_present rate rewards C_star C_h z k
    have hen := complete_cell_enabled_of_episode rate rewards C_star C_h z rho k c hc (by rw [ht]; exact hcover)
    rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled, hr]
    change (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[k.val]).any
      RecordedQueueRun.RoundInput.enabled = true
    change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[k.val] = some c at hc
    rw [hc]
    exact hen


private theorem finishRound_grid_frame
    (eta : ℝ) (t : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (row : CompletePublicTable.CompleteRow p)
    (result : CoordinatorPhaseClock.FinishRoundResult p)
    (h : CoordinatorPhaseClock.finishRound p eta t clock pending row = .ok result) :
    result.clock.g = clock.g := by
  simp only [CoordinatorPhaseClock.finishRound] at h
  repeat' split at h
  all_goals cases h
  all_goals rfl

private theorem complete_live_selection_grid
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time) :
    v.started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨a, q, base, started, _hinstalled, valid, o, serviced, pending, finished, h⟩ :=
    ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
      (rate := rate) rewards C_star C_h z k v hv hlive
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, hinput, _, _, _, _, _, _, _, _, _, _, _, hfinish, hpost, _hout, hnext, _⟩
  have hp := complete_selected_post_payload rate rewards C_star C_h z k v hv
  change storedPayload r.output.next.coordinator = some v.view.payload at hp
  rw [hnext, hpost] at hp
  have hP : a.payload = v.view.payload := Option.some.inj hp
  have hclock := (complete_record_clockAt rate rewards C_star C_h z k).2
  change ReferenceCoordinatorClockDomains.clockAt z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) (r.input.time.val + 1) r.output.next at hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt] at hclock
  rw [hnext, hpost] at hclock
  rcases hclock with ⟨_, hvalid, hsigma, _, _, _, _, _⟩
  have hg : finished.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val a.payload.sigma := by
    rw [hvalid.1, hsigma]
    rfl
  have hin := congrArg (fun x : CoordinatorRecordingOperation.Input p => x.gridBoundary) hinput
  change v.started.clock.g = started.clock.g at hin
  have hf := finishRound_grid_frame rate.eta.val r.input.time started.clock pending r.input.row finished hfinish
  exact hin.trans (hf.symm.trans (hg.trans (congrArg (FollowerCutoffScan.gridBoundary p rate.eta.val) (congrArg (fun X : Payload rate => X.sigma) hP))))

private theorem collectionCall_selection
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) (P : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (hcall : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r = some ⟨P, ledger, started, weights⟩)
    (v : Selection r.input) (hv : r.output.preparation.coordinator.selection = some v) :
    v.view.payload = P ∧ v.started = started := by
  classical
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hcall
  split at hcall
  next =>
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hc] at hcall <;> contradiction
    | collection old oldLedger clock cutoff outcome =>
      cases outcome <;> simp only [hc] at hcall
      all_goals try contradiction
      case continuing core snapshot boundary checked =>
        cases Option.some.inj hcall
        simp only [hc, DispatchCut.selection] at hv
        cases Option.some.inj hv
        exact ⟨rfl, rfl⟩
    | live a b base outcome =>
      cases outcome <;> simp only [hc] at hcall
      all_goals try contradiction
      case cutoffChosen dispatched hs newLedger hi he hd hclock hp hn arm =>
        split at hcall
        next =>
          cases Option.some.inj hcall
          simp only [hc, DispatchCut.selection, selectionAt] at hv
          cases Option.some.inj hv
          exact ⟨rfl, rfl⟩
        next => contradiction
    | invalidCollectionCutoff => simp only [hc] at hcall; contradiction
    | dagger => simp only [hc] at hcall; contradiction
  next => contradiction

/-- The operative pre-choice clock of every actual selected call has exactly
the clipped endpoint derived from its own selected payload. -/
theorem complete_selected_gridBoundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v) :
    v.started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  rcases (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z k).2 with ⟨v', hv', _, hlive, _⟩ | ⟨c, hc⟩
  · have he : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    exact complete_live_selection_grid rate rewards C_star C_h z k v hv hlive
  · obtain ⟨P, ledger, started, weights, out, hcall, _⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hc
    obtain ⟨hP, hs⟩ := collectionCall_selection r P ledger started weights hcall v hv
    rw [hs, hP]
    exact complete_collection_call_grid rate rewards C_star C_h z k P ledger started weights hcall

/-- Source-calendar version of the operative endpoint identity. -/
private theorem actualRecord_selected_gridBoundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T)
    (r : RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r)
    (v : Selection r.input) (hv : r.output.preparation.coordinator.selection = some v) :
    v.started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma := by
  obtain ⟨k, _, he, _⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h q z r hr
  have h := complete_selected_gridBoundary rate rewards C_star C_h z k
  rw [he] at h
  exact h v hv

/-- The unique interval's raw original cell and payload, with source-only
before-choice provenance and no stochastic-law input. -/
theorem nominalEnabled_episode_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T)
    (hen : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h q z = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (rho : Fin R.length) (P_rho : Payload rate)
      (r : RoundRecord (p := p) (rate := rate)) (c : RecordedQueueRun.RoundInput p.K)
      (v : Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧ c.enabled = true ∧
      EpisodeCovers R[rho.val] q ∧ (∀ j, EpisodeCovers R[j.val] q → j = rho) ∧
      InstallationBirth R[rho.val] P_rho ∧ (∀ P, InstallationBirth R[rho.val] P → P = P_rho) ∧
      IsEpisodeStartBeforeChoice R[rho.val] ∧ r.output.preparation.coordinator.selection = some v ∧
      v.view.payload.anchor = P_rho.anchor ∧
      (∀ i, c.rate i = CanonicalRecordingRates.xi p rate.eta.val P_rho.anchor i) ∧
      FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma =
        FollowerCutoffScan.gridBoundary p rate.eta.val R[rho.val].input.time ∧
      v.started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val R[rho.val].input.time := by
  classical
  have h := hen
  unfold ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled at h
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
  | none => simp only [hr, Option.bind_none, Option.any_none, Bool.false_eq_true] at h
  | some r =>
    cases hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r with
    | none => simp only [hr, Option.bind_some, hc, Option.any_none, Bool.false_eq_true] at h
    | some c =>
      have hcen : c.enabled = true := by simpa only [hr, Option.bind_some, hc, Option.any_some] using h
      obtain ⟨k, _, hkr, _⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h q z r hr
      have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z r hr).2.2.1
      obtain ⟨rho, P, v, hb, hcover, hv, hanchor, hrates, hgrid⟩ :=
        complete_enabled_cell_origin rate rewards C_star C_h z k c (by rw [hkr]; exact hc) hcen
      rw [hkr, ht] at hcover
      have hbefore := (complete_episode_birth_iff_before_choice rate rewards C_star C_h z rho).mp hcover.1
      have hdata : ∃ v : Selection r.input, r.output.preparation.coordinator.selection = some v ∧
          v.view.payload.anchor = P.anchor ∧
          FollowerCutoffScan.gridBoundary p rate.eta.val v.view.payload.sigma =
            FollowerCutoffScan.gridBoundary p rate.eta.val
              (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val].input.time := by
        rw [← hkr]
        exact ⟨v, hv, hanchor, hgrid⟩
      obtain ⟨v, hv, hanchor, hgrid⟩ := hdata
      exact ⟨rho, P, r, c, v, rfl, hc, hcen, hcover,
        fun j hj => complete_episode_interval_at_most_one rate rewards C_star C_h z q j rho hj hcover,
        hb, fun P' hP' => ReferenceAssignmentPayloadChronology.installationBirth_payload_unique _ P' P hP' hb,
        hbefore, hv, hanchor, hrates, hgrid,
        (actualRecord_selected_gridBoundary rate rewards C_star C_h z q r hr v hv).trans hgrid⟩

/-- A record index itself supplies a genuine launch; no launch event is an
extra premise of the chronology interface. -/
theorem complete_record_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active := by
  obtain ⟨hc, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
  exact ⟨_, ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate z rewards C_star C_h hc⟩

/-- Before overflow, the unique episode's physical anchor is the weight of
its SAME stopped strict original prefix. Earlier PRE-clear is derived from the
current prefix. Physical continuation after overflow is not identified with
logical stopped weights. -/
theorem complete_episode_pre_clear_restoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T)
    (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hcover : EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] q)
    (hb : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] P) :
    let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z
      (complete_record_launch rate rewards C_star C_h z rho)
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let n := q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    (RecordedQueueRun.run Q (W.take n)).overflow = false →
      (RecordedQueueRun.run Q (W.take rho.val)).overflow = false ∧
      P.anchor = RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take rho.val)) ∧
      (fun i => RecordedQueueSummation.runMarginal Q p.m W n i) =
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take n))) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let hl := complete_record_launch rate rewards C_star C_h z rho
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z hl
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let n := q.val - s
  intro hclear
  change (RecordedQueueRun.run Q (W.take n)).overflow = false at hclear
  have hlen : W.length = R.length := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length rate rewards C_star C_h z hl
  have hRlen : R.length = p.T - s := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  have hs : s ≤ q.val := by
    have h := hcover.2.1
    rw [ht] at h
    exact (Nat.le_add_right _ _).trans h
  have hrn : rho.val ≤ n := by
    have h := hcover.2.1
    rw [ht] at h
    change s + rho.val ≤ q.val at h
    dsimp only [n]
    omega
  have hn : n ≤ W.length := by rw [hlen, hRlen]; dsimp only [n]; omega
  have hfirst : n < UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W := by
    by_contra hnot
    have h := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le Q W n hn).mpr (Nat.le_of_not_gt hnot)
    rw [hclear] at h
    cases h
  have hrootclear : (RecordedQueueRun.run Q (W.take rho.val)).overflow = false := by
    cases hf : (RecordedQueueRun.run Q (W.take rho.val)).overflow with
    | false => rfl
    | true =>
      have h := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le Q W rho.val (hrn.trans hn)).mp hf
      omega
  have hrestore := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration rate rewards C_star C_h z
  rw [Classical.choose_spec hl] at hrestore
  obtain ⟨L, _, _, hfull, _, hbirths, _hbranches, _hweights⟩ := hrestore
  have hLW : L = W := Option.some.inj (hfull.symm.trans
    (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z hl))
  obtain ⟨root, P0, hle, hb0, hepisode, _, _, hanchor, hpow, htime, _hstart, hgrid, _⟩ := hbirths rho P hb
  have hPtime : P.sigma = R[rho.val].input.time :=
    Fin.ext (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ P hb)
  have hself : EpisodeCovers R[rho.val] R[rho.val].input.time :=
    ⟨hcover.1, le_rfl, (FollowerCutoffScan.gridBoundary_bounds p rate.eta.val rate.eta.property rate.sourceCap _).1⟩
  have hrootcover : EpisodeCovers R[root.val] R[rho.val].input.time := by
    refine ⟨hepisode, ?_, ?_⟩
    · have ht0 := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z root
      rw [ht0, ht]
      exact Nat.add_le_add_left hle _
    · rw [htime, hgrid, hPtime]
      exact hself.2.2
  have hroot : root = rho := complete_episode_interval_at_most_one rate rewards C_star C_h z _ root rho hrootcover hself
  have hanchorWord : P.anchor = fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate W i rho.val).1 := by
    funext i
    rw [hanchor, hpow i, hLW, hroot]
  have hnumroot := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_numericalPrefix rate rewards C_star C_h z hl rho.val (hrn.trans hn)
  have hnumcurrent := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_numericalPrefix rate rewards C_star C_h z hl n hn
  change _ ∧ P.anchor = RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take rho.val)) ∧ _
  refine ⟨hrootclear, ?_, ?_⟩
  · rw [hnumroot.2.1, Nat.min_eq_left (by omega : rho.val ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W)]
    exact hanchorWord
  · rw [hnumcurrent.2.1]
    exact hnumcurrent.2.2



/-- FIRST is reached only at the finite launch record, the zeroth original
suffix index. Subsequent records cannot silently restart initialization. -/
private theorem complete_input_first_iff_initial_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.coordinator = .first ↔ k.val = 0 := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  constructor
  · intro hfirst
    by_contra hnot
    have hk : 0 < k.val := Nat.pos_of_ne_zero hnot
    have hlen : k.val < R.length := k.isLt
    have hi : k.val - 1 + 1 < R.length := by omega
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z (k.val - 1) hi
    have he := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 ⟨k.val - 1, by omega⟩
    have hadj' : R[k.val].input.state = R[k.val - 1].output.next := by
      simpa only [Nat.sub_add_cancel hk] using hadj
    change R[k.val].input.state.coordinator = .first at hfirst
    rw [hadj'] at hfirst
    exact he.2.2.2.1 hfirst
  · intro hk
    rcases k with ⟨n, hn⟩
    dsimp only at hk
    subst n
    obtain ⟨hc, span, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z ⟨0, hn⟩
    simp only [List.get_eq_getElem] at hr
    rw [hr]
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt, ReferenceActivePhysicalHorizon.roundInputAt]
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hm : allActiveAtStart initial start :=
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc).activeAtStart
    have hs0 : start + 0 ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      exact Nat.le_trans (Nat.le_of_eq (Nat.add_zero start)) hs
    change (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start 0 hs0 hm).finalState.coordinator = .first
    have hz := ReferenceActivePhysicalHorizon.run_zero_final initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start hs0 hm
    exact (congrArg ReferenceActivePhysicalStep.State.coordinator hz).trans
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc).coordinatorFirst

/-- Before any current draw, the original record starts an episode exactly
at finite launch, or at an incoming empty collection whose old freeze is
reached. A corrected call before that freeze is excluded by this equivalence. -/
theorem complete_episode_birth_iff_launch_or_renewal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    IsEpisodeAnchorBirth r ↔ k.val = 0 ∨ ∃ (P : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
      r.input.state.coordinator = .collection P ledger saved ∧ ledger.pending = ∅ ∧
        ledger.freezeAt ≤ r.input.time.val + 1 := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hbase : IsEpisodeAnchorBirth r ↔ IsEpisodeStartBeforeChoice r :=
    complete_episode_birth_iff_before_choice rate rewards C_star C_h z k
  dsimp only
  rw [hbase]
  constructor
  · intro hbefore
    cases hc : r.input.state.coordinator with
    | first => exact Or.inl ((complete_input_first_iff_initial_index rate rewards C_star C_h z k).mp hc)
    | live a b base => simp only [IsEpisodeStartBeforeChoice, hc] at hbefore
    | dagger => simp only [IsEpisodeStartBeforeChoice, hc] at hbefore
    | collection P ledger saved =>
      exact Or.inr ⟨P, ledger, saved, rfl, by simpa only [IsEpisodeStartBeforeChoice, hc] using hbefore⟩
  · rintro (hk | ⟨P, ledger, saved, hc, hp, hg⟩)
    · have hc := (complete_input_first_iff_initial_index rate rewards C_star C_h z k).mpr hk
      change r.input.state.coordinator = .first at hc
      simp only [IsEpisodeStartBeforeChoice, hc]
    · change r.input.state.coordinator = .collection P ledger saved at hc
      exact (show IsEpisodeStartBeforeChoice r from by
        simpa only [IsEpisodeStartBeforeChoice, hc] using And.intro hp hg)

end Bandits.Support.ReferenceOriginalCalendarEpisodeChronology

end
