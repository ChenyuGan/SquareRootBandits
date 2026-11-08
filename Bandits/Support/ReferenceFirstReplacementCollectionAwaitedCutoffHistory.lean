/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedWaitingCost
public import Bandits.Support.ReferenceFirstCollectionAwaitedCutoffHistory

/-!
# First replacement issued-cutoff history

The strict-past replacement-live observer is intersected with the actual
incoming LIVE clock's pre-choice initialization command. Failed issued commands
remain events. The stopping history bounds only the existing supported waiting
charge, under its original source law. The source-prefix filtration is the
existing analysis filtration, not manuscript Gminus/Gplus or a conditional
coupling assertion. Whole stopped physical collection
coverage is a separate obligation for
`ReferenceFirstReplacementCollectionStoppedChargeDomination`.

Sources: ZIP4 `06_interruptions.tex:9-14,37-70,246-296,431-437,459-487` and
`appendix_a_local_protocol.tex:28-85`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open ReferenceSourcePrefixHistoryFiltration PhaseStartConditionalWaiting
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCutoffHistory

variable {p : ConstructorDimensions.Parameters}

/-- Exactly the strict-past tag of the existing observer, without a future
birth, cutoff or collection-window query. -/
def replacementMarker
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  (ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary
    (ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h t.val z)).1 = 2

/-- The command is queried before arm choice, on the SAME incoming source
record. No successful initializer or choice is required. -/
def replacementIssuedAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  replacementMarker rate rewards C_star C_h t z ∧
    ReferenceFirstCollectionAwaitedCutoffHistory.issuedAt rate rewards C_star C_h t z

/-- The marker retains the complete original installed payload. -/
theorem replacementMarker_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    replacementMarker rate rewards C_star C_h t z ↔
      ∃ payload, ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h t.val z = .replacementLive payload := by
  unfold replacementMarker
  cases ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
    rate rewards C_star C_h t.val z <;>
    simp [ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary]

/-- Adaptation uses countable summary coordinates; the continuous payload is
never equipped with a discrete measurable space. -/
theorem replacementMarker_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | replacementMarker rate rewards C_star C_h t z} := by
  exact (ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary_measurable
    rate rewards C_star C_h control0 t.val).fst (measurableSet_singleton 2)

/-- Both tests consult the existing pre-round source-prefix history. -/
theorem replacementIssuedAt_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | replacementIssuedAt rate rewards C_star C_h t z} := by
  exact (replacementMarker_measurable rate rewards C_star C_h control0 t).inter
    (ReferenceFirstCollectionAwaitedCutoffHistory.issuedAt_measurable
      rate rewards C_star C_h control0 t)

/-- The literal finite calendar of replacement-marked issued commands. -/
def replacementIssuedDateIndices
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  Finset.univ.filter fun t => replacementIssuedAt rate rewards C_star C_h t z

/-- The first replacement-marked issued collection command, with the source-horizon sentinel
when no command occurs. -/
def S_repl
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty then
    ((replacementIssuedDateIndices rate rewards C_star C_h z).min' h).val + 1
  else p.T + 1

theorem mem_replacementIssuedDateIndices_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) :
    t ∈ replacementIssuedDateIndices rate rewards C_star C_h z ↔
      replacementIssuedAt rate rewards C_star C_h t z := by
  simp [replacementIssuedDateIndices]

theorem replacementIssuedAt_implies_S_repl_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (ht : replacementIssuedAt rate rewards C_star C_h t z) :
    S_repl rate rewards C_star C_h z ≤ t.val + 1 := by
  classical
  have hmem : t ∈ replacementIssuedDateIndices rate rewards C_star C_h z :=
    (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z t).2 ht
  have hne : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty := ⟨t, hmem⟩
  rw [S_repl, dite_eq_left hne]
  have hmin := Finset.min'_le (replacementIssuedDateIndices rate rewards C_star C_h z) t hmem
  exact Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hmin) 1

theorem S_repl_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ S_repl rate rewards C_star C_h z ∧ S_repl rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  by_cases h : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty
  · rw [S_repl, dite_eq_left h]
    let t := (replacementIssuedDateIndices rate rewards C_star C_h z).min' h
    have ht := t.isLt
    exact ⟨by omega, by omega⟩
  · rw [S_repl, dite_eq_right h]
    exact ⟨by omega, le_rfl⟩

theorem S_repl_eq_horizon_sentinel_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    S_repl rate rewards C_star C_h z = p.T + 1 ↔
      ∀ t, ¬ replacementIssuedAt rate rewards C_star C_h t z := by
  classical
  constructor
  · intro hS t ht
    have hle := replacementIssuedAt_implies_S_repl_le rate rewards C_star C_h z t ht
    have htT := t.isLt
    omega
  · intro hnone
    rw [S_repl]
    split
    · next hne =>
        obtain ⟨t, ht⟩ := hne
        exact False.elim (hnone t
          ((mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z t).1 ht))
    · rfl

theorem S_repl_eq_horizon_sentinel_of_no_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h p.T z) :
    S_repl rate rewards C_star C_h z = p.T + 1 := by
  apply (S_repl_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
  intro t ht
  rcases ht.2 with ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hr
    cases hr
  have ht := t.isLt
  rcases hlaunch with ⟨hc, hstart⟩
  exact hno ⟨hc, by omega⟩

theorem S_repl_eq_horizon_sentinel_of_terminal_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    S_repl rate rewards C_star C_h z = p.T + 1 := by
  apply (S_repl_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
  intro t ht
  rcases ht.2 with ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩
  have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_terminal_start
    rate rewards C_star C_h t z hterminal
  rw [hnone] at hr
  cases hr


/-- Exact first-date characterization: the command occurs at `t` and no
earlier calendar date has issued one. -/
theorem S_repl_eq_date_iff_first_issued
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) :
    S_repl rate rewards C_star C_h z = t.val + 1 ↔
      replacementIssuedAt rate rewards C_star C_h t z ∧
        ∀ u : Fin p.T, u.val < t.val → ¬ replacementIssuedAt rate rewards C_star C_h u z := by
  classical
  constructor
  · intro hS
    have hne : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty := by
      by_contra hne
      have hsent : S_repl rate rewards C_star C_h z = p.T + 1 := by simp [S_repl, hne]
      have ht := t.isLt
      omega
    let m := (replacementIssuedDateIndices rate rewards C_star C_h z).min' hne
    have hmS : m.val + 1 = t.val + 1 := by
      have hm : S_repl rate rewards C_star C_h z = m.val + 1 := by simp [S_repl, hne, m]
      omega
    have hmEq : m = t := Fin.ext (by omega)
    have hmIssued := (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z m).1
      (Finset.min'_mem (replacementIssuedDateIndices rate rewards C_star C_h z) hne)
    rw [hmEq] at hmIssued
    refine ⟨hmIssued, ?_⟩
    intro u hut hu
    have huMem := (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z u).2 hu
    have hmLe := Finset.min'_le (replacementIssuedDateIndices rate rewards C_star C_h z) u huMem
    have hmLe' : t ≤ u := hmEq ▸ hmLe
    exact (not_le_of_gt hut) (Fin.le_iff_val_le_val.mp hmLe')
  · rintro ⟨htIssued, hnoEarlier⟩
    have hne : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty :=
      ⟨t, (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z t).2 htIssued⟩
    rw [S_repl, dite_eq_left hne]
    have hmin := Finset.min'_mem (replacementIssuedDateIndices rate rewards C_star C_h z) hne
    have hminIssued := (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z _).1 hmin
    have hminLe := Finset.min'_le (replacementIssuedDateIndices rate rewards C_star C_h z) t
      ((mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z t).2 htIssued)
    have hminEq : (replacementIssuedDateIndices rate rewards C_star C_h z).min' hne = t := by
      apply Fin.ext
      by_contra hneVal
      have hlt : ((replacementIssuedDateIndices rate rewards C_star C_h z).min' hne).val < t.val := by
        have := Fin.le_iff_val_le_val.mp hminLe
        omega
      exact hnoEarlier _ hlt hminIssued
    rw [hminEq]

/-- The first issued cutoff is a pre-round stopping time in the original
source-prefix filtration. -/
theorem S_repl_is_pre_round_stopping_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (S_repl rate rewards C_star C_h) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  change ∀ v, MeasurableSet[F v] {z | S_repl rate rewards C_star C_h z ≤ v}
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z | S_repl rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hpos := (S_repl_bounds rate rewards C_star C_h z).1
      omega
    rw [heq]
    exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p) (F 0)
  · by_cases hvT : p.T + 1 ≤ v
    · have heq : {z | S_repl rate rewards C_star C_h z ≤ v} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact le_trans (S_repl_bounds rate rewards C_star C_h z).2 hvT
      rw [heq]
      exact MeasurableSet.univ
    · have hvle : v ≤ p.T := by omega
      have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
          S_repl rate rewards C_star C_h z ≤ v} =
          ⋃ t : Fin p.T,
            {z | t.val + 1 ≤ v ∧ replacementIssuedAt rate rewards C_star C_h t z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro hSv
          have hne : (replacementIssuedDateIndices rate rewards C_star C_h z).Nonempty := by
            by_contra hne
            have hsent : S_repl rate rewards C_star C_h z = p.T + 1 := by simp [S_repl, hne]
            rw [hsent] at hSv
            omega
          let t := (replacementIssuedDateIndices rate rewards C_star C_h z).min' hne
          have hmem := Finset.min'_mem (replacementIssuedDateIndices rate rewards C_star C_h z) hne
          have hissued := (mem_replacementIssuedDateIndices_iff rate rewards C_star C_h z t).1 hmem
          have hS : S_repl rate rewards C_star C_h z = t.val + 1 := by simp [S_repl, hne, t]
          exact ⟨t, by rw [hS] at hSv; omega, hissued⟩
        · rintro ⟨t, htv, htIssued⟩
          exact (replacementIssuedAt_implies_S_repl_le rate rewards C_star C_h z t htIssued).trans htv
      rw [hset]
      apply MeasurableSet.iUnion
      intro t
      by_cases htv : t.val + 1 ≤ v
      · have hmono : F (t.val + 1) ≤ F v := F.mono (by omega)
        have hi := replacementIssuedAt_measurable rate rewards C_star C_h control0 t
        simpa [htv] using
          hmono {z | replacementIssuedAt rate rewards C_star C_h t z} hi
      · simp [htv]



/-- No actual replacement birth can produce a replacement marker. This
uses only the original observer recursion, including absent records. -/
theorem S_repl_eq_horizon_sentinel_of_no_replacement_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ∀ (t : Fin p.T)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      actualRecord rate rewards C_star C_h t z = some r →
        ReferenceFirstReplacementCollectionPendingFoundation.birthPayload r = none) :
    S_repl rate rewards C_star C_h z = p.T + 1 := by
  have hphase : ∀ n,
      ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h n z = .firstLive ∨
      ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h n z = .firstCollection := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase]
        split
        · rename_i hn
          cases hr : actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
          | none => exact ih
          | some r =>
              have hb := hno ⟨n, hn⟩ r hr
              rcases ih with h | h
              · rw [h]
                dsimp only [ReferenceFirstReplacementCollectionPendingFoundation.advance]
                split
                · exact Or.inr rfl
                · exact Or.inl rfl
              · rw [h]
                dsimp only [ReferenceFirstReplacementCollectionPendingFoundation.advance]
                rw [hb]
                exact Or.inr rfl
        · exact ih
  apply (S_repl_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
  intro t ht
  have hm := ht.1
  rcases hphase t.val with h | h <;>
    simp [replacementMarker, h,
      ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at hm

/-- Absence of marked live dates gives the same exact sentinel. -/
theorem S_repl_eq_horizon_sentinel_of_no_marker
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ∀ t, ¬ replacementMarker rate rewards C_star C_h t z) :
    S_repl rate rewards C_star C_h z = p.T + 1 := by
  exact (S_repl_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
    (fun t ht => hno t ht.1)

/-- Recover the command from an equality with the computed dispatcher,
retaining the raw cutoff dispatch and checked-initialization equations. -/
private theorem dispatchLive_cutoff_command
    (input : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output input.registers
      input.ownedRegisters input.followerBaseScore)
    (hs ledger hi he hd hc hp hn selection)
    (h : CoordinatorRoundDispatch.dispatchLive input =
      .cutoffChosen out hs ledger hi he hd hc hp hn selection) :
    out.startResult.ledgerCommand = some (.initializeAt input.registers.time) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive at h
  dsimp only at h
  split at h
  · cases h
  · rename_i actual hactual
    have hstart := CoordinatorRoundDispatch.cutoffDispatch_startResult_eq
      input.registers input.ownedRegisters input.followerBaseScore actual hactual
    split at h
    · cases h
    · cases h
    · have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame input.registers actual.startResult := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hframe] at h
      have hpayload : input.registers.priorClock.sigma = some input.registers.payload.sigma := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hpayload] at h
      have hgrid : input.registers.gridBoundary = input.registers.priorClock.g := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hgrid] at h
      have hscore : input.registers.scoreDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hscore] at h
      have hqueue : input.ownedRegisters.queueDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hqueue] at h
      have hprevious : input.ownedRegisters.previousServiceDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hprevious] at h
      have hbase : ∀ i, input.followerBaseScore i ≤ p.T * D p := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hbase] at h
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hlive] at h
      have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time input.registers.complementWeights := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hchoice] at h
      have hboundary : actual.startResult.clock.g ≤ p.T + 1 := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hboundary] at h
      have henvelope : input.registers.complementEnvelopeValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left henvelope] at h
      split at h
      · rename_i ha
        exact (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          _ _ _ _ _ _ hchoice ha).elim
      · cases h
    · rename_i candidate hcandidate
      have hcommand := (CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
        input.registers input.ownedRegisters input.followerBaseScore actual candidate
        hactual hcandidate).1
      have hresults := Except.ok.inj (hstart.symm.trans hs)
      exact (congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand hresults).symm.trans
        hcommand

private def liveCutoffChosen (x : CoordinatorRoundDispatch.LiveInput p) :
    CoordinatorRoundDispatch.LiveOutcome x → Bool
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem dispatchLive_issued_command
    (x : CoordinatorRoundDispatch.LiveInput p)
    (hchosen : liveCutoffChosen x (CoordinatorRoundDispatch.dispatchLive x) = true) :
    ∃ out, CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok out ∧
      out.ledgerCommand = some (.initializeAt x.registers.time) := by
  cases hactual : CoordinatorRoundDispatch.dispatchLive x with
  | clockFailure failure heq => simp [hactual, liveCutoffChosen] at hchosen
  | initializerFailure out hs checked heq => simp [hactual, liveCutoffChosen] at hchosen
  | localFailure out hs reason => simp [hactual, liveCutoffChosen] at hchosen
  | continuingChosen out hs continuation selected =>
      simp [hactual, liveCutoffChosen] at hchosen
  | cutoffChosen out hs ledger hi he hd hc hp hn selected =>
      exact ⟨out.startResult, hs,
        dispatchLive_cutoff_command x out hs ledger hi he hd hc hp hn selected hactual⟩

private theorem live_chosen_issued_command
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (reg : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters reg)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : x.state.coordinator = .live reg owned base)
    (hchosen : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ out, CoordinatorPhaseClock.startRound p rate.eta.val x.time
      reg.priorClock reg.pendingAtChoice = .ok out ∧
      out.ledgerCommand = some (.initializeAt x.time) := by
  have htag : ReferenceCollectionPhaseHistory.cutoffChosen x =
      liveCutoffChosen (ReferenceActivePhysicalStep.liveInput x reg owned base)
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x reg owned base)) := by
    dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
      ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
    simp only [hcoord, CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x reg owned base) <;> rfl
  rw [htag] at hchosen
  exact dispatchLive_issued_command
    (ReferenceActivePhysicalStep.liveInput x reg owned base) hchosen

/-- Every actual chosen cutoff has an issued pre-choice command at its actual
calendar date. Failed commands are also retained by `issuedAt`. -/
private theorem issuedAt_of_actual_live_cutoffChosen
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (reg : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters reg)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : r.input.state.coordinator = .live reg owned base)
    (hchosen : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    ReferenceFirstCollectionAwaitedCutoffHistory.issuedAt rate rewards C_star C_h t z := by
  obtain ⟨out, hstart, hcommand⟩ := live_chosen_issued_command
    rate r.input reg owned base hcoord hchosen
  have htime := ReferenceFirstCollectionAwaitedCutoffHistory.actualRecord_input_time rate rewards C_star C_h t z r hr
  rw [htime] at hstart hcommand
  exact ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩


/-- The computed live dispatch originates in the actual incoming live state. -/
private theorem dispatch_live_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases x.state.coordinator with
  | first => trivial
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r q base) <;> rfl
  | collection payload ledger saved =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_left hc]
        cases CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved
              ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_right hc]
  | dagger => trivial

/-- On the actual successful replacement-cut branch, the full incoming
payload is the installed birth payload, the strict-past observer is still
replacement-live, and the same date has issued the actual cutoff command.
Absent births/cutoffs and every unsuccessful branch remain explicit. -/
theorem replacement_issued_at_same_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            registers.payload = payload ∧
            ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
              rate rewards C_star C_h cut.input.time.val z = .replacementLive payload ∧
            replacementIssuedAt rate rewards C_star C_h cut.input.time z
          | _ => True
      | _ => True := by
  have hcoordinates :=
    ReferenceFirstReplacementCollectionPendingFoundation.complete_first_replacement_pending_coordinates
      rate rewards C_star C_h control0 z
  have hboundary :=
    ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
      rate z rewards C_star C_h
  dsimp only at hcoordinates hboundary ⊢
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  let c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
      rw [hb] at hcoordinates hboundary
      dsimp only at hcoordinates hboundary ⊢
      cases hborn : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection old ledger clock cutoff outcome =>
          rw [hborn] at hcoordinates hboundary
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hi output hconsistent
            clockData installed selected
          dsimp only [ReferenceActivePhysicalStep.collectionInput] at hcoordinates hboundary ⊢
          have hp : ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth =
              some installed.registers.payload := by
            simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hborn]
            rfl
          cases hc : R[c]? with
          | none => trivial
          | some cut =>
              rw [hc] at hcoordinates hboundary
              dsimp only at hcoordinates hboundary ⊢
              cases hcut : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live registers owned base outcome =>
                  rw [hcut] at hcoordinates hboundary
                  cases outcome <;> try trivial
                  dsimp only at hcoordinates hboundary ⊢
                  let payload := installed.registers.payload
                  let K := cut :: (R.drop (c + 1)).takeWhile
                    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                  have hrecord := (hcoordinates ⟨0, by simp⟩).2.1
                  change actualRecord rate rewards C_star C_h cut.input.time z = some cut at hrecord
                  have htime : cut.input.time.val = s + c := by
                    have ht := hboundary.2.2.2.1
                    change cut.input.time.val = s + v + 1 + tail.length at ht
                    dsimp only [c]
                    omega
                  have hscan :=
                    ReferenceFirstReplacementCollectionPendingFoundation.scan_before_replacement_cut
                      R birth payload hb hp
                  have hphase :
                      ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
                        rate rewards C_star C_h cut.input.time.val z = .replacementLive payload := by
                    rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase_eq_scan]
                    change ReferenceFirstReplacementCollectionPendingFoundation.scan
                      (R.take (cut.input.time.val - s)) = _
                    rw [htime, Nat.add_sub_cancel_left]
                    exact hscan
                  have hprepare := congrArg
                    (fun out : ReferenceActivePhysicalStep.PreparedRound cut.input => out.coordinator)
                    (ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq cut)
                  change cut.output.preparation.coordinator =
                    ReferenceActivePhysicalStep.dispatch cut.input at hprepare
                  have horigin := dispatch_live_origin rate cut.input
                  rw [← hprepare, hcut] at horigin
                  have hchosen : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
                    rw [← ReferenceFirstReplacementCollectionPendingFoundation.isCutoff_eq]
                    simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcut]
                  have hissued := issuedAt_of_actual_live_cutoffChosen
                    rate rewards C_star C_h cut.input.time z cut hrecord
                    registers owned base horigin hchosen
                  exact ⟨hboundary.2.1, hphase,
                    (replacementMarker_iff rate rewards C_star C_h cut.input.time z).2
                      ⟨payload, hphase⟩, hissued⟩

/-- Any nonempty existing supported date is preceded by the actual issued
replacement cutoff. The successful witnesses are produced by localization. -/
theorem S_repl_le_of_pending_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hP : (ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z).Nonempty) :
    S_repl rate rewards C_star C_h z ≤ n + 1 := by
  have hloc :=
    ReferenceFirstReplacementCollectionPendingLocalization.complete_first_replacement_pending_localization
      rate rewards C_star C_h control0 z n hP
  have hissued := replacement_issued_at_same_cut rate rewards C_star C_h control0 z
  dsimp only at hloc hissued
  split at hloc
  · exact hloc.elim
  · split at hloc
    · split at hloc
      · exact hloc.elim
      · split at hloc
        · obtain ⟨a, ha, _, _⟩ := hloc
          simp_all only
          have hcutIssued := hissued.2.2
          have hle := replacementIssuedAt_implies_S_repl_le
            rate rewards C_star C_h z _ hcutIssued
          omega
        all_goals exact hloc.elim
    all_goals exact hloc.elim

/-- Samplewise order against the EXISTING support sigma, including empty
support, whose sigma is the unchanged exact horizon sentinel. -/
theorem S_repl_le_sigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    S_repl rate rewards C_star C_h z ≤
      ReferenceFirstReplacementCollectionPhaseSupport.sigma
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) z := by
  classical
  unfold ReferenceFirstReplacementCollectionPhaseSupport.sigma
  split
  · rename_i hne
    have hm := Finset.min'_mem _ hne
    have hsupport := (ReferenceFirstReplacementCollectionPhaseSupport.mem_supportIndices_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) z _).1 hm
    exact S_repl_le_of_pending_nonempty rate rewards C_star C_h control0 z _ hsupport.2
  · exact (S_repl_bounds rate rewards C_star C_h z).2

/-- The existing stopped history field at the first actual issued cutoff. -/
@[instance_reducible] def GammaS_repl
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (S_repl rate rewards C_star C_h)
    (S_repl_is_pre_round_stopping_time rate rewards C_star C_h control0)

/-- The unchanged awaited-support stopped field used by the waiting bound. -/
@[instance_reducible] def GammaSigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (ReferenceFirstReplacementCollectionPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (control0 := control0))
    (ReferenceFirstReplacementCollectionPhaseSupport.sigma_is_pre_round_stopping_time
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)

/-- Earlier actual cutoff histories are included in the original awaited
support history, using Mathlib's stopped σ-algebras. -/
theorem GammaS_repl_le_GammaSigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaS_repl rate rewards C_star C_h control0 ≤
      GammaSigma rate rewards C_star C_h control0 := by
  unfold GammaS_repl GammaSigma PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
  apply MeasureTheory.IsStoppingTime.measurableSpace_mono
  intro z
  change (S_repl rate rewards C_star C_h z : WithTop ℕ) ≤
    (ReferenceFirstReplacementCollectionPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (control0 := control0) z : WithTop ℕ)
  exact WithTop.coe_le_coe.mpr (S_repl_le_sigma rate rewards C_star C_h control0 z)

/-- Both stopped fields retain the original source-input ambient space. -/
theorem GammaSigma_le_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaSigma rate rewards C_star C_h control0 ≤
      inferInstanceAs (MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
  exact PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le _ _ _

theorem GammaS_repl_le_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaS_repl rate rewards C_star C_h control0 ≤
      inferInstanceAs (MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
  exact (GammaS_repl_le_GammaSigma rate rewards C_star C_h control0).trans
    (GammaSigma_le_ambient rate rewards C_star C_h control0)

/-- The downward tower for the SAME actual awaited waiting charge and the
original source-input law at the earlier issued-cutoff history. -/
theorem actual_replacement_awaited_waiting_charge_downward_tower
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
          rate rewards C_star C_h control0 | GammaSigma rate rewards C_star C_h control0] |
        GammaS_repl rate rewards C_star C_h control0] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
          rate rewards C_star C_h control0 | GammaS_repl rate rewards C_star C_h control0] := by
  exact MeasureTheory.condExp_condExp_of_le
    (GammaS_repl_le_GammaSigma rate rewards C_star C_h control0)
    (GammaSigma_le_ambient rate rewards C_star C_h control0)

/-- Integrability under the unchanged original source-input law. -/
theorem actual_replacement_awaited_waiting_charge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable
      (ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
        rate rewards C_star C_h control0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact ReferenceFirstReplacementCollectionAwaitedWaitingCost.actual_first_replacement_collection_awaited_waiting_charge_integrable
      rate rewards C_star C_h control0

/-- Every event measurable at the earlier issued cutoff has the SAME
unnormalized awaited-charge estimate, including zero-mass events. -/
theorem actual_replacement_awaited_waiting_charge_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[GammaS_repl rate rewards C_star C_h control0] B) :
    (∫ z in B,
      ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
        rate rewards C_star C_h control0 z ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  exact ReferenceFirstReplacementCollectionAwaitedWaitingCost.actual_first_replacement_collection_awaited_waiting_charge_setIntegral_bound
      rate rewards C_star C_h control0 B
      (GammaS_repl_le_GammaSigma rate rewards C_star C_h control0 B hB)

/-- The SAME awaited charge is conditionally bounded by `Bcol` at the actual
first issued-cutoff history, on the original full source law. -/
theorem actual_replacement_awaited_waiting_charge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
        rate rewards C_star C_h control0 | GammaS_repl rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  apply (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
    (GammaS_repl rate rewards C_star C_h control0)
    (GammaS_repl_le_ambient rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedWaitingCost.actualFirstReplacementCollectionAwaitedWaitingCharge
      rate rewards C_star C_h control0)
    (ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p))
    (actual_replacement_awaited_waiting_charge_integrable rate rewards C_star C_h control0)).1
  exact actual_replacement_awaited_waiting_charge_setIntegral_bound rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCutoffHistory

end
