/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownPostcutExclusion
public import Bandits.Support.ReferenceFirstCollectionReadyStream
public import Bandits.Support.ReferenceFirstLiveCoordinatorSafety

import Mathlib.Data.List.TakeWhile

/-!
# Actual inherited first DOWN completion detector containment

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,303-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This internal result joins the actual first-live safety and finite collection
readiness producers to the inherited first-completion cut. All diagnostics,
cohort witnesses and physical indices belong to the original initialized run.
The named consumer is the actual inherited first-completion mixed DOWN
detector census, later joined with the original prelaunch/cohort affine-tail
bounds. Later completions and absent or terminal launches remain outside this
internal result. It makes no manuscript, probability or main regret closure
claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness
open ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceGeneratedInheritedDownDetectorContainment

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

-- A failed dispatch cannot acquire a nonabsorbing successor through FINISH.
-- Conversely, failures after a successful choice do not erase that choice.
private theorem selection_ne_none_of_next_ne_dagger
    (r : Record (p := p) (rate := rate))
    (hnext : r.output.next.coordinator ≠ .dagger) :
    r.output.preparation.coordinator.selection ≠ none := by
  classical
  intro hnone
  apply hnext
  rw [r.output_eq] at hnone ⊢
  change (prepare r.input).coordinator.selection = none at hnone
  change (prepare r.input).observeCoordinator.configuration = .dagger
  unfold PreparedRound.observeCoordinator
  rw [dite_eq_left hnone]
  cases (prepare r.input).coordinator <;> rfl

private theorem ready_selection_ne_none
    (r : Record (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload ledger saved) :
    r.output.preparation.coordinator.selection ≠ none := by
  classical
  obtain ⟨cutoff, _hcutoff, core, snap, hb, hs, hdispatch, _⟩ :=
    ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
      r.input payload ledger saved hready
  rw [r.output_eq]
  change (prepare r.input).coordinator.selection ≠ none
  rw [hdispatch]
  simp only [DispatchCut.selection]
  exact Option.some_ne_none _

-- The collection window's stopping predicate is the actual later choice.
-- Its bound is derived from physical indices, without matching timestamps.
private theorem collectionWindow_index
    (records : List (Record (p := p) (rate := rate))) (w n : ℕ)
    (hwn : w ≤ n) (hn : n < records.length)
    (hnoLater : ∀ k (hk : k < records.length), k ≤ n →
      laterChosen (records[k]'hk).input = false) :
    n - w < (collectionWindow records w).length := by
  classical
  have hhead : ((records.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  by_cases heq : n = w
  · subst n
    simp only [collectionWindow, List.length_append, hhead, Nat.sub_self]
    omega
  have htail : n - w ≤ ((records.drop (w + 1)).takeWhile
      (fun record => !laterChosen record.input)).length := by
    let tail := records.drop (w + 1)
    have hlength : n - w ≤ tail.length := by
      simp only [tail, List.length_drop]
      omega
    have hall : ∀ r ∈ tail.take (n - w), (!laterChosen r.input) = true := by
      intro r hr
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hr
      have hkTail : k < tail.length := by
        have := List.length_take_le (n - w) tail
        simp only [List.length_take, Nat.min_eq_left hlength] at hk
        omega
      have hkBound : k < n - w := by
        have := List.length_take_le (l := tail) (i := n - w)
        omega
      have hrecord : (tail.take (n - w))[k]'hk = records[w + 1 + k]'(by
          simp only [tail, List.length_drop] at hkTail
          omega) := by
        simp only [List.getElem_take, tail, List.getElem_drop]
      have hlater := hnoLater (w + 1 + k) (by
        simp only [tail, List.length_drop] at hkTail
        omega) (by omega)
      rw [← hrecord, he] at hlater
      simp only [hlater, Bool.not_false]
    have htake : (tail.take (n - w)).takeWhile
        (fun record => !laterChosen record.input) = tail.take (n - w) :=
      List.takeWhile_eq_self_iff.mpr hall
    have hprefix := (List.take_prefix (n - w) (tail.takeWhile
      (fun record => !laterChosen record.input))).length_le
    rw [List.take_takeWhile, htake, List.length_take,
      Nat.min_eq_left hlength] at hprefix
    exact hprefix
  rw [collectionWindow, List.length_append, hhead]
  simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_of_le htail

section Stream

variable {source : BootstrapPrivateRoundStreams.SourceInput p}
  {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
  {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}

-- This helper exposes its only conditional input: no focal accepted UP at
-- the specified original window indices. The main proof produces that input
-- using P and actual indexed-record equalities.
private theorem stream_focal_pending
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (i : Fin (p.m - 1)) (limit : ℕ)
    (hnoUp : ∀ k (hk : k < out.window.length), k ≤ limit →
      ∀ message, ¬ AcceptedUp (out.window[k]'hk).input i message)
    (k : Fin out.ell) (hlimit : k.val ≤ limit) :
    i ∈ (out.ledgers k).pending := by
  classical
  have hrec : ∀ k (hk : k < out.ell), k ≤ limit →
      i ∈ (out.ledgers ⟨k, hk⟩).pending := by
    intro k
    induction k with
    | zero =>
      intro hk _
      rw [out.ledgers_are_outputs]
      simp only [List.getElem_cons_zero, out.cutoffPendingUniv, Finset.mem_univ]
    | succ k ih =>
      intro hk hklimit
      obtain ⟨j, r, incoming, cell, _hj, hr, hf, hi⟩ :=
        ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput.cell_at
          out (⟨k + 1, hk⟩ : Fin out.ell) (show 0 < k + 1 from Nat.zero_lt_succ k)
      have hprev : i ∈ incoming.pending := by
        rw [hi]
        exact ih (by omega) (by omega)
      rw [← hf, ReferenceFirstCollectionReadyStream.cell_pending_recurrence]
      cases hevent : acceptedLabel r.input with
      | none =>
        simpa only [eraseEvent, hevent] using hprev
      | some sender =>
        have hne : i ≠ sender := by
          intro heq
          have hrEq : r = out.window[k + 1]'(by
              have := out.withinWindow
              omega) := Option.some.inj
            (hr.symm.trans (List.getElem?_eq_getElem (by
              have := out.withinWindow
              omega)))
          obtain ⟨message, haccepted⟩ := acceptedLabel_witness hevent
          rw [← heq, hrEq] at haccepted
          exact hnoUp (k + 1) (by have := out.withinWindow; omega) hklimit
            message haccepted
        simpa only [eraseEvent, hevent] using Finset.mem_erase.mpr ⟨hne, hprev⟩
  exact hrec k.val k.isLt hlimit

private theorem stream_reaches_index
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (i : Fin (p.m - 1)) (offset : ℕ) (hindex : offset < out.window.length)
    (hnoUp : ∀ k (hk : k < out.window.length), k ≤ offset →
      ∀ message, ¬ AcceptedUp (out.window[k]'hk).input i message) :
    offset < out.ell := by
  by_contra hstop
  have hshorter : out.ell < out.window.length := by omega
  have hempty := out.last_empty_of_not_exhausted hshorter
  have hpending := stream_focal_pending out i offset hnoUp
    ⟨out.ell - 1, by have := out.positiveLength; omega⟩ (by omega)
  rw [hempty] at hpending
  exact Finset.notMem_empty i hpending

end Stream

-- Transport the actual run on equal launch data, including its dependent
-- activation and span proofs. All other physical inputs stay identical.
private theorem run_records_congr
    {initial other : ReferenceActivePhysicalHorizon.State p rate}
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    {start otherStart count : ℕ}
    {span : start + count ≤ p.T} {otherSpan : otherStart + count ≤ p.T}
    {active : allActiveAtStart initial start}
    {otherActive : allActiveAtStart other otherStart}
    (hstate : initial = other) (htime : start = otherStart) :
    (run initial rows J rewards start count span active).records =
      (run other rows J rewards otherStart count otherSpan otherActive).records := by
  cases hstate
  cases htime
  rfl

-- Identify the original corrected launch without clearing any batch or
-- replacing an ordinary follower store. These are public launch fields.
private theorem generated_seed_initial
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    let seed := generatedSourceSeed rate rewards C_star C_h s hs x
    allActiveAtStart seed s ∧ seed.coordinator = .first ∧
      ReferenceFirstLiveConfirmationHistory.InitialFollowers seed ∧
      (∀ j : Fin (p.m - 1), ∃ state memory,
        seed.followers j = .ordinary state memory ∧ state.lastDown = none) := by
  classical
  dsimp only
  let seed := generatedSourceSeed rate rewards C_star C_h s hs x
  have hspec := generatedSourceSeed_spec rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hseedActive : seed = active := Option.some.inj (hspec.1.symm.trans hactive.1)
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hseedFields : seed = activeFields :=
    Option.some.inj (hspec.1.symm.trans hfieldsLaunch)
  have hinitial : seed.coordinator = .first := by
    rw [hseedActive]
    exact hactive.2.1
  have hfollowers : ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
    intro j state memory hstate
    rcases hfields j with ⟨hconfiguration, hlast, _, _, _, _, hunoccupied, _⟩
    have hconfiguration' : seed.followers j = .ordinary
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
          (ActualReferenceInitializationBlock.refFollower j))
        (ActiveFollowerLifecycle.initialMemory p) := by
      rw [hseedFields]
      exact hconfiguration
    rw [hconfiguration'] at hstate
    cases hstate
    exact ⟨hunoccupied, hlast⟩
  refine ⟨hspec.2.1, hinitial, hfollowers, ?_⟩
  intro j
  rcases hfields j with ⟨hconfiguration, hlast, _, _, _, _, _, _⟩
  refine ⟨ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower j),
    ActiveFollowerLifecycle.initialMemory p, ?_, hlast⟩
  change seed.followers j = _
  rw [hseedFields]
  exact hconfiguration

-- No current diagnostic or successful-output premise is used here. Before
-- the cutoff S gives a live successor. Afterwards R supplies actual incoming
-- readiness, and P prevents the focal pending label from ever being erased.
private theorem generated_first_completion_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (hfirst : completedBatchAtRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) ∧
      ∀ l (hl : l < n.val), ¬ completedBatchAtRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2
          ⟨l, lt_trans hl n.isLt⟩)) :
    (generatedSourceRecordAt rate rewards C_star C_h s hs x n).output.preparation.coordinator.selection ≠
      none := by
  classical
  let seed := generatedSourceSeed rate rewards C_star C_h s hs x
  let E := generatedSourceRun rate rewards C_star C_h s hs x
  let F := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  obtain ⟨hactive, hinitial, _hfollowers, _hordinary⟩ :=
    generated_seed_initial rate rewards C_star C_h s hs x
  have hrun : E = run seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
      (p.T - s) (by omega) hactive := rfl
  have hlength : E.records.length = p.T - s := run_record_count _ _ _ _ _ _ _ _
  have hrecord (k : Fin (p.T - s)) :
      E.records[k.val]'(by omega) =
        generatedSourceRecordAt rate rewards C_star C_h s hs x k := by
    have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x k
    change E.records[k.val]? = _ at hget
    rw [List.getElem?_eq_getElem (by omega)] at hget
    exact Option.some.inj hget
  have hsafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    seed x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
    rewards s (p.T - s) (by omega) hactive hinitial
  by_cases hlive : n.val < F.length
  · obtain ⟨_hfailure, recording, _hrecording, registers, owned, base, hnext⟩ :=
      hsafety.1 ⟨n.val, hlive⟩
    have hprefix : F.IsPrefix E.records := List.takeWhile_prefix _
    have heq : F[n.val]'hlive =
        generatedSourceRecordAt rate rewards C_star C_h s hs x n :=
      (hprefix.getElem hlive).trans (hrecord n)
    change (F[n.val]'hlive).output.next.coordinator = _ at hnext
    rw [heq] at hnext
    apply selection_ne_none_of_next_ne_dagger
    rw [hnext]
    intro h
    cases h
  have hpostcut : F.length ≤ n.val := by omega
  have hcutoff := hsafety.2.2 (show F.length < p.T - s from by omega)
  obtain ⟨_hcutIndex, _hcutoff, _hcutNotLive⟩ := hcutoff
  have hhistory :=
    ReferenceGeneratedInheritedDownPostcutExclusion.generated_inherited_first_completion_no_up_or_later
      rate rewards C_star C_h s hs x i n hfirst
  let span : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) x.val rewards C_star C_h + (p.T - s) ≤ p.T := by
    change ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed +
        (p.T - s) ≤ p.T
    rw [x.property.2]
    omega
  let actual := ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
    x.val rewards C_star C_h x.property.1 (p.T - s) span
  have hseedSpec := generatedSourceSeed_spec rate rewards C_star C_h s hs x
  have hseedActual : seed = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate x.val rewards C_star C_h x.property.1 := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.get_of_eq_some _ hseedSpec.1).symm
  have hrecords : actual.records = E.records := by
    rw [hrun]
    dsimp only [actual, ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    exact run_records_congr x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
      hseedActual.symm x.property.2
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow actual.records).length <
      p.T - s := by
    rw [hrecords]
    exact lt_of_le_of_lt hpostcut n.isLt
  obtain ⟨out⟩ := ReferenceFirstCollectionReadyStream.actual_initialized_first_collection_ready_stream
    (rate := rate) x.val rewards C_star C_h x.property.1 (p.T - s) span hshort
  have hwindow : out.window = collectionWindow E.records F.length := by
    rw [out.windowIsActual]
    change collectionWindow actual.records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow actual.records).length = _
    rw [hrecords]
  have hwindowIndex : n.val - F.length < out.window.length := by
    rw [hwindow]
    apply collectionWindow_index E.records F.length n.val hpostcut (by omega)
    intro k hk hkn
    rw [hrecord ⟨k, by omega⟩]
    exact hhistory.2 ⟨k, by omega⟩ hkn
  have hnoUp : ∀ k (hk : k < out.window.length), k ≤ n.val - F.length →
      ∀ message, ¬ AcceptedUp (out.window[k]'hk).input i message := by
    intro k hk hkn message haccepted
    have halign := (out.alignment ⟨k, hk⟩).1
    change actual.records[_]? = some (out.window[k]'hk) at halign
    rw [hrecords] at halign
    change E.records[F.length + k]? = some (out.window[k]'hk) at halign
    have hglobalN : F.length + k ≤ n.val := by omega
    have hglobal : F.length + k < p.T - s := by omega
    have hget : E.records[F.length + k]? =
        some (generatedSourceRecordAt rate rewards C_star C_h s hs x
          ⟨F.length + k, hglobal⟩) := by
      exact (List.getElem?_eq_getElem (by omega)).trans
        (congrArg some (hrecord ⟨F.length + k, hglobal⟩))
    have heq := Option.some.inj (halign.symm.trans hget)
    rw [heq] at haccepted
    exact hhistory.1 ⟨F.length + k, hglobal⟩ hglobalN message haccepted
  have hreach := stream_reaches_index out i (n.val - F.length) hwindowIndex hnoUp
  have hcurrentLookup : out.window[n.val - F.length]? =
      some (generatedSourceRecordAt rate rewards C_star C_h s hs x n) := by
    have halign := (out.alignment ⟨n.val - F.length, hwindowIndex⟩).1
    change actual.records[_]? = some _ at halign
    rw [hrecords] at halign
    change E.records[F.length + (n.val - F.length)]? = some _ at halign
    rw [Nat.add_sub_of_le hpostcut] at halign
    have hget : E.records[n.val]? =
        some (generatedSourceRecordAt rate rewards C_star C_h s hs x n) :=
      (List.getElem?_eq_getElem (by omega)).trans (congrArg some (hrecord n))
    exact (List.getElem?_eq_getElem hwindowIndex).trans (halign.symm.trans hget)
  by_cases hzero : n.val - F.length = 0
  · have hhead : out.cutoff.cut =
        generatedSourceRecordAt rate rewards C_star C_h s hs x n := by
      have hlookup := hcurrentLookup
      rw [hzero, List.getElem?_eq_getElem (by have := out.windowNonempty; omega),
        out.cutoffIsHead] at hlookup
      exact Option.some.inj hlookup
    rw [← hhead]
    apply selection_ne_none_of_next_ne_dagger
    rw [out.cutoff.outputCoordinator]
    intro h
    cases h
  · obtain ⟨j, r, incoming, cell, _hj, hr, _hf, _hi⟩ :=
      ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput.cell_at
        out (⟨n.val - F.length, hreach⟩ : Fin out.ell)
        (show 0 < n.val - F.length from Nat.pos_of_ne_zero hzero)
    have heq : r = generatedSourceRecordAt rate rewards C_star C_h s hs x n :=
      Option.some.inj (hr.symm.trans hcurrentLookup)
    rw [← heq]
    exact ready_selection_ne_none r out.payload incoming out.saved cell.readyInput

/-- An actual inherited first suffix completion with a wrong unique ordinary
candidate belongs to the mixed DOWN detector. The original cut, raw word,
birth, launch cohort and complete physical suffix membership are retained.
The only external conditions are the actual launch, first completion and
saved wrong diagnostic in the stated telescope. -/
theorem generated_inherited_wrong_completion_detector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) ∧
        ∀ l (hl : l < n.val),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 ⟨l, lt_trans hl n.isLt⟩))
    (hwrong : ∃ cut,
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch
    let E := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x
    let F := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n
    ∃ cut word alpha, ∃ hAlpha : alpha ≤ p.T,
      (Rn.output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut ∧
      cut.raw = some word ∧ alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h
        x.val i alpha hAlpha B0.completed.length ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h x.val i B0.completed.length = some alpha ∧
      (∀ test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h s hs i x,
        AffineChannelLaw.affineHash test.sample word = 1) ∧
      Rn ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).take (p.T - s) ∧
      (x.val ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha B0.completed.length hAlpha word control0
          (AffineBatchDecoder.quota p)) := by
  classical
  intro B0 E F Rn
  obtain ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
      hbirth, hboundary, hhash, hcurrentSuffix, hcase⟩ :=
    ReferenceGeneratedInheritedDownPostcutExclusion.generated_inherited_postcut_wrong_completion_cut
      rate rewards C_star C_h s hs x i n control0 hfirst hwrong
  have hselection := generated_first_completion_selection
    rate rewards C_star C_h s hs x i n hfirst
  exact ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
    hbirth, hboundary, hhash, hcurrentSuffix, hcase.resolve_right hselection⟩

end Bandits.Support.ReferenceGeneratedInheritedDownDetectorContainment

end
