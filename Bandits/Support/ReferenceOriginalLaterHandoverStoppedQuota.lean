/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals
public import Bandits.Support.ReferencePostReplacementCollectionHandoverWaitingCost

import Lean.Elab.Tactic.Omega

/-!
# Original inclusive-stop physical service on an actual later H segment

The uncapped charge reads the actual later-installation segment and unmasked
physical service events. The original inclusive gate identifies the incoming
phases of the replay seeded by the whole inherited bank and older accepted
start. Every natural prefix satisfies the quota; retained incoming tasks satisfy
the strict bound. The current detecting failure or overflow service is included.

Sources: ZIP4 `05_binary_transport.tex:253-289`,
`06_interruptions.tex:431-490,493-533`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open HandoverStoppedDecoderReplay
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalLaterHandoverStoppedQuota

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (z : BootstrapPrivateRoundStreams.SourceInput p)

open ReferencePostReplacementCollectionHandoverPhaseCorrespondence
open ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open ReferencePostReplacementCollectionHandoverStoppedFailureCoverage


open _root_.Bandits.Support.ReferencePrelaunchFollower (acceptedStart)
open _root_.Bandits.Support.ReferenceFirstLiveHandoverSnapshotPrefix (installationFlag)
open _root_.Bandits.Support.ReferenceFollowerDownDecoderReplay (preparedOwnObservation replayDownCalls)
open _root_.Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs prefixInputs_launch prefixInputs_append_one)
open _root_.Bandits.Support.ReferenceFirstReplacementCollectionPredictableStages (preRoundStart)
open _root_.Bandits.Support.ReferenceCompleteSignedFirstBadCalendar (firstBadDate)

local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "queueParams" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "H" b => actualHandoverRecords rate rewards C_star C_h z b

/-- The original inclusive-stop physical service tick on the same actual H
record. The incoming selected pending set is read before the current update;
the two service events are the unmasked whole-source physical observations. -/
public def originalHandoverPhysicalTick
    (b : Fin (R).length) (i : Fin (p.m - 1)) (t : Fin p.T) : ℕ :=
  if ∃ j : Fin (H b).length, ((H b)[j.val]'(j.isLt)).input.time = t ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection (((H b)[j.val]'(j.isLt)).input),
        ((H b)[j.val]'(j.isLt)).output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧
        t.val + 1 ≤ firstBadDate rate rewards C_star C_h z ∧
        ((∃ state memory,
            preRoundStart rate rewards C_star C_h t i z = .inr (.success state memory) ∧
            state.status = 0 ∧
            ReferenceFirstLiveHandoverBoundaryFactorization.V_before rate rewards C_star C_h i t z) ∨
          (∃ state memory,
            preRoundStart rate rewards C_star C_h t i z = .inr (.success state memory) ∧
            state.status = 1 ∧
            ReferenceFirstLiveHandoverBoundaryFactorization.V_after rate rewards C_star C_h i t z))
    then 1 else 0

/-- The uncapped physical service count over all original calendar indices
strictly below the supplied natural prefix. -/
public def originalHandoverPhysicalCount
    (b : Fin (R).length) (i : Fin (p.m - 1)) (n : ℕ) : ℕ :=
  ∑ t : Fin p.T, if t.val < n then
    originalHandoverPhysicalTick rate rewards C_star C_h z b i t else 0

/-- The original inclusive gate is exactly strict absence of every earlier
decoder or numerical bad event. This retains the current detecting update. -/
public theorem originalInclusiveGate_noBadEventStrictlyBefore
    (t : Fin p.T)
    (hgate : t.val + 1 ≤ firstBadDate rate rewards C_star C_h z) :
    ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore rate rewards C_star C_h z t :=
  (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff rate rewards C_star C_h z t).mp hgate

/-- Strict-past observer consequences used by the original stopped replay:
numerical overflow is absent, all earlier prelaunch DOWN flags are false,
and the awaited-failure accumulator is false. -/
public theorem originalInclusiveGate_observer_facts
    (t : Fin p.T)
    (hgate : t.val + 1 ≤ firstBadDate rate rewards C_star C_h z) :
    ¬ ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy rate rewards C_star C_h t z ∧
    (∀ u : Fin p.T, u.val < t.val → ∀ i : Fin (p.m - 1),
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i u = false) ∧
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h t.val z = false :=
  (ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_iff_observers
    rate rewards C_star C_h t z).mp
    (originalInclusiveGate_noBadEventStrictlyBefore rate rewards C_star C_h z t hgate)

/-- The same original gate keeps the current date under the accepted
strict-past decoder endpoint. -/
public theorem originalInclusiveGate_decoderDateKeptAt
    (t : Fin p.T)
    (hgate : t.val + 1 ≤ firstBadDate rate rewards C_star C_h z) :
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt rate rewards C_star C_h z t := by
  rw [ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_iff_no_earlier]
  intro u hu hfailure
  rcases hfailure with hpre | hawaited
  · rcases hpre with ⟨k, hk⟩
    have hfacts := originalInclusiveGate_observer_facts rate rewards C_star C_h z t hgate
    have hpreFalse := hfacts.2.1 u hu k
    rw [hpreFalse] at hk
    cases hk
  · have hfacts := originalInclusiveGate_observer_facts rate rewards C_star C_h z t hgate
    have hnoAwaited :=
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
        rate rewards C_star C_h z t.val |>.mp hfacts.2.2
    exact hnoAwaited u hu hawaited

private theorem birth_seed_unique
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    {i : Fin (p.m - 1)}
    {P Q : ReferenceActivePhysicalStep.Payload rate}
    {s t : ReferencePrelaunchFollower.State p rate.eta}
    {m n : ActiveFollowerLifecycle.LocalMemory p}
    (hP : ReferenceAssignmentPayloadPersistence.InstallationBirth r P)
    (hQ : ReferenceAssignmentPayloadPersistence.InstallationBirth r Q)
    (hs : r.input.state.followers i = .ordinary s m)
    (ht : r.input.state.followers i = .ordinary t n) :
    P = Q ∧ s = t ∧ m = n := by
  exact ⟨ReferenceAssignmentPayloadChronology.installationBirth_payload_unique r P Q hP hQ,
    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hs.symm.trans ht)⟩

private theorem handover_index (b : Fin (R).length) (j : Fin (H b).length) :
    ∃ hk : b.val + j.val < (R).length, (H b)[j.val] = R[b.val + j.val]'hk := by
  have hV : (R[b.val] ::
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)).IsPrefix ((R).drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : (H b).IsPrefix ((R).drop b.val) := (List.takeWhile_prefix _).trans hV
  have hlen := hH.length_le
  simp only [List.length_drop] at hlen
  refine ⟨by have := j.isLt; omega, ?_⟩
  rw [hH.getElem j.isLt, List.getElem_drop]

private theorem handover_time (b : Fin (R).length) (j : Fin (H b).length) :
    (H b)[j.val].input.time.val = R[b.val].input.time.val + j.val := by
  obtain ⟨hk, he⟩ := handover_index rate rewards C_star C_h z b j
  rw [he,
    completeSuffixRecord_time rate rewards C_star C_h z ⟨_, hk⟩,
    completeSuffixRecord_time rate rewards C_star C_h z b]
  exact (Nat.add_assoc _ _ _).symm

private theorem handover_lookup (b : Fin (R).length) (j : Fin (H b).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (H b)[j.val].input.time z = some (H b)[j.val] := by
  obtain ⟨hk, he⟩ := handover_index rate rewards C_star C_h z b j
  rw [he]
  have ht := completeSuffixRecord_time rate rewards C_star C_h z ⟨_, hk⟩
  simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ht,
    Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hk]

private theorem handover_calendar
    (b : Fin (R).length) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H b).length) :
    actualLaterHandoverLive rate rewards C_star C_h z payload (H b) (H b)[j.val].input.time =
      ⟨handoverRoundInput payload (H b)[j.val].input.row (H b)[j.val].input.time,
        handoverWholeRewardRow (H b)[j.val],
        installationFlag payload (H b)[j.val]⟩ := by
  apply actualLaterHandoverLive_of_actual_record
    rate rewards C_star C_h z payload (H b) (H b)[j.val].input.time
  · rw [handover_time rate rewards C_star C_h z b j,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
    constructor <;> have := j.isLt <;> omega
  · exact handover_lookup rate rewards C_star C_h z b j

private theorem handover_current_cell
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length) :
    ∃ c, ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (H b)[j.val] = some c := by
  obtain ⟨_P0, rb, _qb, _base, cell, _native, _hlen, _hmap, _hprefix, _hinit,
      _hnext, _hbirth, _hlater, _hbase, hcell, _hnative, _hpayload, _henabled,
      _hprefixNext, _hmapNext, _hdown, htail⟩ :=
    ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
      rate rewards C_star C_h z b hb
  rcases j with ⟨nval, hbound⟩
  have hH := (List.takeWhile_prefix
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).getElem hbound
  change (H b)[nval] = (R[b.val] ::
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1))[nval]'_ at hH
  rw [hH]
  cases nval with
  | zero => exact ⟨cell, hcell⟩
  | succ n =>
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      have hnW : n < W.length := Nat.lt_of_succ_lt_succ
        (lt_of_lt_of_le hbound (List.takeWhile_prefix
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le)
      rcases htail with hterminal | ⟨k, cells, hk, _hstate, hlength, hreadouts, _⟩
      · have hnil : W = [] := by
          simp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
            hterminal, List.drop_length, List.takeWhile_nil]
        rw [hnil] at hnW
        exact (Nat.not_lt_zero n hnW).elim
      · rw [hk] at hlength hreadouts
        change cells.length = W.length at hlength
        change W.map (ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) = cells.map some at hreadouts
        have hnC : n < cells.length := by rw [hlength]; exact hnW
        have hread := congrArg (fun xs => xs[n]?) hreadouts
        simp only [List.getElem?_map, List.getElem?_eq_getElem hnW,
          List.getElem?_eq_getElem hnC, Option.map_some, Option.some.injEq] at hread
        obtain ⟨selected, ho, hs, hbase, hlive, _⟩ :=
          ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ W[n] cells[n] hread
        have hpresent : (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 W[n]).isSome = true :=
          (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain 0 W[n]).mpr
            ⟨selected, hs, by omega, hlive, ho⟩
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hpresent
        refine ⟨c, ?_⟩
        change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate W[n] = some c
        simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hc, Option.some_or]

private theorem handover_cutoff_false
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length) :
    actualHandoverCutoffBefore rate rewards C_star C_h z (H b)[j.val].input.time = false := by
  rw [actualHandoverCutoffBefore, handover_lookup rate rewards C_star C_h z b j]
  change ReferenceCollectionPhaseHistory.cutoffChosen (H b)[j.val].input = false
  rcases j with ⟨nval, hbound⟩
  have hV := (List.takeWhile_prefix
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).getElem hbound
  change (H b)[nval] = (R[b.val] ::
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1))[nval]'_ at hV
  rw [hV]
  cases nval with
  | zero =>
      simp only [List.getElem_cons_zero]
      unfold ReferenceCollectionPhaseHistory.laterChosen at hb
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      cases he : (ReferenceActivePhysicalStep.prepare R[b.val].input).coordinator
        <;> simp only [he, Bool.false_eq_true] at hb ⊢
  | succ n =>
      have hjV := lt_of_lt_of_le hbound
        (List.takeWhile_prefix ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le
      have hnW : n < (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).length := by
        simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hjV
      simp only [List.getElem_cons_succ]
      have hc := List.mem_takeWhile_imp (List.getElem_mem hnW)
      change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest _ = true at hc
      unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hc
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [← ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq]
      cases he : ((ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1))[n]).output.preparation.coordinator
        <;> simp only [he] at hc ⊢
      rename_i registers owned base outcome
      cases outcome <;> simp_all

/-- Presence is proved by appending actual cells, independently of stopping. -/
private theorem original_handover_prefix_present
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length) :
    ∃ N, prefixInputs rate rewards C_star C_h ((H b)[j.val].input.time.val + 1) z = some N := by
  obtain ⟨P0, _hlen, _hmap, hpast⟩ :=
    ReferenceCompleteInstallationPrefixPresence.internal_complete_later_installation_prefix_inputs
      rate rewards C_star C_h z b hb
  have htime (k : Fin (H b).length) : (H b)[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val + k.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      completeSuffixRecord_time rate rewards C_star C_h z b, Nat.add_assoc]
  have happend (k : Fin (H b).length) (N : List (RecordedQueueRun.RoundInput p.K))
      (hN : prefixInputs rate rewards C_star C_h (H b)[k.val].input.time.val z = some N) :
      ∃ next, prefixInputs rate rewards C_star C_h ((H b)[k.val].input.time.val + 1) z = some next := by
    obtain ⟨c, hc⟩ := handover_current_cell rate rewards C_star C_h z b hb k
    have hr := handover_lookup rate rewards C_star C_h z b k
    have hl := prefixInputs_launch rate rewards C_star C_h _ z N hN
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hl.2] at hr
    exact ⟨N ++ [c], prefixInputs_append_one rate rewards C_star C_h _ z N hN (H b)[k.val] c hr hc⟩
  have hprefix : ∀ n, ∀ k : Fin (H b).length, k.val = n →
      ∃ N, prefixInputs rate rewards C_star C_h ((H b)[k.val].input.time.val + 1) z = some N := by
    intro n
    induction n with
    | zero =>
        intro k hk
        apply happend k (P0.take b.val)
        rw [htime, hk, Nat.add_zero]
        exact hpast b.val le_rfl
    | succ n ih =>
        intro k hk
        let prev : Fin (H b).length := ⟨n, by have := k.isLt; omega⟩
        obtain ⟨N, hN⟩ := ih prev rfl
        apply happend k N
        have he : (H b)[k.val].input.time.val = (H b)[prev.val].input.time.val + 1 := by
          rw [htime, htime]
          dsimp only [prev]
          omega
        rw [he]
        exact hN
  exact hprefix j.val j rfl

/-- Only strict predecessors are safe; the current detecting update is retained. -/
private theorem original_predecessor_overflow_false
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length)
    (hgate : (H b)[j.val].input.time.val + 1 ≤
      firstBadDate rate rewards C_star C_h z)
    (k : Fin (H b).length) (hkj : k.val < j.val) :
    actualHandoverOverflowAfter rate rewards C_star C_h z (H b)[k.val].input.time = false := by
  obtain ⟨N, hN⟩ := original_handover_prefix_present rate rewards C_star C_h z b hb k
  have hno := (originalInclusiveGate_observer_facts rate rewards C_star C_h z _ hgate).1
  have hrun : (RecordedQueueRun.run queueParams N).overflow = false := by
    cases hov : (RecordedQueueRun.run queueParams N).overflow with
    | false => rfl
    | true =>
        obtain ⟨a, ha⟩ := (RecordedQueueRun.run_overflow_iff_cutoff queueParams N).mp hov
        apply False.elim
        apply hno
        refine ⟨(H b)[k.val].input.time.val + 1, ?_,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run queueParams N), ?_, a, ?_⟩
        · rw [handover_time rate rewards C_star C_h z b k,
            handover_time rate rewards C_star C_h z b j]
          omega
        · simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
            hN, Option.map_some]
        · exact (RecordedQueueRun.overflowCutoff_iff queueParams _).mpr ha
  rw [actualHandoverOverflowAfter, actualHandoverOverflowAfter?, hN, Option.map_some, hrun]
  rfl

private theorem awaiting_service_classification
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : ActiveRoundActions.Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (bank : DecoderState p)
    (old : ℕ) (t : Fin p.T)
    (hsmall : bank.pending.length < AffineBatchDecoder.quota p)
    (haM : OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p beta)
      old (WaitedWordWindow.sourceRound t) M)
    (hfalse : (serviceStep p beta a data i fixing M (initial p bank old) t).phase ≠ .failedFalse)
    (hamb : (serviceStep p beta a data i fixing M (initial p bank old) t).phase ≠ .failedAmbiguous) :
    serviceStep p beta a data i fixing M (initial p bank old) t =
      let bank' := (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).1
      if (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 =
          some (currentWord p beta M) then
        ⟨bank', M.val.sigma, .acceptedUnconfirmed⟩
      else initial p bank' old := by
  dsimp only
  by_cases hel : AffineBatchDecoder.eligible ((observationTrace p a data i) t)
  · simp only [serviceStep, initial, hel, ite_true] at hfalse hamb ⊢
    by_cases hshort : bank.pending.length + 1 < AffineBatchDecoder.quota p
    · have hraw : (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 = none := by
        change AffineBatchDecoder.stepOutput p (observationTrace p a data i) bank t = none
        simp only [AffineBatchDecoder.stepOutput, AffineBatchDecoder.positiveAt,
          hel, ite_true, List.length_append, List.length_singleton, hshort]
      simp only [receiverStep, hshort, ite_true, hraw, reduceCtorEq, ite_false]
    · simp only [receiverStep, hshort, ite_false] at hfalse hamb ⊢
      cases hp : parseOutput p beta (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 with
      | none =>
          have hn : (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 ≠ some (currentWord p beta M) := by
            intro he
            rw [he, parseOutput_currentWord] at hp
            cases hp
          simp only [hn, ite_false, afterDecision, hp]
          split
          · rename_i hbad
            exact (hamb (by simp only [afterDecision, hp, hbad, ite_true])).elim
          · rfl
      | some other =>
          by_cases ha : OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p beta)
              old (WaitedWordWindow.sourceRound t) other
          · by_cases he : other = M
            · subst other
              have hraw := (ReferenceFirstLiveHandoverPhaseReplay.parseOutput_eq_some_iff
                beta M _).mp hp
              rw [afterDecision, hp]
              simp only [ha, ite_true]
              rw [hraw]
              exact (ite_eq_left rfl).symm
            · have hf : (afterDecision p beta a data i fixing M
                  { initial p bank old with decoder := (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).1 }
                  t (bank.pending ++ [AffineBatchDecoder.entry p (observationTrace p a data i) t])
                  (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2).phase = .failedFalse := by
                simp only [afterDecision, hp, initial, ha, he, ite_true, ite_false]
              exact (hfalse hf).elim
          · have hn : (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 ≠ some (currentWord p beta M) := by
              intro hraw
              have he := Option.some.inj (hp.symm.trans
                (by rw [hraw]; exact parseOutput_currentWord p beta M))
              exact ha (he.symm ▸ haM)
            simp only [hn, ite_false, afterDecision, hp, ha]
  · have hdecode := AffineBatchDecoder.decodeStep_ineligible p (observationTrace p a data i) bank t hsmall hel
    simp only [serviceStep, initial, hel, ite_false, hdecode, reduceCtorEq]

private theorem installation_flag_raw
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hp : selected.view.payload = payload)
    (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (r.output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hn : (r.output.followers i).configuration = .ordinary next nextMemory)
    (hstrict : acceptedStart choice < (payload.downRecord i).val.sigma)
    (hmissing : i ∈ selected.view.pendingAtChoice)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hcomp : cut.rawComparison.isSome = true)
    (hflag : installationFlag payload r i = true) :
    cut.raw = some (currentWord p β (payload.downRecord i)) := by
  have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields r i logged cut hi hd hcomp
  obtain ⟨_, hlast, _⟩ :=
    (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag_ordinary_iff
      payload r i choice next memory nextMemory hc hn).mp hflag
  have hn' : r.output.next.followers i = .ordinary next nextMemory := by
    rw [r.output_eq] at hn ⊢
    exact hn
  obtain ⟨actualChoice, actualMemory, hchoice, _, _, hchange⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology r i next nextMemory hn'
  have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hchoice.symm.trans hc)
  obtain ⟨hchoiceEq, hmemoryEq⟩ := he
  subst actualChoice
  subst actualMemory
  have hnextStart : acceptedStart next = (payload.downRecord i).val.sigma := by
    simp only [acceptedStart, hlast]
  obtain ⟨l, c, after, raw, M, scan, registers, lastService, hil, hdc, ho, _⟩ :=
    hchange (by rw [hnextStart]; exact Nat.ne_of_lt hstrict)
  have hlEq : l = logged := Option.some.inj (hil.symm.trans hi)
  have hcEq : c = cut := Option.some.inj (hdc.symm.trans hd)
  subst l
  subst c
  have hnMismatch := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_no_rawMismatch
    r i logged cut after raw M scan registers lastService hi hd ho
  obtain ⟨_, _, actualLogged, _, _, _, hil', hcutdef⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
  have hlEq : actualLogged = logged := Option.some.inj (hil'.symm.trans hi)
  subst actualLogged
  have hnRaw : ¬ ReferenceDownReception.rawMismatch cut := by
    rw [hcutdef]
    exact hnMismatch
  have hraw : cut.raw = cut.expectedWord := by
    by_contra hne
    exact hnRaw (hfields.2.2.2.2.2.2.2.2.2.trans
      (congrArg some (decide_eq_false hne)))
  have hview : r.output.preparation.coordinator.downView = some selected.view :=
    congrArg (Option.map ReferenceActivePhysicalStep.Selection.view) hs
  have hexpected := selected.expected_down_word i
    ⟨hfields.1.1, hfields.1.2, hmissing⟩
  change ReferenceDownReception.expectedDownFlatWord (some selected.view) i
    r.input.row r.input.time =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) at hexpected
  rw [hp] at hexpected
  calc
    cut.raw = cut.expectedWord := hraw
    _ = ReferenceDownReception.expectedDownFlatWord
        r.output.preparation.coordinator.downView i r.input.row r.input.time :=
      hfields.2.2.2.2.2.2.1
    _ = some (currentWord p β (payload.downRecord i)) := by
      rw [hview, hexpected]
      rfl

private theorem finish_missing_iff
    {a : ActiveRoundActions.Assignment p.m p.K}
    (A : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (row : ActiveRoundActions.RewardRow p.K)
    (flags : ActiveRoundActions.Follower p.m → Bool)
    (i : ActiveRoundActions.Follower p.m) :
    i ∈ (ActiveRoundActions.finishLiveRound p.two_le_m A input row flags).missing ↔
      i ∈ A.missing ∧ ¬ ActiveRoundActions.confirmation p.two_le_m A input row i := by
  change i ∈ (if ActiveRoundActions.confirmation p.two_le_m A input row input.selected then
    A.missing.erase input.selected else A.missing) ↔ _
  by_cases hc : ActiveRoundActions.confirmation p.two_le_m A input row input.selected
  · have hi : ActiveRoundActions.confirmation p.two_le_m A input row i ↔ input.selected = i :=
      ⟨fun h => h.2.1, fun h => h ▸ hc⟩
    simp only [hc, ite_true, Finset.mem_erase, hi]
    tauto
  · have hi : ¬ ActiveRoundActions.confirmation p.two_le_m A input row i :=
      fun h => hc (h.2.1.symm ▸ h)
    simp only [hc, ite_false, hi, not_false_eq_true, and_true]

private theorem handover_bank_step
    (b : Fin (R).length) (k next : Fin (H b).length)
    (hsucc : next.val = k.val + 1)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (seed : DecoderState p)
    (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((H b)[k.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hbank : choice.downBatch = replayDownCalls i ((H b).take k.val) seed)
    (hnextBank : nextChoice.downBatch = replayDownCalls i ((H b).take next.val) seed)
    (hsmall : choice.downBatch.pending.length < AffineBatchDecoder.quota p)
    (hinp : (actualHandoverReplayData rate rewards C_star C_h z payload b
        (H b)[k.val].input.time).input =
      handoverRoundInput payload (H b)[k.val].input.row (H b)[k.val].input.time)
    (hstatus : (actualHandoverReplayData rate rewards C_star C_h z payload b
        (H b)[k.val].input.time).snapshot.status i = choice.status)
    (hinput : ActiveFollowerDownAcceptance.downSelected p i
        (H b)[k.val].input.row (H b)[k.val].input.time →
      choice.status = .unoccupied →
      observationTrace p payload.assignment
          (actualHandoverReplayData rate rewards C_star C_h z payload b) i (H b)[k.val].input.time =
        ActiveFollowerDownAcceptance.currentRoundInput p i (H b)[k.val].input.row (H b)[k.val].input.time
          (preparedOwnObservation (H b)[k.val] i) rate choice) :
    nextChoice.downBatch = (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment
        (actualHandoverReplayData rate rewards C_star C_h z payload b) i)
      choice.downBatch (H b)[k.val].input.time).1 := by
  let r := (H b)[k.val]
  let tr := observationTrace p payload.assignment
    (actualHandoverReplayData rate rewards C_star C_h z payload b) i
  let current := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
    (preparedOwnObservation r i) rate choice
  have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i choice memory hc
  rw [ReferenceFollowerDownDecoderReplay.preparedChoiceTime,
    ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
    (r.output.preparation.follower_alignment i).1,
    (r.output.preparation.follower_alignment i).2.2.1] at hcall
  have hstep : (AffineBatchDecoder.decodeStep p
      (ActiveFollowerDownAcceptance.currentInputExtension p current) choice.downBatch r.input.time).1 =
      (AffineBatchDecoder.decodeStep p tr choice.downBatch r.input.time).1 := by
    by_cases hdu : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        choice.status = .unoccupied
    · exact (congrArg Prod.fst (ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input
        p tr (ActiveFollowerDownAcceptance.currentInputExtension p current)
        choice.downBatch r.input.time (hinput hdu.1 hdu.2))).symm
    · have ha : ¬ AffineBatchDecoder.eligible current := by
        intro hel
        have h := (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff
          p i r.input.row r.input.time _ rate choice).mp hel
        exact hdu ⟨h.1, h.2.1⟩
      have hb : ¬ AffineBatchDecoder.eligible (tr r.input.time) := by
        intro hel
        obtain ⟨hd, hi, _, hu, _⟩ := eligible_iff p payload.assignment
          (actualHandoverReplayData rate rewards C_star C_h z payload b) i r.input.time |>.mp hel
        rw [hinp] at hd hi
        exact hdu ⟨⟨hd, hi⟩, hstatus.symm.trans hu⟩
      rw [AffineBatchDecoder.decodeStep_ineligible p _ _ _ hsmall ha,
        AffineBatchDecoder.decodeStep_ineligible p _ _ _ hsmall hb]
  dsimp only [r] at hcall
  rw [hnextBank, hsucc, List.take_succ_eq_append_getElem k.isLt]
  simp only [replayDownCalls,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, ReferenceFollowerDownDecoderReplay.foldDownCalls,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, hcall,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (AffineBatchDecoder.decodeStep p (ActiveFollowerDownAcceptance.currentInputExtension p current)
    (replayDownCalls i ((H b).take k.val) seed) r.input.time).1 = _
  rw [← hbank]
  exact hstep

private theorem localState_ext (s t : LocalState p)
    (hd : s.decoder = t.decoder) (ha : s.acceptedStart = t.acceptedStart)
    (hp : s.phase = t.phase) : s = t := by
  cases s
  cases t
  congr

private theorem run_pending_lt
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : ActiveRoundActions.Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (dates : List (Fin p.T))
    (s : LocalState p) (hs : s.decoder.pending.length < AffineBatchDecoder.quota p) :
    (run p beta a data i fixing M dates s).decoder.pending.length < AffineBatchDecoder.quota p := by
  induction dates generalizing s with
  | nil => exact hs
  | cons t dates ih =>
      exact ih _ (roundStep_pending_lt p beta a data i fixing M s t hs)

private theorem snapshotBefore_step_of_safe
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Fin (p.m - 1))
    (fixing : Fin p.T) (M : Down p beta) (seed : LocalState p) (t : Fin p.T)
    (ht : fixing.val ≤ t.val) (hc : (data t).cutoffBefore = false)
    (ho : (data t).overflowAfter = false) :
    snapshotBefore p beta a data i fixing M seed (t.val + 1) =
      serviceStep p beta a data i fixing M
        (snapshotBefore p beta a data i fixing M seed t.val) t := by
  let s := snapshotBefore p beta a data i fixing M seed t.val
  rw [ReferenceFirstLiveHandoverPhaseReplay.snapshotBefore_succ beta a data i fixing M seed t]
  change roundStep p beta a data i fixing M s t = serviceStep p beta a data i fixing M s t
  by_cases hu : s.phase.unresolved
  · simp only [roundStep, Nat.not_lt.mpr ht, hu, not_true_eq_false, or_self,
      ite_false, hc, ho, Bool.false_eq_true, false_and]
  · have hs : serviceStep p beta a data i fixing M s t = s := by
      cases hp : s.phase <;> simp only [serviceStep, hp]
      · exact (hu (Or.inl hp)).elim
      · exact (hu (Or.inr hp)).elim
    rw [roundStep_terminal p beta a data i fixing M s t hu, hs]

private theorem actual_normal_service
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (i : Fin (p.m - 1))
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (hstrict : acceptedStart before < (payload.downRecord i).val.sigma)
    (j : Fin (H b).length)
    (hsupport : (H b)[j.val].input.time.val + 1 ≤
      firstBadDate rate rewards C_star C_h z)
    (k : Fin (H b).length) (hkj : k.val < j.val)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((H b)[k.val].output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hkSmall : choice.downBatch.pending.length < AffineBatchDecoder.quota p) :
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let tr := observationTrace p payload.assignment data i
    serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
        (initial p choice.downBatch (acceptedStart before)) (H b)[k.val].input.time =
      let bank' := (AffineBatchDecoder.decodeStep p tr choice.downBatch (H b)[k.val].input.time).1
      if (AffineBatchDecoder.decodeStep p tr choice.downBatch (H b)[k.val].input.time).2 =
          some (currentWord p β (payload.downRecord i)) then
        ⟨bank', (payload.downRecord i).val.sigma, .acceptedUnconfirmed⟩
      else initial p bank' (acceptedStart before) := by
  obtain ⟨fp, fb, fm, hfbirth, hfbefore, _hfu, _hfs, hfailures⟩ :=
    actual_later_handover_awaiting_service_failure_coverage rate rewards C_star C_h z b hb i
  obtain ⟨hfp, hfb, hfm⟩ := birth_seed_unique rate hfbirth hbirth hfbefore hbefore
  subst fp fb fm
  obtain ⟨actual, actualMemory, hactual, hcover⟩ := hfailures k
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hactual.symm.trans hc)
  subst actual actualMemory
  have hsafe := (ReferencePostReplacementCollectionStoppedReleaseAdaptation.safe_iff_decoderDateKeptAt
    rate rewards C_star C_h z (H b)[j.val].input.time).mpr
      (originalInclusiveGate_decoderDateKeptAt rate rewards C_star C_h z _ hsupport)
  have hlt : (H b)[k.val].input.time.val < (H b)[j.val].input.time.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      handover_time rate rewards C_star C_h z b j]
    omega
  have hnotfailed' := fun h => hsafe _ hlt (hcover hu h)
  have htime := handover_time rate rewards C_star C_h z b k
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth
  have haM : OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p β) (acceptedStart before)
      (WaitedWordWindow.sourceRound (H b)[k.val].input.time) (payload.downRecord i) := by
    exact ⟨hstrict, by
      change payload.sigma.val + 1 ≤ (H b)[k.val].input.time.val + 1
      omega⟩
  exact awaiting_service_classification β payload.assignment _ i payload.sigma
    (payload.downRecord i) choice.downBatch _ (H b)[k.val].input.time
    hkSmall haM (fun h => hnotfailed' (Or.inl h)) (fun h => hnotfailed' (Or.inr h))

private theorem actual_flag_decoder_raw
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (i : Fin (p.m - 1))
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (hstrict : acceptedStart before < (payload.downRecord i).val.sigma)
    (k : Fin (H b).length)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((H b)[k.val].output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i (H b)[k.val].input.row (H b)[k.val].input.time)
    (hf : installationFlag payload (H b)[k.val] i = true) :
    (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i)
      choice.downBatch (H b)[k.val].input.time).2 = some (currentWord p β (payload.downRecord i)) := by
  obtain ⟨cp, cb, cm, hcbirth, hcbefore, _hcu, _hcs, hcalls⟩ :=
    actual_later_handover_awaiting_calls rate rewards C_star C_h z b hb i
  obtain ⟨hcp, hcb, hcm⟩ := birth_seed_unique rate hcbirth hbirth hcbefore hbefore
  subst cp cb cm
  obtain ⟨selected, actual, actualMemory, hs, hp, hactual, hawait⟩ := hcalls k
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hactual.symm.trans hc)
  subst actual
  subst actualMemory
  obtain ⟨logged, cut, hi, hd, hloggedBank, _, hcomp, _, _, _⟩ := (hawait hu).2 hdown
  obtain ⟨hk, hrecord⟩ := handover_index rate rewards C_star C_h z b k
  obtain ⟨_, _, _, next, nextMemory, _, _, _, _, hnext, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      rewards C_star C_h z ⟨b.val + k.val, hk⟩ i
  rw [← hrecord] at hnext
  have hmissing : i ∈ selected.view.pendingAtChoice := by
    obtain ⟨_, _, dates⟩ :=
      actual_later_handover_snapshot rewards C_star C_h z b hb
    obtain ⟨sel, states, memories, hsel, _, hconfigs, _, _, _, hmissing⟩ := dates k
    have hselEq := Option.some.inj (hsel.symm.trans hs)
    subst sel
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hconfigs i).symm.trans hc)
    exact hmissing i (he.symm ▸ hu)
  have hraw := installation_flag_raw rate (H b)[k.val] payload selected hs hp i choice next memory
    nextMemory hc hnext (by rw [(hawait hu).1]; exact hstrict) hmissing logged cut hi hd hcomp hf
  obtain ⟨dp, db, dm, hdbirth, hdbefore, _hdu, _hds, hdecoder⟩ :=
    actual_later_handover_decoder_correspondence rewards C_star C_h z b hb i
  obtain ⟨hdp, hdb, hdm⟩ := birth_seed_unique rate hdbirth hbirth hdbefore hbefore
  subst dp db dm
  obtain ⟨_, states, memories, inputState, _, _, _, hconfigs, _, hbank, hchoiceBank,
      _, _, _, _, hcutCases⟩ := hdecoder k
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hconfigs i).symm.trans hc)
  rcases hcutCases cut hd with hn | ⟨l, _, _, _, hraw'⟩
  · rw [hn] at hcomp
    cases hcomp
  · rw [← hbank, ← hchoiceBank, he] at hraw'
    exact hraw'.symm.trans hraw

private theorem live_snapshot_step
    (a : ActiveRoundActions.Assignment p.m p.K)
    (live : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (cutoff overflow : Fin p.T → Bool) (i : Fin (p.m - 1))
    (t u : Fin p.T) (hu : u.val = t.val + 1)
    (hne : (ActiveObservationBridge.liveSnapshotBefore p a live t).missing.Nonempty) :
    let data := fromLive p a live cutoff overflow
    (data u).snapshot.status i = ActiveRoundActions.statusAfterAcceptance
      (data t).snapshot (live t).input (live t).acceptCurrent i ∧
    (i ∈ (data u).snapshot.missing ↔ i ∈ (data t).snapshot.missing ∧
      ¬ physicalConfirmation p a data i t) := by
  dsimp only
  have hs := ReferenceFirstLiveHandoverSnapshotPrefix.snapshot_successor live t u hu
  constructor
  · change (ActiveObservationBridge.liveSnapshotBefore p a live u).status i = _
    rw [hs]
    exact ReferenceFirstLiveHandoverSnapshotPrefix.finish_status_while_missing _ _ _ _ hne i
  · change i ∈ (ActiveObservationBridge.liveSnapshotBefore p a live u).missing ↔ _
    rw [hs]
    exact finish_missing_iff _ _ _ _ i

section CalendarInduction

open _root_.Bandits.Support.ReferenceCompletePhysicalHistory (completeSuffixRecords)
open _root_.Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence
  (actualHandoverRecords actualLaterHandoverLive)

variable
    (b : Fin (completeSuffixRecords rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (completeSuffixRecords rate z rewards C_star C_h)[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (completeSuffixRecords rate z rewards C_star C_h)[b.val] payload)
    (i : Fin (p.m - 1))
    (hbefore : (completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.followers i =
      .ordinary before beforeMemory)
    (hstrict : acceptedStart before < (payload.downRecord i).val.sigma)
    (hwell : before.downBatch.pending.length < AffineBatchDecoder.quota p)
    (selected : ∀ k : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
      ReferenceActivePhysicalStep.Selection (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input)
    (states : Fin (actualHandoverRecords rate rewards C_star C_h z b).length →
      Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (actualHandoverRecords rate rewards C_star C_h z b).length →
      Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hs : ∀ k, (actualHandoverRecords rate rewards C_star C_h z b)[k.val].output.preparation.coordinator.selection =
      some (selected k))
    (hc : ∀ (k : Fin (actualHandoverRecords rate rewards C_star C_h z b).length) (f : Fin (p.m - 1)),
      ((actualHandoverRecords rate rewards C_star C_h z b)[k.val].output.preparation.followers.followers f).configuration =
      .ordinary (states k f) (memories k f))
    (hbankChoice : ∀ k, (states k i).downBatch =
      replayDownCalls i
        ((actualHandoverRecords rate rewards C_star C_h z b).take k.val) before.downBatch)
    (hsnapshot : ∀ k, ActiveObservationBridge.liveSnapshotBefore p payload.assignment
      (actualLaterHandoverLive rate rewards C_star C_h z payload (actualHandoverRecords rate rewards C_star C_h z b))
      (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.time =
        ⟨(selected k).view.pendingAtChoice, fun f => (states k f).status⟩)
    (hinput : ∀ k, ActiveFollowerDownAcceptance.downSelected p i
      (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.row
      (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.time → (states k i).status = .unoccupied →
      observationTrace p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b)
        i (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.time =
      ActiveFollowerDownAcceptance.currentRoundInput p i
        (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.row
        (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.time (preparedOwnObservation
          (actualHandoverRecords rate rewards C_star C_h z b)[k.val] i) rate (states k i))
    (hstageFacts : ∀ k,
      ((states k i).status = .unoccupied ∧ i ∈ (selected k).view.pendingAtChoice ∧
        acceptedStart (states k i) = acceptedStart before) ∨
      ((states k i).status = .pending ∧
        acceptedStart (states k i) = (payload.downRecord i).val.sigma))
include hb hbirth hbefore hstrict hwell hs hc hbankChoice hsnapshot hinput hstageFacts

local notation "qBefore" => actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before

omit hstrict hwell hs hbankChoice hsnapshot hinput hstageFacts in
private theorem actual_accepted_next_start
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1)
    (hu : (states prev i).status = .unoccupied)
    (hserv : (serviceStep p β payload.assignment
      (actualHandoverReplayData rate rewards C_star C_h z payload b) i payload.sigma (payload.downRecord i)
      (initial p (states prev i).downBatch (acceptedStart before))
      (H b)[prev.val].input.time).phase = .acceptedUnconfirmed) :
    acceptedStart (states k i) = (payload.downRecord i).val.sigma := by
  obtain ⟨ap, ab, am, habirth, habefore, _hau, _has, hacceptance⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_current_acceptance_output
      rate rewards C_star C_h z b hb i
  obtain ⟨hap, hab, ham⟩ := birth_seed_unique rate habirth hbirth habefore hbefore
  subst ap ab am
  obtain ⟨choice, memory, hchoice, hout⟩ := hacceptance prev
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hc prev i))
  subst choice
  subst memory
  obtain ⟨_, after, afterMemory, hafter, hlast⟩ := hout hu hserv
  have hadj : (H b)[k.val].input.state = (H b)[prev.val].output.next := by
    obtain ⟨hpk, hpr⟩ := handover_index rate rewards C_star C_h z b prev
    obtain ⟨hkk, hkr⟩ := handover_index rate rewards C_star C_h z b k
    rw [hpr, hkr]
    have had := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z (b.val + prev.val) (by omega)
    simpa only [show b.val + k.val = b.val + prev.val + 1 by omega] using had
  obtain ⟨actualInput, actualMemory, hactualInput, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice (H b)[k.val] i
      (states k i) (memories k i) (hc k i)
  rw [hadj] at hactualInput
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hactualInput.symm.trans hafter)
  subst actualInput
  subst actualMemory
  rw [ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply]
  simp only [acceptedStart, hlast]

omit hwell hs hbankChoice hinput hstageFacts in
private theorem actual_pending_next_raw
    (prev k : Fin (H b).length) (hu : (states prev i).status = .unoccupied)
    (hbp : (states k i).status = .pending)
    (hBS : ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[k.val].input.time).snapshot.status i =
      ActiveRoundActions.statusAfterAcceptance
        ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[prev.val].input.time).snapshot
        ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
      rate rewards C_star C_h z payload (H b)) (H b)[prev.val].input.time).input
        (installationFlag payload (H b)[prev.val]) i)
 :
    (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i)
      (states prev i).downBatch (H b)[prev.val].input.time).2 =
        some (currentWord p β (payload.downRecord i)) := by
  let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
    rate rewards C_star C_h z payload (H b)
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  have hcalendar (k : Fin (H b).length) :=
    handover_calendar rate rewards C_star C_h z b payload hbirth k
  have hstatus (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).snapshot.status i = (states k i).status :=
    congrArg (fun A => A.status i) (hsnapshot k)
  let A := (data (H b)[prev.val].input.time).snapshot
  let B := (data (H b)[k.val].input.time).snapshot
  have htest : A.status i = .unoccupied ∧
      (live (H b)[prev.val].input.time).input.slot = PublicDiscreteDraws.downSlot ∧
      (live (H b)[prev.val].input.time).input.selected = i ∧
      installationFlag payload (H b)[prev.val] i = true := by
    by_contra hn
    have hkeep : B.status i = A.status i := hBS.trans (ite_eq_right hn)
    rw [hstatus k, hstatus prev, hbp, hu] at hkeep
    cases hkeep
  have hdsel : ActiveFollowerDownAcceptance.downSelected p i
      (H b)[prev.val].input.row (H b)[prev.val].input.time := by
    have hd := htest.2.1
    have hid := htest.2.2.1
    rw [congrArg ActiveRoundActions.LiveRoundData.input (hcalendar prev)] at hd hid
    exact ⟨hd, hid⟩
  exact actual_flag_decoder_raw rate rewards C_star C_h z b hb payload before beforeMemory hbirth i
    hbefore hstrict prev (states prev i) (memories prev i) (hc prev i) hu hdsel htest.2.2.2

omit hwell hs hbankChoice hinput in
private theorem actual_calendar_phase_step
    (j : Fin (H b).length)
    (hsupport : (H b)[j.val].input.time.val + 1 ≤
      firstBadDate rate rewards C_star C_h z)
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1) (hkj : k.val ≤ j.val)
    (hprior :
      let q := qBefore (H b)[prev.val].input.time.val
      q.decoder = (states prev i).downBatch ∧
      q.acceptedStart = acceptedStart (states prev i) ∧
      q.phase = if i ∈ (selected prev).view.pendingAtChoice then
        if (states prev i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed)
    (hkSmall : (states prev i).downBatch.pending.length < AffineBatchDecoder.quota p)
    (hbankNext : (states k i).downBatch = (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i) (states prev i).downBatch
      (H b)[prev.val].input.time).1)
    (hBS : ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[k.val].input.time).snapshot.status i =
      ActiveRoundActions.statusAfterAcceptance
        ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[prev.val].input.time).snapshot
        ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
      rate rewards C_star C_h z payload (H b)) (H b)[prev.val].input.time).input
        (installationFlag payload (H b)[prev.val]) i)
    (hmem : i ∈ (selected k).view.pendingAtChoice ↔
      i ∈ (selected prev).view.pendingAtChoice ∧
        ¬ physicalConfirmation p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i (H b)[prev.val].input.time)
    (hq : qBefore (H b)[k.val].input.time.val = serviceStep p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i
      payload.sigma (payload.downRecord i) (qBefore (H b)[prev.val].input.time.val) (H b)[prev.val].input.time) :
    let q := qBefore (H b)[k.val].input.time.val
    q.decoder = (states k i).downBatch ∧
    q.acceptedStart = acceptedStart (states k i) ∧
    q.phase = if i ∈ (selected k).view.pendingAtChoice then
      if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed := by
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let tr := observationTrace p payload.assignment data i
  let q (k : Fin (H b).length) := qBefore (H b)[k.val].input.time.val
  have hstatus (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).snapshot.status i = (states k i).status :=
    congrArg (fun A => A.status i) (hsnapshot k)
  let A := (data (H b)[prev.val].input.time).snapshot
  let B := (data (H b)[k.val].input.time).snapshot
  change (q k).decoder = (states k i).downBatch ∧
    (q k).acceptedStart = acceptedStart (states k i) ∧
    (q k).phase = (if i ∈ (selected k).view.pendingAtChoice then
      if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed)
  change (q prev).decoder = (states prev i).downBatch ∧
    (q prev).acceptedStart = acceptedStart (states prev i) ∧
    (q prev).phase = (if i ∈ (selected prev).view.pendingAtChoice then
      if (states prev i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed) at hprior
  have hqStep : q k = serviceStep p β payload.assignment data i payload.sigma
    (payload.downRecord i) (q prev) (H b)[prev.val].input.time := hq
  obtain ⟨hqd, hqa, hqp⟩ := hprior
  have hprev : prev.val < j.val := by omega
  have hstartNext (hpending : (states k i).status = .pending) :
      acceptedStart (states k i) = (payload.downRecord i).val.sigma := by
    rcases hstageFacts k with h | h
    · rw [hpending] at h
      cases h.1
    · exact h.2
  by_cases hu : (states prev i).status = .unoccupied
  · have hi : i ∈ (selected prev).view.pendingAtChoice := by
      rcases hstageFacts prev with h | h
      · exact h.2.1
      · rw [hu] at h
        cases h.1
    rw [ite_eq_left hi, ite_eq_left hu] at hqp
    have haw : acceptedStart (states prev i) =
        acceptedStart before := by
      rcases hstageFacts prev with h | h
      · exact h.2.2
      · rw [hu] at h
        cases h.1
    have hqaState : q prev = initial p (states prev i).downBatch (acceptedStart before) :=
      localState_ext _ _ hqd (hqa.trans haw) hqp
    have hnormal := actual_normal_service rate rewards C_star C_h z b hb payload before beforeMemory hbirth i hbefore hstrict j hsupport
      prev hprev (states prev i) (memories prev i) (hc prev i) hu hkSmall
    have hnc : ¬ physicalConfirmation p payload.assignment data i (H b)[prev.val].input.time := by
      intro hconfirm
      have ho := ActiveRoundActions.confirmation_implies_occupied p.two_le_m A _ _ i hconfirm
      rcases ho with ho | ho <;> rw [hstatus prev, hu] at ho <;> cases ho
    have hib := hmem.mpr ⟨hi, hnc⟩
    rw [hqStep, hqaState, hnormal]
    dsimp only
    rw [← hbankNext]
    by_cases hraw : (AffineBatchDecoder.decodeStep p tr (states prev i).downBatch
        (H b)[prev.val].input.time).2 = some (currentWord p β (payload.downRecord i))
    · rw [ite_eq_left hraw]
      have hserv : (serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
          (initial p (states prev i).downBatch (acceptedStart before))
          (H b)[prev.val].input.time).phase = .acceptedUnconfirmed := by
        rw [hnormal, ite_eq_left hraw]
      have hcurrentStart := actual_accepted_next_start
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
        (b := b) (hb := hb) (payload := payload) (before := before) (beforeMemory := beforeMemory)
        (hbirth := hbirth) (i := i) (hbefore := hbefore) (states := states) (memories := memories)
        (hc := hc) prev k hk hu hserv
      have hnu : (states k i).status ≠ .unoccupied := by
        intro hub
        rcases hstageFacts k with h | h
        · rw [h.2.2] at hcurrentStart
          omega
        · rw [hub] at h
          cases h.1
      rw [ite_eq_left hib, ite_eq_right hnu, hcurrentStart]
      exact ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right hraw]
      have hub : (states k i).status = .unoccupied := by
        by_contra hnu
        have hbp : (states k i).status = .pending := by
          rcases hstageFacts k with h | h
          · exact (hnu h.1).elim
          · exact h.1
        exact hraw (actual_pending_next_raw
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
          (b := b) (hb := hb) (payload := payload) (before := before) (beforeMemory := beforeMemory)
          (hbirth := hbirth) (i := i) (hbefore := hbefore) (hstrict := hstrict)
          (selected := selected) (states := states) (memories := memories) (hc := hc)
          (hsnapshot := hsnapshot) prev k hu hbp hBS)
      have hstart := hstageFacts k
      rcases hstart with hstart | hstart
      · rw [ite_eq_left hib, ite_eq_left hub, hstart.2.2]
        exact ⟨rfl, rfl, rfl⟩
      · rw [hub] at hstart
        cases hstart.1
  ·
    have hbst : B.status i = A.status i := hBS.trans (ite_eq_right (fun h => hu ((hstatus prev).symm.trans h.1)))
    have hkp : (states k i).status = .pending := by
      rcases hstageFacts prev with h | h
      · exact (hu h.1).elim
      · exact (hstatus k).symm.trans (hbst.trans ((hstatus prev).trans h.1))
    have hnotEligible : ¬ AffineBatchDecoder.eligible (tr (H b)[prev.val].input.time) :=
      fun h => hu ((hstatus prev).symm.trans (eligible_iff p payload.assignment data i _ |>.mp h).2.2.2.1)
    rw [AffineBatchDecoder.decodeStep_ineligible p tr _ _ hkSmall hnotEligible] at hbankNext
    by_cases hi : i ∈ (selected prev).view.pendingAtChoice
    · rw [ite_eq_left hi, ite_eq_right hu] at hqp
      by_cases hconfirm : physicalConfirmation p payload.assignment data i (H b)[prev.val].input.time
      · have hnotmem : i ∉ (selected k).view.pendingAtChoice := fun h => (hmem.mp h).2 hconfirm
        rw [ite_eq_right hnotmem, hqStep]
        simp only [serviceStep, hqp, hconfirm, ite_true]
        refine ⟨hqd.trans hbankNext.symm, ?_, trivial⟩
        rw [hstartNext hkp]
        rcases hstageFacts prev with h | h
        · exact (hu h.1).elim
        · exact hqa.trans h.2
      · rw [ite_eq_left (hmem.mpr ⟨hi, hconfirm⟩), ite_eq_right (by rw [hkp]; decide), hqStep]
        simp only [serviceStep, hqp, hconfirm, ite_false]
        refine ⟨hqd.trans hbankNext.symm, ?_, trivial⟩
        rw [hstartNext hkp]
        rcases hstageFacts prev with h | h
        · exact (hu h.1).elim
        · exact hqa.trans h.2
    · rw [ite_eq_right hi] at hqp
      rw [ite_eq_right (fun h => hi (hmem.mp h).1), hqStep]
      simp only [serviceStep, hqp]
      refine ⟨hqd.trans hbankNext.symm, ?_, trivial⟩
      rw [hstartNext hkp]
      rcases hstageFacts prev with h | h
      · exact (hi h.2.1).elim
      · exact hqa.trans h.2

private theorem actual_calendar_step
    (j : Fin (H b).length)
    (hsupport : (H b)[j.val].input.time.val + 1 ≤
      firstBadDate rate rewards C_star C_h z)
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1) (hkj : k.val ≤ j.val)
    (hprior :
      let q := qBefore (H b)[prev.val].input.time.val
      q.decoder = (states prev i).downBatch ∧
      q.acceptedStart = acceptedStart (states prev i) ∧
      q.phase = if i ∈ (selected prev).view.pendingAtChoice then
        if (states prev i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed) :
    let q := qBefore (H b)[k.val].input.time.val
    q.decoder = (states k i).downBatch ∧
    q.acceptedStart = acceptedStart (states k i) ∧
    q.phase = if i ∈ (selected k).view.pendingAtChoice then
      if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed := by
  let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
    rate rewards C_star C_h z payload (H b)
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q (k : Fin (H b).length) := qBefore (H b)[k.val].input.time.val
  have htime (k : Fin (H b).length) : (H b)[k.val].input.time.val = payload.sigma.val + k.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
  have hcalendar := handover_calendar rate rewards C_star C_h z b payload hbirth prev
  have hstatus : (data (H b)[prev.val].input.time).snapshot.status i = (states prev i).status :=
    congrArg (fun A => A.status i) (hsnapshot prev)
  have hmissing (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).snapshot.missing = (selected k).view.pendingAtChoice :=
    congrArg ActiveRoundActions.Snapshot.missing (hsnapshot k)
  have hdataInput : (data (H b)[prev.val].input.time).input =
      ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
        payload (H b)[prev.val].input.row (H b)[prev.val].input.time :=
    congrArg ActiveRoundActions.LiveRoundData.input hcalendar
  have hprev : prev.val < j.val := by omega
  obtain ⟨hqd, hqa, hqp⟩ := hprior
  have hsucc : (H b)[k.val].input.time.val = (H b)[prev.val].input.time.val + 1 := by
    rw [htime, htime]
    omega
  let A := (data (H b)[prev.val].input.time).snapshot
  have hne : A.missing.Nonempty := by
    rw [hmissing]
    have htest : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        (H b)[prev.val] = true := List.mem_takeWhile_imp (List.getElem_mem prev.isLt)
    unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice at htest
    rw [hs prev] at htest
    exact of_decide_eq_true htest
  obtain ⟨hBS, hmem⟩ := live_snapshot_step payload.assignment live
    (actualHandoverCutoffBefore rate rewards C_star C_h z)
    (actualHandoverOverflowAfter rate rewards C_star C_h z) i
    (H b)[prev.val].input.time (H b)[k.val].input.time hsucc hne
  rw [congrArg ActiveRoundActions.LiveRoundData.acceptCurrent hcalendar] at hBS
  have hmem' : i ∈ (selected k).view.pendingAtChoice ↔
      i ∈ (selected prev).view.pendingAtChoice ∧
        ¬ physicalConfirmation p payload.assignment data i (H b)[prev.val].input.time := by
    rw [← hmissing k, ← hmissing prev]
    exact hmem
  have hcut : (data (H b)[prev.val].input.time).cutoffBefore = false :=
    handover_cutoff_false rate rewards C_star C_h z b hb prev
  have hq : q k = serviceStep p β payload.assignment data i payload.sigma
      (payload.downRecord i) (q prev) (H b)[prev.val].input.time := by
    change snapshotBefore p β payload.assignment data i payload.sigma (payload.downRecord i)
      (initial p before.downBatch (acceptedStart before)) (H b)[k.val].input.time.val = _
    rw [hsucc]
    exact snapshotBefore_step_of_safe β payload.assignment data i payload.sigma
      (payload.downRecord i) _ (H b)[prev.val].input.time
      (by rw [htime]; omega) hcut
      (original_predecessor_overflow_false rate rewards C_star C_h z b hb j hsupport prev hprev)
  have hkSmall : (states prev i).downBatch.pending.length < AffineBatchDecoder.quota p :=
    hqd ▸ run_pending_lt β payload.assignment data i payload.sigma (payload.downRecord i) _ _ hwell
  have hbankNext := handover_bank_step rate rewards C_star C_h z b prev k
    (by omega) payload i before.downBatch (states prev i) (states k i)
    (memories prev i) (hc prev i) (hbankChoice prev) (hbankChoice k) hkSmall
    hdataInput hstatus (hinput prev)
  exact actual_calendar_phase_step
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
    (b := b) (hb := hb) (payload := payload) (before := before) (beforeMemory := beforeMemory)
    (hbirth := hbirth) (i := i) (hbefore := hbefore) (hstrict := hstrict)
    (selected := selected) (states := states) (memories := memories) (hc := hc)
    (hsnapshot := hsnapshot) (hstageFacts := hstageFacts)
    j hsupport prev k hk hkj ⟨hqd, hqa, hqp⟩ hkSmall hbankNext hBS hmem' hq

private theorem actual_calendar_correspondence :
    ∀ j : Fin (H b).length, (H b)[j.val].input.time.val + 1 ≤
      firstBadDate rate rewards C_star C_h z →
      let q := qBefore (H b)[j.val].input.time.val
      q.decoder = (states j i).downBatch ∧
      q.acceptedStart = acceptedStart (states j i) ∧
      q.phase = if i ∈ (selected j).view.pendingAtChoice then
        if (states j i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed := by
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q (k : Fin (H b).length) := qBefore (H b)[k.val].input.time.val
  have htime (k : Fin (H b).length) : (H b)[k.val].input.time.val = payload.sigma.val + k.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
  intro j hsupport
  have hcorrespondence (n : ℕ) : ∀ (k : Fin (H b).length), k.val = n → k.val ≤ j.val →
      (q k).decoder = (states k i).downBatch ∧
      (q k).acceptedStart = acceptedStart (states k i) ∧
      (q k).phase = if i ∈ (selected k).view.pendingAtChoice then
        if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed := by
    induction n with
    | zero =>
        intro k hk _
        have hbank0 := hbankChoice k
        rw [hk, List.take_zero] at hbank0
        change (states k i).downBatch = before.downBatch at hbank0
        have hq : q k = initial p before.downBatch (acceptedStart before) := by
          change snapshotBefore _ _ _ _ _ _ _ _ _ = _
          rw [htime, hk, Nat.add_zero]
          exact ReferenceFirstLiveHandoverPhaseReplay.snapshotBefore_at_or_before_fixing
            β payload.assignment data i payload.sigma (payload.downRecord i) _ payload.sigma.val le_rfl
        have hzeroSnapshot := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive_prebirth_snapshot
          rate rewards C_star C_h z payload (H b) (H b)[k.val].input.time (by rw [htime, hk, Nat.add_zero])
        have hstatus0 : (states k i).status = .unoccupied := by
          have he := (hsnapshot k).symm.trans hzeroSnapshot
          exact congrArg (fun A => A.status i) he
        have haw := hstageFacts k
        rcases haw with haw | haw
        · rw [hq, hbank0, haw.2.2, ite_eq_left haw.2.1, ite_eq_left hstatus0]
          exact ⟨rfl, rfl, rfl⟩
        · rw [hstatus0] at haw
          cases haw.1
    | succ n ih =>
        intro k hk hkj
        let prev : Fin (H b).length := ⟨n, by have := k.isLt; omega⟩
        exact actual_calendar_step rate rewards C_star C_h z b hb payload before beforeMemory hbirth i
          hbefore hstrict hwell selected states memories hs hc hbankChoice hsnapshot hinput hstageFacts
          j hsupport prev k (by dsimp only [prev]; omega) hkj (ih prev rfl (by change n ≤ j.val; omega))
  exact hcorrespondence j.val j rfl le_rfl

end CalendarInduction

/-- Original inclusive-stop correspondence on every actual later birth.
The original gate supplies strict-past safety internally. Pending membership
then gives the incoming replay indicator; no raw replacement label is used. -/
public theorem original_later_handover_originalGate_phase_J
    (b : Fin (R).length) (i : Fin (p.m - 1)) :
    ReferenceCollectionPhaseHistory.laterChosen (R[b.val]'(b.isLt)).input = true →
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) payload ∧
      (R[b.val]'(b.isLt)).input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H b).length, ((H b)[j.val]'(j.isLt)).input.time.val + 1 ≤
          firstBadDate rate rewards C_star C_h z →
        ∃ (selected : ReferenceActivePhysicalStep.Selection (((H b)[j.val]'(j.isLt)).input))
          (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          ((H b)[j.val]'(j.isLt)).output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (((H b)[j.val]'(j.isLt)).output.preparation.followers.followers i).configuration =
            .ordinary choice memory ∧
          let data := actualHandoverReplayData rate rewards C_star C_h z payload b
          let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
            ((H b)[j.val]'(j.isLt)).input.time.val
          q.decoder = choice.downBatch ∧
          q.acceptedStart = acceptedStart choice ∧
          q.phase = (if i ∈ selected.view.pendingAtChoice then
            if choice.status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
          else .confirmed) ∧
          (i ∈ selected.view.pendingAtChoice →
            J p payload.assignment data payload.sigma q ((H b)[j.val]'(j.isLt)).input.time = 1) := by
  intro hb
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict,
      hwell, _hpendingStamps, _hchron, _hcollectedStamps, _hseedPhase, _hseedDates⟩ :=
    actual_later_handover_stoppedReplay_seed rate rewards C_star C_h z b hb i
  obtain ⟨dp, db, dm, hdbirth, hdbefore, _hdu, _hds, hdecoder⟩ :=
    actual_later_handover_decoder_correspondence rewards C_star C_h z b hb i
  obtain ⟨hdp, hdb, hdm⟩ := birth_seed_unique rate hdbirth hbirth hdbefore hbefore
  subst dp db dm
  have hstages :=
    ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_choice_stages
      rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hstages
  obtain ⟨sp, hsbirth, hfollowers⟩ := hstages
  obtain ⟨sb, sm, hsbefore, _hsu, _hss, hstages⟩ := hfollowers i
  obtain ⟨hsp, hsb, hsm⟩ := birth_seed_unique rate hsbirth hbirth hsbefore hbefore
  subst sp sb sm
  dsimp only at hdecoder
  choose selected states memories inputState inputMemory hs hp hc hin hbank
    hchoiceBank hsnapshot hoccupied hnotselected hinput hcutCases using hdecoder
  have hstage (k : Fin (H b).length) := hstages k
  have hstageFacts (k : Fin (H b).length) :
      ((states k i).status = .unoccupied ∧ i ∈ (selected k).view.pendingAtChoice ∧
        acceptedStart (states k i) = acceptedStart before) ∨
      ((states k i).status = .pending ∧
        acceptedStart (states k i) = (payload.downRecord i).val.sigma) := by
    obtain ⟨sel, choice, memory, hsel, _, hchoice, hcases⟩ := hstage k
    have hselEq := Option.some.inj (hsel.symm.trans (hs k))
    subst sel
    obtain ⟨hchoiceEq, hmemoryEq⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (hc k i))
    subst choice
    subst memory
    rcases hcases with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.2⟩
    · exact Or.inr ⟨h.2.1, h.2.2.2⟩
    · exact Or.inr ⟨h.2.1, h.2.2.2⟩
  have hbankChoice (k : Fin (H b).length) : (states k i).downBatch =
      replayDownCalls i ((H b).take k.val) before.downBatch :=
    (hchoiceBank k).trans (hbank k)
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  intro j hgate
  obtain ⟨hqd, hqa, hqp⟩ := actual_calendar_correspondence rate rewards C_star C_h z b hb
    payload before beforeMemory hbirth i hbefore hstrict hwell.1 selected states memories
    hs hc hbankChoice hsnapshot (fun k hd hu => (hinput k hd hu).1) hstageFacts j hgate
  refine ⟨selected j, states j i, memories j i, hs j, hp j, hc j i, hqd, hqa, hqp, ?_⟩
  intro hi
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
    (H b)[j.val].input.time.val
  have hu : q.phase.unresolved := by
    change q.phase = .awaitingDown ∨ q.phase = .acceptedUnconfirmed
    change q.phase = _ at hqp
    rw [hqp, ite_eq_left hi]
    split_ifs <;> simp only [true_or, or_true]
  have ht : payload.sigma.val ≤ (H b)[j.val].input.time.val := by
    rw [handover_time rate rewards C_star C_h z b j,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
    omega
  exact ite_eq_left ⟨ht, hu, handover_cutoff_false rate rewards C_star C_h z b hb j⟩


private theorem original_physical_tick_le_replay
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (t : Fin p.T) :
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before t.val
    originalHandoverPhysicalTick rate rewards C_star C_h z b i t ≤
      J p payload.assignment data payload.sigma q t * X p payload.assignment data i q t := by
  unfold originalHandoverPhysicalTick
  split_ifs with hservice
  · obtain ⟨j, ht, selected, hs, hi, hgate, hservices⟩ := hservice
    subst t
    obtain ⟨P, B, M, hP, hB, _, _, hdates⟩ :=
      original_later_handover_originalGate_phase_J rate rewards C_star C_h z b i hb
    obtain ⟨hP, hB, hM⟩ := birth_seed_unique rate hP hbirth hB hbefore
    subst P B M
    obtain ⟨sel, choice, memory, hsel, hp, hc, _, _, hphase, hJ⟩ := hdates j hgate
    have he := Option.some.inj (hsel.symm.trans hs)
    subst sel
    let r := (H b)[j.val]
    let t := r.input.time
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before t.val
    change 1 ≤ J p payload.assignment data payload.sigma q t * X p payload.assignment data i q t
    rw [hJ hi, one_mul]
    obtain ⟨P, hP, hframes⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
    have he := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      R[b.val] P payload hP hbirth
    subst P
    obtain ⟨sel, states, memories, hsel, hpay, hconfigs, hsnap, hfields, hnotReleased, _⟩ := hframes j
    have he := Option.some.inj (hsel.symm.trans hs)
    subst sel
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hc.symm.trans (hconfigs i))
    subst choice memory
    have hlookup := handover_lookup rate rewards C_star C_h z b j
    have hcalendar := handover_calendar rate rewards C_star C_h z b payload hbirth j
    have hdataInput : (data t).input = handoverRoundInput payload r.input.row t :=
      congrArg ActiveRoundActions.LiveRoundData.input hcalendar
    have hdataRewards : (data t).rewards = handoverWholeRewardRow r :=
      congrArg ActiveRoundActions.LiveRoundData.rewards hcalendar
    have hdataSnapshot : (data t).snapshot =
        ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩ := hsnap
    obtain ⟨input, inputMemory, hin, _, _⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice r i _ _ (hconfigs i)
    obtain ⟨actual, hactual, hcode⟩ :=
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_actual_choice rate rewards C_star C_h t i z r input inputMemory hlookup hin
    obtain ⟨he, _⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hactual.symm.trans (hconfigs i))
    subst actual
    have hfeedback
        (hd : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot)
        (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 t).1 = i) (player : Fin p.m) :
        (r.output.preparation.feedback.observations player).val.val =
          ActiveRoundActions.feedback p.two_le_m (data t).snapshot (data t).input (data t).rewards player := by
      have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
        rw [r.output_eq]; rfl
      have hactions := actual_handover_down_actions r.input selected
        (by rw [← hprep]; exact hs) states memories
        (by intro k; rw [← hprep]; exact hconfigs k)
        (by simpa only [hpay] using hfields) hnotReleased i hi hd hdraw
      rw [hpay] at hactions
      have hactions' : r.output.preparation.arms.actions =
          ActiveRoundActions.actions p.two_le_m
            ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩
            (handoverRoundInput payload r.input.row t) := by
        rw [hprep]; exact hactions
      calc
        _ = FiniteBanditModel.playerFeedback r.output.preparation.arms.actions
            (fun a => ((r.input.rewards t a).val : ℝ) / (D p : ℝ)) player :=
          r.output.preparation.feedback.feedback_scalar_eq_playerFeedback player
        _ = _ := by rw [hactions', hdataSnapshot, hdataInput, hdataRewards]; rfl
    rcases hservices with ⟨code, mem, hstart, hstatus, hv⟩ | ⟨code, mem, hstart, hstatus, hv⟩
    · have hstatusCode : FollowerDownMeasurability.followerStatusCode (states i).status = 0 := by
        have he := Sum.inr.inj (hcode.symm.trans hstart)
        cases he
        exact hstatus
      have hu : (states i).status = .unoccupied := by
        cases h : (states i).status <;>
          simp_all [FollowerDownMeasurability.followerStatusCode]
      obtain ⟨r', hr, hd, hdraw, hpositive⟩ := hv
      have he := Option.some.inj (hr.symm.trans hlookup)
      subst r'
      have hel : AffineBatchDecoder.eligible (observationTrace p payload.assignment data i t) := by
        apply (eligible_iff p payload.assignment data i t).mpr
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hdataInput]; exact hd
        · rw [hdataInput]; exact hdraw
        · rw [hdataSnapshot]; exact hi
        · rw [hdataSnapshot]; exact hu
        · rw [← hfeedback hd hdraw (PublicDiscreteDraws.followerPlayer p.two_le_m i)]
          exact hpositive
      have hphase' : q.phase = .awaitingDown := by
        rw [hphase, ite_eq_left hi, ite_eq_left hu]
      simp only [X, hphase', hel, ite_true, le_refl]
    · have hstatusCode : FollowerDownMeasurability.followerStatusCode (states i).status = 1 := by
        have he := Sum.inr.inj (hcode.symm.trans hstart)
        cases he
        exact hstatus
      have hu : (states i).status = .pending := by
        cases h : (states i).status <;>
          simp_all [FollowerDownMeasurability.followerStatusCode]
      obtain ⟨r', sel', hr, hs', hd, hdraw, hbit, hpositive⟩ := hv
      have he := Option.some.inj (hr.symm.trans hlookup)
      subst r'
      have he := Option.some.inj (hs'.symm.trans hs)
      subst sel'
      have hconfirm : physicalConfirmation p payload.assignment data i t := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hdataInput]; exact hd
        · rw [hdataInput]; exact hdraw
        · rw [hdataSnapshot]; exact hi
        · rw [hdataInput, handoverRoundInput_down_bit, hdraw]
          rw [hp] at hbit
          exact hbit
        · rw [← hfeedback hd hdraw (ActiveRoundActions.coordinator p.two_le_m)]
          exact hpositive
      have hphase' : q.phase = .acceptedUnconfirmed := by
        rw [hphase, ite_eq_left hi, ite_eq_right (by rw [hu]; decide)]
      simp only [X, hphase', hconfirm, ite_true, le_refl]
  · exact Nat.zero_le _

private theorem original_fixed_word
    (payload : ReferenceActivePhysicalStep.Payload rate) (b : Fin (R).length)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (hel : AffineBatchDecoder.eligible (observationTrace p payload.assignment
      (actualHandoverReplayData rate rewards C_star C_h z payload b) i t)) :
    (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).input.down.word =
      currentWord p β (payload.downRecord i) := by
  obtain ⟨_, hselected, _, _, _⟩ := (eligible_iff p payload.assignment _ i t).mp hel
  change (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).input.selected = i at hselected
  have hword : (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).input.down.word =
      CoordinatorLocalArmChoice.storedDownFlatWord payload
        (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).input.selected := by
    unfold actualLaterHandoverLive
    split_ifs
    · cases ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z <;> rfl
    · rfl
  rw [hword, hselected]
  rfl

/-- The uncapped original physical count is dominated at every natural prefix
by the SAME inherited stopped replay, with inclusive and strict incoming quotas.
Only the actual later-chosen branch is asserted. -/
public theorem original_later_handover_physical_service_domination
    (b : Fin (R).length) (i : Fin (p.m - 1)) :
    ReferenceCollectionPhaseHistory.laterChosen (R[b.val]'(b.isLt)).input = true →
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) payload ∧
      (R[b.val]'(b.isLt)).input.state.followers i = .ordinary before beforeMemory ∧
      (∀ n : ℕ,
        originalHandoverPhysicalCount rate rewards C_star C_h z b i n ≤
          N_before p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b)
            i payload.sigma (payload.downRecord i)
            (initial p before.downBatch (acceptedStart before)) n ∧
        N_before p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b)
            i payload.sigma (payload.downRecord i)
            (initial p before.downBatch (acceptedStart before)) n ≤
          2 * AffineBatchDecoder.quota p + 1) ∧
      (∀ (j : Fin (H b).length)
        (selected : ReferenceActivePhysicalStep.Selection (((H b)[j.val]'(j.isLt)).input)),
        ((H b)[j.val]'(j.isLt)).output.preparation.coordinator.selection = some selected →
        i ∈ selected.view.pendingAtChoice → ((H b)[j.val]'(j.isLt)).input.time.val + 1 ≤
          firstBadDate rate rewards C_star C_h z →
        originalHandoverPhysicalCount rate rewards C_star C_h z b i ((H b)[j.val]'(j.isLt)).input.time.val <
          2 * AffineBatchDecoder.quota p + 1) := by
  intro hb
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, _, hstrict, hwell, hpendingStamps, _⟩ :=
    actual_later_handover_stoppedReplay_seed rate rewards C_star C_h z b hb i
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload (H b)
  have hsource : WaitedWordWindow.sourceRound payload.sigma = (payload.downRecord i).val.sigma := rfl
  have hstamps : ∀ e ∈ before.downBatch.pending, e.time.val < payload.sigma.val := by
    intro e he
    rw [ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
    exact hpendingStamps e he
  have hfixed : ∀ t, payload.sigma.val ≤ t.val →
      AffineBatchDecoder.eligible (ActiveObservationBridge.downObservationTrace p payload.assignment live i t) →
      (live t).input.down.word = currentWord p β (payload.downRecord i) := by
    intro t _ hel
    exact original_fixed_word rate rewards C_star C_h z payload b i t hel
  have hdom (n : ℕ) : originalHandoverPhysicalCount rate rewards C_star C_h z b i n ≤
      N_before p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b)
        i payload.sigma (payload.downRecord i)
        (initial p before.downBatch (acceptedStart before)) n := by
    unfold originalHandoverPhysicalCount N_before
    apply Finset.sum_le_sum
    intro t _
    split_ifs
    · exact original_physical_tick_le_replay rate rewards C_star C_h z b hb i
        payload before beforeMemory hbirth hbefore t
    · exact le_rfl
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, ?_, ?_⟩
  · intro n
    exact ⟨hdom n, HandoverStoppedServiceQuota.N_before_le_twoQ_add_one p β payload.assignment live
      (actualHandoverCutoffBefore rate rewards C_star C_h z)
      (actualHandoverOverflowAfter rate rewards C_star C_h z) i payload.sigma (payload.downRecord i)
      (acceptedStart before) before.downBatch hsource hstrict
      hwell.1 hstamps hfixed n⟩
  · intro j selected hs hi hgate
    obtain ⟨P, B, M, hP, hB, _, _, hdates⟩ :=
      original_later_handover_originalGate_phase_J rate rewards C_star C_h z b i hb
    obtain ⟨hP, hB, hM⟩ := birth_seed_unique rate hP hbirth hB hbefore
    subst P B M
    obtain ⟨sel, _, _, hsel, _, _, _, _, _, hJ⟩ := hdates j hgate
    have he := Option.some.inj (hsel.symm.trans hs)
    subst sel
    exact lt_of_le_of_lt (hdom _) (HandoverStoppedServiceQuota.N_before_lt_twoQ_add_one_of_J
      p β payload.assignment live (actualHandoverCutoffBefore rate rewards C_star C_h z)
      (actualHandoverOverflowAfter rate rewards C_star C_h z) i payload.sigma (payload.downRecord i)
      (acceptedStart before) before.downBatch hsource hstrict
      hwell.1 hstamps hfixed (H b)[j.val].input.time (hJ hi))

end Bandits.Support.ReferenceOriginalLaterHandoverStoppedQuota

end
