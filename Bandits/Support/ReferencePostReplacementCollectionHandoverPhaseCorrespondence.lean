/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverStoppedFailureCoverage
public import Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport

/-!
# Chronological stopped replay of actual later-handover prechoice states

This module starts the correspondence from the actual later-chosen birth and
keeps the original calendar's cutoff and post-update queue-overflow markers.
The inherited decoder bank and accepted-start register are used without a
reset. Current-date post-update prefixes retain their detecting overflow updates.
No source cost or quota statement is made.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open HandoverStoppedDecoderReplay
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseCorrespondence

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "queueParams" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "H" b =>
  ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
    rate rewards C_star C_h z b

/-- The actual source cutoff selected before follower service at calendar
date `t`. Absence of an original record remains a separate branch. -/
def actualHandoverCutoffBefore (t : Fin p.T) : Bool :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => false
  | some record => ReferenceCollectionPhaseHistory.cutoffChosen record.input

/-- The post-update overflow bit on the original launch-based numerical
prefix through calendar date `t`. An absent prefix is kept distinct. -/
def actualHandoverOverflowAfter? (t : Fin p.T) : Option Bool :=
  (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h (t.val + 1) z).map fun inputs =>
      (RecordedQueueRun.run queueParams inputs).overflow

/-- Total marker passed to the existing replay. On the replay's pre-fixation
dates the source queue prefix may be absent, and those rounds are inert. -/
def actualHandoverOverflowAfter (t : Fin p.T) : Bool :=
  (actualHandoverOverflowAfter? rate rewards C_star C_h z t).getD false

/-- The existing stopped replay supplied with the actual later-handover live
calendar, original cutoff result, and original post-update queue bit. -/
def actualHandoverReplayData (payload : ReferenceActivePhysicalStep.Payload rate)
    (b : Fin (R).length) (t : Fin p.T) : HandoverStoppedDecoderReplay.RoundData p payload.assignment :=
  HandoverStoppedDecoderReplay.fromLive p payload.assignment
    (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
      rate rewards C_star C_h z payload (H b))
    (actualHandoverCutoffBefore rate rewards C_star C_h z)
    (actualHandoverOverflowAfter rate rewards C_star C_h z) t

/-- The existing chronological snapshot, seeded with the whole supplied birth bank. -/
def actualHandoverSnapshotBefore (payload : ReferenceActivePhysicalStep.Payload rate)
    (b : Fin (R).length) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta) (n : ℕ) : LocalState p :=
  snapshotBefore p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b)
    i payload.sigma (payload.downRecord i)
    (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) n

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

private theorem option_mapM_take {α : Type*} (xs : List (Option α))
    (out : List α) (hout : xs.mapM id = some out) (n : ℕ) :
    (xs.take n).mapM id = some (out.take n) := by
  induction xs generalizing out n with
  | nil =>
      have he : out = [] := (Option.some.inj hout).symm
      subst out
      simp only [List.take_nil, List.mapM_nil, pure]
  | cons x xs ih =>
      cases x with
      | none => simp [List.mapM_cons] at hout
      | some a =>
          cases ht : xs.mapM id with
          | none => simp [List.mapM_cons, ht] at hout
          | some rest =>
              have he : a :: rest = out := by
                simpa [List.mapM_cons, ht] using hout
              subst out
              cases n with
              | zero => rfl
              | succ n =>
                  simp [List.take_succ_cons, List.mapM_cons, ih rest ht n]

private theorem prefixInputs_take
    (t : Fin p.T) (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h t z = some N)
    (n : ℕ)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n)
    (hnt : n ≤ t.val) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z =
        some (N.take (n - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h)) := by
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h t.val z N hN
  have hlaunchN : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z := ⟨hlaunch.1, hs⟩
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h t.val z = some N at hN
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunch] at hN
  have htaken := option_mapM_take _ N hN
    (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  simp only [← List.map_take, List.take_take] at htaken
  have hle : n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z := Nat.sub_le_sub_right hnt _
  rw [Nat.min_eq_left hle] at htaken
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunchN]
  exact htaken

private theorem queueSafe_take
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N)
    (n : ℕ) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (N.take n) := by
  intro k hk a
  have hkn : k ≤ n := le_trans hk (List.length_take_le n N)
  have hkN : k ≤ N.length := le_trans hk (List.length_take_le' n N)
  have hsafe := hN k hkN a
  unfold ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue
  rw [List.take_take, Nat.min_eq_left hkn]
  exact hsafe

private theorem queueSafe_run_false
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N) :
    (RecordedQueueRun.run queueParams N).overflow = false := by
  have hfirst :=
    ReferenceFirstReplacementCollectionInclusiveStoppedCharge.literalQueueSafe_take_iff_before_first
      rate N N.length le_rfl
  rw [List.take_length] at hfirst
  have hlt := hfirst.mp hN
  cases hov : (RecordedQueueRun.run queueParams N).overflow with
  | false => rfl
  | true =>
      have hle := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        queueParams N N.length le_rfl).mp
        (by simpa only [List.take_length] using hov)
      omega

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
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
      rate rewards C_star C_h z ⟨_, hk⟩,
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
      rate rewards C_star C_h z b]
  exact (Nat.add_assoc _ _ _).symm

private theorem handover_lookup (b : Fin (R).length) (j : Fin (H b).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (H b)[j.val].input.time z = some (H b)[j.val] := by
  obtain ⟨hk, he⟩ := handover_index rate rewards C_star C_h z b j
  rw [he]
  have ht := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
    rate rewards C_star C_h z ⟨_, hk⟩
  simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ht,
    Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hk]

private theorem handover_calendar
    (b : Fin (R).length) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H b).length) :
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
        rate rewards C_star C_h z payload (H b) (H b)[j.val].input.time =
      ⟨ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
          payload (H b)[j.val].input.row (H b)[j.val].input.time,
        ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow (H b)[j.val],
        ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[j.val]⟩ := by
  apply ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive_of_actual_record
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
      have hnW : n < W.length := by
        have hlen := (List.takeWhile_prefix
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
          (l := R[b.val] :: W)).length_le
        change (H b).length ≤ (R[b.val] :: W).length at hlen
        simp only [List.length_cons] at hlen
        omega
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

/-- The literal stopped domain supplies the SAME original launch prefix at
all preceding numerical boundaries. In particular every strictly earlier H
update has a present post-update queue word with no overflow. The current
post-update bit is not constrained by this strict-past assertion. -/
public theorem actual_later_handover_strict_predecessor_markers
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length) (i : Fin (p.m - 1))
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z) :
    actualHandoverCutoffBefore rate rewards C_star C_h z (H b)[j.val].input.time = false ∧
      ∃ N : List (RecordedQueueRun.RoundInput p.K),
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h (H b)[j.val].input.time z = some N ∧
        ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N ∧
        ∀ k : Fin (H b).length, k.val < j.val →
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h ((H b)[k.val].input.time.val + 1) z =
              some (N.take ((H b)[k.val].input.time.val + 1 -
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) ∧
          actualHandoverCutoffBefore rate rewards C_star C_h z (H b)[k.val].input.time = false ∧
          actualHandoverOverflowAfter? rate rewards C_star C_h z (H b)[k.val].input.time = some false ∧
          actualHandoverOverflowAfter rate rewards C_star C_h z (H b)[k.val].input.time = false ∧
          ¬ (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z
              (H b)[k.val].input.time ∨
            ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z
              (H b)[k.val].input.time) := by
  obtain ⟨N, hN, hsafe⟩ := hsupport.2.2
  refine ⟨handover_cutoff_false rate rewards C_star C_h z b hb j, N, hN, hsafe, ?_⟩
  intro k hkj
  have hk := handover_time rate rewards C_star C_h z b k
  have hj := handover_time rate rewards C_star C_h z b j
  have hstart := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
    rate rewards C_star C_h z b
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      (H b)[k.val].input.time.val + 1 := by omega
  have ht : (H b)[k.val].input.time.val + 1 ≤ (H b)[j.val].input.time.val := by omega
  have hprefix := prefixInputs_take rate rewards C_star C_h z
    (H b)[j.val].input.time N hN ((H b)[k.val].input.time.val + 1) hs ht
  have hover := queueSafe_run_false rate
    (N.take ((H b)[k.val].input.time.val + 1 -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
    (queueSafe_take rate N hsafe _)
  have hoptional : actualHandoverOverflowAfter? rate rewards C_star C_h z
      (H b)[k.val].input.time = some false := by
    rw [actualHandoverOverflowAfter?, hprefix, Option.map_some, hover]
  refine ⟨hprefix, handover_cutoff_false rate rewards C_star C_h z b hb k,
    hoptional, ?_, ?_⟩
  · rw [actualHandoverOverflowAfter, hoptional]
    rfl
  · exact hsupport.2.1 (H b)[k.val].input.time (by omega)

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
    (hstrict : ReferencePrelaunchFollower.acceptedStart choice < (payload.downRecord i).val.sigma)
    (hmissing : i ∈ selected.view.pendingAtChoice)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hcomp : cut.rawComparison.isSome = true)
    (hflag : ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload r i = true) :
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
  have hnextStart : ReferencePrelaunchFollower.acceptedStart next =
      (payload.downRecord i).val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
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
    (hbank : choice.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
      ((H b).take k.val) seed)
    (hnextBank : nextChoice.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
      ((H b).take next.val) seed)
    (hsmall : choice.downBatch.pending.length < AffineBatchDecoder.quota p)
    (hinp : (actualHandoverReplayData rate rewards C_star C_h z payload b
        (H b)[k.val].input.time).input =
      ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
        payload (H b)[k.val].input.row (H b)[k.val].input.time)
    (hstatus : (actualHandoverReplayData rate rewards C_star C_h z payload b
        (H b)[k.val].input.time).snapshot.status i = choice.status)
    (hinput : ActiveFollowerDownAcceptance.downSelected p i
        (H b)[k.val].input.row (H b)[k.val].input.time →
      choice.status = .unoccupied →
      observationTrace p payload.assignment
          (actualHandoverReplayData rate rewards C_star C_h z payload b) i
          (H b)[k.val].input.time =
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (H b)[k.val].input.row (H b)[k.val].input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (H b)[k.val] i) rate choice) :
    nextChoice.downBatch = (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment
        (actualHandoverReplayData rate rewards C_star C_h z payload b) i)
      choice.downBatch (H b)[k.val].input.time).1 := by
  let r := (H b)[k.val]
  let tr := observationTrace p payload.assignment
    (actualHandoverReplayData rate rewards C_star C_h z payload b) i
  let current := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice
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
  simp only [ReferenceFollowerDownDecoderReplay.replayDownCalls,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, ReferenceFollowerDownDecoderReplay.foldDownCalls,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, hcall,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (AffineBatchDecoder.decodeStep p (ActiveFollowerDownAcceptance.currentInputExtension p current)
    (ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H b).take k.val) seed) r.input.time).1 = _
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

private theorem roundStep_with_overflow
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : ActiveRoundActions.Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (ht : fixing.val ≤ t.val) (hc : (data t).cutoffBefore = false) :
    roundStep p beta a data i fixing M s t =
      let updated := serviceStep p beta a data i fixing M s t
      if (data t).overflowAfter = true ∧ updated.phase.unresolved then
        { updated with phase := .overflow } else updated := by
  by_cases hu : s.phase.unresolved
  · simp only [roundStep, Nat.not_lt.mpr ht, hu, not_true_eq_false, or_self,
      ite_false, hc, Bool.false_eq_true]
  · have hs : serviceStep p beta a data i fixing M s t = s := by
      cases hp : s.phase <;> simp only [serviceStep, hp]
      · exact (hu (Or.inl hp)).elim
      · exact (hu (Or.inr hp)).elim
    rw [roundStep_terminal p beta a data i fixing M s t hu, hs]
    simp only [hu, and_false, ite_false]

private theorem handover_prefix_append
    (b : Fin (R).length) (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H b).length) (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h (H b)[j.val].input.time z = some N)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta) (i : Fin (p.m - 1))
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload) :
    ∃ c, ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (H b)[j.val] = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h ((H b)[j.val].input.time.val + 1) z = some (N ++ [c]) ∧
      actualHandoverOverflowAfter? rate rewards C_star C_h z (H b)[j.val].input.time =
        some (RecordedQueueRun.step queueParams (RecordedQueueRun.run queueParams N) c).overflow ∧
      let data := actualHandoverReplayData rate rewards C_star C_h z payload b
      let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
        (H b)[j.val].input.time.val
      let served := serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i) q (H b)[j.val].input.time
      actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before ((H b)[j.val].input.time.val + 1) =
        if (RecordedQueueRun.step queueParams (RecordedQueueRun.run queueParams N) c).overflow = true ∧
          served.phase.unresolved then { served with phase := .overflow } else served := by
  obtain ⟨c, hc⟩ := handover_current_cell rate rewards C_star C_h z b hb j
  have hrecord := handover_lookup rate rewards C_star C_h z b j
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h (H b)[j.val].input.time.val z N hN
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hlaunch.2] at hrecord
  have hnext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h (H b)[j.val].input.time.val z N hN (H b)[j.val] c hrecord hc
  have hover : actualHandoverOverflowAfter? rate rewards C_star C_h z (H b)[j.val].input.time =
      some (RecordedQueueRun.step queueParams (RecordedQueueRun.run queueParams N) c).overflow := by
    rw [actualHandoverOverflowAfter?, hnext, Option.map_some,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
  refine ⟨c, hc, hnext, hover, ?_⟩
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
    (H b)[j.val].input.time.val
  have ht : payload.sigma.val ≤ (H b)[j.val].input.time.val := by
    rw [handover_time rate rewards C_star C_h z b j,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
    omega
  have hcut : (data (H b)[j.val].input.time).cutoffBefore = false :=
    handover_cutoff_false rate rewards C_star C_h z b hb j
  have htotal : (data (H b)[j.val].input.time).overflowAfter =
      (RecordedQueueRun.step queueParams (RecordedQueueRun.run queueParams N) c).overflow := by
    change actualHandoverOverflowAfter rate rewards C_star C_h z (H b)[j.val].input.time = _
    rw [actualHandoverOverflowAfter, hover]
    rfl
  have hsucc := ReferenceFirstLiveHandoverPhaseReplay.snapshotBefore_succ β payload.assignment data i
    payload.sigma (payload.downRecord i)
    (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) (H b)[j.val].input.time
  have hround := roundStep_with_overflow β payload.assignment data i payload.sigma (payload.downRecord i) q
    (H b)[j.val].input.time ht hcut
  rw [htotal] at hround
  exact hsucc.trans hround

private theorem actual_normal_service
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (i : Fin (p.m - 1))
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (hstrict : ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma)
    (j : Fin (H b).length)
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z)
    (k : Fin (H b).length) (hkj : k.val < j.val)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((H b)[k.val].output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hkSmall : choice.downBatch.pending.length < AffineBatchDecoder.quota p) :
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let tr := observationTrace p payload.assignment data i
    serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
        (initial p choice.downBatch (ReferencePrelaunchFollower.acceptedStart before))
        (H b)[k.val].input.time =
      let bank' := (AffineBatchDecoder.decodeStep p tr choice.downBatch (H b)[k.val].input.time).1
      if (AffineBatchDecoder.decodeStep p tr choice.downBatch (H b)[k.val].input.time).2 =
          some (currentWord p β (payload.downRecord i)) then
        ⟨bank', (payload.downRecord i).val.sigma, .acceptedUnconfirmed⟩
      else initial p bank' (ReferencePrelaunchFollower.acceptedStart before) := by
  obtain ⟨fp, fb, fm, hfbirth, hfbefore, _hfu, _hfs, hfailures⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_strict_predecessor_failure_exclusion
      rate rewards C_star C_h z b hb i
  obtain ⟨hfp, hfb, hfm⟩ := birth_seed_unique rate hfbirth hbirth hfbefore hbefore
  subst fp fb fm
  obtain ⟨actual, actualMemory, hactual, hnotfailed⟩ := (hfailures j hsupport).2 k hkj
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hactual.symm.trans hc)
  subst actual
  subst actualMemory
  have hnotfailed' := hnotfailed hu
  have htime := handover_time rate rewards C_star C_h z b k
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth
  have haM : OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p β)
      (ReferencePrelaunchFollower.acceptedStart before)
      (WaitedWordWindow.sourceRound (H b)[k.val].input.time) (payload.downRecord i) := by
    exact ⟨hstrict, by
      change payload.sigma.val + 1 ≤ (H b)[k.val].input.time.val + 1
      omega⟩
  exact awaiting_service_classification β payload.assignment _ i payload.sigma
    (payload.downRecord i) choice.downBatch _ (H b)[k.val].input.time
    hkSmall haM hnotfailed'.1 hnotfailed'.2

private theorem actual_flag_decoder_raw
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (i : Fin (p.m - 1))
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (hstrict : ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma)
    (k : Fin (H b).length)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((H b)[k.val].output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i (H b)[k.val].input.row (H b)[k.val].input.time)
    (hf : ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[k.val] i = true) :
    (AffineBatchDecoder.decodeStep p
      (observationTrace p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i)
      choice.downBatch (H b)[k.val].input.time).2 = some (currentWord p β (payload.downRecord i)) := by
  obtain ⟨cp, cb, cm, hcbirth, hcbefore, _hcu, _hcs, hcalls⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_awaiting_calls
      rate rewards C_star C_h z b hb i
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
      ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_snapshot
        rewards C_star C_h z b hb
    obtain ⟨sel, states, memories, hsel, _, hconfigs, _, _, _, hmissing⟩ := dates k
    have hselEq := Option.some.inj (hsel.symm.trans hs)
    subst sel
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hconfigs i).symm.trans hc)
    exact hmissing i (he.symm ▸ hu)
  have hraw := installation_flag_raw rate (H b)[k.val] payload selected hs hp i choice next memory
    nextMemory hc hnext (by rw [(hawait hu).1]; exact hstrict) hmissing logged cut hi hd hcomp hf
  obtain ⟨dp, db, dm, hdbirth, hdbefore, _hdu, _hds, hdecoder⟩ :=
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_decoder_correspondence
      rewards C_star C_h z b hb i
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

private theorem live_status_successor
    (a : ActiveRoundActions.Assignment p.m p.K)
    (live : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (i : ActiveRoundActions.Follower p.m) (t u : Fin p.T) (hu : u.val = t.val + 1)
    (hne : (ActiveObservationBridge.liveSnapshotBefore p a live t).missing.Nonempty) :
    (ActiveObservationBridge.liveSnapshotBefore p a live u).status i =
      ActiveRoundActions.statusAfterAcceptance
        (ActiveObservationBridge.liveSnapshotBefore p a live t) (live t).input (live t).acceptCurrent i := by
  rw [ReferenceFirstLiveHandoverSnapshotPrefix.snapshot_successor live t u hu]
  exact ReferenceFirstLiveHandoverSnapshotPrefix.finish_status_while_missing _ _ _ _ hne i

private theorem handover_pending_nonempty (b : Fin (R).length) (k : Fin (H b).length)
    (selected : ReferenceActivePhysicalStep.Selection (H b)[k.val].input)
    (hs : (H b)[k.val].output.preparation.coordinator.selection = some selected) :
    selected.view.pendingAtChoice.Nonempty := by
  have htest : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (H b)[k.val] = true :=
    List.mem_takeWhile_imp (List.getElem_mem k.isLt)
  unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice at htest
  rw [hs] at htest
  exact of_decide_eq_true htest

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
    (hstrict : ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma)
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
      ReferenceFollowerDownDecoderReplay.replayDownCalls i
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
        (actualHandoverRecords rate rewards C_star C_h z b)[k.val].input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
          (actualHandoverRecords rate rewards C_star C_h z b)[k.val] i) rate (states k i))
    (hstageFacts : ∀ k,
      ((states k i).status = .unoccupied ∧ i ∈ (selected k).view.pendingAtChoice ∧
        ReferencePrelaunchFollower.acceptedStart (states k i) = ReferencePrelaunchFollower.acceptedStart before) ∨
      ((states k i).status = .pending ∧
        ReferencePrelaunchFollower.acceptedStart (states k i) = (payload.downRecord i).val.sigma))
include hb hbirth hbefore hstrict hwell hs hc hbankChoice hsnapshot hinput hstageFacts

local notation "qBefore" => actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before

omit hstrict hwell hs hbankChoice hsnapshot hinput hstageFacts in
private theorem actual_accepted_next_start
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1)
    (hu : (states prev i).status = .unoccupied)
    (hserv : (serviceStep p β payload.assignment
      (actualHandoverReplayData rate rewards C_star C_h z payload b) i payload.sigma (payload.downRecord i)
      (initial p (states prev i).downBatch (ReferencePrelaunchFollower.acceptedStart before))
      (H b)[prev.val].input.time).phase = .acceptedUnconfirmed) :
    ReferencePrelaunchFollower.acceptedStart (states k i) = (payload.downRecord i).val.sigma := by
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
  simp only [ReferencePrelaunchFollower.acceptedStart, hlast]

omit hwell hs hbankChoice hinput hstageFacts in
private theorem actual_pending_next_raw
    (prev k : Fin (H b).length) (hu : (states prev i).status = .unoccupied)
    (hbp : (states k i).status = .pending)
    (hBS : ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[k.val].input.time).snapshot.status i =
      ActiveRoundActions.statusAfterAcceptance
        ((actualHandoverReplayData rate rewards C_star C_h z payload b) (H b)[prev.val].input.time).snapshot
        ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
      rate rewards C_star C_h z payload (H b)) (H b)[prev.val].input.time).input
        (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[prev.val]) i)
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
      ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[prev.val] i = true := by
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
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z)
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1) (hkj : k.val ≤ j.val)
    (hprior :
      let q := qBefore (H b)[prev.val].input.time.val
      q.decoder = (states prev i).downBatch ∧
      q.acceptedStart = ReferencePrelaunchFollower.acceptedStart (states prev i) ∧
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
        (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[prev.val]) i)
    (hmem : i ∈ (selected k).view.pendingAtChoice ↔
      i ∈ (selected prev).view.pendingAtChoice ∧
        ¬ physicalConfirmation p payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i (H b)[prev.val].input.time)
    (hq : qBefore (H b)[k.val].input.time.val = serviceStep p β payload.assignment (actualHandoverReplayData rate rewards C_star C_h z payload b) i
      payload.sigma (payload.downRecord i) (qBefore (H b)[prev.val].input.time.val) (H b)[prev.val].input.time) :
    let q := qBefore (H b)[k.val].input.time.val
    q.decoder = (states k i).downBatch ∧
    q.acceptedStart = ReferencePrelaunchFollower.acceptedStart (states k i) ∧
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
    (q k).acceptedStart = ReferencePrelaunchFollower.acceptedStart (states k i) ∧
    (q k).phase = (if i ∈ (selected k).view.pendingAtChoice then
      if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed)
  change (q prev).decoder = (states prev i).downBatch ∧
    (q prev).acceptedStart = ReferencePrelaunchFollower.acceptedStart (states prev i) ∧
    (q prev).phase = (if i ∈ (selected prev).view.pendingAtChoice then
      if (states prev i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed) at hprior
  have hqStep : q k = serviceStep p β payload.assignment data i payload.sigma
    (payload.downRecord i) (q prev) (H b)[prev.val].input.time := hq
  obtain ⟨hqd, hqa, hqp⟩ := hprior
  have hprev : prev.val < j.val := by omega
  have hstartNext (hpending : (states k i).status = .pending) :
      ReferencePrelaunchFollower.acceptedStart (states k i) = (payload.downRecord i).val.sigma := by
    rcases hstageFacts k with h | h
    · rw [hpending] at h
      cases h.1
    · exact h.2
  by_cases hi : i ∈ (selected prev).view.pendingAtChoice
  · rw [ite_eq_left hi] at hqp
    by_cases hu : (states prev i).status = .unoccupied
    · rw [ite_eq_left hu] at hqp
      have haw : ReferencePrelaunchFollower.acceptedStart (states prev i) =
          ReferencePrelaunchFollower.acceptedStart before := by
        rcases hstageFacts prev with h | h
        · exact h.2.2
        · rw [hu] at h
          cases h.1
      have hqaState : q prev = initial p (states prev i).downBatch
          (ReferencePrelaunchFollower.acceptedStart before) :=
        localState_ext _ _ hqd (hqa.trans haw) hqp
      have hnc : ¬ physicalConfirmation p payload.assignment data i (H b)[prev.val].input.time := by
        intro hconfirm
        have ho := ActiveRoundActions.confirmation_implies_occupied p.two_le_m A _ _ i hconfirm
        rcases ho with ho | ho <;> rw [hstatus prev, hu] at ho <;> cases ho
      have hib := hmem.mpr ⟨hi, hnc⟩
      rw [hqStep, hqaState, actual_normal_service rate rewards C_star C_h z b hb payload before beforeMemory hbirth i hbefore hstrict j hsupport
        prev hprev (states prev i) (memories prev i) (hc prev i) hu hkSmall]
      dsimp only
      rw [← hbankNext]
      by_cases hraw : (AffineBatchDecoder.decodeStep p tr (states prev i).downBatch
          (H b)[prev.val].input.time).2 = some (currentWord p β (payload.downRecord i))
      · rw [ite_eq_left hraw]
        have hserv : (serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
            (initial p (states prev i).downBatch (ReferencePrelaunchFollower.acceptedStart before))
            (H b)[prev.val].input.time).phase = .acceptedUnconfirmed := by
          rw [actual_normal_service rate rewards C_star C_h z b hb payload before beforeMemory hbirth i hbefore hstrict j hsupport
        prev hprev (states prev i) (memories prev i) (hc prev i) hu hkSmall, ite_eq_left hraw]
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
    · rw [ite_eq_right hu] at hqp
      have hbst : B.status i = A.status i := hBS.trans (ite_eq_right (fun h => hu ((hstatus prev).symm.trans h.1)))
      have hkp : (states k i).status = .pending := by
        rcases hstageFacts prev with h | h
        · exact (hu h.1).elim
        · exact (hstatus k).symm.trans (hbst.trans ((hstatus prev).trans h.1))
      have hnotEligible : ¬ AffineBatchDecoder.eligible (tr (H b)[prev.val].input.time) :=
        fun h => hu ((hstatus prev).symm.trans (eligible_iff p payload.assignment data i _ |>.mp h).2.2.2.1)
      rw [AffineBatchDecoder.decodeStep_ineligible p tr _ _ hkSmall hnotEligible] at hbankNext
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
    have hnu : (states prev i).status ≠ .unoccupied := by
      intro hu
      rcases hstageFacts prev with h | h
      · exact hi h.2.1
      · rw [hu] at h
        cases h.1
    have hbst : B.status i = A.status i := hBS.trans (ite_eq_right (fun h => hnu ((hstatus prev).symm.trans h.1)))
    have hkp : (states k i).status = .pending := by
      rcases hstageFacts prev with h | h
      · exact (hi h.2.1).elim
      · exact (hstatus k).symm.trans (hbst.trans ((hstatus prev).trans h.1))
    have hnotEligible : ¬ AffineBatchDecoder.eligible (tr (H b)[prev.val].input.time) :=
      fun h => hnu ((hstatus prev).symm.trans (eligible_iff p payload.assignment data i _ |>.mp h).2.2.2.1)
    rw [AffineBatchDecoder.decodeStep_ineligible p tr _ _ hkSmall hnotEligible] at hbankNext
    rw [ite_eq_right (fun h => hi (hmem.mp h).1), hqStep]
    simp only [serviceStep, hqp]
    refine ⟨hqd.trans hbankNext.symm, ?_, trivial⟩
    rw [hstartNext hkp]
    rcases hstageFacts prev with h | h
    · exact (hi h.2.1).elim
    · exact hqa.trans h.2

private theorem actual_calendar_step
    (j : Fin (H b).length)
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z)
    (prev k : Fin (H b).length) (hk : k.val = prev.val + 1) (hkj : k.val ≤ j.val)
    (hprior :
      let q := qBefore (H b)[prev.val].input.time.val
      q.decoder = (states prev i).downBatch ∧
      q.acceptedStart = ReferencePrelaunchFollower.acceptedStart (states prev i) ∧
      q.phase = if i ∈ (selected prev).view.pendingAtChoice then
        if (states prev i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed) :
    let q := qBefore (H b)[k.val].input.time.val
    q.decoder = (states k i).downBatch ∧
    q.acceptedStart = ReferencePrelaunchFollower.acceptedStart (states k i) ∧
    q.phase = if i ∈ (selected k).view.pendingAtChoice then
      if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
    else .confirmed := by
  let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
    rate rewards C_star C_h z payload (H b)
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q (k : Fin (H b).length) := qBefore (H b)[k.val].input.time.val
  have htime (k : Fin (H b).length) :
      (H b)[k.val].input.time.val = payload.sigma.val + k.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
  have hcalendar (k : Fin (H b).length) :=
    handover_calendar rate rewards C_star C_h z b payload hbirth k
  have hstatus (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).snapshot.status i = (states k i).status :=
    congrArg (fun A => A.status i) (hsnapshot k)
  have hmissing (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).snapshot.missing = (selected k).view.pendingAtChoice :=
    congrArg ActiveRoundActions.Snapshot.missing (hsnapshot k)
  have hdataInput (k : Fin (H b).length) :
      (data (H b)[k.val].input.time).input =
        ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
          payload (H b)[k.val].input.row (H b)[k.val].input.time :=
    congrArg ActiveRoundActions.LiveRoundData.input (hcalendar k)
  have hsmall (k : Fin (H b).length) :
      (q k).decoder.pending.length < AffineBatchDecoder.quota p :=
    run_pending_lt β payload.assignment data i payload.sigma (payload.downRecord i) _ _ hwell
  obtain ⟨_, N, hN, hsafeN, hmarkers⟩ :=
    actual_later_handover_strict_predecessor_markers rate rewards C_star C_h z b hb j i hsupport
  have hprev : prev.val < j.val := by omega
  obtain ⟨hqd, hqa, hqp⟩ := hprior
  have hsucc : (H b)[k.val].input.time.val = (H b)[prev.val].input.time.val + 1 := by
    rw [htime, htime]
    omega
  let A := (data (H b)[prev.val].input.time).snapshot
  let B := (data (H b)[k.val].input.time).snapshot
  have hne : A.missing.Nonempty := by
    rw [hmissing]
    exact handover_pending_nonempty rate rewards C_star C_h z b prev (selected prev) (hs prev)
  have hBS : B.status i = ActiveRoundActions.statusAfterAcceptance A
      (live (H b)[prev.val].input.time).input
      (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload (H b)[prev.val]) i := by
    have h := live_status_successor payload.assignment live i (H b)[prev.val].input.time
      (H b)[k.val].input.time hsucc hne
    rw [congrArg ActiveRoundActions.LiveRoundData.acceptCurrent (hcalendar prev)] at h
    exact h
  have hmem : i ∈ (selected k).view.pendingAtChoice ↔
      i ∈ (selected prev).view.pendingAtChoice ∧
        ¬ physicalConfirmation p payload.assignment data i (H b)[prev.val].input.time := by
    rw [← hmissing k, ← hmissing prev]
    change i ∈ (ActiveObservationBridge.liveSnapshotBefore p payload.assignment live (H b)[k.val].input.time).missing ↔ _
    rw [ReferenceFirstLiveHandoverSnapshotPrefix.snapshot_successor live
      (H b)[prev.val].input.time (H b)[k.val].input.time hsucc]
    exact finish_missing_iff _ _ _ _ i
  have hround := roundStep_with_overflow β payload.assignment data i payload.sigma
    (payload.downRecord i) (q prev) (H b)[prev.val].input.time
    (by rw [htime]; omega) (hmarkers prev hprev).2.1
  have hnoOverflow : (data (H b)[prev.val].input.time).overflowAfter = false := (hmarkers prev hprev).2.2.2.1
  rw [hnoOverflow] at hround
  simp only [Bool.false_eq_true, false_and, ite_false] at hround
  have hq : q k = serviceStep p β payload.assignment data i payload.sigma
      (payload.downRecord i) (q prev) (H b)[prev.val].input.time := by
    change snapshotBefore _ _ _ _ _ _ _ _ _ = _
    rw [hsucc]
    exact (ReferenceFirstLiveHandoverPhaseReplay.snapshotBefore_succ β payload.assignment data i
      payload.sigma (payload.downRecord i) _ (H b)[prev.val].input.time).trans hround
  have hkSmall : (states prev i).downBatch.pending.length < AffineBatchDecoder.quota p :=
    hqd ▸ hsmall prev
  have hbankNext := handover_bank_step rate rewards C_star C_h z b prev k
    (by omega) payload i before.downBatch (states prev i) (states k i)
    (memories prev i) (hc prev i) (hbankChoice prev) (hbankChoice k) hkSmall
    (hdataInput prev) (hstatus prev) (hinput prev)
  exact actual_calendar_phase_step
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
    (b := b) (hb := hb) (payload := payload) (before := before) (beforeMemory := beforeMemory)
    (hbirth := hbirth) (i := i) (hbefore := hbefore) (hstrict := hstrict)
    (selected := selected) (states := states) (memories := memories) (hc := hc)
    (hsnapshot := hsnapshot) (hstageFacts := hstageFacts)
    j hsupport prev k hk hkj ⟨hqd, hqa, hqp⟩ hkSmall hbankNext hBS hmem hq

private theorem actual_calendar_correspondence :
    ∀ j : Fin (H b).length,
      ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h (H b)[j.val].input.time i z →
      let q := qBefore (H b)[j.val].input.time.val
      q.decoder = (states j i).downBatch ∧
      q.acceptedStart = ReferencePrelaunchFollower.acceptedStart (states j i) ∧
      q.phase = if i ∈ (selected j).view.pendingAtChoice then
        if (states j i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed := by
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q (k : Fin (H b).length) := qBefore (H b)[k.val].input.time.val
  have htime (k : Fin (H b).length) :
      (H b)[k.val].input.time.val = payload.sigma.val + k.val := by
    rw [handover_time rate rewards C_star C_h z b k,
      ← ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth]
  intro j hsupport
  have hcorrespondence (n : ℕ) : ∀ (k : Fin (H b).length), k.val = n → k.val ≤ j.val →
      (q k).decoder = (states k i).downBatch ∧
      (q k).acceptedStart = ReferencePrelaunchFollower.acceptedStart (states k i) ∧
      (q k).phase = if i ∈ (selected k).view.pendingAtChoice then
        if (states k i).status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
      else .confirmed := by
    induction n with
    | zero =>
        intro k hk _
        have hbank0 := hbankChoice k
        rw [hk, List.take_zero] at hbank0
        change (states k i).downBatch = before.downBatch at hbank0
        have hq : q k = initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before) := by
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

/-- The full chronological stopped replay, started with the actual inherited
bank, agrees with the ordinary CHOICE state at every literal retained H date.
The current update is not required to be safe. Its actual numerical cell is
appended before testing overflow; local failures retain their detecting decoder
call. Removed followers are confirmed, while pending occupied followers confirm
from their incoming phase. Current acceptance installs the same physical word
and cannot confirm on its acceptance date. -/
public theorem actual_later_handover_stoppedReplay_correspondence
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H b).length,
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h (H b)[j.val].input.time i z →
        ∃ (selected : ReferenceActivePhysicalStep.Selection (H b)[j.val].input)
          (choice inputState : ReferencePrelaunchFollower.State p rate.eta)
          (memory inputMemory : ActiveFollowerLifecycle.LocalMemory p),
          (H b)[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          ((H b)[j.val].output.preparation.followers.followers i).configuration =
            .ordinary choice memory ∧
          (H b)[j.val].input.state.followers i = .ordinary inputState inputMemory ∧
          choice.downBatch = inputState.downBatch ∧
          let data := actualHandoverReplayData rate rewards C_star C_h z payload b
          let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
            (H b)[j.val].input.time.val
          let served := serviceStep p β payload.assignment data i payload.sigma
            (payload.downRecord i) q (H b)[j.val].input.time
          q.decoder = inputState.downBatch ∧
          q.acceptedStart = ReferencePrelaunchFollower.acceptedStart choice ∧
          (q.phase = if i ∈ selected.view.pendingAtChoice then
            if choice.status = .unoccupied then .awaitingDown else .acceptedUnconfirmed
          else .confirmed) ∧
          (q.phase = .awaitingDown → served.decoder =
            (AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
              q.decoder (H b)[j.val].input.time).1) ∧
          (q.phase = .awaitingDown →
            served.phase = .failedFalse ∨ served.phase = .failedAmbiguous →
            ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z (H b)[j.val].input.time ∨
              ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z (H b)[j.val].input.time) ∧
          (q.phase = .awaitingDown → served.phase = .acceptedUnconfirmed →
            ¬ physicalConfirmation p payload.assignment data i (H b)[j.val].input.time ∧
              ∃ (next : ReferencePrelaunchFollower.State p rate.eta)
                (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                (H b)[j.val].output.next.followers i = .ordinary next nextMemory ∧
                next.lastDown = some (payload.downRecord i)) ∧
          (ActiveFollowerDownAcceptance.downSelected p i (H b)[j.val].input.row (H b)[j.val].input.time →
            choice.status = .unoccupied →
            AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
                q.decoder (H b)[j.val].input.time =
              ActiveFollowerDownAcceptance.currentDecodeStep p i (H b)[j.val].input.row
                (H b)[j.val].input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (H b)[j.val] i)
                rate choice) ∧
          ∃ (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K),
            ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
              rate rewards C_star C_h (H b)[j.val].input.time z = some N ∧
            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (H b)[j.val] = some c ∧
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h ((H b)[j.val].input.time.val + 1) z = some (N ++ [c]) ∧
            (RecordedQueueRun.run queueParams N).overflow = false ∧
            let overflow := (RecordedQueueRun.step queueParams (RecordedQueueRun.run queueParams N) c).overflow
            actualHandoverOverflowAfter? rate rewards C_star C_h z (H b)[j.val].input.time = some overflow ∧
            actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
                ((H b)[j.val].input.time.val + 1) =
              if overflow = true ∧ served.phase.unresolved then
                { served with phase := .overflow } else served := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict,
      hwell, _hpendingStamps, _hchron, _hcollectedStamps, _hseedPhase, _hseedDates⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_stoppedReplay_seed
      rate rewards C_star C_h z b hb i
  obtain ⟨dp, db, dm, hdbirth, hdbefore, _hdu, _hds, hdecoder⟩ :=
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_decoder_correspondence
      rewards C_star C_h z b hb i
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
  obtain ⟨fp, fb, fm, hfbirth, hfbefore, _hfu, _hfs, hfailures⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_awaiting_service_failure_coverage
      rate rewards C_star C_h z b hb i
  obtain ⟨hfp, hfb, hfm⟩ := birth_seed_unique rate hfbirth hbirth hfbefore hbefore
  subst fp fb fm
  obtain ⟨ap, ab, am, habirth, habefore, _hau, _has, hacceptance⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_current_acceptance_output
      rate rewards C_star C_h z b hb i
  obtain ⟨hap, hab, ham⟩ := birth_seed_unique rate habirth hbirth habefore hbefore
  subst ap ab am
  dsimp only at hdecoder
  obtain ⟨selected, hselected⟩ := Classical.axiomOfChoice hdecoder
  obtain ⟨states, hstates⟩ := Classical.axiomOfChoice hselected
  obtain ⟨memories, hmemories⟩ := Classical.axiomOfChoice hstates
  obtain ⟨inputState, hinputState⟩ := Classical.axiomOfChoice hmemories
  obtain ⟨inputMemory, hframes⟩ := Classical.axiomOfChoice hinputState
  choose hs hp hc hin hbank hchoiceBank hsnapshot hoccupied hnotselected hinput hcutCases using hframes
  have hstage (k : Fin (H b).length) := hstages k
  have hstageFacts (k : Fin (H b).length) :
      ((states k i).status = .unoccupied ∧ i ∈ (selected k).view.pendingAtChoice ∧
        ReferencePrelaunchFollower.acceptedStart (states k i) =
          ReferencePrelaunchFollower.acceptedStart before) ∨
      ((states k i).status = .pending ∧
        ReferencePrelaunchFollower.acceptedStart (states k i) = (payload.downRecord i).val.sigma) := by
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
      ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H b).take k.val) before.downBatch :=
    (hchoiceBank k).trans (hbank k)
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  intro j hsupport
  obtain ⟨hqd, hqa, hqp⟩ := actual_calendar_correspondence rate rewards C_star C_h z b hb
    payload before beforeMemory hbirth i hbefore hstrict hwell.1 selected states memories
    hs hc hbankChoice hsnapshot (fun k hd hu => (hinput k hd hu).1) hstageFacts j hsupport
  refine ⟨selected j, states j i, inputState j, memories j i, inputMemory j,
    hs j, hp j, hc j i, hin j, hchoiceBank j, ?_⟩
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
    (H b)[j.val].input.time.val
  let served := serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
    q (H b)[j.val].input.time
  have hawaiting (haw : q.phase = .awaitingDown) :
      (states j i).status = .unoccupied ∧ q =
        initial p (states j i).downBatch (ReferencePrelaunchFollower.acceptedStart before) := by
    have hu : (states j i).status = .unoccupied := by
      by_contra hnu
      have hp := hqp
      rw [ite_eq_right hnu] at hp
      split_ifs at hp <;> rw [haw] at hp <;> cases hp
    have hs : ReferencePrelaunchFollower.acceptedStart (states j i) =
        ReferencePrelaunchFollower.acceptedStart before := by
      rcases hstageFacts j with h | h
      · exact h.2.2
      · rw [hu] at h
        cases h.1
    exact ⟨hu, localState_ext _ _ hqd (hqa.trans hs) haw⟩
  refine ⟨hqd.trans (hchoiceBank j), hqa, hqp, ?_, ?_, ?_, ?_, ?_⟩
  · intro haw
    change q.phase = .awaitingDown at haw
    have hsmall := run_pending_lt β payload.assignment data i payload.sigma (payload.downRecord i)
      (AffineBatchDecoder.roundPrefix p (H b)[j.val].input.time.val)
      (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) hwell.1
    change q.decoder.pending.length < AffineBatchDecoder.quota p at hsmall
    by_cases hel : AffineBatchDecoder.eligible (observationTrace p payload.assignment data i (H b)[j.val].input.time)
    · change (serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i) q _).decoder = _
      simp only [serviceStep, haw, hel, ite_true]
      exact receiverStep_decoder p β payload.assignment data i payload.sigma (payload.downRecord i) q _
    · change (serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i) q _).decoder = _
      simp only [serviceStep, haw, hel, ite_false]
      change q.decoder = (AffineBatchDecoder.decodeStep p
        (observationTrace p payload.assignment data i) q.decoder (H b)[j.val].input.time).1
      exact (congrArg Prod.fst (AffineBatchDecoder.decodeStep_ineligible p _ _ _ hsmall hel)).symm
  · intro haw hfailed
    obtain ⟨choice, memory, hchoice, hcover⟩ := hfailures j
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (hc j i))
    subst choice
    subst memory
    obtain ⟨hu, hq⟩ := hawaiting haw
    apply hcover hu
    change served.phase = .failedFalse ∨ served.phase = .failedAmbiguous at hfailed
    dsimp only [served] at hfailed
    rw [hq] at hfailed
    exact hfailed
  · intro haw haccepted
    obtain ⟨choice, memory, hchoice, hout⟩ := hacceptance j
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (hc j i))
    subst choice
    subst memory
    obtain ⟨hu, hq⟩ := hawaiting haw
    apply hout hu
    change served.phase = .acceptedUnconfirmed at haccepted
    dsimp only [served] at haccepted
    rw [hq] at haccepted
    exact haccepted
  · intro hd hu
    change AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
      q.decoder (H b)[j.val].input.time = _
    rw [hqd, hbankChoice j]
    exact (hinput j hd hu).2
  · obtain ⟨N, hN, hsafe⟩ := hsupport.2.2
    obtain ⟨c, hcell, hnext, hover, htransition⟩ :=
      handover_prefix_append rate rewards C_star C_h z b hb j N hN payload before i hbirth
    exact ⟨N, c, hN, hcell, hnext, queueSafe_run_false rate N hsafe, hover, htransition⟩

end Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseCorrespondence

end
