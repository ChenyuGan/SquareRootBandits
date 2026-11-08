/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNativeDownOverflowCover

import Mathlib.Tactic

/-!
# Reached native DOWN queue observations

This module observes the literal native DOWN replay sites before the later
served-sum and backlog output checks. On actual complete-source diagnostics,
the ordinary source output proves that recovery succeeds, allowing each reached
observation to refine to the accepted successful-prefix event.

Sources: ZIP4 `appendix_a_local_protocol.tex:8-64`,
`06_interruptions.tex:40-100,192-233,246-299,355-361,391-408,425-426`,
`04_slow_fast_learner.tex:157-187,256-290`, and
`05_binary_transport.tex:7-43,60-114` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords birthIndex)

namespace Bandits.Support.ReferenceFirstCorrectedReachedDownQueueOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Payload" => ReferenceActivePhysicalStep.Payload rate

/-- The three source sites of one native DOWN queue replay. -/
inductive DownQueueSite where
  | initial
  | checked (k : ℕ)
  | computed (k : ℕ)
  deriving DecidableEq

/-- Observe the seed, a successful checked prefix, or the queue candidate
computed after `k` successful updates. The candidate query checks the raw
arrival and service before exposing the transition; it deliberately precedes
both output-register checks of `checkedReplayUpdate`. -/
def downReplayQueue? (q : ℕ) (A : List (Bool × ℕ)) :
    DownQueueSite → Option ℕ
  | .initial => some q
  | .checked k =>
      if k ≤ A.length then
        match ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
            (4 * rate.n) 0 ⟨(0, q), 0⟩ (A.take k) with
        | .ok middle => some middle.registers.2
        | .error _ => none
      else none
  | .computed k =>
      (A[k]?).bind fun r =>
        match ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
            (4 * rate.n) 0 ⟨(0, q), 0⟩ (A.take k) with
        | .error _ => none
        | .ok middle =>
            if r.2 ≤ D p ∧
                ActiveFollowerDownAcceptance.replayService (4 * rate.n) middle r ≤ D p then
              some (QueueReplay.transition (4 * rate.n) middle.registers r).2
            else none

/-- Exact characterization of computed DOWN reads. Its guards are precisely
the array lookup, preceding successful replay, raw-arrival check, and service
check. No post-transition served-sum or backlog test occurs here; hence this
equivalence also exposes a candidate when either later output test fails. -/
theorem downReplayQueue?_computed_iff (seed : ℕ) (A : List (Bool × ℕ))
    (k : ℕ) (q : ℕ) :
    downReplayQueue? rate seed A (.computed k) = some q ↔
      ∃ r middle,
        A[k]? = some r ∧
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
          (4 * rate.n) 0 ⟨(0, seed), 0⟩ (A.take k) = .ok middle ∧
        r.2 ≤ D p ∧
        ActiveFollowerDownAcceptance.replayService (4 * rate.n) middle r ≤ D p ∧
        q = (QueueReplay.transition (4 * rate.n) middle.registers r).2 := by
  constructor
  · intro hread
    cases hlookup : A[k]? with
    | none => simp [downReplayQueue?, hlookup] at hread
    | some r =>
        cases hprefix : ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
            (4 * rate.n) 0 ⟨(0, seed), 0⟩ (A.take k) with
        | error failure =>
            simp [downReplayQueue?, hlookup, hprefix] at hread
        | ok middle =>
            by_cases hguards :
                r.2 ≤ D p ∧
                  ActiveFollowerDownAcceptance.replayService (4 * rate.n) middle r ≤ D p
            · simp [downReplayQueue?, hlookup, hprefix, hguards] at hread
              refine ⟨r, middle, rfl, rfl, hguards.1, hguards.2, ?_⟩
              exact hread.symm
            · simp [downReplayQueue?, hlookup, hprefix, hguards] at hread
  · rintro ⟨r, middle, hlookup, hprefix, harrival, hservice, hq⟩
    simp [downReplayQueue?, hlookup, hprefix, harrival, hservice, hq]

/-- The preceding computed-query guards still expose the transition when
either of the two later output-register checks fails. -/
theorem downReplayQueue?_computed_survives_output_failure (seed : ℕ)
    (A : List (Bool × ℕ)) (k : ℕ) (r : Bool × ℕ)
    (middle : ActiveFollowerDownAcceptance.ReplayRegisters)
    (hlookup : A[k]? = some r)
    (hprefix : ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
      (4 * rate.n) 0 ⟨(0, seed), 0⟩ (A.take k) = .ok middle)
    (harrival : r.2 ≤ D p)
    (hservice : ActiveFollowerDownAcceptance.replayService (4 * rate.n) middle r ≤ D p)
    (houtputFailure : ¬ (QueueReplay.transition (4 * rate.n) middle.registers r).1 ≤ p.T * D p ∨
      ¬ (QueueReplay.transition (4 * rate.n) middle.registers r).2 ≤ p.T * D p) :
    downReplayQueue? rate seed A (.computed k) =
      some (QueueReplay.transition (4 * rate.n) middle.registers r).2 := by
  have hread := (downReplayQueue?_computed_iff rate seed A k
    (QueueReplay.transition (4 * rate.n) middle.registers r).2).2
      ⟨r, middle, hlookup, hprefix, harrival, hservice, rfl⟩
  rcases houtputFailure with _ | _
  · exact hread
  · exact hread

/-- Parse the actual expected-filtered DOWN word and apply the accepted-start
register test and original cutoff scan. -/
def downCutRecoveryInput? (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate) :
    Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) × ℕ) := by
  classical
  exact (ReferenceDownReception.ordinaryParse p rate cut.filteredRaw).bind fun M =>
    if ha : OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) M then
      some (M, (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M time
        (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M time logged ha) row).endpoint)
    else none

/-- Read the actual source diagnostic, retaining every optional absence and
the literal recovery records produced from the accepted DOWN input. -/
def recordDownQueue? (r : Record) (i : Fin (p.m - 1))
    (site : DownQueueSite) : Option ℕ :=
  (r.output.followers i).downInput.bind fun logged =>
    (r.output.followers i).down.bind fun cut =>
      (downCutRecoveryInput? rate r.input.row r.input.time logged cut).bind fun input =>
        downReplayQueue? rate input.1.val.q
          (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate input.1 logged input.2) site

/-- A reached recovery read on the actual reference DOWN operation is either
accepted or carries an explicit replay failure. The latter is eliminated from
actual complete-source diagnostics by their ordinary follower output. -/
theorem downCutRecoveryInput?_outcome
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (feedback : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (endpoint : ℕ)
    (hread : downCutRecoveryInput? rate row time logged
      (ReferenceDownReception.referenceDownCut p view i row time feedback rate logged) =
        some (M, endpoint)) :
    (∃ after raw scan registers lastService,
      (ReferenceDownReception.referenceDownCut p view i row time feedback rate logged).outcome =
        .accepted logged after raw M scan registers lastService ∧
      scan.endpoint = endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged endpoint =
        .ok (⟨registers, lastService⟩ : ActiveFollowerDownAcceptance.ReplayRegisters)) ∨
    (∃ reason,
      (ReferenceDownReception.referenceDownCut p view i row time feedback rate logged).outcome =
        .outputFailure logged reason) := by
  classical
  by_cases hs : ActiveFollowerDownAcceptance.downSelected p i row time
  · by_cases ht : logged.status = .unoccupied
    · by_cases hr : ActiveFollowerDownAcceptance.registerInputDomain p rate logged
      · by_cases hd : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch
        · by_cases hb : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer
          · by_cases hm : (ActiveFollowerDownAcceptance.currentDecodeStep
                p i row time feedback rate logged).2 =
                ReferenceDownReception.expectedDownFlatWord view i row time
            · cases hp : ReferenceDownReception.ordinaryParse p rate
                  (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i row time feedback rate logged).2 with
              | none =>
                  simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
                    hs, ht, hr, hd, hb, ← hm, hp] at hread
              | some M0 =>
                  by_cases ha : OrdinaryMessageCodec.acceptDown
                      (ReferencePrelaunchFollower.codecParams p rate.eta)
                      (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) M0
                  · let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M0 time
                      (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M0 time logged ha) row
                    have heq : (M0, scan.endpoint) = (M, endpoint) := by
                      simpa [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
                        hs, ht, hr, hd, hb, ← hm, hp, ha, scan] using hread
                    have hM : M0 = M := congrArg Prod.fst heq
                    have he : scan.endpoint = endpoint := congrArg Prod.snd heq
                    subst M
                    subst endpoint
                    cases hc : ActiveFollowerDownAcceptance.checkedRecovery p rate M0 logged
                        scan.endpoint with
                    | error reason =>
                        right
                        refine ⟨.replay reason, ?_⟩
                        simp only [scan] at hc
                        simp [ReferenceDownReception.referenceDownCut,
                          hs, ht, hr, hd, hb, ← hm, hp, ha, hc]
                    | ok recovered =>
                        left
                        refine ⟨{ logged with
                          lastDown := some M0
                          downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                            p i row time feedback rate logged).1
                          S := recovered.registers.1
                          delta := recovered.lastService
                          backlog := recovered.registers.2
                          status := if scan.endpoint = time.val + 2 then .pending else .unoccupied
                          buffer := [] },
                          (ActiveFollowerDownAcceptance.currentDecodeStep
                            p i row time feedback rate logged).2,
                          scan, recovered.registers, recovered.lastService, ?_, rfl, ?_⟩
                        · simp only [scan] at hc
                          simp [ReferenceDownReception.referenceDownCut,
                            hs, ht, hr, hd, hb, ← hm, hp, ha, hc, scan]
                        · cases recovered
                          rfl
                  · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
                      hs, ht, hr, hd, hb, ← hm, hp, ha] at hread
            · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
                hs, ht, hr, hd, hb, hm, ReferenceDownReception.ordinaryParse,
                OrdinaryMessageCodec.parseDown, Option.map] at hread
          · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
              hs, ht, hr, hd, hb, ReferenceDownReception.ordinaryParse,
              OrdinaryMessageCodec.parseDown, Option.map] at hread
        · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
            hs, ht, hr, hd, ReferenceDownReception.ordinaryParse,
            OrdinaryMessageCodec.parseDown, Option.map] at hread
      · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
          hs, ht, hr, ReferenceDownReception.ordinaryParse,
          OrdinaryMessageCodec.parseDown, Option.map] at hread
    · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
        hs, ht, ReferenceDownReception.ordinaryParse, OrdinaryMessageCodec.parseDown, Option.map] at hread
  · simp [downCutRecoveryInput?, ReferenceDownReception.referenceDownCut,
      hs, ReferenceDownReception.ordinaryParse, OrdinaryMessageCodec.parseDown, Option.map] at hread

/-- Under a successful complete checked replay, every exposed site is either
the untouched seed or a positive prefix ending at a successful queue state. -/
theorem downReplayQueue?_attributed (seed : ℕ) (A : List (Bool × ℕ))
    (final : ActiveFollowerDownAcceptance.ReplayRegisters)
    (hfull : ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
      (4 * rate.n) 0 ⟨(0, seed), 0⟩ A = .ok final)
    (site : DownQueueSite) (q : ℕ)
    (hread : downReplayQueue? rate seed A site = some q) :
    q = seed ∨ ∃ k middle, 1 ≤ k ∧ k ≤ A.length ∧
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
        (4 * rate.n) 0 ⟨(0, seed), 0⟩ (A.take k) = .ok middle ∧
      middle.registers.2 = q := by
  classical
  cases site with
  | initial => exact Or.inl (Option.some.inj hread).symm
  | checked k =>
      simp only [downReplayQueue?] at hread
      split at hread
      next hk =>
        obtain ⟨middle, hp, _hdomain, heq⟩ :=
          ActiveFollowerDownAcceptance.checkedReplay_success_prefix
            (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, seed), 0⟩ final A hfull k
        rw [hp] at hread
        have hq : middle.registers.2 = q := Option.some.inj hread
        by_cases hz : k = 0
        · left
          subst k
          simpa only [List.take_zero, QueueReplay.replay, List.foldl_nil] using
            hq.symm.trans (congrArg Prod.snd heq)
        · exact Or.inr ⟨k, middle, by omega, hk, hp, hq⟩
      next => cases hread
  | computed k =>
      obtain ⟨r, before, hlookup, hp, _harrival, _hservice, hq⟩ :=
        (downReplayQueue?_computed_iff rate seed A k q).mp hread
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
      obtain ⟨before', hp', _beforedomain, heq⟩ :=
        ActiveFollowerDownAcceptance.checkedReplay_success_prefix
          (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, seed), 0⟩ final A hfull k
      have hbefore : before' = before := Except.ok.inj (hp'.symm.trans hp)
      subst before'
      obtain ⟨after, ha, _hadomain, haEq⟩ :=
        ActiveFollowerDownAcceptance.checkedReplay_success_prefix
          (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, seed), 0⟩ final A hfull (k + 1)
      refine Or.inr ⟨k + 1, after, by omega, by omega, ha, ?_⟩
      rw [haEq, List.take_succ_eq_append_getElem hk, QueueReplay.replay_append,
        QueueReplay.replay, List.foldl_cons, List.foldl_nil, ← heq, hget]
      exact hq.symm

/-- The reached diagnostic's recovery input is accepted on the actual source
branch. No-failure follows internally from the complete source outcome. -/
theorem actualDownRecoveryInput_accepted (z : X)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (endpoint : ℕ)
    (hlogged : (((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val]).output.followers i).downInput = some logged)
    (hdown : (((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val]).output.followers i).down = some cut)
    (hread : downCutRecoveryInput? rate
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val]).input.row
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val]).input.time
      logged cut = some (M, endpoint)) :
    ∃ after raw scan registers lastService,
      cut.outcome = .accepted logged after raw M scan registers lastService ∧
      scan.endpoint = endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged endpoint =
        .ok (⟨registers, lastService⟩ : ActiveFollowerDownAcceptance.ReplayRegisters) := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val]
  obtain ⟨choice, memory, logged0, _hchoice, _hstatus, _hlogging, hinput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  have heq : logged0 = logged := Option.some.inj (hinput.symm.trans hlogged)
  subst logged0
  obtain ⟨hrow, hi, ht⟩ := ReferenceFollowerFixedReply.actualChoice_alignment r i
  change (ReferenceFollowerFixedReply.actualChoice r i).row = r.input.row at hrow
  change (ReferenceFollowerFixedReply.actualChoice r i).follower = i at hi
  change (ReferenceFollowerFixedReply.actualChoice r i).time = r.input.time at ht
  change cut = ReferenceDownReception.referenceDownCut p _
    (ReferenceFollowerFixedReply.actualChoice r i).follower
    (ReferenceFollowerFixedReply.actualChoice r i).row
    (ReferenceFollowerFixedReply.actualChoice r i).time _ rate logged at hcut
  rw [hrow, hi, ht] at hcut
  have hreached := downCutRecoveryInput?_outcome rate
    r.output.preparation.coordinator.downView i r.input.row r.input.time
    (r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    logged M endpoint (by rw [← hcut]; exact hread)
  rw [← hcut] at hreached
  rcases hreached with haccepted | ⟨reason, hfailure⟩
  · exact haccepted
  · obtain ⟨_logged, _hlogged, _hmismatch, houtcomes⟩ :=
      ReferenceFirstCorrectedNativeDownCalendarReplay.complete_down_diagnostic_outcomes
        rewards C_star C_h z j i cut hdown
    rcases houtcomes with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩ <;> rw [hfailure] at h <;> cases h

/-- A literal reached native DOWN queue query refines, on the same source,
birth, installation, current selection, and recovery diagnostic, to the
accepted successful-prefix event. Pointwise attribution needs no time-control
assumption and makes no claim of full physical-site coverage. -/
theorem recordDownQueue?_mem_nativeDownComputedOverflowEvent
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? = some birth)
    (P : Payload) (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (hsigma : P.sigma = t)
    (j : Fin (sourceRecords rate rewards C_star C_h z).length)
    (hbj : birthIndex rate rewards C_star C_h z ≤ j.val)
    (current : ReferenceActivePhysicalStep.Selection
      (sourceRecords rate rewards C_star C_h z)[j.val].input)
    (hselected : (sourceRecords rate rewards C_star C_h z)[j.val].output.preparation.coordinator.selection =
      some current) (hpayload : current.view.payload = P)
    (i : Fin (p.m - 1)) (site : DownQueueSite) (q : ℕ)
    (hread : recordDownQueue? rate (sourceRecords rate rewards C_star C_h z)[j.val] i site = some q)
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedNativeDownOverflowCover.nativeDownComputedOverflowEvent
      rate rewards C_star C_h u t := by
  classical
  simp only [recordDownQueue?, Option.bind_eq_some_iff] at hread
  obtain ⟨logged, hlogged, cut, hdown, ⟨M, endpoint⟩, hinput, hqueue⟩ := hread
  obtain ⟨after, raw, scan, registers, lastService, haccepted, hend, hchecked⟩ :=
    actualDownRecoveryInput_accepted rate rewards C_star C_h z j i logged cut M endpoint
      hlogged hdown hinput
  have hb := (List.getElem?_eq_some_iff.mp hbirth).1
  have hget := (List.getElem?_eq_some_iff.mp hbirth).2
  have hborn' : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z] P := by
    rw [hget]
    exact hborn
  have hM := (ReferenceFirstCorrectedNativeDownCalendarReplay.complete_birth_current_down_physical_recovery
    rewards C_star C_h z ⟨birthIndex rate rewards C_star C_h z, hb⟩ j P hborn' hbj
      current hselected hpayload i logged after cut raw M scan registers lastService
      hlogged hdown haccepted).1
  change z ∈ correctedCell rate rewards C_star C_h u t ∧ _
  refine ⟨hz, birth, P, hbirth, hborn, hsigma, j, hbj, current, hselected, hpayload,
    i, logged, cut, hlogged, hdown, logged, after, raw, M, scan, registers, lastService,
    haccepted, hM, ?_⟩
  rw [← hend] at hqueue hchecked
  rw [ActiveFollowerDownAcceptance.checkedRecovery_eq_checkedReplay] at hchecked
  rcases downReplayQueue?_attributed rate M.val.q _ _ hchecked site q hqueue with
    hseed | ⟨k, middle, hkpos, hkbound, hkchecked, hq⟩
  · exact Or.inl (by simpa only [hseed] using hlarge)
  · exact Or.inr ⟨k, middle, hkpos, hkbound, hkchecked, by simpa only [hq] using hlarge⟩

end Bandits.Support.ReferenceFirstCorrectedReachedDownQueueOverflowCover
