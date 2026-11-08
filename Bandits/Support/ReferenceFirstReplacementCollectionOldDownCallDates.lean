/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOldDownSenderReadiness
public import Bandits.Support.ReferenceFirstReplacementCollectionOldDownReceiverReadiness

import Lean.Elab.Tactic.Omega

/-!
# Actual first-replacement OLD DOWN call dates

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-295,327-348,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:20-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module names OLD from the actual choice-time configuration and defines
the positive service coordinates from actual selected channels and own
feedback. The helper results below retain the physical decoder input and its
original sample; they do not assert a service quota or a decoder-failure event.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionOldDownCallDates

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- OLD means the actual arm-choice configuration is ordinary and unoccupied,
with a last DOWN word other than the installed word. -/
def actualOldAt
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) : Prop :=
  ∃ state memory,
    (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
    state.status = .unoccupied ∧ state.lastDown ≠ some M

/-- The positive OLD DOWN service dates in a requested physical prefix. A
failure on the current date is included; only a failure strictly before that
date excludes it. -/
def countedOldDownServiceAt
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) : Prop :=
  a.val < j ∧ actualOldAt (K.get a) i M ∧
    ReferenceSelectedAffinePairLaw.selectedChannel p
      ((K.get a).input.row.2 (K.get a).input.time).1 = some (0, i) ∧
    0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val ∧
    ∀ r ∈ K.take a.val,
      ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r

/-- The literal list of actual positive OLD DOWN service coordinates. -/
def countedOldDownServiceIndices
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    List (Fin K.length) := by
  classical
  exact (List.finRange K.length).filter fun a =>
    decide (countedOldDownServiceAt K j i M a)

theorem mem_countedOldDownServiceIndices
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) :
    a ∈ countedOldDownServiceIndices K j i M ↔
      countedOldDownServiceAt K j i M a := by
  classical
  simp [countedOldDownServiceIndices, countedOldDownServiceAt]

private theorem downSelected_of_selectedChannel
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p
      (row.2 time).1 = some (0, i)) :
    ActiveFollowerDownAcceptance.downSelected p i row time := by
  have hdown : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.downSlot := by
    by_contra hn
    unfold ReferenceSelectedAffinePairLaw.selectedChannel
      ReferenceSelectedAffinePairLaw.channelFromDraws at h
    simp only [ite_eq_right hn] at h
    by_cases hup : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot
    · simp only [ite_eq_left hup] at h
      have hf := congrArg Prod.fst (Option.some.inj h)
      cases hf
    · simp only [ite_eq_right hup] at h
      cases h
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p (row.2 time).1 hdown] at h
  exact ⟨hdown, (Prod.mk.inj (Option.some.inj h)).2⟩

/-- Equal physical dates in the cutoff collection are the same coordinate.
The supplied calendar equation is the one derived from the canonical source
run by the first-replacement prefix roots. -/
theorem coordinate_eq_of_calendar
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)) (u : ℕ)
    (calendar : ∀ a : Fin K.length, (K.get a).input.time.val + 1 = u + a.val)
    (a a' : Fin K.length)
    (hdate : (K.get a).input.time.val = (K.get a').input.time.val) :
    a = a' := by
  apply Fin.ext
  have ha := calendar a
  have ha' := calendar a'
  omega

/-- From a real OLD ordinary choice and positive selected DOWN observation,
the actual retained call has the original physical DOWN sample and contributes
that positive entry to the actual decoder-call list for this record. -/
theorem actualOldPositiveDownCall_retained
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hOld : actualOldAt r i M)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) :
    ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
      ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call ∧
      call.1 = r.input.time ∧
      call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample r.input ∧
      ⟨r.input.time, ReferenceDownPhysicalHashRule.originalDownSample r.input⟩ ∈
        ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
  rcases hOld with ⟨state, memory, hchoice, hstatus, _⟩
  let call : ReferenceFollowerDownDecoderReplay.Call p :=
    (r.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
      r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate state)
  have hconfig :
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r i = .ordinary state memory :=
    hchoice
  have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i = r.input.row := by
    exact (ReferenceFollowerFixedReply.actualChoice_alignment r i).1
  have htime : ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i = r.input.time :=
    ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime r i
  have hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call := by
    rw [ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i state memory hconfig,
      htime, hrow]
  have heligible : AffineBatchDecoder.eligible call.2 := by
    exact (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i r.input.row
      r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate state).2
        ⟨hselected, hstatus, hpositive⟩
  have hsample :=
    ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_sample_original_of_eligible
      r i call hcall heligible
  have hcallTime : call.1 = r.input.time := by
    simp only [call]
  have hcalls : ReferenceFollowerDownDecoderReplay.actualDownCalls i [r] = [call] := by
    simp [ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall]
  have hentry : ⟨call.1, call.2.sample⟩ ∈
      ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
    rw [ReferenceFollowerDownDecoderReplay.actualDownPositives, hcalls]
    unfold ReferenceFollowerDownDecoderReplay.positiveCallEntries
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [AffineBatchDecoder.positiveAt, heligible, AffineBatchDecoder.entry,
      ActiveFollowerDownAcceptance.currentInputExtension]
  refine ⟨call, hcall, hcallTime, hsample, ?_⟩
  simpa only [hcallTime, hsample] using hentry

/-- Source-root call/date producer for the actual first replacement cutoff.
Every counted coordinate is built from the original whole source run and its
literal birth and cutoff matches. The service list itself uses the actual
choice, actual selected DOWN channel, own positive feedback, requested physical
prefix, and strict-past physical-failure exclusion. -/
theorem complete_first_replacement_collection_old_down_positive_call_dates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let _J := ActualInitializationPhysicalStep.selectedRowIndex p source
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
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let M := fun (i : Fin (p.m - 1)) => payload.downRecord i
            (cut.input.time.val = s + c) ∧
            (∀ a : Fin K.length,
              (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val) ∧
            Function.Injective (fun a : Fin K.length => (K.get a).input.time) ∧
              ∀ (i : Fin (p.m - 1)) (j : ℕ) (a : Fin K.length),
                a ∈ countedOldDownServiceIndices K j i (M i) →
                  ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
                    ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get a) = some call ∧
                    call.1 = (K.get a).input.time ∧
                    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample
                      (K.get a).input ∧
                    ⟨(K.get a).input.time,
                      ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩ ∈
                      ReferenceFollowerDownDecoderReplay.actualDownPositives i [K.get a]
          | _ => True
      | _ => True := by
  classical
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  have hSelected :=
    ReferenceFirstReplacementCollectionSelectedUpAwaitedFields.complete_first_replacement_collection_selected_up_awaited_fields
      rate source rewards C_star C_h
  have hSeed :=
    ReferenceFirstReplacementCollectionSeedEndpoint.complete_first_replacement_collection_seed_endpoint
      rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hRoot hSelected hSeed ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hRoot hSelected hSeed ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hRoot hSelected hSeed ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hRoot hSelected ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hRoot hSelected hSeed ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hRoot hSelected hSeed ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hSeed ⊢
          rcases hRoot with ⟨hcalendar, _, hfollowers, _⟩
          rcases hSeed with ⟨_, _, hcutTime, _⟩
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let M := fun (i : Fin (p.m - 1)) => payload.downRecord i
          refine ⟨hcutTime, hcalendar, ?_, ?_⟩
          · intro a a' htime
            exact coordinate_eq_of_calendar K (cut.input.time.val + 1) hcalendar
              a a' (congrArg Fin.val htime)
          · intro i j a hmem
            have hdates := (mem_countedOldDownServiceIndices K j i (M i) a).1 hmem
            rcases hdates with ⟨_, hold, hchannel, hpositive, _⟩
            have hdown := downSelected_of_selectedChannel
              (K.get a).input.row (K.get a).input.time i hchannel
            exact actualOldPositiveDownCall_retained (K.get a) i (M i)
              hold hdown hpositive

/-- For an actual produced ordinary unoccupied choice, OLD is exactly failure
of the current-word test. No trajectory or decoder premise is used. -/
theorem actualOldAt_iff_lastDown_ne
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (hstatus : state.status = .unoccupied) :
    actualOldAt r i M ↔ state.lastDown ≠ some M := by
  constructor
  · rintro ⟨other, otherMemory, hother, _, hne⟩
    have heq := hchoice.symm.trans hother
    cases heq
    exact hne
  · intro hne
    exact ⟨state, memory, hchoice, hstatus, hne⟩

/-- Positive entries retained on a record remain in any containing physical
record list; this uses the actual calls and never reads the reward table. -/
theorem actualDownPositives_of_record_mem
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hr : r ∈ records)
    (he : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r]) :
    entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records := by
  unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
    ReferenceFollowerDownDecoderReplay.positiveCallEntries at he ⊢
  obtain ⟨call, hcall, he⟩ := List.mem_flatMap.mp he
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  have hrecordEq : record = r := by simpa only [List.mem_singleton] using hrecord
  subst record
  exact List.mem_flatMap.mpr ⟨call,
    List.mem_filterMap.mpr ⟨r, hr, hcall⟩, he⟩

/-- Complete original-source assembly of OLD DOWN dates and readiness. The
receiver supplies every actual ordinary unoccupied choice, including cutoff.
Its actual logging, zero-feedback calls and diagnostic survive independently
of favorable sender availability. The sender supplies pending/exclusion and
local acceptance facts internally; favorable sending requires the inclusive
failure-free prefix, while counted dates use strict-past exclusion. Recovery
retains the original queue seed and every checked prefix. The original bank
is replayed from corrected launch, retaining completed and pending history.

This is internal deterministic mathematics for `StoppedOldDownQuota`. It
asserts no two-batch quota, composite quota, failure probability, or waiting
bound and does not certify a manuscript theorem. -/
theorem complete_first_replacement_collection_old_down_call_dates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
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
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            let u := cut.input.time.val + 1
            cut.input.time.val = s + c ∧
            (∀ a : Fin K.length,
              (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val) ∧
            Function.Injective (fun a : Fin K.length => (K.get a).input.time) ∧
            E 0 = cut.output.next ∧
            Z 0 = cut.input.state ∧
            (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
            (∀ (a : Fin K.length) (i : Fin (p.m - 1)),
              let r := K.get a
              ∃ state memory logged post diag,
                (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (r.output.followers i).downInput = some logged ∧
                (r.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
                    r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i r =
                    some (r.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (r.input.row.2 r.input.time).2 (0, i) ∧
                  input.sample = ReferenceDownPhysicalHashRule.originalDownSample r.input ∧
                  input.roundedReward =
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) ∧
                (actualOldAt r i (M i) ↔ state.lastDown ≠ some (M i)) ∧
                (actualOldAt r i (M i) →
                  r.input.time.val = s + (c + a.val) ∧
                  r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  (M i).val.sigma ≤ r.input.time.val + 1 ∧
                  ActiveFollowerLifecycle.localStateDomainValid state ∧
                  ActiveFollowerDownAcceptance.operationInputDomain p rate state ∧
                  ReferenceDownReception.ordinaryParse p rate
                    (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) = some (M i) ∧
                  ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time state
                    (ReferenceDownReception.ordinaryParse p rate
                      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))) ∧
                  i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (K.take a.val)).toFinset ∧
                  (∀ b : Fin K.length, b.val < a.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get b) i (M i)) ∧
                  (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                    let own := r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                      p i r.input.row r.input.time own rate state
                    let diag := ReferenceDownReception.referenceDownCut p
                      r.output.preparation.coordinator.downView i r.input.row r.input.time own rate state
                    (∃ post,
                      r.output.followers i = ⟨.ordinary post memory, none, some state, some diag⟩) ∧
                    diag.raw = decoded.2 ∧
                    ((∀ record ∈ K.take (a.val + 1),
                        ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt record) →
                      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
                        r.output.preparation.coordinator.selection = some selected ∧
                        selected.view.payload = payload ∧ i ∈ selected.view.pendingAtChoice ∧
                        ReferenceDownReception.selectedDownSenderBranch selected.view i r.input.row r.input.time ∧
                        ReferenceActiveAffinePositiveTest.downSent r.input =
                          some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                        ReferenceDownReception.expectedDownFlatWord
                          r.output.preparation.coordinator.downView i r.input.row r.input.time =
                            some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                        r.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
                          ActiveRoundActions.sendArm
                            (CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 r.input.time) i)
                            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
                              (ActiveRoundActions.coordinator p.two_le_m))
                            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
                              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                        (0 < own.val.val →
                          AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample r.input)
                            (CoordinatorLocalArmChoice.storedDownFlatWord payload i) = 1) ∧
                        (decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
                          ∃ (accepted : OrdinaryMessageCodec.acceptDown
                              (ReferencePrelaunchFollower.codecParams p rate.eta)
                              (ReferencePrelaunchFollower.acceptedStart state) (r.input.time.val + 1) (M i))
                            (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                            (post : ReferencePrelaunchFollower.State p rate.eta),
                            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate (M i)
                              r.input.time (ActiveFollowerDownAcceptance.acceptedDownStartLE
                                p rate (M i) r.input.time state accepted) r.input.row
                            scan.endpoint = u ∧
                            ActiveFollowerDownAcceptance.checkedRecovery p rate (M i) state u = .ok recovered ∧
                            recovered.registers = QueueReplay.replay (4 * rate.n) (0, (M i).val.q)
                              (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) state u) ∧
                            (∀ j : ℕ, ∃ middle,
                              ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                                ⟨(0, (M i).val.q), 0⟩
                                ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) state u).take j) =
                                  .ok middle ∧
                              middle.registers = QueueReplay.replay (4 * rate.n) (0, (M i).val.q)
                                ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) state u).take j)) ∧
                            post.lastDown = some (M i) ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
                            post.downBatch = decoded.1 ∧ diag.raw = decoded.2 ∧
                            diag.outcome = .accepted state post decoded.2 (M i) scan
                              recovered.registers recovered.lastService ∧
                            r.output.followers i = ⟨.ordinary post memory, none, some state, some diag⟩ ∧
                            r.output.next.followers i = .ordinary post memory ∧
                            ReferenceAcceptedUpFollowerHistory.RetainedDown r i (M i) ∧
                            ∃ b : ℕ, b = a.val + 1 ∧ b ≤ K.length ∧
                              (Z b).followers i = .ordinary post memory))))) ∧
            (∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
                ReferenceCorrectedInitializationLaunch.correctedLaunch
                  rate source rewards C_star C_h = some initial ∧
                ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
                ∀ i : Fin (p.m - 1), ∀ j : ℕ, j ≤ K.length →
                  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)
                  let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
                  ∃ span : s + (c + j) ≤ p.T,
                    ∃ state memory base baseMemory,
                    (Z j).followers i = .ordinary state memory ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).records.drop c = K.take j ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).finalState = Z j ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint state (s + c + j) ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      c (by omega) active).finalState.followers i = .ordinary base baseMemory ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                    (∃ choice choiceMemory,
                      (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                        .ordinary choice choiceMemory ∧
                      choice.downBatch = base.downBatch) ∧
                    state.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls
                      base.downBatch ∧
                    AffineBatchDecoder.collected state.downBatch =
                      AffineBatchDecoder.collected base.downBatch ++
                        positives ∧
                    base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                    (∀ entry ∈ base.downBatch.pending, entry.time.val < s + c) ∧
                    calls.Pairwise
                      (fun first second => first.1.val < second.1.val) ∧
                    (calls.map Prod.fst).map
                      Fin.val = ReferenceActivePhysicalHorizon.calendar (s + c) j ∧
                    positives.Pairwise
                      (fun earlier later => earlier.time.val < later.time.val) ∧
                    (∀ entry ∈ positives,
                      s + c ≤ entry.time.val ∧ entry.time.val < s + c + j)) ∧
            ∀ (i : Fin (p.m - 1)) (j : ℕ) (a : Fin K.length),
                a ∈ countedOldDownServiceIndices K j i (M i) →
                  ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
                    ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get a) = some call ∧
                    call.1 = (K.get a).input.time ∧
                    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample
                      (K.get a).input ∧
                    ⟨(K.get a).input.time,
                      ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩ ∈
                      ReferenceFollowerDownDecoderReplay.actualDownPositives i [K.get a] ∧
                    ⟨(K.get a).input.time,
                      ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩ ∈
                      ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
          | _ => True
      | _ => True := by
  classical
  have hDates := complete_first_replacement_collection_old_down_positive_call_dates
    rate source rewards C_star C_h
  have hReceiver :=
    ReferenceFirstReplacementCollectionOldDownReceiverReadiness.complete_first_replacement_collection_old_down_receiver_readiness
      rate source rewards C_star C_h
  have hSender :=
    ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_first_replacement_collection_old_down_sender_readiness
      rate source rewards C_star C_h
  simp only [] at hDates hReceiver hSender ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    have hbSource := hb
    dsimp only [R, w, v] at hbSource
    simp only [hbSource] at hReceiver
    simp only [hb] at hDates hReceiver hSender ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hDates hReceiver hSender ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hDates hReceiver hSender ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        have hcSource := hc
        dsimp only [R, w, v, tail, c] at hcSource
        simp only [hcSource] at hReceiver
        simp only [hc] at hDates hReceiver hSender ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hDates hReceiver hSender ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hDates hReceiver hSender ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hDates with ⟨hcutTime, hcalendar, hinjective, hpositiveDates⟩
          rcases hSender with ⟨hZzero, hZsucc, hOldSender⟩
          rcases hReceiver with ⟨hCutoffReceivers, hLaterReceivers, hBank⟩
          have hAllReceivers : ∀ (a : Fin K.length) (i : Fin (p.m - 1)),
              let r := K.get a
              ∃ state memory logged post diag,
                (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (r.output.followers i).downInput = some logged ∧
                (r.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
                    r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i r =
                    some (r.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (r.input.row.2 r.input.time).2 (0, i) ∧
                  input.roundedReward =
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) := by
            intro ⟨a, ha⟩ i
            cases a with
            | zero =>
              have h := hCutoffReceivers i
              rw [← hcut] at h
              exact h
            | succ a =>
              have haW : a < W.length := by
                change a + 1 < W.length + 1 at ha
                omega
              exact hLaterReceivers ⟨a, haW⟩ i
          refine ⟨hcutTime, hcalendar, hinjective, rfl, hZzero, hZsucc, ?_, hBank, ?_⟩
          · intro a i
            obtain ⟨state, memory, logged, post, diag, hchoice, hstatus, hdomain,
              hclassification, hlogging, hbuffer, hstamps, hbatch, hfailure,
              hdownInput, hdiag, hdiagEq, houtput, hpostFailure, hpostStatus,
              hpostDomain, hselected⟩ := hAllReceivers a i
            refine ⟨state, memory, logged, post, diag, hchoice, hstatus, hdomain,
              hclassification, hlogging, hbuffer, hstamps, hbatch, hfailure,
              hdownInput, hdiag, hdiagEq, houtput, hpostFailure, hpostStatus,
              hpostDomain, ?_, actualOldAt_iff_lastDown_ne (K.get a) i (M i)
                state memory hchoice hstatus, ?_⟩
            · intro hdown
              obtain ⟨hlogged, hcall, hselected, henabled, hsample, hreward⟩ := hselected hdown
              refine ⟨hlogged, hcall, hselected, henabled, hsample, ?_, hreward⟩
              rw [hsample, ReferenceDownPhysicalHashRule.originalDownSample,
                ReferenceActivePhysicalStep.upSenderIndex,
                CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw, hdown.2]
            · intro hOld
              exact hOldSender a i state memory hchoice hstatus
                ((actualOldAt_iff_lastDown_ne (K.get a) i (M i)
                  state memory hchoice hstatus).mp hOld)
          · intro i j a hmem
            obtain ⟨call, hcall, htime, hsample, hentry⟩ := hpositiveDates i j a hmem
            refine ⟨call, hcall, htime, hsample, hentry, ?_⟩
            apply actualDownPositives_of_record_mem (K.take j) (K.get a) i _ _ hentry
            have hindex := (mem_countedOldDownServiceIndices K j i (M i) a).mp hmem |>.1
            exact List.mem_take_iff_getElem.mpr
              ⟨a.val, lt_min hindex a.isLt, rfl⟩

end Bandits.Support.ReferenceFirstReplacementCollectionOldDownCallDates

end
