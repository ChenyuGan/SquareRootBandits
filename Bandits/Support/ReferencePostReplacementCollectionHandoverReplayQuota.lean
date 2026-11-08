/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseCorrespondence
public import Bandits.Support.ReferencePostReplacementCollectionHandoverFreshService
public import Bandits.Support.HandoverStoppedServiceQuota

/-!
# Physical service count on the actual stopped later-handover records

The count below is formed from the original before/after physical service
indicators, restricted to the same actual later-handover records and literal
stopped support. A natural prefix `n` counts calendar indices `t < n`; hence
the first detecting service/update is retained in the prefix ending at `t+1`.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open Bandits.Support.HandoverStoppedDecoderReplay
open Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseCorrespondence
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverReplayQuota

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "H" b =>
  ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
    rate rewards C_star C_h z b
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val

/-- One literal physical service on the same actual H record, after retaining
the global strict-past decoder condition and original numerical queue safety.
The source indicators are the existing real-valued FreshService indicators;
their zero-one theorem identifies the natural tick below. -/
public def actualLiteralHandoverServiceTick
    (b : Fin (R).length) (i : Fin (p.m - 1)) (t : Fin p.T) : ℕ :=
  if ∃ j : Fin (H b).length,
      (H b)[j.val].input.time = t ∧
      ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h t i z ∧
      ReferencePostReplacementCollectionHandoverFreshService.X_before
          rate rewards C_star C_h t i z +
        ReferencePostReplacementCollectionHandoverFreshService.X_after
          rate rewards C_star C_h t i z = 1
  then 1 else 0

/-- Uncapped stopped physical service count over the first `n` calendar
indices. Indices beyond the finite horizon contribute zero. -/
public def actualLiteralHandoverServiceCount
    (b : Fin (R).length) (i : Fin (p.m - 1)) (n : ℕ) : ℕ :=
  ∑ t : Fin p.T, if t.val < n then actualLiteralHandoverServiceTick
    rate rewards C_star C_h z b i t else 0

private theorem actualHandover_index
    (b : Fin (R).length)
    (j : Fin (H b).length) :
    ∃ hk : b.val + j.val < (R).length,
      (H b)[j.val] = R[b.val + j.val]'hk := by
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let V := (R)[b.val] :: W
  let H' := ((R)[b.val] :: W).takeWhile
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  have hV : V.IsPrefix ((R).drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : H'.IsPrefix ((R).drop b.val) :=
    (List.takeWhile_prefix _).trans hV
  have hlen : H'.length ≤ (R).length - b.val := by
    simpa only [List.length_drop] using hH.length_le
  have hj' : j.val < H'.length := by
    simpa only [H',
      ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords]
      using j.isLt
  have hk : b.val + j.val < (R).length := by
    omega
  refine ⟨hk, ?_⟩
  change H'[j.val] = (R)[b.val + j.val]'hk
  rw [hH.getElem hj', List.getElem_drop]

private theorem actualHandover_time
    (b : Fin (R).length)
    (j : Fin (H b).length) :
    (H b)[j.val].input.time.val = (R)[b.val].input.time.val + j.val := by
  obtain ⟨hk, heq⟩ := actualHandover_index rate rewards C_star C_h z b j
  have htime := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
    rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  have htime' : ((R)[b.val + j.val]'hk).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + j.val) := by
    simpa only [Fin.val_mk] using htime
  have hbirth := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
    rate rewards C_star C_h z b
  rw [heq]
  change ((R)[b.val + j.val]'hk).input.time.val =
    (R)[b.val].input.time.val + j.val
  rw [htime', hbirth]
  omega

private theorem actualHandover_lookup
    (b : Fin (R).length)
    (j : Fin (H b).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (H b)[j.val].input.time z = some (H b)[j.val] := by
  obtain ⟨hk, heq⟩ := actualHandover_index rate rewards C_star C_h z b j
  rw [heq]
  have ht := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.completeSuffixRecord_time
    rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  have htime : ((R)[b.val + j.val]'hk).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + j.val) := by
    simpa only [List.get_eq_getElem] using ht
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      ((R)[b.val + j.val]'hk).input.time.val := by
    rw [htime]
    omega
  have hindex : ((R)[b.val + j.val]'hk).input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
        b.val + j.val := by
    rw [htime]
    omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact List.getElem?_eq_getElem hk

private theorem handoverRoundInput_word_eq
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i) :
    (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
      payload record.input.row record.input.time).down.word =
      HandoverStoppedDecoderReplay.currentWord p β (payload.downRecord i) := by
  simp only [ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput,
    CoordinatorLocalArmChoice.storedDownFlatWord,
    HandoverStoppedDecoderReplay.currentWord,
    AssignmentStartPayload.Input.downWord]
  rw [hselected]
  rfl

private theorem actualLaterHandoverLive_word_eq_stored
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (b : Fin (R).length) (t : Fin p.T) :
    (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
      rate rewards C_star C_h z payload (H b) t).input.down.word =
      CoordinatorLocalArmChoice.storedDownFlatWord payload
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
          rate rewards C_star C_h z payload (H b) t).input.selected := by
  classical
  unfold ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
  split_ifs with hwindow
  · cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z <;>
      rfl
  · rfl

private theorem startCode_status_eq
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hcode : ReferencePostReplacementCollectionHandoverFreshService.startCode
      rate rewards C_star C_h t i z = .inr (.success
        (FollowerDownMeasurability.followerStateCode rate state)
        (FollowerLifecycleMeasurability.localMemoryCode memory)))
    (s : Fin 3)
    (hstage : ∃ code memoryCode,
      ReferencePostReplacementCollectionHandoverFreshService.startCode
        rate rewards C_star C_h t i z = .inr (.success code memoryCode) ∧
          code.status = s) :
    FollowerDownMeasurability.followerStatusCode state.status = s := by
  obtain ⟨code, memoryCode, hcode', hstatus⟩ := hstage
  have heq := Sum.inr.inj (hcode.symm.trans hcode')
  cases heq
  exact hstatus

private theorem actual_task_frame_stage_status
    (t : Fin p.T) (i : Fin (p.m - 1))
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.rawHTaskSupport
      rate rewards C_star C_h t i z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧
      (∀ j, (record.output.preparation.followers.followers j).configuration =
        .ordinary (states j) (memories j)) ∧
      (z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_before
        rate rewards C_star C_h t i → (states i).status = .unoccupied) ∧
      (z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_after
        rate rewards C_star C_h t i → (states i).status = .pending) := by
  obtain ⟨record, selected, states, memories, hrecord, hselected, hpending,
      hconfigs, hlastDown, hnotReleased, hcode⟩ :=
    ReferencePostReplacementCollectionHandoverFreshService.actual_task_frame
      rate rewards C_star C_h t i z hsupport
  refine ⟨record, selected, states, memories, hrecord, hselected, hpending,
    hconfigs, ?_, ?_⟩
  · intro hbefore
    change ReferencePostReplacementCollectionHandoverSourcePrefix.rawHTaskSupport
        rate rewards C_star C_h t i z ∧
      ∃ stateCode memoryCode,
        ReferencePostReplacementCollectionHandoverFreshService.startCode
          rate rewards C_star C_h t i z = .inr (.success stateCode memoryCode) ∧
          stateCode.status = 0 at hbefore
    obtain ⟨_, stateCode, memoryCode, hstage, hstatus⟩ := hbefore
    have hstatusCode := startCode_status_eq rate rewards C_star C_h t i z
      (states i) (memories i) hcode 0 ⟨stateCode, memoryCode, hstage, hstatus⟩
    cases hstate : (states i).status <;>
      simp_all [FollowerDownMeasurability.followerStatusCode]
  · intro hafter
    change ReferencePostReplacementCollectionHandoverSourcePrefix.rawHTaskSupport
        rate rewards C_star C_h t i z ∧
      ∃ stateCode memoryCode,
        ReferencePostReplacementCollectionHandoverFreshService.startCode
          rate rewards C_star C_h t i z = .inr (.success stateCode memoryCode) ∧
          stateCode.status = 1 at hafter
    obtain ⟨_, stateCode, memoryCode, hstage, hstatus⟩ := hafter
    have hstatusCode := startCode_status_eq rate rewards C_star C_h t i z
      (states i) (memories i) hcode 1 ⟨stateCode, memoryCode, hstage, hstatus⟩
    cases hstate : (states i).status with
    | unoccupied => simp [hstate, FollowerDownMeasurability.followerStatusCode] at hstatusCode
    | pending => rfl
    | released => simp [hstate, FollowerDownMeasurability.followerStatusCode] at hstatusCode

/-- The existing physical before/after source indicators are exactly the two
original source events on a date where the real-valued sum is one. -/
public theorem actual_service_real_one_iff
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    ReferencePostReplacementCollectionHandoverFreshService.X_before
        rate rewards C_star C_h t i z +
      ReferencePostReplacementCollectionHandoverFreshService.X_after
        rate rewards C_star C_h t i z = 1 ↔
      (z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_before
          rate rewards C_star C_h t i ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_before
          rate rewards C_star C_h i t z) ∨
      (z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_after
          rate rewards C_star C_h t i ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t z) := by
  classical
  constructor
  · intro hone
    have hdisjoint := Set.disjoint_left.mp
      (ReferencePostReplacementCollectionHandoverFreshService.A_before_disjoint_A_after
        rate rewards C_star C_h t i)
    by_cases hb : z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_before
        rate rewards C_star C_h t i
    · have ha : z ∉ ReferencePostReplacementCollectionHandoverFreshService.A_after
          rate rewards C_star C_h t i := hdisjoint hb
      by_cases hv : ReferenceFirstLiveHandoverBoundaryFactorization.V_before
          rate rewards C_star C_h i t z
      · exact Or.inl ⟨hb, hv⟩
      · simp [ReferencePostReplacementCollectionHandoverFreshService.X_before,
          ReferencePostReplacementCollectionHandoverFreshService.X_after, hb, ha, hv] at hone
    · by_cases ha : z ∈ ReferencePostReplacementCollectionHandoverFreshService.A_after
          rate rewards C_star C_h t i
      · by_cases hv : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
            rate rewards C_star C_h i t z
        · exact Or.inr ⟨ha, hv⟩
        · simp [ReferencePostReplacementCollectionHandoverFreshService.X_before,
            ReferencePostReplacementCollectionHandoverFreshService.X_after, hb, ha, hv] at hone
      · simp [ReferencePostReplacementCollectionHandoverFreshService.X_before,
          ReferencePostReplacementCollectionHandoverFreshService.X_after, hb, ha] at hone
  · rintro (⟨hb, hv⟩ | ⟨ha, hv⟩)
    · have hdisjoint := Set.disjoint_left.mp
        (ReferencePostReplacementCollectionHandoverFreshService.A_before_disjoint_A_after
          rate rewards C_star C_h t i)
      have hnot : z ∉ ReferencePostReplacementCollectionHandoverFreshService.A_after
          rate rewards C_star C_h t i := hdisjoint hb
      simp [ReferencePostReplacementCollectionHandoverFreshService.X_before,
        ReferencePostReplacementCollectionHandoverFreshService.X_after, hb, hnot, hv]
    · have hdisjoint := Set.disjoint_left.mp
        (ReferencePostReplacementCollectionHandoverFreshService.A_before_disjoint_A_after
          rate rewards C_star C_h t i)
      have hnot : z ∉ ReferencePostReplacementCollectionHandoverFreshService.A_before
          rate rewards C_star C_h t i := fun h => hdisjoint h ha
      simp [ReferencePostReplacementCollectionHandoverFreshService.X_before,
        ReferencePostReplacementCollectionHandoverFreshService.X_after, hnot, ha, hv]

private theorem actual_later_handover_fixed_word
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (b : Fin (R).length) (i : Fin (p.m - 1)) :
    ∀ t : Fin p.T,
      AffineBatchDecoder.eligible
        (HandoverStoppedDecoderReplay.observationTrace p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment
            (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
              rate rewards C_star C_h z payload (H b))
            (ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
              rate rewards C_star C_h z)
            (ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
              rate rewards C_star C_h z)) i t) →
      (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
        rate rewards C_star C_h z payload (H b) t).input.down.word =
        HandoverStoppedDecoderReplay.currentWord p β (payload.downRecord i) := by
  intro t hel
  let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
    rate rewards C_star C_h z payload (H b)
  let data := HandoverStoppedDecoderReplay.fromLive p payload.assignment live
    (ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
      rate rewards C_star C_h z)
    (ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
      rate rewards C_star C_h z)
  obtain ⟨_, hselected, _, _, _⟩ :=
    (HandoverStoppedDecoderReplay.eligible_iff p payload.assignment data i t).mp hel
  dsimp [data, HandoverStoppedDecoderReplay.fromLive] at hselected
  change (live t).input.selected = i at hselected
  change (live t).input.down.word =
    HandoverStoppedDecoderReplay.currentWord p β (payload.downRecord i)
  rw [actualLaterHandoverLive_word_eq_stored rate rewards C_star C_h z payload b t]
  rw [hselected]
  rfl

/-- A literal supported H date has incoming replay indicator `J = 1`. The
payload, bank, accepted-start value and physical pending state are produced
from the same actual birth; separately obtained witnesses are identified by
InstallationBirth uniqueness. -/
public theorem actual_later_handover_supported_J_eq_one
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1))
    (j : Fin (H b).length)
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      ∃ (selected : ReferenceActivePhysicalStep.Selection (H b)[j.val].input)
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
      (H b)[j.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧
      ((H b)[j.val].output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory ∧
      i ∈ selected.view.pendingAtChoice ∧
      (let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
          rate rewards C_star C_h z payload (H b)
       let cutoff := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
          rate rewards C_star C_h z
       let overflow := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
          rate rewards C_star C_h z
       (snapshotBefore p β payload.assignment
            (fromLive p payload.assignment live cutoff overflow) i payload.sigma
            (payload.downRecord i)
            (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
            (H b)[j.val].input.time.val).phase =
          if i ∈ selected.view.pendingAtChoice then
            if choice.status = .unoccupied then
              HandoverStoppedDecoderReplay.Phase.awaitingDown
            else HandoverStoppedDecoderReplay.Phase.acceptedUnconfirmed
          else HandoverStoppedDecoderReplay.Phase.confirmed) ∧
      (let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
          rate rewards C_star C_h z payload (H b)
       let cutoff := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
          rate rewards C_star C_h z
       let overflow := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
          rate rewards C_star C_h z
       J p payload.assignment (fromLive p payload.assignment live cutoff overflow)
          payload.sigma
          (snapshotBefore p β payload.assignment
            (fromLive p payload.assignment live cutoff overflow) i payload.sigma
            (payload.downRecord i)
            (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
            (H b)[j.val].input.time.val)
          (H b)[j.val].input.time = 1) ∧
      (let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
          rate rewards C_star C_h z payload (H b)
       let cutoff := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
          rate rewards C_star C_h z
       let overflow := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
          rate rewards C_star C_h z
       N_before p β payload.assignment (fromLive p payload.assignment live cutoff overflow)
          i payload.sigma (payload.downRecord i)
          (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
          (H b)[j.val].input.time.val < 2 * AffineBatchDecoder.quota p + 1) := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, _hunoccupied,
      hstrict, hwell, hpendingStamps, _hchron, _hcollectedStamps,
      _hseedPhase, _hseedDates⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_stoppedReplay_seed
      rate rewards C_star C_h z b hb i
  obtain ⟨phasePayload, phaseBefore, phaseMemory, hphaseBirth, hphaseBefore,
      _hphaseUnoccupied, _hphaseStrict, hcorrespondence⟩ :=
    ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actual_later_handover_stoppedReplay_correspondence
      rate rewards C_star C_h z b hb i
  have hpayloadEq :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      R[b.val] payload phasePayload hbirth hphaseBirth
  subst phasePayload
  have hbeforeEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hphaseBefore.symm.trans hbefore)
  rcases hbeforeEq with ⟨hstateEq, hmemoryEq⟩
  subst phaseBefore
  subst phaseMemory
  let t := (H b)[j.val].input.time
  obtain ⟨selected, choice, inputState, memory, inputMemory, hselected, hselectedPayload,
      hchoiceConfig, _hinputState, _hbatch, _hdecoder, _hacceptedStart, hphase, _⟩ :=
    hcorrespondence j hsupport
  obtain ⟨record, selectedTask, taskStates, taskMemories, hrecord,
      hselectedTask, hpending, _hframes, _hlastDown, _hnotReleased, _hstartCode⟩ :=
    ReferencePostReplacementCollectionHandoverFreshService.actual_task_frame
      rate rewards C_star C_h t i z hsupport.1
  have hlookup := actualHandover_lookup rate rewards C_star C_h z b j
  have hrecordEq : record = (H b)[j.val] :=
    Option.some.inj (hrecord.symm.trans hlookup)
  subst record
  have hselectedEq : selectedTask = selected :=
    Option.some.inj (hselectedTask.symm.trans hselected)
  subst selectedTask
  obtain ⟨hcutoff, _, _⟩ :=
    ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actual_later_handover_strict_predecessor_markers
      rate rewards C_star C_h z b hb j i hsupport
  let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
    rate rewards C_star C_h z payload (H b)
  let cutoff := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverCutoffBefore
    rate rewards C_star C_h z
  let overflow := ReferencePostReplacementCollectionHandoverPhaseCorrespondence.actualHandoverOverflowAfter
    rate rewards C_star C_h z
  have hmember : i ∈ selected.view.pendingAtChoice := hpending
  have hphaseNorm :
      (snapshotBefore p β payload.assignment
        (fromLive p payload.assignment live cutoff overflow) i payload.sigma
        (payload.downRecord i)
        (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
        t.val).phase =
        if i ∈ selected.view.pendingAtChoice then
          if choice.status = .unoccupied then
            HandoverStoppedDecoderReplay.Phase.awaitingDown
          else HandoverStoppedDecoderReplay.Phase.acceptedUnconfirmed
        else HandoverStoppedDecoderReplay.Phase.confirmed := by
    change (snapshotBefore p β payload.assignment
      (fromLive p payload.assignment live cutoff overflow) i payload.sigma
      (payload.downRecord i)
      (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
      t.val).phase = _ at hphase
    exact hphase
  have hphaseUnresolved :
      (snapshotBefore p β payload.assignment
        (fromLive p payload.assignment live cutoff overflow) i payload.sigma
        (payload.downRecord i)
        (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
        t.val).phase.unresolved := by
    change (snapshotBefore p β payload.assignment
      (fromLive p payload.assignment live cutoff overflow) i payload.sigma
      (payload.downRecord i)
      (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
      t.val).phase =
        HandoverStoppedDecoderReplay.Phase.awaitingDown ∨
      (snapshotBefore p β payload.assignment
        (fromLive p payload.assignment live cutoff overflow) i payload.sigma
        (payload.downRecord i)
        (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
        t.val).phase = HandoverStoppedDecoderReplay.Phase.acceptedUnconfirmed
    rw [hphaseNorm, ite_eq_left hmember]
    by_cases hstatus : choice.status = .unoccupied <;>
      simp [hstatus]
  have hbirthTime :=
    ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      R[b.val] payload hbirth
  have htime := actualHandover_time rate rewards C_star C_h z b j
  have hfix : payload.sigma.val ≤ t.val := by
    dsimp [t]
    rw [htime, ← hbirthTime]
    omega
  have hJ : J p payload.assignment (fromLive p payload.assignment live cutoff overflow)
      payload.sigma
      (snapshotBefore p β payload.assignment
        (fromLive p payload.assignment live cutoff overflow) i payload.sigma
        (payload.downRecord i)
        (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) t.val)
      t = 1 := by
    have hphaseUnresolved' :
        (snapshotBefore p β payload.assignment
          (fromLive p payload.assignment live cutoff overflow) i payload.sigma
          (payload.downRecord i)
          (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before))
          t.val).phase.unresolved := hphaseUnresolved
    have hcutoff' : (fromLive p payload.assignment live cutoff overflow t).cutoffBefore = false :=
      hcutoff
    unfold J
    rw [ite_eq_left ⟨hfix, hphaseUnresolved', hcutoff'⟩]
  have hseedTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have hsource : WaitedWordWindow.sourceRound payload.sigma =
      (payload.downRecord i).val.sigma := by rfl
  have hpendingFixed : ∀ e ∈ before.downBatch.pending, e.time.val < payload.sigma.val := by
    intro e he
    rw [hseedTime]
    exact hpendingStamps e he
  have hfixed : ∀ t' : Fin p.T, payload.sigma.val ≤ t'.val →
      AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p payload.assignment live i t') →
      (live t').input.down.word = HandoverStoppedDecoderReplay.currentWord p β
        (payload.downRecord i) := by
    intro t' htime' hel
    have hel' : AffineBatchDecoder.eligible
        (HandoverStoppedDecoderReplay.observationTrace p payload.assignment
          (fromLive p payload.assignment live cutoff overflow) i t') := by
      change AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p payload.assignment live i t')
      exact hel
    exact actual_later_handover_fixed_word rate rewards C_star C_h z payload b i t' hel'
  have hbound := HandoverStoppedServiceQuota.N_before_lt_twoQ_add_one_of_J
    p β payload.assignment live cutoff overflow i payload.sigma (payload.downRecord i)
    (ReferencePrelaunchFollower.acceptedStart before) before.downBatch hsource hstrict
    hwell.1 hpendingFixed hfixed t hJ
  refine ⟨payload, before, beforeMemory, hbirth, hbefore,
    selected, choice, memory, hselected, hselectedPayload, ?_, hmember, hphaseNorm,
    hJ, hbound⟩
  · exact hchoiceConfig

open ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open ReferencePostReplacementCollectionHandoverFreshService

/-- Casting the natural tick recovers the literal before/after physical
indicator, masked only by this birth's actual H records and literal support.
In particular, a recorded zero service remains zero; no replay counter is used
to define the physical tick. -/
public theorem actualLiteralHandoverServiceTick_real
    (b : Fin (R).length) (i : Fin (p.m - 1)) (t : Fin p.T) :
    (actualLiteralHandoverServiceTick rate rewards C_star C_h z b i t : ℝ) =
      if ∃ j : Fin (H b).length,
        (H b)[j.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z
      then X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z
      else 0 := by
  by_cases hmask : ∃ j : Fin (H b).length,
      (H b)[j.val].input.time = t ∧
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h t i z
  · rcases service_zero_or_one rate rewards C_star C_h t i z with hzero | hone
    · have hnot : ¬ ∃ j : Fin (H b).length,
          (H b)[j.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z ∧
          X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
        rintro ⟨_, _, _, h⟩
        rw [hzero] at h
        exact zero_ne_one h
      rw [actualLiteralHandoverServiceTick, ite_eq_right hnot, ite_eq_left hmask,
        hzero, Nat.cast_zero]
    · obtain ⟨j, ht, hs⟩ := hmask
      have hservice : ∃ j : Fin (H b).length,
          (H b)[j.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z ∧
          X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 :=
        ⟨j, ht, hs, hone⟩
      rw [actualLiteralHandoverServiceTick, ite_eq_left hservice,
        ite_eq_left (show (∃ k : Fin (H b).length, (H b)[k.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z) from ⟨j, ht, hs⟩), hone, Nat.cast_one]
  · have hnot : ¬ ∃ j : Fin (H b).length,
        (H b)[j.val].input.time = t ∧
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h t i z ∧
        X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
      rintro ⟨j, ht, hs, _⟩
      exact hmask ⟨j, ht, hs⟩
    rw [actualLiteralHandoverServiceTick, ite_eq_right hnot, ite_eq_right hmask, Nat.cast_zero]

private theorem actual_record_rewards
    (t : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record) :
    record.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst record
    rfl
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- Each actual physical service on literal support is a service of the same
uncapped stopped replay. The canonical birth state is retained in both
factors; the proof makes no comparison after a detecting failure. -/
private theorem actual_later_handover_service_JX_eq_one
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (j : Fin (H b).length)
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z)
    (hone : X_before rate rewards C_star C_h (H b)[j.val].input.time i z +
      X_after rate rewards C_star C_h (H b)[j.val].input.time i z = 1) :
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before
      (H b)[j.val].input.time.val
    J p payload.assignment data payload.sigma q (H b)[j.val].input.time *
      X p payload.assignment data i q (H b)[j.val].input.time = 1 := by
  obtain ⟨P, B, M, hP, hB, selected, choice, memory, hs, hp, hc, hi, hphase, hJ, _⟩ :=
    actual_later_handover_supported_J_eq_one rate rewards C_star C_h z b hb i j hsupport
  have heq := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  rw [heq] at hp hphase hJ
  obtain ⟨heqB, heqM⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hB.symm.trans hbefore)
  subst B M
  obtain ⟨P, hP, hsnapshots⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
  have heq := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  rw [heq] at hsnapshots
  obtain ⟨S, states, memories, hS, hSP, hconfigs, hsnapshot, _hfields, hnotReleased, _⟩ :=
    hsnapshots j
  have heqS := Option.some.inj (hS.symm.trans hs)
  subst S
  obtain ⟨heqChoice, _⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hc.symm.trans (hconfigs i))
  subst choice
  let r := (H b)[j.val]
  let t := r.input.time
  let data := actualHandoverReplayData rate rewards C_star C_h z payload b
  let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before t.val
  change J p payload.assignment data payload.sigma q t *
    X p payload.assignment data i q t = 1
  change J p payload.assignment data payload.sigma q t = 1 at hJ
  change q.phase = _ at hphase
  rw [hJ, one_mul]
  have hlookup := actualHandover_lookup rate rewards C_star C_h z b j
  have hcalendar : actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t =
      ⟨handoverRoundInput payload r.input.row t, handoverWholeRewardRowAt r t,
        ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload r⟩ := by
    apply actualLaterHandoverLive_of_actual_record rate rewards C_star C_h z payload (H b) t
    · have ht := actualHandover_time rate rewards C_star C_h z b j
      have hbt := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        R[b.val] payload hbirth
      change r.input.time.val = _ at ht
      constructor <;> dsimp only [t, r] <;> rw [ht, ← hbt] <;>
        have := j.isLt <;> omega
    · exact hlookup
  have hdataSnapshot : (data t).snapshot =
      ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩ := hsnapshot
  have hdataInput : (data t).input = handoverRoundInput payload r.input.row t := by
    change (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).input = _
    rw [hcalendar]
  have hdataRewards : (data t).rewards = handoverWholeRewardRowAt r t := by
    change (actualLaterHandoverLive rate rewards C_star C_h z payload (H b) t).rewards = _
    rw [hcalendar]
  have hinv : ActiveRoundActions.no_released_while_missing (data t).snapshot := by
    intro _ k
    rw [hdataSnapshot]
    exact hnotReleased k
  obtain ⟨taskRecord, taskSelected, taskStates, taskMemories, htaskRecord,
      htaskSelected, _htaskPending, htaskConfigs, hbeforeStatus, hafterStatus⟩ :=
    actual_task_frame_stage_status rate rewards C_star C_h z t i hsupport.1
  have heqRecord := Option.some.inj (htaskRecord.symm.trans hlookup)
  subst taskRecord
  obtain ⟨hstate, _⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((htaskConfigs i).symm.trans (hconfigs i))
  have hbeforeStatus' : z ∈ A_before rate rewards C_star C_h t i →
      (states i).status = .unoccupied := by
    intro hz
    rw [← hstate]
    exact hbeforeStatus hz
  have hafterStatus' : z ∈ A_after rate rewards C_star C_h t i →
      (states i).status = .pending := by
    intro hz
    rw [← hstate]
    exact hafterStatus hz
  have hreward := actual_record_rewards rate rewards C_star C_h z t r hlookup
  have hpositive (hpos : 0 < (rewards t
      ((handoverRoundInput payload r.input.row t).tuple.val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) :
      0 < (data t).rewards.val
        ((data t).input.tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    rw [hdataRewards, hdataInput]
    change 0 < ((r.input.rewards t _).val : ℝ) / (D p : ℝ)
    rw [hreward]
    exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast D_pos p)
  rcases (actual_service_real_one_iff rate rewards C_star C_h z t i).mp hone with
    ⟨hstage, hv⟩ | ⟨hstage, hv⟩
  · obtain ⟨record, S, hr, hS, hgeometry⟩ :=
      before_physical_service rate rewards C_star C_h t i z hstage
    have heqRecord := Option.some.inj (hr.symm.trans hlookup)
    subst record
    have heqS := Option.some.inj (hS.symm.trans hs)
    subst S
    obtain ⟨hslot, hselected, hbit, hpos⟩ := hgeometry.mp hv
    rw [hp] at hbit
    have hu := hbeforeStatus' hstage
    have hslot' : (data t).input.slot = PublicDiscreteDraws.downSlot := by
      rw [hdataInput]
      exact hslot
    have hselected' : (data t).input.selected = i := by
      rw [hdataInput]
      exact hselected
    have hi' : (data t).input.selected ∈ (data t).snapshot.missing := by
      rw [hselected', hdataSnapshot]
      exact hi
    have hu' : (data t).snapshot.status (data t).input.selected = .unoccupied := by
      rw [hselected', hdataSnapshot]
      exact hu
    have hbit' : (data t).input.down.bit = 1 := by
      rw [hdataInput, handoverRoundInput_down_bit, hselected]
      exact hbit
    have hfeedback := ActiveRoundActions.unoccupied_down_feedback p.two_le_m
      (data t).snapshot (data t).input (data t).rewards hslot' hi' hinv hu'
    rw [hbit', ite_eq_left rfl, hselected'] at hfeedback
    have hel : AffineBatchDecoder.eligible (observationTrace p payload.assignment data i t) := by
      apply (eligible_iff p payload.assignment data i t).mpr
      refine ⟨hslot', hselected', ?_, ?_, ?_⟩
      · rw [hdataSnapshot]; exact hi
      · rw [hdataSnapshot]; exact hu
      · rw [hfeedback]
        exact hpositive hpos
    have hphase' : q.phase = .awaitingDown := by
      rw [hphase, ite_eq_left hi, ite_eq_left hu]
    simp only [X, hphase', hel, ite_true]
  · obtain ⟨record, S, hr, hS, hgeometry⟩ :=
      after_physical_service rate rewards C_star C_h t i z hstage
    have heqRecord := Option.some.inj (hr.symm.trans hlookup)
    subst record
    have heqS := Option.some.inj (hS.symm.trans hs)
    subst S
    obtain ⟨hslot, hselected, hbit, hpos⟩ := hgeometry.mp hv
    rw [hp] at hbit
    have hu := hafterStatus' hstage
    have hslot' : (data t).input.slot = PublicDiscreteDraws.downSlot := by
      rw [hdataInput]; exact hslot
    have hselected' : (data t).input.selected = i := by
      rw [hdataInput]; exact hselected
    have hi' : (data t).input.selected ∈ (data t).snapshot.missing := by
      rw [hselected', hdataSnapshot]; exact hi
    have hu' : (data t).snapshot.status (data t).input.selected = .pending := by
      rw [hselected', hdataSnapshot]; exact hu
    have hbit' : (data t).input.down.bit = 0 := by
      rw [hdataInput, handoverRoundInput_down_bit, hselected]
      exact hbit
    have hfeedback := ActiveRoundActions.pending_down_coordinator_feedback p.two_le_m
      (data t).snapshot (data t).input (data t).rewards hslot' hi' hinv hu' hbit'
    rw [hselected'] at hfeedback
    have hconfirm : physicalConfirmation p payload.assignment data i t := by
      refine ⟨hslot', hselected', ?_, hbit', ?_⟩
      · rw [hdataSnapshot]; exact hi
      · rw [hfeedback]
        exact hpositive hpos
    have hnotu : (states i).status ≠ .unoccupied := by rw [hu]; decide
    have hphase' : q.phase = .acceptedUnconfirmed := by
      rw [hphase, ite_eq_left hi, ite_eq_right hnotu]
    simp only [X, hphase', hconfirm, ite_true]

private theorem actual_literal_service_tick_le_replay
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (t : Fin p.T) :
    let data := actualHandoverReplayData rate rewards C_star C_h z payload b
    let q := actualHandoverSnapshotBefore rate rewards C_star C_h z payload b i before t.val
    actualLiteralHandoverServiceTick rate rewards C_star C_h z b i t ≤
      J p payload.assignment data payload.sigma q t * X p payload.assignment data i q t := by
  dsimp only
  unfold actualLiteralHandoverServiceTick
  split_ifs with hservice
  · obtain ⟨j, ht, hsupport, hone⟩ := hservice
    subst t
    rw [actual_later_handover_service_JX_eq_one rate rewards C_star C_h z b hb i
      payload before beforeMemory hbirth hbefore j hsupport hone]
  · exact Nat.zero_le _

private theorem actual_literal_service_count_le_replay
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (hbefore : R[b.val].input.state.followers i = .ordinary before beforeMemory)
    (n : ℕ) :
    actualLiteralHandoverServiceCount rate rewards C_star C_h z b i n ≤
      N_before p β payload.assignment
        (actualHandoverReplayData rate rewards C_star C_h z payload b) i payload.sigma
        (payload.downRecord i)
        (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) n := by
  unfold actualLiteralHandoverServiceCount N_before
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ht
  · exact actual_literal_service_tick_le_replay rate rewards C_star C_h z b hb i
      payload before beforeMemory hbirth hbefore t
  · exact Nat.le_refl 0

/-- The actual stopped physical count is dominated by the same uncapped
replay at every natural calendar prefix. Both the inclusive replay quota and
the strict incoming physical quota use the actual birth's whole inherited
bank and accepted-start register. Empty support contributes zero termwise. -/
public theorem actual_later_handover_physical_service_domination
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      (∀ n : ℕ,
        let replayCount := N_before p β payload.assignment
          (actualHandoverReplayData rate rewards C_star C_h z payload b) i payload.sigma
          (payload.downRecord i)
          (initial p before.downBatch (ReferencePrelaunchFollower.acceptedStart before)) n
        actualLiteralHandoverServiceCount rate rewards C_star C_h z b i n ≤ replayCount ∧
          replayCount ≤ 2 * AffineBatchDecoder.quota p + 1) ∧
      (∀ j : Fin (H b).length,
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h (H b)[j.val].input.time i z →
        actualLiteralHandoverServiceCount rate rewards C_star C_h z b i
          (H b)[j.val].input.time.val < 2 * AffineBatchDecoder.quota p + 1) := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, _hunoccupied,
      hstrict, hwell, hpendingStamps, _hchron, _hcollectedStamps,
      _hseedPhase, _hseedDates⟩ :=
    ReferencePostReplacementCollectionHandoverStoppedFailureCoverage.actual_later_handover_stoppedReplay_seed
      rate rewards C_star C_h z b hb i
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload (H b)
  let cutoff := actualHandoverCutoffBefore rate rewards C_star C_h z
  let overflow := actualHandoverOverflowAfter rate rewards C_star C_h z
  have hsource : WaitedWordWindow.sourceRound payload.sigma =
      (payload.downRecord i).val.sigma := rfl
  have hseedTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have hpendingFixed : ∀ e ∈ before.downBatch.pending, e.time.val < payload.sigma.val := by
    intro e he
    rw [hseedTime]
    exact hpendingStamps e he
  have hfixed : ∀ t : Fin p.T, payload.sigma.val ≤ t.val →
      AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p payload.assignment live i t) →
      (live t).input.down.word = currentWord p β (payload.downRecord i) := by
    intro t _ hel
    exact actual_later_handover_fixed_word rate rewards C_star C_h z payload b i t hel
  have hdom := actual_literal_service_count_le_replay rate rewards C_star C_h z b hb i
    payload before beforeMemory hbirth hbefore
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, ?_, ?_⟩
  · intro n
    exact ⟨hdom n, HandoverStoppedServiceQuota.N_before_le_twoQ_add_one
      p β payload.assignment live cutoff overflow i payload.sigma (payload.downRecord i)
      (ReferencePrelaunchFollower.acceptedStart before) before.downBatch hsource hstrict
      hwell.1 hpendingFixed hfixed n⟩
  · intro j hsupport
    obtain ⟨P, B, M, hP, hB, selected, choice, memory, _hs, hp, _hc, _hi,
        _hphase, _hJ, hbound⟩ :=
      actual_later_handover_supported_J_eq_one rate rewards C_star C_h z b hb i j hsupport
    have hP_eq := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      R[b.val] P payload hP hbirth
    rw [hP_eq] at hbound
    obtain ⟨hB_eq, hM_eq⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hB.symm.trans hbefore)
    rw [hB_eq] at hbound
    exact lt_of_le_of_lt (hdom (H b)[j.val].input.time.val) hbound

/-- Inclusive physical quota on the actual stopped H task. The prefix is an
arbitrary natural number, so this also covers dates beyond the horizon. -/
public theorem actual_later_handover_physical_service_count_le
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) (n : ℕ) :
    actualLiteralHandoverServiceCount rate rewards C_star C_h z b i n ≤
      2 * AffineBatchDecoder.quota p + 1 := by
  obtain ⟨_payload, _before, _memory, _hbirth, _hbefore, hcounts, _hstrict⟩ :=
    actual_later_handover_physical_service_domination rate rewards C_star C_h z b hb i
  exact (hcounts n).1.trans (hcounts n).2

/-- At a literal supported current H date the same follower is still pending,
so its strictly incoming physical service count is below the inclusive quota. -/
public theorem actual_later_handover_physical_service_count_lt_of_supported
    (b : Fin (R).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) (j : Fin (H b).length)
    (hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h (H b)[j.val].input.time i z) :
    actualLiteralHandoverServiceCount rate rewards C_star C_h z b i
      (H b)[j.val].input.time.val < 2 * AffineBatchDecoder.quota p + 1 := by
  obtain ⟨_payload, _before, _memory, _hbirth, _hbefore, _hcounts, hstrict⟩ :=
    actual_later_handover_physical_service_domination rate rewards C_star C_h z b hb i
  exact hstrict j hsupport

end Bandits.Support.ReferencePostReplacementCollectionHandoverReplayQuota

end
