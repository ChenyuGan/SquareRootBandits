/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPendingFormation

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection DOWN origin and formation date

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-296,327-348,459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-108`.

The current pending boundary and its earlier retained acceptance use the same
initialized dispatch and canonical physical run. Acceptance is after the play
in source round `s+j+1`; the first subsequent choice is in round `s+j+2`.
The formation coordinate is clipped at the actual cutoff choice. This module
supplies chronology only, without a fixed-reply interval or a formation-bank
claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower
open ReferenceFollowerReplyChronology
open ReferenceAcceptedUpFollowerHistory
open ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceFirstCollectionFormationOrigin

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Strict increase between two actual retained acceptances. The ordinary
endpoint is an explicit internal input, obtained from the produced boundary. -/
private theorem retained_down_starts_strict
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (i : Fin (p.m - 1)) (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlast : final.followers i = .ordinary last lastMemory)
    (a b : ℕ) (ha : a < records.length) (hb : b < records.length)
    (hab : a < b)
    (left right : DownRecord (p := p) (rate := rate))
    (hleft : RetainedDown records[a] i left)
    (hright : RetainedDown records[b] i right) :
    left.val.sigma < right.val.sigma := by
  obtain ⟨next, nextMemory, hnext, _⟩ :=
    connected_output_chronology chain i last lastMemory hlast b hb
  obtain ⟨choice, choiceMemory, hchoice, hstrict, _⟩ :=
    record_appliedDown_strict records[b] i right.val.sigma
      (retainedDown_appliedDown hright) next nextMemory hnext
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    record_input_to_choice records[b] i choice choiceMemory hchoice
  have hstart := acceptedStart_eq_of_reply_eq hreply
  have hprefix := connected_take_to_input chain b hb
  have haTake : a < (records.take b).length := by
    simp only [List.length_take]
    exact lt_min hab ha
  obtain ⟨afterLeft, afterMemory, hafter, hbound⟩ :=
    connected_output_chronology hprefix i before beforeMemory hbefore a haTake
  rw [List.getElem_take] at hafter
  obtain ⟨_, _, _, _, hafterStart⟩ :=
    record_appliedDown_strict records[a] i left.val.sigma
      (retainedDown_appliedDown hleft) afterLeft afterMemory hafter
  omega

/-- Uniqueness refers to every actual indexed diagnostic for the same word. -/
private theorem retained_down_index_unique
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (i : Fin (p.m - 1)) (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlast : final.followers i = .ordinary last lastMemory)
    (a b : ℕ) (ha : a < records.length) (hb : b < records.length)
    (message : DownRecord (p := p) (rate := rate))
    (hleft : RetainedDown records[a] i message)
    (hright : RetainedDown records[b] i message) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := retained_down_starts_strict chain i last lastMemory hlast
      a b ha hb hab message message hleft hright
    omega
  · exact hab
  · have h := retained_down_starts_strict chain i last lastMemory hlast
      b a hb ha hab message message hright hleft
    omega

/-- Internal composition on a genuinely constructed dispatch. The record,
ordinary endpoint and formed selector are explicit inputs here; the public
root below produces them from the original source on its same witness. -/
private theorem actual_formed_origin
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort)
    (n : Fin d.stream.ell)
    (r : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hr : d.stream.window[n.val]? = some r)
    (hold : r.input.state.followers i = .ordinary old memory)
    (hformed : old.lastDown = some (d.stream.payload.downRecord i)) :
    let out := d.stream
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    (out.payload.downRecord i).val.sigma = s + 1 ∧ acceptedStart old = s + 1 ∧
    ∃ (j : ℕ) (acceptedRecord : RoundRecord (p := p) (rate := rate)),
      j < w + n.val ∧ E.records[j]? = some acceptedRecord ∧
      RetainedDown acceptedRecord i (out.payload.downRecord i) ∧
      (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
        (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
        (after : ReferencePrelaunchFollower.State p rate.eta)
        (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
        (scan : FollowerCutoffScan.ScanResult p.T)
        (registers : ℕ × ℕ) (lastService : ℕ),
        (acceptedRecord.output.followers i).downInput = some logged ∧
        (acceptedRecord.output.followers i).down = some cut ∧
        cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
          logged after raw (out.payload.downRecord i) scan registers lastService) ∧
      acceptedRecord.input.time.val + 1 = s + j + 1 ∧
      acceptedRecord.input.rows = source.1.2 ∧
      acceptedRecord.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      acceptedRecord.input.rewards = rewards ∧
      (∀ (j' : ℕ) (other : RoundRecord (p := p) (rate := rate)),
        j' < w + n.val → E.records[j']? = some other →
          RetainedDown other i (out.payload.downRecord i) → j' = j) ∧
      let f := if j < w then 0 else j - w + 1
      ∃ hf : f < B.length,
        f ≤ n.val ∧ B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) ∧
        (j < w → f = 0) ∧ (j = w → f = 1) := by
  classical
  let out := d.stream
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hwindow : out.window = B := by
    simpa only [ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  have hnWindow : n.val < out.window.length := lt_of_lt_of_le n.isLt out.withinWindow
  have hnB : n.val < B.length := by simpa only [hwindow] using hnWindow
  have hrElem : out.window[n.val] = r :=
    (List.getElem?_eq_some_iff.mp hr).2
  have hlookup : E.records[w + n.val]? = some r := by
    simpa only [hrElem, E, w, ReferenceFirstCollectionReadyStream.actualEpoch] using
      (out.alignment ⟨n.val, hnWindow⟩).1
  have hindex : w + n.val < E.records.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hrecord : E.records[w + n.val] = r :=
    (List.getElem?_eq_some_iff.mp hlookup).2
  have hendpoint : E.records[w + n.val].input.state.followers i =
      .ordinary old memory := by rw [hrecord]; exact hold
  have hprefix := connected_take_to_input E.connected (w + n.val) hindex
  have hmessageStart : (out.payload.downRecord i).val.sigma = s + 1 := by
    change out.payload.sigma.val + 1 = s + 1
    rw [out.payloadMatchesCutoff]
    exact congrArg (fun t : ℕ => t + 1) out.cutoffContext.2.1
  have holdStart : acceptedStart old = s + 1 := by
    simp only [acceptedStart, hformed]
    exact hmessageStart
  have hseed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hseed with ⟨_, _, _, _, _, _, _, hfollowers⟩
  have hfirst := hfollowers i
  rcases hfirst with ⟨hfirst, _hfirstDown, hfirstStart, _⟩
  have hfirstI : I.followers i = .ordinary
      (ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
        (ActualReferenceInitializationBlock.refFollower i))
      (ActiveFollowerLifecycle.initialMemory p) := by
    simpa only [I, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirst
  obtain ⟨first, firstMemory, hfirstOrdinary, _, _, hchange⟩ :=
    connected_ordinary_chronology hprefix i old memory hendpoint
  have hfirstEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hfirstOrdinary.symm.trans hfirstI)
  have hzero : acceptedStart first = 0 := by rw [hfirstEq.1]; exact hfirstStart
  obtain ⟨acceptedRecord, hmem, sigma, happlied, _, _⟩ := hchange (by omega)
  obtain ⟨j, hjTake, hjRecord⟩ := List.mem_iff_getElem.mp hmem
  have hj : j < w + n.val := by
    simp only [List.length_take] at hjTake
    omega
  have hjE : j < E.records.length := by omega
  have hjEq : E.records[j] = acceptedRecord := by
    simpa only [List.getElem_take] using hjRecord
  have hjLookup : E.records[j]? = some acceptedRecord := by
    rw [List.getElem?_eq_getElem hjE, hjEq]
  obtain ⟨logged, cut, after, raw, message, scan, registers, lastService,
    hdownInput, hdown, houtcome, _⟩ := happlied
  have hretained : RetainedDown acceptedRecord i message :=
    ⟨logged, cut, after, raw, scan, registers, lastService, hdownInput, hdown, houtcome⟩
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases horigin.origin with ⟨originCut, P0, _birth, live, owned, base,
    ⟨hw, horiginCut⟩, _huniqueCut, hcoordinator, _hcutoffChosen, hP0,
    _hsigma, _hqueues, _hfirstCutoff, _hbirthMem, _hbirth, _hbirthTime,
    _hbirthSelection, _halignment, _hselection, _hcurrent, hearlier⟩
  have horiginLookup : E.records[w]? = some originCut := by
    rw [horiginCut]
    exact List.getElem?_eq_getElem hw
  have hsameCut : originCut = out.cutoff.cut :=
    Option.some.inj (horiginLookup.symm.trans out.cutoff.cutIndex)
  obtain ⟨execution⟩ := out.cutoffExecution
  have hsameLive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live live owned base =
      .live execution.live execution.owned execution.base := by
    rw [hsameCut] at hcoordinator
    exact hcoordinator.symm.trans execution.actualLive
  have hlive : live = execution.live := by injection hsameLive
  have hP0Out : P0 = out.payload := by
    calc
      P0 = live.payload := hP0
      _ = execution.live.payload := congrArg
        (fun x : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => x.payload) hlive
      _ = out.cutoff.payload := execution.payloadIsLive.symm
      _ = out.payload := out.payloadMatchesCutoff.symm
  have hmessage : message = out.payload.downRecord i := by
    have h := hearlier ⟨n.val, hnB⟩ j hj acceptedRecord hjLookup i message hretained
    exact h.1.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate =>
      P.downRecord i) hP0Out)
  subst message
  have htime : acceptedRecord.input.time.val + 1 = s + j + 1 := by
    have hm : (E.records.map (fun r => r.input.time.val))[j]? =
        some acceptedRecord.input.time.val := by
      simp only [List.getElem?_map, hjLookup, Option.map_some]
    have hcalendar := run_time_values I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
    change E.records.map (fun r => r.input.time.val) = ReferenceActivePhysicalHorizon.calendar s count at hcalendar
    rw [hcalendar] at hm
    have hjCount : j < count := by
      have hc := run_record_count I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
      change E.records.length = count at hc
      omega
    have hcal : (ReferenceActivePhysicalHorizon.calendar s count)[j]? = some (s + j) := by
      rw [List.getElem?_eq_getElem (by simpa [ReferenceActivePhysicalHorizon.calendar] using hjCount)]
      simp [ReferenceActivePhysicalHorizon.calendar]
    rw [hcal] at hm
    exact congrArg (fun t : ℕ => t + 1) (Option.some.inj hm).symm
  have hinputs : acceptedRecord.input.rows = source.1.2 ∧
      acceptedRecord.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      acceptedRecord.input.rewards = rewards := by
    apply run_record_inputs I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1 acceptedRecord
    exact List.mem_iff_getElem.mpr ⟨j, hjE, hjEq⟩
  refine ⟨hmessageStart, holdStart, j, acceptedRecord, hj, hjLookup, hretained,
    ⟨logged, cut, after, raw, scan, registers, lastService, hdownInput, hdown, houtcome⟩,
    htime, hinputs.1, hinputs.2.1, hinputs.2.2, ?_, ?_⟩
  · intro j' other hj' hother hotherRetained
    change j' < w + n.val at hj'
    change E.records[j']? = some other at hother
    have hj'E : j' < E.records.length := (List.getElem?_eq_some_iff.mp hother).1
    have hj'Take : j' < (E.records.take (w + n.val)).length := by
      simp only [List.length_take]
      exact lt_min hj' hj'E
    have hotherEq : E.records[j'] = other :=
      (List.getElem?_eq_some_iff.mp hother).2
    have hleft : RetainedDown (E.records.take (w + n.val))[j'] i
        (out.payload.downRecord i) := by
      simpa only [List.getElem_take, hotherEq] using hotherRetained
    have hright : RetainedDown (E.records.take (w + n.val))[j] i
        (out.payload.downRecord i) := by
      simpa only [List.getElem_take, hjEq] using hretained
    exact retained_down_index_unique hprefix i old memory hendpoint j' j
      hj'Take hjTake (out.payload.downRecord i) hleft hright
  · let f := if j < w then 0 else j - w + 1
    have hfn : f ≤ n.val := by dsimp only [f]; split <;> omega
    have hf : f < B.length := lt_of_le_of_lt hfn hnB
    have hcalendar := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
      rate source rewards C_star C_h count hcross hspan hshort ⟨f, hf⟩
    have hfTime : B[f].input.time.val + 1 = s + w + 1 + f := hcalendar.2.1
    have hdate : B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) := by
      rw [hfTime]
      dsimp only [f]
      split <;> omega
    exact ⟨hf, hfn, hdate, fun h => ite_eq_left h,
      fun h => by simp only [h, lt_self_iff_false, ↓reduceIte, Nat.sub_self, Nat.zero_add]⟩

/-- The Gamma-only producer. The dispatch, pending boundary, checked current
UP offer and the accepted-DOWN origin all share the witness returned by the
admitted pending-formation theorem. No ordinary history or accepted diagnostic
is a root premise. This is an internal chronology result, not regret closure. -/
theorem actual_initialized_first_collection_formation_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        E.records[w]? = some cutRecord ∧
        cutRecord.input.state.coordinator = .live registers owned base ∧
        registers.payload = out.payload ∧
        out.cutoff.ledger.pending = Finset.univ ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : ReferenceActivePhysicalStep.Ledger rate)
                (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  source rewards E.records (w + n.val) count
                  (ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed)
                  r out.payload incoming out.saved)
                (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 =
                  ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed +
                    w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                cell.serviceLedger = out.ledgers n ∧
                r.input.state.followers i = .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
                state.S + state.backlog ≤ w * D p ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  state.lastDown = some (out.payload.downRecord i)) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  ∃ U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta),
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    1 ≤ U.val.sigma ∧
                    (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
                      PublicDiscreteDraws.slotDraw
                          (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                            .ordinary state memory ∧
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                          (r.input.state.activations i) r.input.time state = .offer U ∧
                        ReferenceFollowerFixedReply.actualUpExpected r =
                          some ((OrdinaryMessageCodec.wordEquivFlat
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                            (OrdinaryMessageCodec.encodeUp
                              (CoordinatorCollectionLedger.codecParams p rate.eta.val) U)))) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  (out.payload.downRecord i).val.sigma = s + 1 ∧
                  acceptedStart state = s + 1 ∧
                  ∃ (j : ℕ) (acceptedRecord : RoundRecord (p := p) (rate := rate)),
                    j < w + n.val ∧ E.records[j]? = some acceptedRecord ∧
                    RetainedDown acceptedRecord i (out.payload.downRecord i) ∧
                    (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                      (after : ReferencePrelaunchFollower.State p rate.eta)
                      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
                      (scan : FollowerCutoffScan.ScanResult p.T)
                      (registers : ℕ × ℕ) (lastService : ℕ),
                      (acceptedRecord.output.followers i).downInput = some logged ∧
                      (acceptedRecord.output.followers i).down = some cut ∧
                      cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                        logged after raw (out.payload.downRecord i) scan registers lastService) ∧
                    acceptedRecord.input.time.val + 1 = s + j + 1 ∧
                    acceptedRecord.input.rows = source.1.2 ∧
                    acceptedRecord.input.selected =
                      ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                    acceptedRecord.input.rewards = rewards ∧
                    (∀ (j' : ℕ) (other : RoundRecord (p := p) (rate := rate)),
                      j' < w + n.val → E.records[j']? = some other →
                        RetainedDown other i (out.payload.downRecord i) → j' = j) ∧
                    let f := if j < w then 0 else j - w + 1
                    ∃ hf : f < B.length,
                      f ≤ n.val ∧
                      B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) ∧
                      (j < w → f = 0) ∧ (j = w → f = 1))) := by
  classical
  obtain ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hboundaries⟩ :=
    ReferenceFirstCollectionPendingFormation.actual_initialized_first_collection_pending_formation
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, ?_⟩
  intro n hn i hi
  obtain ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
    hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
    hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast, hup⟩ :=
    hboundaries n hn i hi
  refine ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
    hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
    hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast, hup, ?_⟩
  intro hformed
  exact actual_formed_origin source rewards C_star C_h count hcross hspan hshort
    d n r i state memory hr hstate hformed

end Bandits.Support.ReferenceFirstCollectionFormationOrigin

end
