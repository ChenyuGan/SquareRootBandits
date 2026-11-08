/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedOccupiedCalendarPreservation
public import Bandits.Support.ReferenceFirstCorrectedNativeDownCalendarReplay

import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

/-!
# Actual native DOWN seeding of the first corrected LIVE follower prefix

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:110-163,192-233,246-299`, and
`04_slow_fast_learner.tex:157-187,256-290` under `sources/zip4/manuscript/`.

This module connects the actual accepted native DOWN replay to the literal
initialization required by occupied LIVE storage on the same corrected
assignment. The conditional occupied-prefix result is consumed only after its
seed is derived from a real accepted outcome and actual record adjacency.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCorrectedAssignedArrivalPrefix
open ReferenceCompletePhysicalHistory
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceCompleteLaterLiveComplementPrefixReplay
open ReferenceCompleteOccupiedFollowerDataArrival
open ReferenceLaterLiveNumericalReadout
open ActiveFollowerLifecycle
open ActiveFollowerQueueOperation
open DeclaredFollowerLocalRound
open ActiveFollowerDownAcceptance
open ReferenceFollowerReplyChronology

namespace Bandits.Support.ReferenceFirstCorrectedAssignedNativeFollowerPrefix

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem continuing_prefix_eq_liveTail
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h source
        (birthIndex rate rewards C_star C_h source + 1) =
      liveTail rate rewards C_star C_h source := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  have htest :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    funext r
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    cases r.output.preparation.coordinator with
    | live rv qv base chosen => cases chosen <;> rfl
    | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
  rw [htest]

/-- Consecutive records in the original complete source execution share the
actual successor state. This is the physical adjacency used for the seed. -/
private theorem complete_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, hr0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, hr1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [hr0, hr1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

/-- On the actual later installation constructor, the record's own selected
view is the just-installed complete payload. -/
private theorem birth_selected_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen record.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload := by
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
      rw [← hprep, hcoord] at hchosen
      simp at hchosen
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output
          hlocal clockData installed arm =>
          have hborn' : payload = installed.registers.payload ∧
              payload.sigma.val = record.input.time.val := by
            simpa only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] using hborn
          have hpayload : payload = installed.registers.payload := hborn'.1
          subst payload
          have htime : instruction.time = record.input.time :=
            ReferenceActivePhysicalStep.later_instruction_time record.input old ledger clock cutoff
              core started instruction hstart hinstruction
          let selected : ReferenceActivePhysicalStep.Selection record.input := {
            view := {
              payload := installed.registers.payload
              pendingAtChoice := started.pending
              cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
              complementWeights := installed.registers.complementWeights }
            started := started
            pending_eq := rfl
            cutoff_eq := rfl
            arm := arm.arm
            choice_eq := by
              simpa only [ReferenceActivePhysicalStep.collectionInput, htime] using
                arm.armChoice_eq }
          let actualOutcome :
              CoordinatorRoundDispatch.CollectionOutcome
                (ReferenceActivePhysicalStep.collectionInput record.input old ledger clock cutoff) :=
            .laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed arm
          have hselection :
              (ReferenceActivePhysicalStep.DispatchCut.collection old ledger clock cutoff
                actualOutcome).selection =
                some selected := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, htime, selected, actualOutcome]
          refine ⟨selected, ?_, rfl⟩
          simpa only [hcoord] using hselection
      | _ =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn

private theorem source_slice_getElem?
    {α : Type} (R xs : List α) (b N : ℕ)
    (_hN : b + N ≤ R.length)
    (hslice : (R.drop b).take N = xs)
    (j : Fin xs.length) :
    R[b + j.val]? = some (xs[j.val]) := by
  have hlen : xs.length = min N (R.length - b) := by
    rw [← hslice]
    simp only [List.length_take, List.length_drop]
  have hjlen : j.val < min N (R.length - b) := by simpa [hlen] using j.isLt
  have hjN : j.val < N := (lt_min_iff.mp hjlen).1
  have hjdrop : j.val < R.length - b := (lt_min_iff.mp hjlen).2
  have htakeDrop : ((R.drop b).take N)[j.val]? = R[b + j.val]? := by
    rw [List.getElem?_take_of_lt hjN, List.getElem?_drop]
  have hsliceGet := congrArg (fun ys : List α => ys[j.val]?) hslice
  calc
    R[b + j.val]? = ((R.drop b).take N)[j.val]? := htakeDrop.symm
    _ = xs[j.val]? := hsliceGet
    _ = some (xs[j.val]) := List.getElem?_eq_getElem j.isLt

/-- The status of an actually accepted DOWN identifies its LIVE endpoint. -/
private theorem accepted_occupied_endpoint
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hinput : (r.output.followers i).downInput = some logged)
    (hdown : (r.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService)
    (hoccupied : after.status ≠ .unoccupied) :
    scan.endpoint = r.input.time.val + 2 := by
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    r i logged cut after raw M scan registers lastService hinput hdown haccepted
  have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
    (r.output.preparation.followers.followers i).follower
    (r.output.preparation.followers.followers i).row
    (r.output.preparation.followers.followers i).time
    (r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
    registers lastService htransition
  have hafter := hchecked.2.2.2.2.2.2
  have htime := (r.output.preparation.follower_alignment i).2.2.1
  by_contra hne
  have hne' : scan.endpoint ≠ (r.output.preparation.followers.followers i).time.val + 2 := by
    simpa only [htime] using hne
  have hstatus := congrArg ReferencePrelaunchFollower.State.status hafter
  simp only [hne', ite_false] at hstatus
  exact hoccupied hstatus

private theorem relative_live_endpoint (start b j sigma date endpoint : ℕ)
    (hpos : 1 ≤ j) (hbirth : start + b = sigma)
    (hdate : date = start + (b + j - 1)) (hend : endpoint = date + 2) :
    endpoint - (sigma + 1) = j := by
  omega

private theorem first_occupied_predecessor_input
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birthD : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (PD : Payload rate)
    (hbirthD : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[
      birthIndex rate rewards C_star C_h source]? = some birthD)
    (hchosenSrc : ReferenceCollectionPhaseHistory.laterChosen birthD.input = true)
    (hbornD : ReferenceAssignmentPayloadPersistence.InstallationBirth birthD PD) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    let V := (R.drop b).take (1 + W.length)
    ∀ (_hVshape : V = birthD :: W) (_hN : b + (1 + W.length) ≤ R.length)
      (i : Fin (p.m - 1)) (j0 : ℕ) (_hpos0 : 1 ≤ j0) (hj0 : j0 < V.length),
      (∀ j, 1 ≤ j → ∀ (hlt : j < j0) state memory,
        (V[j]'(Nat.lt_trans hlt hj0)).input.state.followers i = .ordinary state memory →
          state.status = .unoccupied) →
      let q := b + j0 - 1
      ∀ _hqFinLt : q < R.length,
      (∃ state memory,
          R[q].input.state.followers i = .ordinary state memory ∧
            state.status = .unoccupied) ∧
      (∃ selected : Selection R[q].input,
        R[q].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = PD) := by
  classical
  intro R b W V hVshape hN i j0 hpos0 hj0 hbeforeUnoccupied hqFinLt
  let q := b + j0 - 1
  have hb : b < R.length := (List.getElem?_eq_some_iff.mp hbirthD).1
  let bFin : Fin R.length := ⟨b, hb⟩
  have hVlen : V.length = 1 + W.length := by
    simp only [hVshape, List.length_cons, Nat.add_comm]
  have hj0Bound := hj0
  have hjN : j0 < 1 + W.length := by omega
  intro hqFinLt
  let qFin : Fin R.length := ⟨q, hqFinLt⟩
  have hLiveBoundary :=
    ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_first_corrected_actual_tail_boundary
      rate source rewards C_star C_h birthD PD hbirthD hchosenSrc hbornD
  by_cases hjone : j0 = 1
  · subst j0
    have hbirthGet : R[b]? = some birthD := hbirthD
    have hbRecord : R[b] = birthD :=
      (List.getElem?_eq_some_iff.mp hbirthGet).2
    have hbornAt : ReferenceAssignmentPayloadPersistence.InstallationBirth
        R[b] PD := by
      rw [hbRecord]
      exact hbornD
    obtain ⟨seed, choice, memory, hseedInput, _hdomain, hseedStatus,
      _hstart, _hchoice, _hchoiceStatus, _hvalid, _hpair, _htimes⟩ :=
      ReferenceCompleteFollowerRetainedDownRecovery.complete_installation_carried_buffer_seed
        rewards C_star C_h source bFin PD hbornAt i
    have hqB : q = b := by dsimp only [q]; omega
    have hqFinEq : qFin = bFin := by
      apply Fin.ext
      exact hqB
    have hbFinGet : R.get bFin = birthD := by
      simpa only [List.get_eq_getElem] using
        (List.getElem?_eq_some_iff.mp hbirthD).2
    have hqBirth : R[q] = birthD := by
      have hqGet : R.get qFin = birthD :=
        (congrArg (fun x : Fin R.length => R.get x) hqFinEq).trans hbFinGet
      simpa only [List.get_eq_getElem] using hqGet
    have hinputBirth : R[q].input.state.followers i = .ordinary seed memory := by
      have hseedInput' : (R.get bFin).input.state.followers i = .ordinary seed memory := by
        simpa only [List.get_eq_getElem] using hseedInput
      have hinputGet : (R.get qFin).input.state.followers i = .ordinary seed memory := by
        simpa only [hqFinEq] using hseedInput'
      simpa only [List.get_eq_getElem] using hinputGet
    have hselectedBirth :
        ∃ selected : Selection R[q].input,
          R[q].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = PD := by
      obtain ⟨selected, hsel, hpay⟩ :=
        birth_selected_payload birthD PD hchosenSrc hbornD
      cases hqBirth
      exact ⟨selected, hsel, hpay⟩
    exact ⟨⟨seed, memory, hinputBirth, hseedStatus⟩, hselectedBirth⟩
  · have hjtwo : 2 ≤ j0 := by omega
    let k0 : Fin W.length := ⟨j0 - 2, by
      have : j0 < W.length + 1 := by simpa only [Nat.add_comm] using hjN
      omega⟩
    obtain ⟨hindex, selectedPred, statePred, memoryPred, nextPred, nextMemoryPred,
      _hrows, _hselectedRow, _hrewards, hselectionPred, hpayloadPred, _hlive,
      hinputPred, _hdomain, _hlastDown, _hprepare, _houtput, _hfailure,
      _hpreserves, _hdecision, _hmemory, _hnextMemory⟩ := hLiveBoundary i k0
    have hidxNum : j0 - 1 = k0.val + 1 := by dsimp only [k0]; omega
    have hidxOption := congrArg
      (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
        xs[j0 - 1]?) hVshape
    rw [hidxNum, List.getElem?_cons_succ,
      List.getElem?_eq_getElem k0.isLt] at hidxOption
    have hprevBound : j0 - 1 < V.length := Nat.lt_trans (by omega) hj0Bound
    let jprev : Fin V.length := ⟨j0 - 1, hprevBound⟩
    have hidxOption' : V[jprev.val]? = some (W.get k0) := by
      have hval : jprev.val = k0.val + 1 := by
        dsimp only [jprev]
        exact hidxNum
      rw [hval]
      simpa only [List.get_eq_getElem] using hidxOption
    have hidxGet : V.get jprev = W.get k0 := by
      rw [List.getElem?_eq_getElem jprev.isLt] at hidxOption'
      exact Option.some.inj hidxOption'
    rcases List.getElem?_eq_some_iff.mp hindex with ⟨hindexLt, hindexGet⟩
    let indexFin : Fin R.length := ⟨b + 1 + k0.val, hindexLt⟩
    have hindexGet' : R.get indexFin = W.get k0 := by
      simpa only [List.get_eq_getElem] using hindexGet
    have hqIndex : q = b + 1 + k0.val := by dsimp only [q, k0]; omega
    have hqFinEq : qFin = indexFin := by
      apply Fin.ext
      exact hqIndex
    have hqGet : R.get qFin = W.get k0 := by
      rw [hqFinEq]
      exact hindexGet'
    have hqRecord : R[q] = W.get k0 := by
      simpa only [List.get_eq_getElem] using hqGet
    have hprevInputGet : (V.get jprev).input.state.followers i =
        .ordinary statePred memoryPred := by
      rw [hidxGet]
      exact hinputPred
    have hprevInputV : (V[j0 - 1]'hprevBound).input.state.followers i =
        .ordinary statePred memoryPred := by
      change (V.get jprev).input.state.followers i = .ordinary statePred memoryPred
      exact hprevInputGet
    have hstatusPred := hbeforeUnoccupied (j0 - 1) (by omega) (by omega)
      statePred memoryPred hprevInputV
    have hprevInput : R[q].input.state.followers i = .ordinary statePred memoryPred := by
      have hprevInputGet : (R.get qFin).input.state.followers i =
          .ordinary statePred memoryPred := by
        rw [hqGet]
        exact hinputPred
      simpa only [List.get_eq_getElem] using hprevInputGet
    have hselectedTail :
        ∃ selected : Selection R[q].input,
          R[q].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = PD := by
      generalize hactual : W.get k0 = actual at *
      cases hqRecord
      exact ⟨selectedPred, hselectionPred, hpayloadPred⟩
    exact ⟨⟨statePred, memoryPred, hprevInput, hstatusPred⟩, hselectedTail⟩

/-- The first actually occupied input on this corrected LIVE slice has its
literal numerical seed from the preceding accepted native DOWN on the same
payload. The seed is selected internally by the actual occupation status. -/
theorem actual_first_corrected_native_down_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    let V := (R.drop b).take (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      ReferenceCollectionPhaseHistory.laterChosen birth.input = true ∧
      ∀ i : Fin (p.m - 1),
        (∀ j0 : ℕ, 1 ≤ j0 → ∀ (hj0 : j0 < V.length) state memory,
          (V[j0]'hj0).input.state.followers i = .ordinary state memory →
          state.status = .unoccupied) ∨
        ∃ (j0 : ℕ) (state0 : ReferencePrelaunchFollower.State p rate.eta)
          (memory0 : ActiveFollowerLifecycle.LocalMemory p),
          1 ≤ j0 ∧ ∃ (hj0 : j0 < V.length),
          (V[j0]'hj0).input.state.followers i = .ordinary state0 memory0 ∧
          state0.status ≠ .unoccupied ∧
          state0.lastDown = some (P.downRecord i) ∧
          (∀ j, 1 ≤ j → ∀ (hlt : j < j0) state memory,
            (V[j]'(Nat.lt_trans hlt hj0)).input.state.followers i = .ordinary state memory →
            state.status = .unoccupied) ∧
          ∃ (word : List (Bool × ℕ)) (prev : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate))
            (logged after : ReferencePrelaunchFollower.State p rate.eta)
            (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
            (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
            (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
            (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ)
            (lastService : ℕ) (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
            R[b + j0 - 1]? = some prev ∧
            (prev.output.followers i).downInput = some logged ∧
            (prev.output.followers i).down = some cut ∧
            cut.outcome = .accepted logged after raw M scan registers lastService ∧
            M = P.downRecord i ∧
            scan.endpoint - (P.sigma.val + 1) = j0 ∧
            (V.take (scan.endpoint - (P.sigma.val + 1))).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
            registers = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
            after.lastDown = some (P.downRecord i) ∧ after.S = registers.1 ∧
            after.delta = lastService ∧ after.backlog = registers.2 ∧
            prev.output.next.followers i = .ordinary after nextMemory ∧
            state0 = after ∧
            state0.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
            state0.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let W := liveTail rate rewards C_star C_h source
  let V := (R.drop b).take (1 + W.length)
  obtain ⟨L, c, birthD, PD, hL, hc, hprefix, hlen, hbirthD, hbornD,
    hSigmaD, hqueues, hdownQueues, hVD, hNbound, htotal, hcollection,
    hdiagnostics⟩ :=
    ReferenceFirstCorrectedNativeDownCalendarReplay.firstCell_native_down_calendar_replay
      rate rewards C_star C_h u t source hz
  obtain ⟨Lsrc, csrc, birthSrc, Psrc, base, hLsrc, hcsrc, _hprefixSrc,
    hlenSrc, hbirthSrc, _hrecordSrc, htimeSrc, _hrowsSrc, _hselectedSrc,
    _hrewardsSrc, _hrecordDataSrc, hchosenSrc, _henabledSrc, hbornSrc,
    hSigmaSrc, _hrateSrc, _hrewardSrc, _hqueuesSrc, _hbaseSrc, _hterminalSrc,
    _hterminalWordSrc, _htailSrc⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t source hz
  have hL_eq : L = Lsrc := Option.some.inj (hL.symm.trans hLsrc)
  have hc_eq : c = csrc := Option.some.inj (hc.symm.trans hcsrc)
  have hbirth_eq : birthD = birthSrc := Option.some.inj (hbirthD.symm.trans hbirthSrc)
  subst birthSrc
  have hbornD' : ReferenceAssignmentPayloadPersistence.InstallationBirth birthD PD := hbornD
  have hP_eq : PD = Psrc :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birthD PD Psrc hbornD' hbornSrc
  subst Psrc
  have hb : b < R.length := (List.getElem?_eq_some_iff.mp hbirthD).1
  have hbornTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    birthD PD hbornD
  let bFin : Fin R.length := ⟨b, hb⟩
  obtain ⟨_, _, hWeq⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨b, hb⟩
  have hBirthTime : birthD.input.time = t := htimeSrc
  have hSigma : PD.sigma = t := hSigmaD
  have htailEq := continuing_prefix_eq_liveTail rate rewards C_star C_h source
  have hprefix_eq :
      (R.drop b).take (1 + W.length) = birthD :: W := by
    simpa only [R, b, W, htailEq] using hVD
  have hVshape : V = birthD :: W := by
    dsimp only [V]
    exact hprefix_eq
  have hVslice : (R.drop b).take (1 + W.length) = V := rfl
  have hVlen : V.length = 1 + W.length := by
    simp only [hVshape, List.length_cons, Nat.add_comm]
  have hN : b + (1 + W.length) ≤ R.length := by
    simpa only [R, b, W, htailEq] using hNbound
  refine ⟨birthD, PD, hbirthD, hbornD, hSigma, hchosenSrc, ?_⟩
  intro i
  classical
  let occupied (j : ℕ) : Prop :=
    1 ≤ j ∧ ∃ hj : j < V.length,
      ∃ state memory, (V[j]'hj).input.state.followers i = .ordinary state memory ∧
        state.status ≠ .unoccupied
  by_cases hoccExists : ∃ j, occupied j
  · let j0 := Nat.find hoccExists
    have hfirst := Nat.find_spec hoccExists
    rcases hfirst with ⟨hpos0, hj0, state0, memory0, hinput0, hoccupied0⟩
    have hmin : ∀ j, occupied j → j0 ≤ j := fun j hj => Nat.find_min' hoccExists hj
    have hj0Bound : j0 < V.length := by
      change Nat.find hoccExists < V.length
      exact hj0
    have hbeforeUnoccupied : ∀ j, 1 ≤ j → ∀ (hlt : j < j0),
        ∀ state memory,
          (V[j]'(Nat.lt_trans hlt hj0Bound)).input.state.followers i = .ordinary state memory →
          state.status = .unoccupied := by
      intro j hj hlt state memory hinput
      by_contra hnot
      have hoccupied : state.status ≠ .unoccupied := by
        intro heq
        exact hnot heq
      have hjV : j < V.length := Nat.lt_trans hlt hj0Bound
      have hmember : occupied j := ⟨hj, ⟨hjV, state, memory, hinput, hoccupied⟩⟩
      exact (Nat.not_le_of_gt hlt) (hmin j hmember)
    let q := b + j0 - 1
    have hjN : j0 < (1 + W.length) := by
      rw [hVlen] at hj0Bound
      omega
    have hq_lt : q + 1 < R.length := by
      have h := hN
      dsimp only [q]
      omega
    have hprevSlice := source_slice_getElem? R V b (1 + W.length) hN hVslice
      ⟨j0 - 1, by omega⟩
    have hcurSlice := source_slice_getElem? R V b (1 + W.length) hN hVslice
      ⟨j0, by omega⟩
    have hqEq : b + (j0 - 1) = q := by dsimp only [q]; omega
    have hqNextEq : b + j0 = q + 1 := by dsimp only [q]; omega
    have hprevRecord : R[q]? = some V[j0 - 1] := by
      simpa only [hqEq] using hprevSlice
    have hcurRecord : R[q + 1]? = some V[j0] := by
      simpa only [hqNextEq] using hcurSlice
    have hqFinLt : q < R.length := by omega
    let qFin : Fin R.length := ⟨q, hqFinLt⟩
    have hqAt : R[q] = V[j0 - 1] := by
      exact (List.getElem?_eq_some_iff.mp hprevRecord).2
    have hqNextAt : R[q + 1] = V[j0] :=
      (List.getElem?_eq_some_iff.mp hcurRecord).2
    have hadj := complete_adjacent rate source rewards C_star C_h q hq_lt
    have hAdj : (R[q + 1]'hq_lt).input.state = (R[q]'hqFinLt).output.next := by
      simpa only [R, List.get_eq_getElem] using hadj.1
    have hnextInput : R[q].output.next.followers i = .ordinary state0 memory0 := by
      have hstate := congrArg (fun s => s.followers i) hAdj
      rw [hqAt, hqNextAt] at hstate
      have hstate' := hstate.symm.trans hinput0
      rw [← hqAt] at hstate'
      exact hstate'
    have hprevAndSelected :
        (∃ state memory,
          R[q].input.state.followers i = .ordinary state memory ∧
            state.status = .unoccupied) ∧
        (∃ selected : Selection R[q].input,
          R[q].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = PD) :=
      first_occupied_predecessor_input rate rewards C_star C_h source birthD PD
        hbirthD hchosenSrc hbornD hVshape hN i j0 hpos0 hj0 hbeforeUnoccupied hqFinLt
    obtain ⟨⟨statePred, memoryPred, hinputPred, hstatusPred⟩,
      ⟨selectedPred, hselectionPred, hpayloadPred⟩⟩ := hprevAndSelected
    have hqFinBound : b ≤ q := by
      change b ≤ b + j0 - 1
      have hsum : b + 1 ≤ b + j0 := Nat.add_le_add_left hpos0 b
      exact Nat.le_sub_of_add_le hsum
    have hdiag := hdiagnostics ⟨q, hqFinLt⟩ hqFinBound i
    have hdiagAccepted := hdiag.2.2 selectedPred hselectionPred
    rw [hpayloadPred] at hdiagAccepted
    simp only at hdiagAccepted
    have hacceptedRecord :
        ∃ logged cut after raw M scan registers lastService,
          (R[q].output.followers i).downInput = some logged ∧
          (R[q].output.followers i).down = some cut ∧
          cut.outcome =
            .accepted logged after raw M scan registers lastService := by
      have hnext' : R[q].output.next.followers i = .ordinary state0 memory0 := hnextInput
      have hchron := ReferenceFollowerReplyChronology.record_ordinary_chronology
        R[q] i state0 memory0 hnext'
      rcases hchron with ⟨before, memory, hstartState, hmono, hkeep, happly⟩
      have hbeforeEq := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hstartState.symm.trans hinputPred)).1
      subst before
      have hstartsNe :
          ReferencePrelaunchFollower.acceptedStart statePred ≠
            ReferencePrelaunchFollower.acceptedStart state0 := by
        intro heq
        have hkept := hkeep hstatusPred heq
        exact hoccupied0 hkept.1
      rcases happly hstartsNe with
        ⟨logged, cut, after, raw, M, scan, registers, lastService,
          hdownInput, hdownCut, haccepted, _hsigma⟩
      exact ⟨logged, cut, after, raw, M, scan, registers, lastService,
        hdownInput, hdownCut, haccepted⟩
    rcases hacceptedRecord with
      ⟨logged, cut, after, raw, M, scan, registers, lastService,
        hdownInput, hdownCut, haccepted⟩
    have hsourceData := hdiagAccepted logged logged after cut raw M scan
      registers lastService hdownInput hdownCut haccepted
    rcases hsourceData with ⟨_hbefore, _hnoRaw, word, hmapWord, hM, hscan,
      _hvpos, _hvbound, _hlate, _hseedBirth, _hnoReset, _hrecords, _hchecked,
      hregisters, _hprefix, _hinterval, _hserviceWord, hlastDown, hS, hdelta,
      hbacklog, nextMemory, hnextAfter⟩
    have hafterState : state0 = after := by
      have hnextEq := hnextInput.symm.trans hnextAfter
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hnextEq).1
    have hendpoint : scan.endpoint = R[q].input.time.val + 2 :=
      accepted_occupied_endpoint R[q] i logged after cut raw M scan registers lastService
        hdownInput hdownCut haccepted (by simpa only [hafterState] using hoccupied0)
    have hscanAt : scan.endpoint =
        min (FollowerCutoffScan.firstCutoff p rate.eta.val PD.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))))
          (R[q].input.time.val + 2) := hscan
    have hscanCurrent : scan.endpoint = R[q].input.time.val + 2 := hendpoint
    have hv : scan.endpoint - (PD.sigma.val + 1) = j0 := by
      have hstartEq : ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + b = t.val :=
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
          rate rewards C_star C_h u t source hz
      have hqTime : R[q].input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + q :=
        ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨q, hqFinLt⟩
      rw [hSigma]
      exact relative_live_endpoint _ b j0 t.val _ _ hpos0 hstartEq hqTime hscanCurrent
    have hmapWord' : (V.take (scan.endpoint - (PD.sigma.val + 1))).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? PD i) = some word := by
      simpa only [htailEq] using hmapWord
    have hregistersReplay : registers =
        QueueReplay.replay (4 * rate.n) (0, (PD.downRecord i).val.q) word := by
      simpa only [hM] using hregisters
    have hstateReplay : (state0.S, state0.backlog) =
        QueueReplay.replay (4 * rate.n) (0, (PD.downRecord i).val.q) word := by
      rw [hafterState, hS, hbacklog, hregistersReplay]
    have hstateLastDown : state0.lastDown = some (PD.downRecord i) := by
      rw [hafterState]
      exact hlastDown
    refine Or.inr ⟨j0, state0, memory0, hpos0,
      ⟨hj0, hinput0, hoccupied0, hstateLastDown, hbeforeUnoccupied, ?_⟩⟩
    refine ⟨word, R[q], logged, after, cut, raw, M, scan, registers,
      lastService, nextMemory, ?_, hdownInput, hdownCut, haccepted, ?_, hv,
      hmapWord', hregistersReplay, hlastDown, hS, hdelta, hbacklog,
      hnextAfter, hafterState, ?_, ?_⟩
    · exact List.getElem?_eq_getElem hqFinLt
    · exact hM
    · rw [hafterState]
      simpa only [hregistersReplay] using hS
    · rw [hafterState]
      simpa only [hregistersReplay] using hbacklog
  · left
    intro j hj hjvalid state memory hinput
    by_contra hnot
    have hoccupied : state.status ≠ .unoccupied := by
      intro heq
      exact hnot heq
    have hmember : occupied j := ⟨hj, ⟨hjvalid, state, memory, hinput, hoccupied⟩⟩
    exact hoccExists ⟨j, hmember⟩

private theorem actual_live_start_identity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[
      birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1)) :
    let W := liveTail rate rewards C_star C_h source
    ∀ j (_hpos : 1 ≤ j) (hj : j < (birth :: W).length) state memory,
      ((birth :: W)[j]).input.state.followers i = .ordinary state memory →
      ActiveFollowerLifecycle.startRound rate.eta ((birth :: W)[j]).input.time state memory =
        .ok (state, memory) ∧
      (((birth :: W)[j]).output.preparation.followers.followers i).configuration = .ordinary state memory := by
  intro W j hpos hj state memory hin
  have hk : j - 1 < W.length := by have hlen : (birth :: W).length = W.length + 1 := rfl; omega
  let k : Fin W.length := ⟨j - 1, hk⟩
  have hjk : j = k.val + 1 := by dsimp only [k]; omega
  have hr : (birth :: W)[j] = W.get k := by
    simp only [hjk, List.getElem_cons_succ, List.get_eq_getElem]
  obtain ⟨_hindex, selected, actual, mem, next, nextMemory, _hrows, _hselected,
    _hrewards, _hsel, _hpay, _hlive, hin', _hdomain, _hdown, hprep, _hout,
    _hfailure, _hpreserves, hdecision, _htoken, _hnextToken⟩ :=
    ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_first_corrected_actual_tail_boundary
      rate source rewards C_star C_h birth P hb hchosen hborn i k
  rw [← hr] at hin' hprep hdecision
  have heq := LocalConfiguration.ordinary.inj (hin'.symm.trans hin)
  rw [heq.1, heq.2] at hprep hdecision
  exact ⟨by simp [ActiveFollowerLifecycle.startRound, hdecision], hprep⟩

/-- Actual occupied LIVE storage. The local occupation selector is the only
branch premise; the numerical initialization is derived from native DOWN. -/
theorem actual_first_corrected_occupied_live_storage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ _hq : t.val + 1 < p.T,
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate) (B : List (RecordedQueueRun.RoundInput p.K)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧ c.enabled = true ∧
      ∃ hB : B.length = W.length,
        (R.drop b).take (1 + W.length) = birth :: W ∧
        let V := birth :: W
        let word := fun (i : Fin (p.m - 1)) (v : ℕ) =>
          ([c] ++ B.take (v - 1)).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
              (P.assignment.assigned i))
        (∀ i v, 1 ≤ v → v ≤ V.length →
          (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some (word i v)) ∧
        (∀ k : Fin W.length, (B[k.val]'(by omega)).enabled = true) ∧
        (∀ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          R[b + 1 + W.length]? = some r → ∀ i : Fin (p.m - 1),
          ∃ state memory,
            r.input.state.followers i = .ordinary state memory ∧
            ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
              .ok ({state with status := .unoccupied}, memory) ∧
            (r.output.preparation.followers.followers i).configuration =
              .ordinary {state with status := .unoccupied} memory) ∧
        ∀ (i : Fin (p.m - 1)) (j : ℕ) (_hpos : 1 ≤ j) (hj : j < V.length)
          (input : ReferencePrelaunchFollower.State p rate.eta)
          (inputMemory : ActiveFollowerLifecycle.LocalMemory p),
          (V[j]).input.state.followers i = .ordinary input inputMemory →
          input.status ≠ .unoccupied →
            let r := V[j]
            ∃ (selected : Selection r.input) (ho : preparedOrdinary r)
              (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p)
              (next : ReferencePrelaunchFollower.State p rate.eta)
              (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b + j]? = some r ∧
              r.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = P ∧
              CoordinatorLocalArmChoice.assignmentIsLive P selected.view.cutoff r.input.time ∧
              r.input.state.followers i = .ordinary state memory ∧
              (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              preparedStates r ho i = state ∧ preparedMemories r ho i = memory ∧
              state.status ≠ .unoccupied ∧ state.lastDown = some (P.downRecord i) ∧
              interruptionDecision rate.eta r.input.time state memory = .ok false ∧
              (state.S, state.backlog) =
                QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j) ∧
              (r.output.followers i).configuration = .ordinary next nextMemory ∧
              (r.output.followers i).failure = none ∧
              r.output.next.followers i = .ordinary next nextMemory ∧
              next.status ≠ .unoccupied ∧ next.lastDown = some (P.downRecord i) ∧
              next.buffer = state.buffer ∧
              (next.S, next.backlog) =
                QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i (j + 1)) ∧
              next.delta =
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i (j + 1))).1 -
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j)).1 ∧
              (∃ token, memory.lastProposalRead = some token ∧
                token.timestamp.val + 1 = r.input.time.val ∧
                token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  r.input.row token.timestamp) ∧
              (∃ token, nextMemory.lastProposalRead = some token ∧
                token.timestamp.val = r.input.time.val ∧
                token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  r.input.row token.timestamp) ∧
              (∀ hnext : j + 1 < V.length,
                (V[j + 1]).input.state.followers i = .ordinary next nextMemory ∧
                (V[j + 1]).input.time.val = r.input.time.val + 1) ∧
              (∀ hafter : b + j + 1 < R.length,
                (R.get ⟨b + j + 1, hafter⟩).input.state.followers i = .ordinary next nextMemory ∧
                (R.get ⟨b + j + 1, hafter⟩).input.time.val = r.input.time.val + 1) ∧
              let prep := ReferenceActivePhysicalStep.prepare r.input
              let f := prep.followers.followers i
              let y := prep.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let arrival := RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (B[j - 1]'(by
                  have hlen : V.length = W.length + 1 := rfl
                  rw [hB]
                  omega))
                (P.assignment.assigned i)
              ∃ serviced,
                ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
                  f.follower f.row f.activation f.time y (preparedStates r ho i) = .success serviced ∧
                serviced.arrival = arrival ∧
                serviced.service = min (4 * rate.n) (state.backlog + arrival) ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).result =
                    .ok serviced.output ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).downInput = none ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).down = none ∧
                DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time y
                  (preparedStates r ho i) (preparedMemories r ho i) serviced.output = .ok (next, nextMemory) ∧
                serviced.output.S = next.S ∧ serviced.output.backlog = next.backlog ∧
                serviced.output.delta = next.delta ∧ next.delta = serviced.service ∧
                (next.status = .released ↔ state.status = .released ∨
                  (state.status = .pending ∧ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                    y (P.downRecord i))) ∧
                (next.status = .pending ↔ state.status = .pending ∧
                  ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                    y (P.downRecord i)) := by
  classical
  intro hq
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let W := liveTail rate rewards C_star C_h source
  obtain ⟨c, birth, P, B, hb, hborn, hSigma, hc, hB, hdrop, hwords,
    henabled, hcutoff, hpropagate⟩ :=
    ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_occupied_live_prefix_from_actual_seed
      rate rewards C_star C_h u t source hz hq
  obtain ⟨birthS, PS, hbS, hbornS, _hSigmaS, hchosenS, hseeds⟩ :=
    actual_first_corrected_native_down_seed rate rewards C_star C_h u t source hz
  have hbirthEq : birthS = birth := Option.some.inj (hbS.symm.trans hb)
  subst birthS
  have hPEq : PS = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth PS P hbornS hborn
  subst PS
  rw [hdrop] at hseeds
  refine ⟨c, birth, P, B, hb, hborn, hSigma, hc, hB, hdrop, hwords,
    henabled, hcutoff, ?_⟩
  let V := birth :: W
  let word := fun (i : Fin (p.m - 1)) (v : ℕ) =>
    ([c] ++ B.take (v - 1)).map fun cell =>
      (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
        (P.assignment.assigned i))
  intro i j hpos hj input inputMemory hinput hoccupied
  rcases hseeds i with hnever | hfirst
  · exact False.elim (hoccupied (hnever j hpos hj input inputMemory hinput))
  · rcases hfirst with ⟨j0, state0, memory0, hpos0, hj0, hinput0, hoccupied0,
      _hlastDown0, hbefore, seedWord, prev, logged, after, cut, raw, M, scan,
      registers, lastService, nextMemory, _hprev, _hdownInput, _hdown, _haccepted,
      _hM, hv, hmapSeed, _hregisters, _hlastDown, _hS, _hdelta, _hbacklog,
      _hnext, _hstate, hscore0, hbacklog0⟩
    have hword0 := hwords i j0 hpos0 (Nat.le_of_lt hj0)
    rw [hv] at hmapSeed
    have hwordEq : seedWord = word i j0 := Option.some.inj (hmapSeed.symm.trans hword0)
    obtain ⟨_hstart0, _hprepare0⟩ := actual_live_start_identity
      rate rewards C_star C_h source birth P hb hchosenS hborn i j0 hpos0 hj0 state0 memory0 hinput0
    have hseed : (state0.S, state0.backlog) =
        QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j0) := by
      rw [hscore0, hbacklog0, hwordEq]
    have hle : j0 ≤ j := by
      apply le_of_not_gt
      intro hlt
      exact hoccupied (hbefore j hpos hlt input inputMemory hinput)
    -- Both numerical seed fields are produced by the actual native DOWN above.
    -- This is the application of accepted occupied preservation, on the same P/word.
    exact hpropagate i j0 hpos0 hj0 state0 memory0 hinput0 hoccupied0 hseed j hj hle

private theorem mapM_take_of_some {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) (n : ℕ) :
    (xs.take n).mapM f = some (ys.take n) := by
  induction xs generalizing ys n with
  | nil =>
      have hy : [] = ys := Option.some.inj h
      subst ys
      simp only [List.take_nil, List.mapM_nil, Option.pure_def]
  | cons x xs ih =>
      cases hx : f x with
      | none => simp only [List.mapM_cons, hx, Option.bind_eq_bind, Option.bind_none] at h; cases h
      | some y =>
          cases hs : xs.mapM f with
          | none =>
              simp only [List.mapM_cons, hx, hs, Option.bind_eq_bind,
                Option.bind_some, Option.bind_none] at h
              cases h
          | some rest =>
              have hy : y :: rest = ys := by
                simpa only [List.mapM_cons, hx, hs, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def, Option.some.injEq] using h
              subst ys
              cases n with
              | zero => simp only [List.take_zero, List.mapM_nil, Option.pure_def]
              | succ n =>
                  simp only [List.take_succ_cons, List.mapM_cons, hx, ih rest hs n,
                    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem previous_word {α β : Type} (f : α → Option β) (V : List α)
    (j : ℕ) (before after : List β)
    (hb : (V.take j).mapM f = some before)
    (ha : (V.take (j + 1)).mapM f = some after) : before = after.take j := by
  have ht := mapM_take_of_some f (V.take (j + 1)) after ha j
  rw [List.take_take, Nat.min_eq_left (Nat.le_succ j)] at ht
  exact Option.some.inj (hb.symm.trans ht)

private theorem occupied_output_accepted
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (before next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : r.input.state.followers i = .ordinary before memory)
    (hu : before.status = .unoccupied)
    (hout : r.output.next.followers i = .ordinary next nextMemory)
    (ho : next.status ≠ .unoccupied) :
    ∃ logged cut after raw M scan registers lastService,
      (r.output.followers i).downInput = some logged ∧
      (r.output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw M scan registers lastService := by
  obtain ⟨actual, actualMemory, hactual, _hmono, hkeep, happly⟩ :=
    ReferenceFollowerReplyChronology.record_ordinary_chronology r i next nextMemory hout
  have heq := (LocalConfiguration.ordinary.inj (hactual.symm.trans hin)).1
  subst actual
  have hne : ReferencePrelaunchFollower.acceptedStart before ≠
      ReferencePrelaunchFollower.acceptedStart next := by
    intro heq
    exact ho (hkeep hu heq).1
  obtain ⟨logged, cut, after, raw, M, scan, registers, lastService,
    hinput, hdown, haccepted, _hsigma⟩ := happly hne
  exact ⟨logged, cut, after, raw, M, scan, registers, lastService, hinput, hdown, haccepted⟩

private theorem actual_slice_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[
      birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1)) :
    let W := liveTail rate rewards C_star C_h source
    ∀ j (hj : j < (birth :: W).length),
      ∃ selected : Selection ((birth :: W)[j]).input,
        ((birth :: W)[j]).output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = P := by
  intro W j hj
  cases j with
  | zero => exact birth_selected_payload birth P hchosen hborn
  | succ k =>
      have hk : k < W.length := Nat.lt_of_succ_lt_succ hj
      obtain ⟨_hr, selected, state, memory, next, nextMemory,
        _hrows, _hselected, _hrewards, hs, hp, _rest⟩ :=
        ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_first_corrected_actual_tail_boundary
          rate source rewards C_star C_h birth P hb hchosen hborn i ⟨k, hk⟩
      exact ⟨selected, hs, hp⟩

/-- Numerical projection of actual occupied storage, including the empty and
terminal cases by exclusion of a nonexistent LIVE input. -/
private theorem occupied_live_numerical
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[
      birthIndex rate rewards C_star C_h source]? = some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P) :
    let V := birth :: liveTail rate rewards C_star C_h source
    ∀ (i : Fin (p.m - 1)) (j : ℕ) (_hpos : 1 ≤ j) (hj : j < V.length)
      (input : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (V[j]).input.state.followers i = .ordinary input memory →
      input.status ≠ .unoccupied →
      ∃ beforeWord afterWord next nextMemory,
        (V.take j).mapM (attributedArrival? P i) = some beforeWord ∧
        (V.take (j + 1)).mapM (attributedArrival? P i) = some afterWord ∧
        input.lastDown = some (P.downRecord i) ∧
        (input.S, input.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) beforeWord ∧
        ((V[j]).output.followers i).configuration = .ordinary next nextMemory ∧
        (V[j]).output.next.followers i = .ordinary next nextMemory ∧
        next.status ≠ .unoccupied ∧ next.lastDown = some (P.downRecord i) ∧
        (next.S, next.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) afterWord ∧
        next.delta = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) afterWord).1 -
          (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) beforeWord).1 := by
  classical
  intro V i j hpos hj input memory hin ho
  by_cases hq : t.val + 1 < p.T
  · obtain ⟨c, birthO, PO, B, hbO, hbornO, _hsigma, _hc, _hB, _hdrop, hwords,
      _henabled, _hcutoff, hstorage⟩ :=
      actual_first_corrected_occupied_live_storage rate rewards C_star C_h u t source hz hq
    have heq : birthO = birth := Option.some.inj (hbO.symm.trans hb)
    subst birthO
    have hPeq : PO = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth PO P hbornO hborn
    subst PO
    obtain ⟨selected, hordinary, state, mem, next, nextMemory, _hr, _hsel, _hpay,
      _hlive, hin', _hprep, _hstates, _hmem, _hocc, hld, _hdecision, hreplay,
      hout, _hfailure, hnext, hnextOcc, hnextDown, _hbuffer, hnextReplay,
      hdelta, _htoken, _hnextToken, _hcarry, _hcarryR, _hservice⟩ :=
      hstorage i j hpos hj input memory hin ho
    have heq := (LocalConfiguration.ordinary.inj (hin'.symm.trans hin)).1
    rw [heq] at hld hreplay
    exact ⟨_, _, next, nextMemory, hwords i j hpos (Nat.le_of_lt hj),
      hwords i (j + 1) (Nat.succ_pos j) hj, hld, hreplay, hout, hnext,
      hnextOcc, hnextDown, hnextReplay, hdelta⟩
  · have hterminal : t.val + 1 = p.T := by have ht := t.isLt; omega
    obtain ⟨birthT, PT, hbT, _hbornT, _hend, hW, _hlen, _hnone⟩ :=
      ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_first_corrected_terminal_no_live_boundary
        rate rewards C_star C_h u t source hz hterminal
    change j < (birth :: liveTail rate rewards C_star C_h source).length at hj
    rw [hW] at hj
    simp only [List.length_cons, List.length_nil] at hj
    omega

private theorem output_relative_endpoint (start b j sigma date endpoint : ℕ)
    (hbirth : start + b = sigma) (hdate : date = start + (b + j))
    (hend : endpoint = date + 2) : endpoint - (sigma + 1) = j + 1 := by
  omega

/-- Actual native follower storage on the entire first corrected assignment.
Every word is the literal attributed `mapM` on the same source slice. Occupied
outputs include both online service and a current native DOWN acceptance;
unoccupied outputs are not assigned the current word. -/
theorem actual_first_corrected_native_follower_storage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    let V := (R.drop b).take (1 + W.length)
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate) (base : Fin (p.m - 1) → ℕ),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t source = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t source = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) source = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a, P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i, base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length (P.assignment.assigned i)).1 ∧
        (P.downRecord i).val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length (P.assignment.assigned i)).2) ∧
      V = birth :: W ∧ b + (1 + W.length) ≤ R.length ∧
      (t.val + 1 = p.T → b + 1 = R.length ∧ W = [] ∧ V.length = 1) ∧
      ∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length),
        let r := V[j]
        ∃ input memory choice next nextMemory,
          R[b + j]? = some r ∧
          r.input.state.followers i = .ordinary input memory ∧
          ActiveFollowerLifecycle.startRound rate.eta r.input.time input memory = .ok (choice, memory) ∧
          (r.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
          (r.output.followers i).configuration = .ordinary next nextMemory ∧
          (r.output.followers i).failure = none ∧
          r.output.next.followers i = .ordinary next nextMemory ∧
          (j = 0 → input.status = .unoccupied) ∧
          (1 ≤ j → input.status ≠ .unoccupied → ∃ word,
            (V.take j).mapM (attributedArrival? P i) = some word ∧
            input.lastDown = some (P.downRecord i) ∧
            (input.S, input.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word) ∧
          (next.status ≠ .unoccupied → ∃ word,
            (V.take (j + 1)).mapM (attributedArrival? P i) = some word ∧
            next.lastDown = some (P.downRecord i) ∧
            (next.S, next.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
            next.delta = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
              (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take j)).1) ∧
          (∀ hnext : j + 1 < V.length,
            (V[j + 1]).input.state.followers i = .ordinary next nextMemory ∧
            (V[j + 1]).input.time.val = r.input.time.val + 1) := by
  classical
  intro R b W V
  obtain ⟨L, c, birth, P, base, hL, hc, hprefix, hlen, hb, _hrecord, _htime,
    _hrows, _hselected, _hrewards, _hdata, hchosen, _henabled, hborn, hSigma,
    _hrate, _hreward, hqueues, hbase, hterm, _htermWord, _hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t source hz
  obtain ⟨LD, cD, birthD, PD, hLD, hcD, _hprefD, _hlenD, hbD, hbornD,
    _hsigmaD, _hqueuesD, _hdownQueuesD, hVD, hND, _htotalD, _hcollectionD, hdiagnostics⟩ :=
    ReferenceFirstCorrectedNativeDownCalendarReplay.firstCell_native_down_calendar_replay
      rate rewards C_star C_h u t source hz
  have hLEq : LD = L := Option.some.inj (hLD.symm.trans hL)
  have hcEq : cD = c := Option.some.inj (hcD.symm.trans hc)
  subst LD cD
  have hbirthEq : birthD = birth := Option.some.inj (hbD.symm.trans hb)
  subst birthD
  have hPEq : PD = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth PD P hbornD hborn
  subst PD
  have htailEq := continuing_prefix_eq_liveTail rate rewards C_star C_h source
  simp only [htailEq] at hVD hND hdiagnostics
  have hshape : V = birth :: W := hVD
  have hN : b + (1 + W.length) ≤ R.length := hND
  have hVlen : V.length = 1 + W.length := by simp only [hshape, List.length_cons, Nat.add_comm]
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbGet : R[b] = birth := (List.getElem?_eq_some_iff.mp hb).2
  have hbornAt : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b] P := by
    rw [hbGet]
    exact hborn
  have hbirthStatus : ∀ i, ∃ seed memory,
      birth.input.state.followers i = .ordinary seed memory ∧ seed.status = .unoccupied := by
    intro i
    obtain ⟨seed, choice, memory, hin, _hdomain, hu, _hstart, _hchoice,
      _hchoiceStatus, _hvalid, _hpair, _htimes⟩ :=
      ReferenceCompleteFollowerRetainedDownRecovery.complete_installation_carried_buffer_seed
        rewards C_star C_h source ⟨b, hbLt⟩ P hbornAt i
    rw [hbGet] at hin
    exact ⟨seed, memory, hin, hu⟩
  refine ⟨L, c, birth, P, base, hL, hc, hprefix, hlen, hb, hborn, hSigma,
    hqueues, hbase, hshape, hN, ?_, ?_⟩
  · intro hterminal
    obtain ⟨_birthT, _PT, _hbT, _hbornT, _hend, hW, _hlenT, _hnone⟩ :=
      ReferenceFirstCorrectedOccupiedCalendarPreservation.internal_first_corrected_terminal_no_live_boundary
        rate rewards C_star C_h u t source hz hterminal
    have hW' : W = [] := hW
    exact ⟨hterm hterminal, hW, by rw [hshape, hW']; rfl⟩
  · intro i j hj
    let r := V[j]
    have hjShape : j < (birth :: W).length := by simpa only [hshape] using hj
    have hrShape : r = (birth :: W)[j] := by
      have hh := congrArg (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)) => xs[j]?) hshape
      rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjShape] at hh
      exact Option.some.inj hh
    have hslice := source_slice_getElem? R V b (1 + W.length) hN rfl ⟨j, hj⟩
    have hglobal : b + j < R.length := (List.getElem?_eq_some_iff.mp hslice).1
    have hR : R[b + j] = r := (List.getElem?_eq_some_iff.mp hslice).2
    have hphysical := ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_preservation
      (rate := rate) rewards C_star C_h source ⟨b + j, hglobal⟩ i
    rw [hR] at hphysical
    obtain ⟨input, memory, choice, next, nextMemory, hin, _hinputDomain, hstart, hchoice, _hchoiceDomain,
      _hoperationDomain, _hnextDomain, hout, hfailure, hnext⟩ := hphysical
    have hbirthInput : j = 0 → input.status = .unoccupied := by
      intro hjzero
      obtain ⟨seed, seedMemory, hseed, hstatus⟩ := hbirthStatus i
      have hinBirth : birth.input.state.followers i = .ordinary input memory := by
        simpa only [r, hjzero, hshape, List.getElem_cons_zero] using hin
      have heq := (LocalConfiguration.ordinary.inj (hseed.symm.trans hinBirth)).1
      simpa only [heq] using hstatus
    have hinputNumerical : 1 ≤ j → input.status ≠ .unoccupied → ∃ word,
        (V.take j).mapM (attributedArrival? P i) = some word ∧
        input.lastDown = some (P.downRecord i) ∧
        (input.S, input.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word := by
      intro hpos hocc
      have hj' : j < (birth :: W).length := by simpa only [hshape] using hj
      have hin' : ((birth :: W)[j]).input.state.followers i = .ordinary input memory := by
        simpa only [r, hshape] using hin
      obtain ⟨wi, wo, _next, _nextMem, hwi, _hwo, hld, hreplay, _rest⟩ :=
        occupied_live_numerical rate rewards C_star C_h u t source hz birth P hb hborn
          i j hpos hj' input memory hin' hocc
      exact ⟨wi, by simpa only [hshape] using hwi, hld, hreplay⟩
    refine ⟨input, memory, choice, next, nextMemory, hslice, hin, hstart, hchoice, hout,
      hfailure, hnext, hbirthInput, hinputNumerical, ?_, ?_⟩
    · intro hnextOcc
      by_cases hu : input.status = .unoccupied
      · obtain ⟨logged, cut, after, raw, M, scan, registers, lastService,
          hdownInput, hdown, haccepted⟩ :=
          occupied_output_accepted r i input next memory nextMemory hin hu hnext hnextOcc
        have hdiag := hdiagnostics ⟨b + j, hglobal⟩ (Nat.le_add_right b j) i
        rw [hR] at hdiag
        have hselection := actual_slice_selection rate rewards C_star C_h source birth P hb
          hchosen hborn i j (by simpa only [hshape] using hj)
        rw [← hrShape] at hselection
        obtain ⟨selected, hsel, hpay⟩ := hselection
        have hcurrentDiagnostics := hdiag.2.2 selected hsel
        rw [hpay] at hcurrentDiagnostics
        simp only at hcurrentDiagnostics
        obtain ⟨_hbefore, _hnoRaw, word, hword, _hM, _hscan, _hvpos, _hvbound,
          _hlate, _hseedBirth, _hnoReset, _hrecords, _hchecked, hregisters,
          _hprefix, _hinterval, hservice, hlastDown, hS, hdelta, hbacklog,
          afterMemory, hafterNext⟩ :=
          hcurrentDiagnostics logged logged after cut raw M scan registers lastService hdownInput hdown haccepted
        have hafterEq : after = next :=
          (LocalConfiguration.ordinary.inj (hafterNext.symm.trans hnext)).1
        have hendpoint : scan.endpoint = r.input.time.val + 2 :=
          accepted_occupied_endpoint r i logged after cut raw M scan registers lastService
            hdownInput hdown haccepted (by simpa only [hafterEq] using hnextOcc)
        have hstartEq : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b = t.val :=
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
            rate rewards C_star C_h u t source hz
        have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨b + j, hglobal⟩
        rw [hR] at htime
        have hv : scan.endpoint - (P.sigma.val + 1) = j + 1 := by
          rw [hSigma]
          exact output_relative_endpoint _ b j t.val _ _ hstartEq htime hendpoint
        rw [hv] at hword hservice
        refine ⟨word, hword, ?_, ?_, ?_⟩
        · simpa only [hafterEq] using hlastDown
        · rw [← hafterEq, hS, hbacklog, hregisters]
        · rw [← hafterEq, hdelta]
          simpa only [Nat.add_sub_cancel] using hservice
      · have hpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (fun heq => hu (hbirthInput heq))
        have hj' : j < (birth :: W).length := by simpa only [hshape] using hj
        have hin' : ((birth :: W)[j]).input.state.followers i = .ordinary input memory := by
          simpa only [r, hshape] using hin
        obtain ⟨wi, wo, nextO, memoryO, hwi, hwo, _hld, _hinReplay, _hout,
          hnextO, _hoccO, hldO, hreplayO, hdeltaO⟩ :=
          occupied_live_numerical rate rewards C_star C_h u t source hz birth P hb hborn
            i j hpos hj' input memory hin' hu
        have hnextEq : nextO = next :=
          (LocalConfiguration.ordinary.inj (hnextO.symm.trans (by rw [← hrShape]; exact hnext))).1
        have hprevious := previous_word (attributedArrival? P i) (birth :: W) j wi wo hwi hwo
        rw [hprevious, hnextEq] at hdeltaO
        exact ⟨wo, by simpa only [hshape] using hwo,
          by simpa only [hnextEq] using hldO,
          by simpa only [hnextEq] using hreplayO, hdeltaO⟩
    · intro hjnext
      have hsliceNext := source_slice_getElem? R V b (1 + W.length) hN rfl ⟨j + 1, hjnext⟩
      have hnextGlobal : b + j + 1 < R.length := by
        have h := (List.getElem?_eq_some_iff.mp hsliceNext).1
        simpa only [Nat.add_assoc] using h
      have hadj := complete_adjacent rate source rewards C_star C_h (b + j) hnextGlobal
      have hRnext : R[b + j + 1] = V[j + 1] := by
        simpa only [Nat.add_assoc] using (List.getElem?_eq_some_iff.mp hsliceNext).2
      simp only [List.get_eq_getElem] at hadj
      rw [hR, hRnext] at hadj
      exact ⟨(congrArg (fun s => s.followers i) hadj.1).trans hnext, hadj.2⟩

/-- At the actual first cutoff START, the follower retains the final LIVE
output, including its current DOWN and last service. The replay word ends
before the cutoff collection record, so this is the follower queue at U. -/
theorem actual_first_corrected_first_cutoff_carry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    let V := (R.drop b).take (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (P : Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ V = birth :: W ∧
      ∀ (cutoff : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        R[b + 1 + W.length]? = some cutoff → ∀ i : Fin (p.m - 1),
        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p) (hlast : V.length - 1 < V.length),
          ((V[V.length - 1]).output.followers i).configuration = .ordinary endpoint memory ∧
          (V[V.length - 1]).output.next.followers i = .ordinary endpoint memory ∧
          cutoff.input.state.followers i = .ordinary endpoint memory ∧
          cutoff.input.time.val = (V[V.length - 1]).input.time.val + 1 ∧
          ActiveFollowerLifecycle.startRound rate.eta cutoff.input.time endpoint memory =
            .ok ({endpoint with status := .unoccupied}, memory) ∧
          (cutoff.output.preparation.followers.followers i).configuration =
            .ordinary {endpoint with status := .unoccupied} memory ∧
          (endpoint.status ≠ .unoccupied → ∃ word,
            V.mapM (attributedArrival? P i) = some word ∧
            endpoint.lastDown = some (P.downRecord i) ∧
            (endpoint.S, endpoint.backlog) = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
            endpoint.delta = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
              (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take (V.length - 1))).1) := by
  classical
  intro R b W V
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hprefix, _hlen, hb, hborn, _hsigma,
    _hqueues, _hbase, hshape, _hN, hterminal, hall⟩ :=
    actual_first_corrected_native_follower_storage rate rewards C_star C_h u t source hz
  have hshapeLocal : V = birth :: W := hshape
  have hVlen : V.length = 1 + W.length := by simp only [hshapeLocal, List.length_cons, Nat.add_comm]
  have hlast : V.length - 1 < V.length := by rw [hVlen]; omega
  have hlastValue : V.length - 1 = W.length := by rw [hVlen]; omega
  have hlastNext : V.length - 1 + 1 = V.length := Nat.sub_add_cancel (by rw [hVlen]; omega)
  refine ⟨birth, P, hb, hborn, hshape, ?_⟩
  intro cutoff hr i
  have hcutGlobal : b + 1 + W.length < R.length := (List.getElem?_eq_some_iff.mp hr).1
  have hq : t.val + 1 < p.T := by
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt t.isLt) with hq | ht
    · exact hq
    · obtain ⟨hend, hW, _hV⟩ := hterminal ht
      have hWlen : W.length = 0 := congrArg List.length hW
      rw [hWlen, Nat.add_zero, hend] at hcutGlobal
      exact False.elim ((Nat.lt_irrefl _) hcutGlobal)
  obtain ⟨_cO, birthO, PO, _B, hbO, hbornO, _hSigmaO, _hcO, _hB,
    _hdropO, _hwordsO, _henabledO, hcutoff, _hstorageO⟩ :=
    actual_first_corrected_occupied_live_storage rate rewards C_star C_h u t source hz hq
  have hbirthEq : birthO = birth := Option.some.inj (hbO.symm.trans hb)
  subst birthO
  have hPEq : PO = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth PO P hbornO hborn
  subst PO
  obtain ⟨input, inputMemory, choice, endpoint, memory, hrec, _hin, _hstart, _hprep,
    hout, _hfailure, hnext, _hbirthStatus, _hinputNumeric, houtputNumeric, _hcarry⟩ :=
    hall i (V.length - 1) hlast
  have hfinalGet : R[b + (V.length - 1)] = V[V.length - 1] :=
    (List.getElem?_eq_some_iff.mp hrec).2
  have hindexEq : b + (V.length - 1) + 1 = b + 1 + W.length := by
    rw [hlastValue, Nat.add_right_comm]
  have hcutGet : R[b + (V.length - 1) + 1] = cutoff := by
    simpa only [hindexEq] using (List.getElem?_eq_some_iff.mp hr).2
  have hadj := complete_adjacent rate source rewards C_star C_h (b + (V.length - 1))
    (by rw [hindexEq]; exact hcutGlobal)
  simp only [List.get_eq_getElem] at hadj
  rw [hfinalGet, hcutGet] at hadj
  have hcutInput : cutoff.input.state.followers i = .ordinary endpoint memory :=
    (congrArg (fun s => s.followers i) hadj.1).trans hnext
  obtain ⟨state, mem, hinput, hstart, hprepared⟩ := hcutoff cutoff hr i
  have heq := LocalConfiguration.ordinary.inj (hinput.symm.trans hcutInput)
  rw [heq.1, heq.2] at hstart hprepared
  refine ⟨endpoint, memory, hlast, hout, hnext, hcutInput, hadj.2, hstart, hprepared, ?_⟩
  intro hoccupied
  obtain ⟨word, hword, hlastDown, hreplay, hdelta⟩ := houtputNumeric hoccupied
  rw [hlastNext, List.take_length] at hword
  exact ⟨word, hword, hlastDown, hreplay, hdelta⟩

end Bandits.Support.ReferenceFirstCorrectedAssignedNativeFollowerPrefix

end
