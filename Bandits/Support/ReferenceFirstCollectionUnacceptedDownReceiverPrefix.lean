/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUnacceptedDownAwaitedPrefix
public import Bandits.Support.ReferenceFirstCollectionControlGeometry

import Lean.Elab.Tactic.Omega

/-!
# Fixed DOWN sender and checked receiver in the actual first collection

Internal pointwise results on the original corrected-launch physical run.
The current ordinary input and `lastDown = none` are local stage selectors.
Decoder outcomes are retained literally; no solver, delivery, bank replay,
waiting-time, probability, or manuscript closure is asserted.

Sources: `sources/zip4/manuscript/06_interruptions.tex:163-174,476-480`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionUnacceptedDownReceiverPrefix

open ConstructorDimensions
open ReferenceFirstCollectionReadyStream (startTime actualEpoch actualWindow)
open ReferencePrelaunchFollower (acceptedStart)
open ReferenceActivePhysicalStep (Selection)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (source : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (count : ℕ)
  (hcross : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
  (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)

local notation "s" => startTime (rate := rate) source rewards C_star C_h
local notation "E" => actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan
local notation "w" => List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan)))
local notation "B" => actualWindow (rate := rate) source rewards C_star C_h hcross count hspan

/-- The two public corrected-launch witnesses describe the same launch.
No private source array, selected row, reward, rate, or clock is replaced. -/
private theorem actual_records_eq_generated :
    (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s rfl count hspan).records = (E).records := by
  have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hactual : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h =
        some (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross) := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.some_get _).symm
  have hlaunch := Option.some.inj (hactual.symm.trans hgenerated)
  change (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s count hspan _).records =
    (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s count hspan _).records
  cases hlaunch
  rfl

variable (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)

include hshort in
private theorem actual_cutoff_prepared_domain (k : Fin (B).length) (hk : k.val = 0)
    (i : Fin (p.m - 1)) :
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) := B[k.val]
    ∃ choice memory,
      (record.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid choice := by
  classical
  have hrun := actual_records_eq_generated rate source rewards C_star C_h count hcross hspan
  have hshortG : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records).length < count := by
    simpa only [hrun] using hshort
  have halign := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort k
  have hlookup : (E).records[w + k.val]? = some B[k.val] := halign.1
  have hseed := ReferenceGeneratedFirstCutoffFollowerSeed.actual_first_cutoff_follower_seed
    rate source rewards C_star C_h hcross s rfl count hspan hshortG
  simp only [hrun] at hseed
  rcases hseed with ⟨r, q, base, _, _, _, dispatched, hstart, ledger, hinit,
    hledger, hdomain, hclock, hpending, hnoAssignment, selected,
    _hbranch, _hu, _huBound, _hfirstCutoff, hfollowers, _⟩
  obtain ⟨old, memory, choice, logged, diagnostic, recordPost, post,
    _hinput, _hunoccupied, _hoccupied, _holdDomain, _holdBuffer, _holdDecoder,
    _hpair, _hstamps, _hstart, hprepared, hchoice, hchoiceDomain, _⟩ := hfollowers i
  have hwIndex : w < (E).records.length := by
    have h := (List.getElem?_eq_some_iff.mp hlookup).1
    simpa only [hk, Nat.add_zero] using h
  have hcut : (E).records[w]'(by
      have h := (List.getElem?_eq_some_iff.mp hlookup).1
      simpa only [hk, Nat.add_zero] using h) = B[k.val] := by
    have h := (List.getElem?_eq_some_iff.mp hlookup).2
    simpa only [hk, Nat.add_zero] using h
  refine ⟨choice, memory, ?_, ?_, hchoiceDomain⟩
  · change (((E).records[w]'hwIndex).output.preparation.followers.followers i).configuration = _ at hprepared
    rw [hcut] at hprepared
    exact hprepared
  · rw [hchoice]

include hshort in
private theorem actual_continuing_prepared_domain (k : Fin (B).length) (hk : k.val ≠ 0)
    (i : Fin (p.m - 1)) :
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) := B[k.val]
    ∃ choice memory,
      (record.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid choice := by
  classical
  have hrun := actual_records_eq_generated rate source rewards C_star C_h count hcross hspan
  have hshortG : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records).length < count := by
    simpa only [hrun] using hshort
  have halign := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort k
  have hlookup : (E).records[w + k.val]? = some B[k.val] := halign.1
  have hprefix := ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
    rate source rewards C_star C_h hcross s rfl count hspan hshortG
  simp only [hrun] at hprefix
  rcases hprefix with ⟨r, q, base, _, _, _, dispatched, hstart, ledger, hinit,
    hledger, hdomain, hclock, hpending, hnoAssignment, selected, _hprepared,
    _hu, _huT, _huGrid, _hsigma, _hcutoff, _hscan, _hsuccessor,
    _hmoving, _hboundaries, hrecords⟩
  let tail := ((E).records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hlength : (B).length = tail.length + 1 := by
    dsimp only [actualWindow, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append]
    have hcount : (E).records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hfirst : (((E).records.drop w).take 1).length = 1 := by
      simp only [List.length_take, List.length_drop]
      omega
    rw [hfirst]
    exact Nat.add_comm 1 tail.length
  have hj : k.val - 1 < tail.length := by have := k.isLt; omega
  obtain ⟨choice, memory, _hinput, hstatus, hvalid, _hbuffer, _hdecoder,
    _hS, _hdelta, _hbacklog, _hmass, _hstamps, _hnodup, _hquantized,
    _hpair, _hcalendar, _hpending, _hcompleted, _hlast, _hstart,
    hprepared, _⟩ := hrecords (k.val - 1) hj i
  have hindex : w + 1 + (k.val - 1) = w + k.val := by omega
  have hbound : w + 1 + (k.val - 1) < (E).records.length := by
    rw [hindex]
    exact (List.getElem?_eq_some_iff.mp hlookup).1
  have hrecord : (E).records[w + 1 + (k.val - 1)]'hbound = B[k.val] := by
    simpa only [hindex] using (List.getElem?_eq_some_iff.mp hlookup).2
  change (((E).records[w + 1 + (k.val - 1)]'hbound).output.preparation.followers.followers i).configuration =
    _ at hprepared
  rw [hrecord] at hprepared
  exact ⟨choice, memory, hprepared, hstatus, hvalid⟩

include hshort in
private theorem actual_collection_prepared_domain (k : Fin (B).length)
    (i : Fin (p.m - 1)) :
    let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) := B[k.val]
    ∃ choice memory,
      (record.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid choice := by
  by_cases hk : k.val = 0
  · exact actual_cutoff_prepared_domain rate source rewards C_star C_h count hcross hspan hshort k hk i
  · exact actual_continuing_prepared_domain rate source rewards C_star C_h count hcross hspan hshort k hk i

private theorem lastDown_none_of_start_zero
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstart : acceptedStart state = 0) : state.lastDown = none := by
  cases hlast : state.lastDown with
  | none => rfl
  | some message =>
      have hpositive := message.property.1
      simp only [acceptedStart, hlast] at hstart
      omega

/-- Backward chronology reaches every earlier actual input, including the
current input. This says nothing about the output after the current call. -/
private theorem earlier_unaccepted_inputs
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (n : Fin out.ell) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hfi : (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
      .ordinary before memory)
    (hnone : before.lastDown = none)
    (k : Fin (n.val + 1)) :
    ∃ prior priorMemory,
      (out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
        (Nat.lt_of_lt_of_le n.isLt out.withinWindow))).input.state.followers i =
        .ordinary prior priorMemory ∧ prior.lastDown = none := by
  have hnWindow := Nat.lt_of_lt_of_le n.isLt out.withinWindow
  have hkWindow := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) hnWindow
  have hnLookup := (out.alignment ⟨n.val, hnWindow⟩).1
  have hkLookup := (out.alignment ⟨k.val, hkWindow⟩).1
  have hnIndex := (List.getElem?_eq_some_iff.mp hnLookup).1
  have hnRecord := (List.getElem?_eq_some_iff.mp hnLookup).2
  have hkRecord := (List.getElem?_eq_some_iff.mp hkLookup).2
  have hcurrent : (E).records[w + n.val].input.state.followers i = .ordinary before memory := by
    rw [hnRecord]
    exact hfi
  by_cases heq : k.val = n.val
  · exact ⟨before, memory, by simpa only [heq] using hfi, hnone⟩
  · have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
      (E).connected (w + n.val) hnIndex
    have hlength : ((E).records.take (w + n.val)).length = w + n.val := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hnIndex)]
    have hkTake : w + k.val < ((E).records.take (w + n.val)).length := by
      rw [hlength]
      exact Nat.add_lt_add_left (by omega) w
    obtain ⟨next, nextMemory, hnext, hnextLe⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology hprefix i before memory
        hcurrent (w + k.val) hkTake
    have htake := List.getElem_take (xs := (E).records) (j := w + n.val)
      (i := w + k.val) (h := hkTake)
    rw [htake, hkRecord] at hnext
    obtain ⟨prior, priorMemory, hprior, hle, _, _⟩ :=
      ReferenceFollowerReplyChronology.record_ordinary_chronology out.window[k.val]
        i next nextMemory hnext
    have hzero : acceptedStart before = 0 := by simp only [acceptedStart, hnone]
    exact ⟨prior, priorMemory, hprior,
      lastDown_none_of_start_zero rate prior (by omega)⟩

/-- Identify the stream's payload with the actual payload-origin witness by
comparing the two LIVE configurations at the same indexed cutoff. -/
private theorem stream_payload_origin
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    out.payload.sigma.val = s ∧
    (∀ i, (out.payload.downRecord i).val.sigma = s + 1 ∧
      (out.payload.downRecord i).val.q = 0) ∧
    ∀ (k : Fin out.window.length) (selected : Selection out.window[k.val].input),
      out.window[k.val].output.preparation.coordinator.selection = some selected →
        selected.view.payload = out.payload := by
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases horigin.origin with
    ⟨cut, payload, birth, r, q, base, ⟨hcutIndex, hcut⟩, _, hlive, _, hpayload,
      hsigma, hqueues, _, _, _, _, _, _, hselection, _⟩
  obtain ⟨execution⟩ := out.cutoffExecution
  have hcutEq : cut = out.cutoff.cut := by
    rw [hcut]
    exact (List.getElem?_eq_some_iff.mp out.cutoff.cutIndex).2
  have hlive' : out.cutoff.cut.input.state.coordinator = .live r q base := by
    rw [← hcutEq]
    exact hlive
  have hr : r = execution.live := by
    have heq := hlive'.symm.trans execution.actualLive
    injection heq
  have hroot : payload = out.payload := by
    calc
      payload = r.payload := hpayload
      _ = execution.live.payload := congrArg CoordinatorLiveChoiceRecorderStep.Registers.payload hr
      _ = out.cutoff.payload := execution.payloadIsLive.symm
      _ = out.payload := out.payloadMatchesCutoff.symm
  refine ⟨hroot ▸ hsigma, ?_, ?_⟩
  · intro i
    constructor
    · rw [out.payload.downRecord_fields, ← hroot, hsigma]
    · rw [out.payload.downRecord_initialQueue, ← hroot]
      exact hqueues _
  · intro k selected hselected
    have hk : k.val < (B).length := by simpa only [out.windowIsActual] using k.isLt
    let kb : Fin (B).length := ⟨k.val, hk⟩
    have h := hselection kb out.window[k.val] (out.alignment k).1 selected hselected
    exact h.trans hroot

private theorem selection_of_cutoff_chosen
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ selected : Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r q base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected =>
          let checked : Selection x := {
            view := {
              payload := r.payload
              pendingAtChoice := dispatched.startResult.pending
              cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
              complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights }
            started := dispatched.startResult, pending_eq := rfl, cutoff_eq := rfl
            arm := selected.arm, choice_eq := selected.armChoice_eq }
          refine ⟨checked, ?_, hpending⟩
          simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt]
          rfl
      | _ => simp only [hcoord, Bool.false_eq_true] at hcut
  | _ => simp only [hcoord, Bool.false_eq_true] at hcut

/-- The actual origin's cutoff selector supplies the reset pending set. -/
private theorem cutoff_selection
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    ∃ selected : Selection out.cutoff.cut.input,
      out.cutoff.cut.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ := by
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases horigin.origin with
    ⟨cut, payload, birth, r, q, base, ⟨hindex, hcut⟩, _, _, hchosen, _⟩
  have heq : cut = out.cutoff.cut := by
    rw [hcut]
    exact (List.getElem?_eq_some_iff.mp out.cutoff.cutIndex).2
  rw [heq] at hchosen
  obtain ⟨selected, hselection, hpending⟩ := selection_of_cutoff_chosen rate out.cutoff.cut.input hchosen
  refine ⟨selected, ?_, hpending⟩
  rw [out.cutoff.cut.output_eq]
  exact hselection

private theorem continuing_selection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload ledger saved) :
    ∃ selected : Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      selected.view.payload = payload ∧ selected.view.pendingAtChoice = ledger.pending := by
  obtain ⟨cutoff, _, core, snap, hb, hs, hcoord, _⟩ :=
    ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
      x payload ledger saved hready
  let checked : Selection x := {
    view := {
      payload := payload
      pendingAtChoice := snap.clockStarted.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snap.clockStarted.clock.u
      complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput x payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)
        snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq }
    started := snap.clockStarted, pending_eq := rfl, cutoff_eq := rfl
    arm := snap.arm, choice_eq := by
      have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snap.clockStarted.clock.u =
          some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
        rw [snap.clockStarted_frame.1]
        change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff).u = _
        rfl
      rw [hcutoff]
      exact snap.armChoice_eq }
  refine ⟨checked, ?_, rfl, snap.clockStarted_frame.2.1⟩
  rw [hcoord]
  rfl

/-- Domains of the real PREPARE state imply an executed selected DOWN call.
The logged state equals the choice state on DOWN, without a reward test. The
actual tail may fail; both diagnostic options survive every tail branch. -/
private theorem selected_receiver_call
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time) :
    let own := record.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let cut := ReferenceDownReception.referenceDownCut p
      record.output.preparation.coordinator.downView i record.input.row record.input.time own rate choice
    ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
      record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
    (record.output.followers i).downInput = some choice ∧
    (record.output.followers i).down = some cut ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
    cut.rawComparison.isSome = true ∧
    cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
      p i record.input.row record.input.time own rate choice).2 ∧
    cut.filteredRaw = if cut.raw = cut.expectedWord then cut.raw else none := by
  classical
  intro own cut
  have hl : ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
      record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice := by
    rw [ReferenceActiveAffinePositiveTest.checkedLogging_eq_of_down _ _ _ _ _ _ hdown.1,
      ite_eq_left hvalid.2.1]
  have hr : ActiveFollowerDownAcceptance.registerInputDomain p rate choice := hvalid.1
  have hb : ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch := hvalid.2.2
  have hf : ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer := by
    refine ⟨?_, hvalid.2.1.2.1⟩
    intro saved hsaved
    obtain ⟨q, hq, hy⟩ := hvalid.2.1.2.2 saved hsaved
    exact ⟨(hvalid.2.1.1 saved hsaved).1, (hvalid.2.1.1 saved hsaved).2, ⟨q, by omega⟩, hy⟩
  have hoptions : (record.output.followers i).downInput = some choice ∧
      (record.output.followers i).down = some cut := by
    have halign := record.output.preparation.follower_alignment i
    have hrecorded : (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.output.preparation.followers.followers i).arm own choice).downInput = some choice ∧
      (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
        i record.input.row (record.input.state.activations i) record.input.time (record.input.active i)
        (record.output.preparation.followers.followers i).arm own choice).down = some cut := by
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl]
      exact ⟨trivial, rfl⟩
    have hd : record.output.followers i = ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i) own := by
      dsimp only [own]
      rw [record.output_eq]
      rfl
    rw [hd]
    simp only [ReferenceActivePhysicalStep.finishFollower, hprepared]
    simp only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    split
    · exact hrecorded
    · split <;> exact hrecorded
  refine ⟨hl, hoptions.1, hoptions.2, hr, hb, hf, ?_, ?_, ?_⟩
  all_goals
    dsimp only [cut]
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hdown,
      dite_eq_left hu, dite_eq_left hr, dite_eq_left hb, dite_eq_left hf]
    split <;> simp_all only [Option.isSome_some]

private theorem selected_receiver_fields
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hu : state.status = .unoccupied)
    (hr : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hb : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hf : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer) :
    let cut := ReferenceDownReception.referenceDownCut p view i row time own rate state
    cut.expectedWord = ReferenceDownReception.expectedDownFlatWord view i row time ∧
    cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
    (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time state cut.ordinaryParse) ∧
    cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
    (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected state
      { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate state).1 }
      cut.raw) := by
  classical
  dsimp only
  simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hdown,
    dite_eq_left hu, dite_eq_left hr, dite_eq_left hb, dite_eq_left hf]
  split
  · rename_i hmatch
    exact ⟨rfl, rfl, Iff.rfl, by simp only [hmatch, decide_true], fun h => (h hmatch).elim⟩
  · rename_i hmatch
    exact ⟨rfl, rfl, Iff.rfl, by simp only [hmatch, decide_false], fun _ => rfl⟩

/-- The complete executed outcome keeps the ordinary checked tail on a raw
match, including its genuine output failures. A mismatch changes only the
decoder batch. Neither alternative assumes a solver or recovery result. -/
private theorem selected_receiver_outcome
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hu : state.status = .unoccupied)
    (hr : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hb : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hf : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer) :
    let cut := ReferenceDownReception.referenceDownCut p view i row time own rate state
    cut.outcome = if cut.raw = cut.expectedWord then
      ActiveFollowerDownAcceptance.downTransition p i row time own rate state
    else .decodeOrParseRejected state
      { state with downBatch :=
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate state).1 }
      cut.raw := by
  classical
  intro cut
  have hfields := selected_receiver_fields rate view i row time own state hdown hu hr hb hf
  by_cases hmatch : cut.raw = cut.expectedWord
  · rw [ite_eq_left hmatch]
    apply ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
    change cut.rawComparison ≠ some false
    rw [hfields.2.2.2.1]
    change some (decide (cut.raw = cut.expectedWord)) ≠ some false
    rw [decide_eq_true hmatch]
    intro hfalse
    cases hfalse
  · rw [ite_eq_right hmatch]
    exact hfields.2.2.2.2 hmatch

/-- A literal encoded stored word parses as the original DOWN record. -/
theorem ordinaryParse_stored_down_word
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
        some (payload.downRecord i) := by
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  rw [Equiv.symm_apply_apply, payload.parseDown_downWord i]

/-- One internally produced dispatcher and one fixed original payload serve
all selected DOWN calls through the current input. Only the current ordinary
configuration and its unaccepted old word select the local stage. No premise
is imposed on the result of the current receiver or its recovery/finish. -/
theorem actual_collection_unaccepted_down_receiver_prefix :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let P0 := out.payload
      out.window = B ∧ P0.sigma.val = s ∧
      (∀ i, (P0.downRecord i).val.sigma = s + 1 ∧ (P0.downRecord i).val.q = 0) ∧
      ∀ (n : Fin out.ell) (hn : 0 < n.val)
        (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
          .ordinary before memory →
        before.lastDown = none →
        i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending ∧
        (∀ k : Fin n.val,
          ReferenceCollectionPhaseHistory.acceptedLabel
            (out.window[k.val]'(Nat.lt_of_lt_of_le (Nat.lt_trans k.isLt n.isLt)
              out.withinWindow)).input ≠ some i) ∧
        ∀ k : Fin (n.val + 1),
          let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
            out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
              (Nat.lt_of_lt_of_le n.isLt out.withinWindow))
          ∃ prior priorMemory,
            record.input.state.followers i = .ordinary prior priorMemory ∧ prior.lastDown = none ∧
            (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
              ∃ (selected : Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P0 ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                (record.output.preparation.followers.followers i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let cut := ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView i record.input.row record.input.time own rate choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
                (record.output.followers i).downInput = some choice ∧
                (record.output.followers i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i)) = some (P0.downRecord i) ∧
                acceptedStart choice = 0 ∧ (P0.downRecord i).val.sigma = s + 1 ∧
                (P0.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (P0.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) = 1)) := by
  classical
  obtain ⟨d, hpending⟩ :=
    ReferenceFirstCollectionUnacceptedDownAwaitedPrefix.actual_collection_unaccepted_down_pending
      rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  obtain ⟨hsigma, hrecords, hselections⟩ := stream_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort out
  refine ⟨d, out.windowIsActual, hsigma, hrecords, ?_⟩
  intro n hn i before memory hfi hnone
  obtain ⟨hp, hnoAccepted⟩ := hpending n hn i before memory hfi hnone
  refine ⟨hp, hnoAccepted, ?_⟩
  intro k record
  have hkN : k.val ≤ n.val := Nat.le_of_lt_succ k.isLt
  have hkWindow : k.val < out.window.length :=
    Nat.lt_of_le_of_lt hkN (Nat.lt_of_lt_of_le n.isLt out.withinWindow)
  let kw : Fin out.window.length := ⟨k.val, hkWindow⟩
  let ks : Fin out.ell := ⟨k.val, Nat.lt_of_le_of_lt hkN n.isLt⟩
  obtain ⟨prior, priorMemory, hprior, hpriorNone⟩ := earlier_unaccepted_inputs
    rate source rewards C_star C_h count hcross hspan hshort out n i before memory hfi hnone k
  refine ⟨prior, priorMemory, hprior, hpriorNone, ?_⟩
  intro hdown
  have hkB : k.val < (B).length := by simpa only [out.windowIsActual] using hkWindow
  let kb : Fin (B).length := ⟨k.val, hkB⟩
  obtain ⟨choice, choiceMemory, hc, hu, hv⟩ := actual_collection_prepared_domain
    rate source rewards C_star C_h count hcross hspan hshort kb i
  have hrecordB : B[k.val]'hkB = record := by
    change B[k.val]'hkB = out.window[k.val]'hkWindow
    simp only [out.windowIsActual]
  rw [hrecordB] at hc
  obtain ⟨old, oldMemory, hold, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice record i choice choiceMemory hc
  have holdEq : old = prior :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hold.symm.trans hprior)).1
  have hchoiceNone : choice.lastDown = none := by
    have hlast := congrArg Prod.fst hreply
    exact hlast.trans (holdEq ▸ hpriorNone)
  have hchoiceZero : acceptedStart choice = 0 := by simp only [acceptedStart, hchoiceNone]
  have hselected : ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = out.payload ∧ i ∈ selected.view.pendingAtChoice := by
    by_cases hz : k.val = 0
    · have hcut : record = out.cutoff.cut := by
        dsimp only [record]
        simpa only [hz] using out.cutoffIsHead
      obtain ⟨selected, hselection, hpendingReset⟩ := cutoff_selection
        rate source rewards C_star C_h count hcross hspan hshort out
      have hsource : ∃ selected : Selection record.input,
          record.output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = Finset.univ := by
        rw [hcut]
        exact ⟨selected, hselection, hpendingReset⟩
      obtain ⟨selected, hselection, hreset⟩ := hsource
      exact ⟨selected, hselection, hselections kw selected hselection,
        hreset ▸ Finset.mem_univ i⟩
    · have hpos : 0 < ks.val := by dsimp only [ks]; omega
      obtain ⟨j, r, incoming, cell, _hj, hr, _hf, hincoming⟩ := out.cell_at ks hpos
      have hrEq : r = record := (List.getElem?_eq_some_iff.mp hr).2.symm
      obtain ⟨selected, hselection, hpayload, hset⟩ := continuing_selection rate r.input
        out.payload incoming out.saved cell.readyInput
      have hsel : r.output.preparation.coordinator.selection = some selected := by
        rw [r.output_eq]
        exact hselection
      have hip : i ∈ incoming.pending := by
        rw [hincoming]
        exact (hpending ks hpos i prior priorMemory hprior hpriorNone).1
      have hmem : i ∈ selected.view.pendingAtChoice := hset ▸ hip
      subst r
      exact ⟨selected, hsel, hpayload, hmem⟩
  obtain ⟨selected, hselection, hpayload, hip⟩ := hselected
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i
      record.input.row record.input.time := ⟨hdown.1, hdown.2, hip⟩
  have hview : record.output.preparation.coordinator.downView = some selected.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselection, Option.map_some]
  have hexpected : ReferenceDownReception.expectedDownFlatWord
      record.output.preparation.coordinator.downView i record.input.row record.input.time =
      some (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) := by
    rw [hview, ← hpayload]
    exact selected.expected_down_word i hbranch
  have hsent : ReferenceActiveAffinePositiveTest.downSent record.input =
      some (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) := by
    unfold ReferenceActiveAffinePositiveTest.downSent
    rw [← record.output.preparation.coordinator_eq,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdown.2]
    exact hexpected
  obtain ⟨hl, hdi, hd, hreg, hbatch, hbuffer, hcall, hraw, hfiltered⟩ :=
    selected_receiver_call rate record i choice choiceMemory hc hu hv hdown
  have hfields := selected_receiver_fields rate record.output.preparation.coordinator.downView
    i record.input.row record.input.time
    (record.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    choice hdown hu hreg hbatch hbuffer
  have htime := (out.alignment kw).2
  change record.input.time.val + 1 = s + w + 1 + k.val at htime
  have hstartLE : (out.payload.downRecord i).val.sigma ≤ record.input.time.val + 1 := by
    rw [(hrecords i).1]
    omega
  have haccept : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
      (some (out.payload.downRecord i)) := by
    exact ⟨by rw [hchoiceZero, (hrecords i).1]; omega, hstartLE⟩
  refine ⟨selected, choice, choiceMemory, hselection, hpayload, hip, hsent, hc, hu,
    hchoiceNone, hv, hl, hdi, hd, hreg, hbatch, hbuffer,
    hfields.1.trans hexpected, hcall, hraw, hfiltered,
    hfields.2.1, hfields.2.2.1, hfields.2.2.2.1, hfields.2.2.2.2,
    selected_receiver_outcome rate _ _ _ _ _ _ hdown hu hreg hbatch hbuffer,
    ordinaryParse_stored_down_word rate out.payload i, hchoiceZero,
    (hrecords i).1, hstartLE, haccept, ?_⟩
  intro hpositive
  have hpositiveTest : ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_diagnostic,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdown.2]
    change (ReferenceActiveAffinePositiveTest.downDiagnosticCall
      ((ReferenceActivePhysicalStep.step record.input).followers i) &&
      decide (0 < ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) = true
    have hpreparation : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    rw [← hpreparation, ← record.output_eq]
    simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hd, hcall,
      hpositive, decide_true, Bool.true_and]
  exact ReferenceDownPhysicalHashRule.downPositive_sent_hash_one record.input
    (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) hsent hpositiveTest

end Bandits.Support.ReferenceFirstCollectionUnacceptedDownReceiverPrefix

end
