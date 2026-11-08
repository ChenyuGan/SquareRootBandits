/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOccupiedFollowerDataArrival

import Lean.Elab.Tactic.Omega

/-!
# Complete follower retained-DOWN recovery components

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,180-240,354-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-121,192-349,425-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-84`.

These internal results derive the accepted UP assignment's actual installation,
retained DOWN record, live calendar interval, carried buffer, canonical suffix,
original-candidate contributions, and checked numerical DOWN recovery. The
recovery starts from the installed payload queue and preserves the physical
contribution list through the checked scanner endpoint. It does not identify
that list with the whole original enabled-calendar arm-marker list or prove the
terminal UP reply identity.
-/
@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerRetainedDownRecovery

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selectionAt_payload
    (x : RoundInput p rate) (P : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection P started time weights x.row)
    (v : Selection x) (hv : selectionAt x P started time weights arm = some v) :
    v.view.payload = P := by
  unfold selectionAt at hv
  split at hv
  · cases hv
    rfl
  · cases hv

/-- A successful tail can only retain its actual selected payload. This
includes cutoff collection and later installation, with failures left intact. -/
private theorem selected_output_payload_frame
    (r : RoundRecord (p := p) (rate := rate)) (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v) :
    storedPayload r.output.next.coordinator = none ∨
      storedPayload r.output.next.coordinator = some v.view.payload := by
  classical
  have hnext : r.output.next.coordinator =
      r.output.preparation.observeCoordinator.configuration := by
    rw [r.output_eq]
    rfl
  have hnonempty : r.output.preparation.coordinator.selection ≠ none := by
    rw [hv]
    exact Option.some_ne_none _
  rw [hnext]
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          have hp := selectionAt_payload r.input _ _ _ _ arm v
            (by simpa only [hc, DispatchCut.selection] using hv)
          rw [observeCoordinator_first_equation r.output.preparation _ hc]
          have hn := hnonempty
          rw [hc] at hn
          rw [ite_eq_right hn]
          rw [hp]
          exact livePostChoice_payload_frame r.output.preparation _ _ _ _
      | choiceDomainFailure _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | recorderBoundaryFailure _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | choiceRejected _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          have hp := selectionAt_payload r.input registers.payload dispatched.startResult
            r.input.time (liveRegistersAt registers r.input.time).complementWeights arm v
            (by simpa only [hc, DispatchCut.selection] using hv)
          rw [observeCoordinator_live_equation r.output.preparation _ _ _ _ hc]
          have hn := hnonempty
          rw [hc] at hn
          rw [ite_eq_right hn]
          rw [hp]
          exact livePostChoice_payload_frame r.output.preparation _ _ _ _
      | cutoffChosen dispatched hstart ledger hinit heq hdomain hclock hpending hassign arm =>
          have hp := selectionAt_payload r.input registers.payload dispatched.startResult
            r.input.time (liveRegistersAt registers r.input.time).complementWeights arm v
            (by simpa only [hc, DispatchCut.selection] using hv)
          rw [observeCoordinator_live_equation r.output.preparation _ _ _ _ hc]
          have hn := hnonempty
          rw [hc] at hn
          rw [ite_eq_right hn]
          rw [hp]
          exact collectionPostChoice_payload_frame r.output.preparation _ _ _ _
      | clockFailure _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | initializerFailure _ _ _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | localFailure _ _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
  | collection P ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hp : v.view.payload = P := by
            have hm : (DispatchCut.collection P ledger clock cutoff
                (.continuing core snapshot boundary scores)).selection.map
                  (fun w => w.view.payload) = some P := by
              simp only [DispatchCut.selection, Option.map_some]
            rw [← hc, hv] at hm
            exact Option.some.inj hm
          rw [observeCoordinator_collection_equation r.output.preparation _ _ _ _ _ hc]
          have hn := hnonempty
          rw [hc] at hn
          rw [ite_eq_right hn, hp]
          exact collectionPostChoice_payload_frame r.output.preparation _ _ _ _
      | laterChosen core consistent started hstart instruction hinstruction output
          hlocal clockData installed arm =>
          have hp := selectionAt_payload r.input _ _ _ _ arm v
            (by simpa only [hc, DispatchCut.selection] using hv)
          rw [observeCoordinator_collection_equation r.output.preparation _ _ _ _ _ hc]
          have hn := hnonempty
          rw [hc] at hn
          rw [ite_eq_right hn, hp]
          exact livePostChoice_payload_frame r.output.preparation _ _ _ _
      | clockFailure _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | localFailure _ _ _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | coreFailure _ _ _ _ => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | laterReconstructionFailure _ _ _ _ _ _ _ _ =>
          simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ =>
          simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | laterOrientationFailure _ _ _ _ _ _ _ _ =>
          simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
          simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
  | invalidCollectionCutoff => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
  | dagger => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv

private theorem next_stored_selection
    (r : RoundRecord (p := p) (rate := rate)) (P : Payload rate)
    (hnext : storedPayload r.output.next.coordinator = some P) :
    ∃ v : Selection r.input,
      r.output.preparation.coordinator.selection = some v ∧ v.view.payload = P := by
  classical
  have hn : r.output.preparation.coordinator.selection ≠ none := by
    intro h
    have hf := ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection r h
    rw [hnext] at hf
    cases hf
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨v, hv, ?_⟩
  rcases selected_output_payload_frame r v hv with hnone | hsome
  · rw [hnext] at hnone
    cases hnone
  · exact Option.some.inj (hsome.symm.trans hnext)

private theorem connected_successor_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = (records[n]'(by omega)).output.next := by
  induction records generalizing initial n with
  | nil => simp at hn
  | cons head tail ih =>
      simp only [Connected] at hconnected
      cases n with
      | zero =>
          cases tail with
          | nil => simp at hn
          | cons next rest => exact hconnected.2.1
      | succ n =>
          have ht : n + 1 < tail.length := by simp at hn; omega
          simpa only [List.getElem_cons_succ] using ih hconnected.2 n ht

private theorem complete_adjacent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[n + 1].input.state =
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[n]'(by omega)).output.next := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl] at hn
  | some active =>
      exact connected_successor_input
        (ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate source rewards C_star C_h active hl) n hn

private theorem accepted_up_has_choice
    (x : RoundInput p rate) (i : Fin (p.m - 1))
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp x i U) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice x = some c := by
  classical
  obtain ⟨tail, recording, started, decoded, bank, htail, _⟩ := hacc
  unfold ReferenceCollectionPhaseHistory.executedTail at htail
  dsimp only at htail
  split at htail
  · contradiction
  next hn =>
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [ite_eq_right hn]
    cases hc : (prepare x).coordinator with
    | first outcome =>
        cases outcome <;> simp only [hc] at htail
        all_goals contradiction
    | live r q base outcome =>
        cases outcome <;> simp only [hc] at htail
        all_goals first | contradiction | exact ⟨_, rfl⟩
    | collection P ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc] at htail
        all_goals first | contradiction | exact ⟨_, rfl⟩
    | invalidCollectionCutoff => simp only [hc] at htail; contradiction
    | dagger => simp only [hc] at htail; contradiction

private theorem choice_has_selection
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ∃ v : Selection x,
      (prepare x).coordinator.selection = some v ∧ v.view.payload = c.payload := by
  classical
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · contradiction
  next hn =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨v, hv, ?_⟩
    cases hd : (prepare x).coordinator with
    | first outcome =>
        cases outcome <;>
          simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals contradiction
    | live r q base outcome =>
        cases outcome <;>
          simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        cases Option.some.inj hc
        exact selectionAt_payload x _ _ _ _ _ v
          (by simpa only [hd, DispatchCut.selection] using hv)
    | collection P ledger clock cutoff outcome =>
        cases outcome <;>
          simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        cases Option.some.inj hc
        simp only [hd, DispatchCut.selection] at hv
        cases Option.some.inj hv
        rfl
    | invalidCollectionCutoff =>
        simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        contradiction
    | dagger =>
        simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        contradiction

private theorem stored_between_birth_and_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val] P)
    (hcurrent : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (n : Fin R.length), b.val < n.val → n.val ≤ k.val →
      storedPayload R[n.val].input.state.coordinator = some P := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hk : k.val < R.length := k.isLt
  have htime (n : Fin R.length) : R[n.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source n
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] P hbirth
  rw [htime b] at hbirthTime
  have hback : ∀ d, ∀ (hd : d ≤ k.val), b.val < k.val - d →
      storedPayload (R[k.val - d]'(by omega)).input.state.coordinator = some P := by
    intro d
    induction d with
    | zero => intro hd hb; simpa only [Nat.sub_zero] using hcurrent
    | succ d ih =>
        intro hd hb
        have hprev := ih (by omega) (by omega)
        let n : Fin R.length := ⟨k.val - (d + 1), by omega⟩
        have hnext : storedPayload R[n.val].output.next.coordinator = some P := by
          have ha := complete_adjacent (rate := rate) rewards C_star C_h source n.val
            (by dsimp [n]; omega)
          rw [← ha]
          have hindex : n.val + 1 = k.val - d := by dsimp [n]; omega
          simpa only [hindex] using hprev
        have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification
          R[n.val].input
        have houtput : ReferenceActivePhysicalStep.step R[n.val].input = R[n.val].output :=
          R[n.val].output_eq.symm
        rw [houtput] at hclass
        rcases hclass with hnone | ⟨old, hold, hout⟩ | ⟨fresh, hfresh, hout⟩
        · rw [hnext] at hnone
          cases hnone
        · have heq : old = P := Option.some.inj (hout.symm.trans hnext)
          simpa only [heq] using hold
        · have heq : fresh = P := Option.some.inj (hout.symm.trans hnext)
          have hfreshRecord : InstallationBirth R[n.val] P := by
            have hr : ReferenceAssignmentPayloadChronology.actualStepRecord R[n.val].input =
                R[n.val] := by
              cases hr : R[n.val] with
              | mk input output heq =>
                  dsimp only [ReferenceAssignmentPayloadChronology.actualStepRecord]
                  cases heq
                  rfl
            simpa only [heq, hr] using hfresh
          have hfreshTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
            R[n.val] P hfreshRecord
          rw [htime n] at hfreshTime
          dsimp only [n] at hfreshTime
          omega
  intro n hbn hnk
  have h := hback (k.val - n.val) (by omega) (by omega)
  have hi : k.val - (k.val - n.val) = n.val := by omega
  simpa only [hi] using h

/-- Actual accepted UP produces its original installation and every actual
selected payload from that birth until the acceptance. No selected interval,
matching trace, numerical arrival, or zero initial queue is an input. -/
theorem complete_accepted_up_selected_payload_interval
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧ InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      R[k.val].input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      U.val.sigma = c.payload.sigma.val + 1 ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      c.preLedger.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      (∀ n : Fin R.length, b.val < n.val → n.val ≤ k.val →
        storedPayload R[n.val].input.state.coordinator = some c.payload) ∧
      (∀ n : Fin R.length, b.val ≤ n.val → n.val < k.val →
        storedPayload R[n.val].output.next.coordinator = some c.payload ∧
        ∃ v : Selection R[n.val].input,
          R[n.val].output.preparation.coordinator.selection = some v ∧
          v.view.payload = c.payload) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hk : k.val < R.length := k.isLt
  obtain ⟨c, hc⟩ := accepted_up_has_choice R[k.val].input i U hacc
  obtain ⟨b, j, F, mu, hbj, hjk, hbirth, hretained, hinput, hdown,
    hsigma, hledgerSigma, hS, hdelta, hq, hcutoff, hbase⟩ :=
    ReferenceAcceptedUpAssignmentBirthJoin.complete_accepted_up_birth_join
      rate rewards C_star C_h source k c hc i U hacc
  have hbk : b.val < k.val := by omega
  obtain ⟨v, hv, hp⟩ := choice_has_selection R[k.val].input c hc
  have hselection : R[k.val].output.preparation.coordinator.selection = some v := by
    have hprep : R[k.val].output.preparation = prepare R[k.val].input := by
      rw [R[k.val].output_eq]
      rfl
    rw [hprep]
    exact hv
  have hstored : storedPayload R[k.val].input.state.coordinator = some c.payload := by
    rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
        R[k.val] v hselection with hstored | hborn
    · simpa only [hp] using hstored
    · have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val]
        c.payload hbirth
      have hu := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[k.val]
        v.view.payload hborn
      rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source b] at ht
      rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source k, hp] at hu
      omega
  have hbetween := stored_between_birth_and_current (rate := rate) rewards C_star C_h
    source b k c.payload hbirth hstored
  have hbase' : ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
      some c.preLedger.baseScore := by
    cases hcoord : R[b.val].output.preparation.coordinator with
    | first outcome =>
        cases outcome <;>
          simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | live registers owned base outcome =>
        simp_all only [R]
    | collection P ledger clock cutoff outcome =>
        cases outcome <;>
          simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | invalidCollectionCutoff =>
        simp_all only [R]
    | dagger =>
        simp_all only [R]
  refine ⟨c, b, j, F, mu, hc, hbj, hjk, hbirth, hretained, hinput, hdown,
    hsigma.trans hledgerSigma, hS, hdelta, hq, hledgerSigma, hcutoff, hbase',
    hbetween, ?_⟩
  intro n hbn hnk
  let successor : Fin R.length := ⟨n.val + 1, by omega⟩
  have hsucc := hbetween successor (by dsimp [successor]; omega)
    (by dsimp [successor]; omega)
  have hnext : storedPayload R[n.val].output.next.coordinator = some c.payload := by
    rw [← complete_adjacent (rate := rate) rewards C_star C_h source n.val (by omega)]
    exact hsucc
  exact ⟨hnext, next_stored_selection R[n.val] c.payload hnext⟩

private theorem complete_clock
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) r.input.time.val r.input.state ∧
      ReferenceCoordinatorClockDomains.clockAt source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (r.input.time.val + 1) r.output.next := by
  classical
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl] at hk
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hl]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hr := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial hcanonical
      dsimp only
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          initial := by
        have hf : initial.coordinator = .first := seed.coordinatorFirst
        simp only [ReferenceCoordinatorClockDomains.clockAt, hf]
      have hclock := ReferenceRunClockPreservation.run_clockAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h initial hcanonical) hseed
      have hm : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] ∈
          (run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                  rate source rewards C_star C_h; omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate source rewards C_star C_h initial hcanonical)).records := by
        rw [← hr]
        exact List.getElem_mem k.isLt
      have hrecord := hclock.2.2.2 _ hm
      exact ⟨hrecord.1, hrecord.2.1⟩

private theorem selectionAt_cutoff
    (x : RoundInput p rate) (P : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection P started time weights x.row)
    (v : Selection x) (hv : selectionAt x P started time weights arm = some v) :
    v.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
  unfold selectionAt at hv
  split at hv
  · cases hv
    rfl
  · cases hv

private theorem finish_clock_u
    (clock : CoordinatorPhaseClock.ClockRegisters p) (t : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) (row : CompletePublicTable.CompleteRow p)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hf : CoordinatorPhaseClock.finishRound p rate.eta.val t clock pending row = .ok finished) :
    finished.clock.u = clock.u := by
  classical
  simp only [CoordinatorPhaseClock.finishRound] at hf
  repeat' split at hf
  all_goals
    cases hf
    all_goals simp_all

private theorem live_tail_clock_u
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : (livePostChoice prepared registers owned base started).configuration =
      .live next nextOwned nextBase) :
    next.priorClock.u = started.clock.u := by
  classical
  unfold livePostChoice at hnext
  cases hr : CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared registers started) with
  | none => simp only [hr] at hnext; cases hnext
  | some recording =>
      cases hs : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp only [hr, hs] at hnext; cases hnext
      | ok serviced =>
          cases hp : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp only [hr, hs, hp] at hnext; cases hnext
          | some pending =>
              cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp only [hr, hs, hp, hf] at hnext; cases hnext
              | ok finished =>
                  simp only [hr, hs, hp, hf] at hnext
                  have heq := CoordinatorConfiguration.live.inj hnext
                  have hr : next = _ := heq.1.symm
                  rw [hr]
                  exact finish_clock_u started.clock x.time pending x.row finished hf

private theorem collection_tail_ne_live
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (P : Payload rate) (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ) :
    (collectionPostChoice prepared P ledger started weights).configuration ≠
      .live next nextOwned nextBase := by
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    prepared P ledger started weights
  rcases hphase with hd | ⟨P', ledger', saved, hc⟩
  · rw [hd]
    intro h
    cases h
  · rw [hc]
    intro h
    cases h

private theorem selected_cutoff_none_of_next_live
    (r : RoundRecord (p := p) (rate := rate)) (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : r.output.next.coordinator = .live next nextOwned nextBase)
    (hu : next.priorClock.u = none) : v.view.cutoff = none := by
  classical
  have hobs : r.output.preparation.observeCoordinator.configuration =
      .live next nextOwned nextBase := by
    have he : r.output.next.coordinator =
        r.output.preparation.observeCoordinator.configuration := by rw [r.output_eq]; rfl
    exact he.symm.trans hnext
  have hn : r.output.preparation.coordinator.selection ≠ none := by rw [hv]; simp
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> try { simp only [hc, DispatchCut.selection, reduceCtorEq] at hv }
      rename_i installed arm
      have hv' : selectionAt r.input _ _ _ _ arm = some v := by
        simpa only [hc, DispatchCut.selection] using hv
      have hcut := selectionAt_cutoff r.input _ _ _ _ arm v hv'
      rw [observeCoordinator_first_equation r.output.preparation _ hc] at hobs
      rw [hc] at hn
      rw [ite_eq_right hn] at hobs
      have ht := live_tail_clock_u r.output.preparation _ _ _ _ next nextOwned nextBase hobs
      rw [← ht, hu] at hcut
      exact hcut
  | live registers owned base outcome =>
      cases outcome <;> try { simp only [hc, DispatchCut.selection, reduceCtorEq] at hv }
      · rename_i dispatched hstart ledger hinit heq hdomain hclock hpending hassign arm
        rw [observeCoordinator_live_equation r.output.preparation _ _ _ _ hc] at hobs
        rw [hc] at hn
        rw [ite_eq_right hn] at hobs
        exact (collection_tail_ne_live r.output.preparation _ _ _ _ next nextOwned nextBase hobs).elim
      · rename_i dispatched hstart continuation arm
        have hv' : selectionAt r.input registers.payload dispatched.startResult r.input.time
            (liveRegistersAt registers r.input.time).complementWeights arm = some v := by
          simpa only [hc, DispatchCut.selection] using hv
        have hcut := selectionAt_cutoff r.input _ _ _ _ arm v hv'
        rw [observeCoordinator_live_equation r.output.preparation _ _ _ _ hc] at hobs
        rw [hc] at hn
        rw [ite_eq_right hn] at hobs
        have ht := live_tail_clock_u r.output.preparation _ _ _ _ next nextOwned nextBase hobs
        rw [← ht, hu] at hcut
        exact hcut
  | collection P ledger clock cutoff outcome =>
      cases outcome <;> try { simp only [hc, DispatchCut.selection, reduceCtorEq] at hv }
      · rw [observeCoordinator_collection_equation r.output.preparation _ _ _ _ _ hc] at hobs
        rw [hc] at hn
        rw [ite_eq_right hn] at hobs
        exact (collection_tail_ne_live r.output.preparation _ _ _ _ next nextOwned nextBase hobs).elim
      · rename_i core consistent started hstart instruction hinstruction output hlocal data installed arm
        have hv' : selectionAt r.input _ _ _ _ arm = some v := by
          simpa only [hc, DispatchCut.selection] using hv
        have hcut := selectionAt_cutoff r.input _ _ _ _ arm v hv'
        rw [observeCoordinator_collection_equation r.output.preparation _ _ _ _ _ hc] at hobs
        rw [hc] at hn
        rw [ite_eq_right hn] at hobs
        have ht := live_tail_clock_u r.output.preparation _ _ _ _ next nextOwned nextBase hobs
        rw [← ht, hu] at hcut
        exact hcut
  | invalidCollectionCutoff => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv
  | dagger => simp only [hc, DispatchCut.selection, reduceCtorEq] at hv

private theorem complete_choice_cutoff_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c) :
    c.preLedger.cutoff ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.time.val + 1 := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  have hclock := (complete_clock (rate := rate) rewards C_star C_h source k).1
  change ReferenceCoordinatorClockDomains.clockAt source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) r.input.time.val r.input.state at hclock
  change ReferenceCollectionSegmentExtraction.choice r.input = some c at hc
  cases hs : r.input.state.coordinator with
  | first =>
      rw [ReferenceCollectionSegmentExtraction.choice_first_none r.input hs] at hc
      cases hc
  | dagger =>
      have hd : (prepare r.input).coordinator = .dagger := dispatch_dagger r.input hs
      simp [ReferenceCollectionSegmentExtraction.choice, hd, DispatchCut.selection] at hc
  | collection P ledger proposal =>
      have hpre := (ReferenceCollectionSegmentExtraction.choice_collection_pre
        r.input P ledger proposal c hs hc).1
      simp only [ReferenceCoordinatorClockDomains.clockAt, hs] at hclock
      rw [hpre]
      exact hclock.2.2.2.2.1.trans (Nat.le_succ _)
  | live registers owned base =>
      unfold ReferenceCollectionSegmentExtraction.choice at hc
      split at hc
      · contradiction
      next hn =>
        change ReferenceCollectionSegmentExtraction.choiceOfCut (dispatch r.input) = some c at hc
        have hd : dispatch r.input = .live registers owned base
            (CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base)) := by
          simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hd] at hc
        cases ho : CoordinatorRoundDispatch.dispatchLive
            (liveInput r.input registers owned base) <;>
          simp only [ho, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        rename_i dispatched hstart ledger hinit heq hdomain hclock hpending hassign arm
        cases Option.some.inj hc
        rw [heq]
        exact le_rfl

private theorem complete_stored_live_before_cutoff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : Payload rate)
    (hstored : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (hbefore : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.time.val <
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))) :
    ∃ registers owned base,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.coordinator =
          .live registers owned base ∧ registers.payload = P := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  have hbirth := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  have hclock := (complete_clock (rate := rate) rewards C_star C_h source k).1
  change ReferenceCoordinatorClockDomains.clockAt source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) r.input.time.val r.input.state at hclock
  change storedPayload r.input.state.coordinator = some P at hstored
  cases hs : r.input.state.coordinator with
  | first => simp only [hs, storedPayload] at hstored; cases hstored
  | dagger => simp only [hs, storedPayload] at hstored; cases hstored
  | live registers owned base =>
      refine ⟨registers, owned, base, rfl, ?_⟩
      exact Option.some.inj (by simpa only [hs, storedPayload] using hstored)
  | collection Q ledger proposal =>
      have hQP : Q = P := Option.some.inj (by simpa only [hs, storedPayload] using hstored)
      dsimp only at hbirth
      have hs' := hs
      dsimp only [r] at hs'
      rw [hs'] at hbirth
      have hcut := hbirth.2.2.2
      rw [hQP] at hcut
      simp only [ReferenceCoordinatorClockDomains.clockAt, hs] at hclock
      have hle := hclock.2.2.2.2.1
      rw [hcut] at hle
      exact (Nat.not_lt_of_ge hle hbefore).elim

/-- An actual installation begins from the carried ordinary, unoccupied
follower and its real chronological buffer. Earlier assignments' reply fields
and the current coordinator configuration are retained by the seed. -/
theorem complete_installation_carried_buffer_seed
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val] P) (i : Fin (p.m - 1)) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val]
    ∃ (seed choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      r.input.state.followers i = .ordinary seed memory ∧
      ActiveFollowerLifecycle.localStateDomainValid seed ∧
      seed.status = .unoccupied ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time seed memory = .ok (choice, memory) ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧
      ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ seed.buffer, saved.calendarRound ≤ P.sigma.val) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hb : b.val < R.length := b.isLt
  obtain ⟨hc, hspan, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source b
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hs : s < p.T := by dsimp only [s]; omega
  let x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs :=
    ⟨source, hc, rfl⟩
  have hgeneratedSeed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  have hgenerated : R = (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x).records := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate source rewards
      C_star C_h (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs x) hgeneratedSeed.1
  let n : Fin (p.T - s) := ⟨b.val, by
    have hl := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate source rewards C_star C_h
    change R.length = p.T - s at hl
    omega⟩
  have hrecord : R[b.val] =
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n := by
    have hg := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x n
    rw [← hgenerated, List.getElem?_eq_getElem hb] at hg
    exact Option.some.inj hg
  obtain ⟨seed, memory, choice, hinput, hdomain, hstart, hchoice, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source b i
  have hbirth' : InstallationBirth
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) P := by rw [← hrecord]; exact hbirth
  have hchoice' : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) i).configuration = .ordinary choice memory := by
    rw [← hrecord]
    exact hchoice
  obtain ⟨hchoiceStatus, before, beforeMemory, hbefore, hbeforeStatus, _⟩ :=
    ReferenceGeneratedInstallationFollowerSeed.generated_installation_choice_unoccupied
      rate rewards C_star C_h s hs x i n P hbirth' choice memory hchoice'
  have hbefore' : R[b.val].input.state.followers i = .ordinary before beforeMemory := by
    rw [hrecord]
    exact hbefore
  have heq : before = seed :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbefore'.symm.trans hinput)).1
  have hseedStatus : seed.status = .unoccupied := by rw [← heq]; exact hbeforeStatus
  obtain ⟨hvalid, hpair, htimes⟩ :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_input_buffer_chronological
      rate source rewards C_star C_h b i seed memory hinput
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] P hbirth
  refine ⟨seed, choice, memory, hinput, hdomain, hseedStatus, hstart, hchoice,
    hchoiceStatus, hvalid, hpair, ?_⟩
  intro saved hsaved
  have ht := htimes saved hsaved
  change saved.calendarRound < R[b.val].input.time.val + 1 at ht
  omega

/-- The accepted reply's pre-cutoff list is the actual calendar interval.
Every cell produces its selected payload, live view, and whole ordinary
choice family. The first cutoff and the interval are derived from acceptance. -/
theorem complete_accepted_up_live_calendar_interval
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate) (b j : Fin R.length),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧ InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      let sigma := c.payload.sigma.val + 1
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
      let L := (R.drop b.val).take (u - sigma)
      1 ≤ u - sigma ∧ u ≤ R[k.val].input.time.val + 1 ∧
      L.map (fun r => r.input.time.val + 1) = List.range' sigma (u - sigma) ∧
      (∀ n : Fin L.length,
        ∃ v : Selection L[n.val].input,
          L[n.val].output.preparation.coordinator.selection = some v ∧
          v.view.payload = c.payload ∧ v.view.cutoff = none ∧
          CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff L[n.val].input.time ∧
          ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
            (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
            (∀ f, (ReferenceFollowerFixedReply.actualChoice L[n.val] f).configuration =
              .ordinary (states f) (memories f)) ∧
            (∀ f, (states f).status ≠ .unoccupied →
              (states f).lastDown = some (c.payload.downRecord f))) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hk : k.val < R.length := k.isLt
  obtain ⟨c, b, j, F, mu, hc, hbj, hjk, hbirth, hretained, hinput, hdown,
    hUsigma, hS, hdelta, hq, hledgerSigma, hcutoff, hbase, hbetween, hselected⟩ :=
    complete_accepted_up_selected_payload_interval (rate := rate) rewards C_star C_h source k i U hacc
  let sigma := c.payload.sigma.val + 1
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
  let L := (R.drop b.val).take (u - sigma)
  have hbTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] c.payload hbirth
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b]
    at hbTime
  have hktime : R[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source k
  have hule : u ≤ R[k.val].input.time.val + 1 := by
    dsimp only [u]
    rw [← hcutoff]
    exact complete_choice_cutoff_le (rate := rate) rewards C_star C_h source k c hc
  have hpositive : 1 ≤ u - sigma := by
    have hb := (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
      rate.sourceCap c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))).1
    dsimp only [u, sigma]
    omega
  have hsize : u - sigma ≤ R.length - b.val := by dsimp only [sigma]; omega
  have hlength : L.length = u - sigma := by simp only [L, List.length_take, List.length_drop, Nat.min_eq_left hsize]
  have hcell (n : Fin L.length) : b.val + n.val < R.length := by
    have hn : n.val < u - sigma := by simpa only [hlength] using n.isLt
    omega
  have hget (n : Fin L.length) : L[n.val] = R[b.val + n.val]'(hcell n) := by
    simp only [L, List.getElem_take, List.getElem_drop]
  have htime (n : Fin L.length) : L[n.val].input.time.val + 1 = sigma + n.val := by
    rw [hget]
    have ht : R[b.val + n.val].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
          (b.val + n.val) := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h source ⟨b.val + n.val, hcell n⟩
    dsimp only [sigma]
    omega
  refine ⟨c, b, j, hc, hbj, hjk, hbirth, hretained, hbase, hpositive, hule, ?_, ?_⟩
  · change L.map (fun r => r.input.time.val + 1) = List.range' sigma (u - sigma)
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range', hlength]
    · intro n hleft hright
      simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
      exact htime ⟨n, by simpa only [List.length_map] using hleft⟩
  · intro n
    let a : Fin R.length := ⟨b.val + n.val, hcell n⟩
    have ha : a.val < k.val := by
      have hn : n.val < u - sigma := by
        calc n.val < L.length := n.isLt
             _ = u - sigma := hlength
      dsimp only [a]
      dsimp only [sigma] at hn
      omega
    obtain ⟨hnextStored, v, hv, hp⟩ := hselected a (by dsimp [a]; omega) ha
    let successor : Fin R.length := ⟨a.val + 1, by omega⟩
    have hsuccStored := hbetween successor (by dsimp [successor, a]; omega)
      (by dsimp [successor]; omega)
    have hsuccTime : R[successor.val].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + successor.val :=
      ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source successor
    have hbefore : R[successor.val].input.time.val < u := by
      have hn : n.val < u - sigma := by
        calc n.val < L.length := n.isLt
             _ = u - sigma := hlength
      dsimp only [successor, a] at hsuccTime ⊢
      dsimp only [sigma] at hn
      omega
    obtain ⟨registers, owned, base, hsuccLive, hP⟩ :=
      complete_stored_live_before_cutoff (rate := rate) rewards C_star C_h source
        successor c.payload hsuccStored hbefore
    have hnext : R[a.val].output.next.coordinator = .live registers owned base := by
      rw [← complete_adjacent (rate := rate) rewards C_star C_h source a.val (by omega)]
      exact hsuccLive
    have hclock := (complete_clock (rate := rate) rewards C_star C_h source successor).1
    simp only [ReferenceCoordinatorClockDomains.clockAt, hsuccLive] at hclock
    have hvnone := selected_cutoff_none_of_next_live R[a.val] v hv registers owned base hnext
      hclock.2.2.2.1
    have hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
        R[a.val].input.time := by
      rw [hp, hvnone]
      have ht : R[a.val].input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + a.val :=
        ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source a
      simp only [CoordinatorLocalArmChoice.assignmentIsLive, CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.sourceRound, CoordinatorLocalArmChoice.cutoffRound, Option.elim_none]
      have hT := R[a.val].input.time.isLt
      have hba : b.val ≤ a.val := by dsimp only [a]; omega
      constructor <;> omega
    obtain ⟨states, memories, hactual, hfields, _, _⟩ :=
      ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
        (rate := rate) rewards C_star C_h source a v hv
    rw [hget n]
    refine ⟨v, hv, hp, hvnone, hlive, states, memories, hactual, ?_⟩
    intro f hf
    simpa only [hp] using hfields f hf

/-- On an actual selected live cell, each unoccupied follower's emitted
contribution is its canonical arm event times the original reward floor.
Actual whole choice families and collision geometry are produced internally;
zero rewards, zero floors, and failed event tests remain literal zero cases. -/
theorem complete_selected_original_candidate_contribution
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val]
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ i, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary (states i) (memories i)) ∧
      ∀ i, (states i).status = .unoccupied →
        ReferenceFollowerSparseEmissionRecovery.emissionContribution (v.view.payload.downRecord i) i r =
          if SnapshotRecordingKernel.recordingMap p
              (.live v.view.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot v states))
              true rate.eta.val rate.eta.property v.view.payload.eta_le_source_cap
              v.view.payload.anchor v.view.payload.anchor
              v.view.payload.anchor_pos v.view.payload.anchor_pos
              (fun _ => le_rfl) (fun j => by
                rw [two_mul]
                exact le_add_of_nonneg_right (le_of_lt (v.view.payload.anchor_pos j)))
              (r.input.row.2 r.input.time).1 = some (v.view.payload.assignment.assigned i)
          then Nat.floor ((D p : ℝ) * rate.eta.val *
            (((rewards r.input.time (v.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
              OrdinaryMessageCodec.dyadicRate (v.view.payload.downRecord i).val.h)
          else 0 := by
  classical
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val]
  obtain ⟨states, memories, hprepare, hactual, hprepared, hfields, hgeometry⟩ :=
    ReferenceCompleteDataOwnerFeedback.complete_selected_source_data_owner_geometry
      (rate := rate) rewards C_star C_h source k v hv
  refine ⟨states, memories, hactual, ?_⟩
  intro i hunoccupied
  let P := v.view.payload
  let a := P.assignment.assigned i
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let snapshot := ReferenceActiveDataOwnership.choiceSnapshot v states
  let slice := (r.input.row.2 r.input.time).1
  let hupper : ∀ j, P.anchor j ≤ 2 * P.anchor j := fun j => by
    rw [two_mul]
    exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos j))
  let marker := SnapshotRecordingKernel.recordingMap p (.live P.assignment snapshot)
    true rate.eta.val rate.eta.property P.eta_le_source_cap P.anchor P.anchor
    P.anchor_pos P.anchor_pos (fun _ => le_rfl) hupper slice
  have hsel : (prepare r.input).coordinator.selection = some v := by
    rw [← hprepare]
    exact hv
  have hchoice : (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i) := hactual i
  have hcandidate := ReferenceSelectedCandidateRecorderEvent.current_selected_candidate_eq_marker
    r v hsel i snapshot (states i) (memories i) hchoice hunoccupied rfl
    P.anchor P.anchor_pos (fun _ => le_rfl) hupper
  have hdownH : (P.downRecord i).val.h = P.exponent a :=
    congrArg OrdinaryMessageCodec.DownFields.h (P.downRecord_fields i)
  have hcontribution : ReferenceFollowerSparseEmissionRecovery.emissionContribution
      (P.downRecord i) i r =
      if marker = some a then Nat.floor ((D p : ℝ) * rate.eta.val *
        (r.output.ownEntries player).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val P.anchor a) else 0 := by
    simpa only [ReferenceFollowerSparseEmissionRecovery.emissionContribution,
      ReferenceFollowerBufferProvenance.logEmission, hchoice, hunoccupied, dite_true,
      hdownH, ReferenceActiveDataOwnership.downRecord_arm, P, a, marker, snapshot,
      slice, player] using hcandidate
  change ReferenceFollowerSparseEmissionRecovery.emissionContribution (P.downRecord i) i r =
    if marker = some a then _ else 0
  rw [hcontribution]
  by_cases hevent : marker = some a
  · rw [ite_eq_left hevent, ite_eq_left hevent]
    obtain ⟨hdataScalar, hactionMap, hownerMap, hmaskMap, _⟩ :=
      (SnapshotRecordingKernel.recordingMap_some_iff p (.live P.assignment snapshot)
        rate.eta.val rate.eta.property P.eta_le_source_cap P.anchor P.anchor
        P.anchor_pos P.anchor_pos (fun _ => le_rfl) hupper slice a).mp hevent
    have hplayerNe : player ≠ ActiveRoundActions.coordinator p.two_le_m :=
      ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
    have hindex : ActiveRoundActions.followerIndex p.two_le_m player hplayerNe = i :=
      ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe
    have howner : SnapshotRecordingKernel.owns p (.live P.assignment snapshot) player a := by
      simp only [SnapshotRecordingKernel.owns, dite_eq_right hplayerNe, hindex]
      rfl
    have hsource := SnapshotRecordingKernel.owns_unique p (.live P.assignment snapshot) a
      _ player hownerMap howner
    rw [hsource] at hactionMap hmaskMap
    have hdata : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot := by
      simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hdataScalar
    have hdataAction : SnapshotRecordingKernel.dataAction p (.live P.assignment snapshot)
        rate.eta.val rate.eta.property P.eta_le_source_cap P.anchor P.anchor
        P.anchor_pos P.anchor_pos (fun _ => le_rfl) hupper slice player =
        PublicDiscreteDraws.pilotDraw (K_pos p) player slice := by
      simp only [SnapshotRecordingKernel.dataAction, dite_eq_right hplayerNe, hindex,
        snapshot, ReferenceActiveDataOwnership.choiceSnapshot, hunoccupied, dite_eq_left]
    have haction : (prepare r.input).arms.actions player = a := by
      rw [PreparedRound.action_follower]
      have ha := ReferenceActiveDataOwnership.ordinary_data_arm P i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (r.input.state.followers i) (states i) (memories i) (hprepared i) (hfields i) hdata
      rw [ite_eq_left hunoccupied] at ha
      exact ha.trans (hdataAction.symm.trans hactionMap)
    have hvalue := ((hgeometry hlive hdata).1 player a haction howner hmaskMap).2.2
    have hown : (r.output.ownEntries player).2 = (prepare r.input).feedback.observations player := by
      rw [r.output_eq]
      rfl
    have hrate : OrdinaryMessageCodec.dyadicRate (P.downRecord i).val.h =
        CanonicalRecordingRates.xi p rate.eta.val P.anchor a := by
      rw [hdownH, P.dyadicRate_eq_rate, P.rate_eq_canonical]
    rw [hown, hvalue, hrate]
  · rw [ite_eq_right hevent, ite_eq_right hevent]

/-- Executed acceptance produces the real birth buffer and the selected-view
restriction on the actual original-record prefix before its retained DOWN.
The initial state is the birth input, including its actual coordinator. -/
theorem complete_accepted_up_birth_buffer_interval
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate) (b j : Fin R.length)
      (seed choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧ InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      R[b.val].input.state.followers i = .ordinary seed memory ∧
      ActiveFollowerLifecycle.localStateDomainValid seed ∧ seed.status = .unoccupied ∧
      ActiveFollowerLifecycle.startRound rate.eta R[b.val].input.time seed memory = .ok (choice, memory) ∧
      (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧ ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ seed.buffer, saved.calendarRound ≤ c.payload.sigma.val) ∧
      (c.payload.downRecord i).val.q = c.payload.queues (c.payload.assignment.assigned i) ∧
      ReferenceFollowerSparseEmissionRecovery.selectedViewInterval c.payload.sigma.val
        ((R.drop b.val).take (j.val - b.val)) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨c, b, j, F, mu, hc, hbj, hjk, hbirth, hretained, hinput, hdown,
    hUsigma, hS, hdelta, hq, hledgerSigma, hcutoff, hbase, hbetween, hselected⟩ :=
    complete_accepted_up_selected_payload_interval (rate := rate) rewards C_star C_h source k i U hacc
  obtain ⟨seed, choice, memory, hseed, hdomain, hstatus, hstart, hchoice,
    hchoiceStatus, hvalid, hpair, htimes⟩ :=
    complete_installation_carried_buffer_seed (rate := rate) rewards C_star C_h source b c.payload hbirth i
  refine ⟨c, b, j, seed, choice, memory, hc, hbj, hjk, hbirth, hretained, hseed,
    hdomain, hstatus, hstart, hchoice, hchoiceStatus, hvalid, hpair, htimes,
    c.payload.downRecord_initialQueue i, ?_⟩
  change ReferenceFollowerSparseEmissionRecovery.selectedViewInterval c.payload.sigma.val
    ((R.drop b.val).take (j.val - b.val))
  intro record hrecord view hview
  obtain ⟨l, hl, hget⟩ := List.mem_iff_getElem.mp hrecord
  have hbounds : l < j.val - b.val ∧ l < R.length - b.val := by
    simpa only [List.length_take, List.length_drop, Nat.lt_min] using hl
  let n : Fin R.length := ⟨b.val + l, by omega⟩
  have hcell : ((R.drop b.val).take (j.val - b.val))[l]'hl = R[n.val] := by
    simp only [List.getElem_take, List.getElem_drop]
    rfl
  rw [hcell] at hget
  subst record
  obtain ⟨_, v, hv, hp⟩ := hselected n (by dsimp [n]; omega) (by dsimp [n]; omega)
  change R[n.val].output.preparation.coordinator.selection.map Selection.view = some view at hview
  rw [hv] at hview
  have heq : v.view = view := Option.some.inj hview
  rw [← heq, hp]

private theorem roundInput_eq_of_fields
    {x y : RoundInput p rate} (hs : x.state = y.state) (hr : x.rows = y.rows)
    (hj : x.selected = y.selected) (ht : x.time.val = y.time.val)
    (hw : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  simp only at hs hr hj ht hw
  subst_vars
  congr
  exact Fin.ext ht

private theorem run_restart
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left count : ℕ) (hspan : start + (left + count) ≤ p.T)
    (mode : allActiveAtStart initial start) :
    let prefixRun := run initial rows J rewards start left (by omega) mode
    let restartMode := run_allActiveAtEnd initial rows J rewards start left (by omega) mode
    let suffix := run prefixRun.finalState rows J rewards (start + left) count (by omega) restartMode
    (run initial rows J rewards start (left + count) hspan mode).finalState = suffix.finalState ∧
      (run initial rows J rewards start (left + count) hspan mode).records =
        prefixRun.records ++ suffix.records := by
  dsimp only
  let prefixRun := run initial rows J rewards start left (by omega) mode
  let restartMode := run_allActiveAtEnd initial rows J rewards start left (by omega) mode
  induction count with
  | zero =>
      simp only [Nat.add_zero, run_zero_final, run_zero_records, List.append_nil]
      exact ⟨True.intro, True.intro⟩
  | succ count ih =>
      have hprev := ih (by omega)
      let x := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
        start (left + count) (by omega) mode
      let y := ReferenceAssignmentPayloadChronology.actualRunRecordAt prefixRun.finalState rows J rewards
        (start + left) count (by omega) restartMode
      have hinput : x.input = y.input := by
        apply roundInput_eq_of_fields
        · exact hprev.1
        · rfl
        · rfl
        · change start + (left + count) = start + left + count
          omega
        · rfl
      have hrecord : x = y := by
        change ReferenceAssignmentPayloadChronology.actualStepRecord x.input =
          ReferenceAssignmentPayloadChronology.actualStepRecord y.input
        rw [hinput]
      have hfullRecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start (left + count) (by omega) mode
      have htailRecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        prefixRun.finalState rows J rewards (start + left) count (by omega) restartMode
      have hfullState := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards start (left + count) (by omega) mode
      have htailState := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        prefixRun.finalState rows J rewards (start + left) count (by omega) restartMode
      constructor
      · change (run initial rows J rewards start ((left + count) + 1) _ mode).finalState = _
        rw [hfullState, htailState]
        exact congrArg (fun r => r.output.next) hrecord
      · change (run initial rows J rewards start ((left + count) + 1) _ mode).records = _
        rw [hfullRecords, htailRecords, hprev.2]
        change (prefixRun.records ++ _ ++ [x]) = prefixRun.records ++ (_ ++ [y])
        rw [hrecord, List.append_assoc]

private theorem run_records_congr
    {left right : ReferenceActivePhysicalStep.State p rate} {s t : ℕ}
    (hstate : left = right) (htime : s = t)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (count : ℕ)
    (leftSpan : s + count ≤ p.T) (leftMode : allActiveAtStart left s)
    (rightSpan : t + count ≤ p.T) (rightMode : allActiveAtStart right t) :
    (run left rows J rewards s count leftSpan leftMode).records =
      (run right rows J rewards t count rightSpan rightMode).records := by
  cases hstate
  cases htime
  rfl

/-- Restarting at any actual complete-suffix input reproduces the original
calendar slice. All state fields, rows, J, rewards and activation evidence
come from that same input; no fresh first configuration is substituted. -/
theorem complete_input_suffix_reindex
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (count : ℕ) (hcount : b.val + count ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let r := R[b.val]
    ∃ (hspan : r.input.time.val + count ≤ p.T)
      (mode : allActiveAtStart r.input.state r.input.time.val),
      (run r.input.state source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards r.input.time.val count hspan mode).records = (R.drop b.val).take count := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hlength : R.length = p.T - start :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h
  have hstart : start ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  have hbound : start + (b.val + count) ≤ p.T := by change b.val + count ≤ R.length at hcount; omega
  obtain ⟨hc, hbspan, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source b
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let mode : allActiveAtStart initial start := seed.activeAtStart
  let prefixRun := run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start b.val (by omega) mode
  have hstate : R[b.val].input.state = prefixRun.finalState := by
    change (R.get b).input.state = _
    rw [hrecord]
    rfl
  have htime : R[b.val].input.time.val = start + b.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b
  have hcomplete := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate source rewards C_star C_h hc)
  have hprefix : (run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start (b.val + count) hbound mode).records = R.take (b.val + count) := by
    obtain ⟨rest, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
      (b.val + count) (p.T - start - (b.val + count)) (by omega) mode
    have heq : b.val + count + (p.T - start - (b.val + count)) = p.T - start := by omega
    simp only [heq] at hp
    have hR : R = (run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start (p.T - start) (by omega) mode).records := hcomplete
    rw [hR, hp, List.take_append_of_le_length (by rw [run_record_count])]
    rw [List.take_of_length_le (by rw [run_record_count])]
  have hsplit := run_restart initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start b.val count hbound mode
  dsimp only at hsplit
  have hslice := congrArg (List.drop b.val) hsplit.2
  have hpLength : prefixRun.records.length = b.val := run_record_count _ _ _ _ _ _ _ _
  have hdrop : prefixRun.records.drop b.val = [] := List.drop_eq_nil_of_le (by omega)
  change (run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start (b.val + count) hbound mode).records.drop b.val =
      (prefixRun.records ++ _).drop b.val at hslice
  rw [hprefix, List.drop_take, Nat.add_sub_cancel_left, List.drop_append, hpLength,
    hdrop, Nat.sub_self, List.drop_zero, List.nil_append] at hslice
  have hspan : R[b.val].input.time.val + count ≤ p.T := by rw [htime]; omega
  refine ⟨hspan, R[b.val].input.active, ?_⟩
  change (run R[b.val].input.state source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards R[b.val].input.time.val count hspan R[b.val].input.active).records = (R.drop b.val).take count
  exact (run_records_congr hstate htime source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards count
    hspan R[b.val].input.active _ _).trans hslice.symm

/-- An actual accepted DOWN has the recovered fields in its actual physical
successor. This includes delayed acceptance after the assignment cutoff. -/
theorem complete_accepted_down_output
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (i : Fin (p.m - 1))
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).downInput = some logged)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw M scan registers lastService) :
    after.lastDown = some M ∧ after.S = registers.1 ∧ after.delta = lastService ∧
      after.backlog = registers.2 ∧ ∃ nextMemory : ActiveFollowerLifecycle.LocalMemory p,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val].output.next.followers i = .ordinary after nextMemory := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[j.val]
  have ht := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    r i logged cut after raw M scan registers lastService hlogged hdown houtcome
  obtain ⟨_, _, _, _, _, _, hafter⟩ := ActiveFollowerDownAcceptance.downTransition_accepted_checked
    p _ _ _ _ rate logged after raw M scan registers lastService ht
  obtain ⟨before, beforeMemory, atChoice, next, nextMemory, _, hactualChoice, _, _, houtput, _, hnext⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      (rate := rate) rewards C_star C_h source j i
  have hchoiceCall : (r.output.preparation.followers.followers i).configuration =
      .ordinary atChoice beforeMemory := hactualChoice
  have heq := (ReferenceFirstLiveDownNumericalRecovery.accepted_down_release_finish_frame
    r i atChoice beforeMemory hchoiceCall logged after cut raw M scan registers lastService
    hlogged hdown houtcome next nextMemory houtput).2
  refine ⟨?_, ?_, ?_, ?_, nextMemory, ?_⟩
  · rw [hafter]
  · rw [hafter]
  · rw [hafter]
  · rw [hafter]
  · rw [← heq]
    exact hnext

/-- The retained DOWN underlying actual UP acceptance has a checked replay
from its actual payload queue over the original calendar records. Logging on
the acceptance round is included before the buffer is cleared. -/
theorem complete_accepted_up_retained_down_recovery
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate) (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧ InstallationBirth R[b.val] c.payload ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      scan.endpoint = min
        (FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))))
        (R[j.val].input.time.val + 2) ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate (c.payload.downRecord i)
        logged scan.endpoint = .ok ⟨registers, lastService⟩ ∧
      registers = QueueReplay.replay (4 * rate.n)
        (0, c.payload.queues (c.payload.assignment.assigned i))
        (((R.drop b.val).take (scan.endpoint - (c.payload.sigma.val + 1))).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution
            (c.payload.downRecord i) i r))) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hk : k.val < R.length := k.isLt
  obtain ⟨c, b, j, seed, choice, memory, hc, hbj, hjk, hbirth, hretained,
    hseed, hdomain, hstatus, hstart, hchoice, hchoiceStatus, hvalid, hpair,
    htimes, hqueue, hwindow⟩ := complete_accepted_up_birth_buffer_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  let M := c.payload.downRecord i
  let s := R[b.val].input.time.val
  let l := j.val - b.val
  have hsigma : M.val.sigma = s + 1 := by
    have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] c.payload hbirth
    have hm := congrArg OrdinaryMessageCodec.DownFields.sigma (c.payload.downRecord_fields i)
    exact hm.trans (congrArg (fun n => n + 1) ht)
  have hMsigma : M.val.sigma = c.payload.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (c.payload.downRecord_fields i)
  obtain ⟨span, mode, hfull⟩ := complete_input_suffix_reindex
    (rate := rate) rewards C_star C_h source b (l + 1) (by dsimp [l]; omega)
  obtain ⟨prefixSpan, prefixMode, hprior⟩ := complete_input_suffix_reindex
    (rate := rate) rewards C_star C_h source b l (by dsimp [l]; omega)
  let current := ReferenceFollowerSparseEmissionRecovery.successorRecord R[b.val].input.state
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s l span mode
  have hphysical : ReferenceFollowerSparseEmissionRecovery.physicalRecords R[b.val].input.state
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s l span mode =
      (R.drop b.val).take (l + 1) := by
    rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords_eq_run_successor]
    exact hfull
  have hcurrent : current = R[j.val] := by
    have hg := congrArg (fun records : List (RoundRecord (p := p) (rate := rate)) => records[l]?) hphysical
    rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords,
      List.getElem?_append_right (by
        rw [ReferenceFollowerSparseEmissionRecovery.priorRun, run_record_count])]
      at hg
    have hindex : b.val + l = j.val := by dsimp [l]; omega
    simp only [ReferenceFollowerSparseEmissionRecovery.priorRun, run_record_count,
      Nat.sub_self, List.getElem?_cons_zero, List.getElem?_take, Nat.lt_succ_self, ite_true,
      List.getElem?_drop, hindex] at hg
    rw [List.getElem?_eq_getElem (show j.val < R.length from j.isLt)] at hg
    exact Option.some.inj hg
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hlogged, hdown, houtcome⟩ := hretained
  have hwindow' : ReferenceFollowerSparseEmissionRecovery.selectedViewInterval s
      (ReferenceFollowerSparseEmissionRecovery.priorRun R[b.val].input.state source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s l span mode).records := by
    have hbTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] c.payload hbirth
    change ReferenceFollowerSparseEmissionRecovery.selectedViewInterval s
      (run R[b.val].input.state source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s l _ mode).records
    rw [hprior]
    simpa only [s, l, hbTime] using hwindow
  have htimes' : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s := by
    have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] c.payload hbirth
    simpa only [ht, s] using htimes
  have hlogCurrent : (current.output.followers i).downInput = some logged := by rw [hcurrent]; exact hlogged
  have hdownCurrent : (current.output.followers i).down = some cut := by rw [hcurrent]; exact hdown
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    R[j.val] i logged cut after raw M scan registers lastService hlogged hdown houtcome
  have halign := R[j.val].output.preparation.follower_alignment i
  have htransition' : ActiveFollowerDownAcceptance.downTransition p i R[j.val].input.row
      R[j.val].input.time (R[j.val].output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged =
        .accepted logged after raw M scan registers lastService := by
    simpa only [halign.1, halign.2.1, halign.2.2.1] using htransition
  have hscan := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint i R[j.val].input.row
    R[j.val].input.time _ logged after raw M scan registers lastService htransition'
  have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = c.payload.sigma := by
    apply Fin.ext
    change M.val.sigma - 1 = c.payload.sigma.val
    rw [hMsigma, Nat.add_sub_cancel]
  obtain ⟨_, _, hrj⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source j
  have hrow : R[j.val].input.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    change (R.get j).input.row = _
    rw [hrj]
    rfl
  rw [hstartP, hrow] at hscan
  have hjtime : R[j.val].input.time.val = s + l := by
    have hb := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b
    have hj := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source j
    change R[b.val].input.time.val = _ at hb
    change R[j.val].input.time.val = _ at hj
    dsimp only [s, l]
    rw [hb, hj, Nat.add_assoc, Nat.add_sub_of_le hbj]
  have hle : scan.endpoint - M.val.sigma ≤ l + 1 := by
    have hmin := Nat.min_le_right
      (FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))))
      (R[j.val].input.time.val + 2)
    rw [← hscan, hjtime] at hmin
    have hdiff := Nat.sub_le_sub_right hmin M.val.sigma
    rw [hsigma] at hdiff
    omega
  have hresult := ReferenceFollowerSparseEmissionRecovery.accepted_window_checked_physical_queue
    R[b.val].input.state source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s l span mode i seed memory hseed hvalid hpair htimes' logged cut after raw M scan
    registers lastService hlogCurrent hdownCurrent houtcome hsigma hwindow'
  obtain ⟨hchecked, hreplay, _⟩ := hresult
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService, hc, hbj, hjk,
    hbirth, hlogged, hdown, houtcome, hscan, hchecked, ?_⟩
  rw [hphysical, List.take_take, Nat.min_eq_left hle, hMsigma, hqueue] at hreplay
  exact hreplay

end Bandits.Support.ReferenceCompleteFollowerRetainedDownRecovery

end
