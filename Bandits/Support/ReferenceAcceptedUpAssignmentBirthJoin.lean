/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAssignmentRetainedBirthProvenance

/-!
# Accepted UP assignment birth provenance

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-282,303-348`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
The historical join concerns the actual collection choice, receiver, sender,
and installation. It does not assert numerical queue or score identities.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceAcceptedUpAssignmentBirthJoin

open ConstructorDimensions
open ReferenceActivePhysicalStep

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

private theorem choice_executedTail
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    unfold ReferenceCollectionPhaseHistory.executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction

private theorem choice_selectedPayload
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ∃ selected : Selection x,
      (prepare x).coordinator.selection = some selected ∧ selected.view.payload = c.payload := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    obtain ⟨selected, hselected⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨selected, hselected, ?_⟩
    cases hc : (prepare x).coordinator with
    | first outcome =>
        cases outcome <;>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals contradiction
    | live r q base outcome =>
        cases outcome <;>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals try contradiction
        cases Option.some.inj hchoice
        simp only [hc, DispatchCut.selection, selectionAt, dite_true] at hselected
        cases Option.some.inj hselected
        rfl
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        all_goals try contradiction
        cases Option.some.inj hchoice
        simp only [hc, DispatchCut.selection] at hselected
        cases Option.some.inj hselected
        rfl
    | invalidCollectionCutoff =>
        simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        contradiction
    | dagger =>
        simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        contradiction

private theorem startRound_sigma
    (ledger started : Ledger rate) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound ledger t enabled raw = .success started) :
    started.sigma = ledger.sigma := by
  rw [CollectionCheckedExecution.startRound_success_candidate ledger started t enabled raw hstart]
  rfl

private theorem decodeUp_sigma
    (ledger decoded : Ledger rate) (i : Fin (p.m - 1))
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger i (some U) = .success decoded) :
    U.val.sigma = ledger.sigma := by
  by_contra hnot
  simp [CoordinatorCollectionLedger.decodeUp, CoordinatorCollectionLedger.acceptUpCheck,
    hnot] at hdecode
  split at hdecode <;> try contradiction
  split at hdecode <;> contradiction

private theorem acceptedUp_choice_sigma
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp x i U) :
    U.val.sigma = c.preLedger.sigma := by
  obtain ⟨tail, recording, started, decoded, bank, htail, hrecording, hstarted,
    hreceived, hparsed, hindex⟩ := haccepted
  have htailEq := Option.some.inj ((choice_executedTail x c hchoice).symm.trans htail)
  cases htailEq
  have hcheck := ReferenceCollectionSegmentExtraction.receiveUp_input_check x started
    (by rw [hreceived]; intro h; cases h)
  rw [ReferenceCollectionSegmentExtraction.receiveUp_filtered x started hcheck] at hreceived
  have hdecode : CoordinatorCollectionLedger.decodeUp started (upSenderIndex x)
      (ReferenceCollectionSegmentExtraction.effectiveParse x started) = .success decoded := by
    cases hd : CoordinatorCollectionLedger.decodeUp started (upSenderIndex x)
        (ReferenceCollectionSegmentExtraction.effectiveParse x started) with
    | invalid =>
        simp only [hd, CoordinatorUpReception.packDecodeResult] at hreceived
        cases hreceived
    | rejected out =>
        simp only [hd, CoordinatorUpReception.packDecodeResult] at hreceived
        cases hreceived
    | success out =>
        simp only [hd, CoordinatorUpReception.packDecodeResult,
          CoordinatorCollectionLedger.Checked.success.injEq, Prod.mk.injEq] at hreceived
        exact congrArg CoordinatorCollectionLedger.Checked.success hreceived.1
  change ReferenceCollectionSegmentExtraction.effectiveParse x started = some U at hparsed
  rw [hparsed] at hdecode
  exact (decodeUp_sigma started decoded (upSenderIndex x) U hdecode).trans
    (startRound_sigma c.preLedger started _ _ _ hstarted)

private theorem retainedDown_selectedPayload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (prior : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i prior) :
    ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      prior = selected.view.payload.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hinput, hdown, haccepted⟩ := hretained
  obtain ⟨choice, memory, actualLogged, hconfiguration, hunoccupied, hlogging,
    hactualInput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hactualIndex := (record.output.preparation.follower_alignment i).2.1
  have hloggedEq : actualLogged = logged := Option.some.inj (hactualInput.symm.trans hinput)
  subst actualLogged
  rw [hcut] at haccepted
  obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  rw [hview] at haccepted
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  have hmap : record.output.preparation.coordinator.selection.map Selection.view = some view := hview
  obtain ⟨selected, hselection, hselectedView⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨selected, hselection, ?_⟩
  have hmessage : prior = view.payload.downRecord i := by
    simpa only [hactualIndex] using hfields.1
  simpa only [hselectedView] using hmessage

private theorem run_record_time
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.length) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records[k.val].input.time.val = start + k.val := by
  have ht := ReferenceActivePhysicalHorizon.run_time_values
    initial rows selected rewards start count hspan hmode
  have hindex : k.val < count := by
    simpa only [ReferenceActivePhysicalHorizon.run_record_count] using k.isLt
  have hget := congrArg (fun times : List ℕ => times[k.val]?) ht
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar start count)[k.val]? =
      some (start + k.val) := by
    rw [List.getElem?_eq_getElem (by
      simpa only [ReferenceActivePhysicalHorizon.calendar, List.length_range'] using hindex)]
    exact congrArg some (List.getElem_range'_1 _ _)
  rw [hcalendar] at hget
  simp only [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some] at hget
  exact Option.some.inj hget

/-- An actually accepted UP belongs to the same installation as the actual
collection choice. The ordinary state is the detecting-round input, before
the interruption at arm choice, and no follower output assumption is used. -/
theorem complete_accepted_up_birth_join
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    let R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown (R[j.val]'j.isLt) i (c.payload.downRecord i) ∧
      (R[k.val]'k.isLt).input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      U.val.sigma = c.preLedger.sigma ∧ c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.preLedger.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma bits ∧
      (match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installed _) => c.preLedger.baseScore = installed.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          c.preLedger.baseScore = installed.retainedBaseScore
      | _ => False) := by
  classical
  have hreplySigma := acceptedUp_choice_sigma _ c hchoice i U haccepted
  have hprovenance :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h source k c hchoice
  dsimp only at hprovenance ⊢
  obtain ⟨b, hbk, hbirth, harm, hsigma, hcutoff, hbase⟩ := hprovenance
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).1 (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial hcanonical
      revert hchoice haccepted hbk hbirth hbase
      revert b
      revert k
      rw [hrecords]
      intro k b hchoice haccepted hbk hbirth hbase
      obtain ⟨j, hjk, prior, hretained, happlied, hpriorSigma, sender, offered, memory,
        hsender, hconfiguration, hunoccupied, hoff, hstart, hstarted, hS, hdelta, hq,
        hlast, hpriorSigma', hpositive⟩ :=
        ReferenceAcceptedUpFollowerHistory.run_acceptedUp_prior_down
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ _ _ _ i (seed.followers i) (seed.memory i)
          (seed.configuration i) (seed.lastDown_none i) k U haccepted
      obtain ⟨oldSelected, holdSelected, hpriorRecord⟩ :=
        retainedDown_selectedPayload _ i prior hretained
      obtain ⟨currentSelected, hcurrentSelected, hcurrentPayload⟩ :=
        choice_selectedPayload _ c hchoice
      have hcurrentSelection :
          ((ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            _ _ _ _).records[k.val]).output.preparation.coordinator.selection =
              some currentSelected := by
        rw [((ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          _ _ _ _).records[k.val]).output_eq]
        exact hcurrentSelected
      have hpriorStart : prior.val.sigma = oldSelected.view.payload.sigma.val + 1 := by
        rw [hpriorRecord]
        rfl
      have hselectedSigma : oldSelected.view.payload.sigma.val =
          currentSelected.view.payload.sigma.val := by
        have hcurrentSigma := congrArg (fun payload : Payload rate => payload.sigma.val)
          hcurrentPayload
        omega
      have hpayload :=
        ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ _ _ _ seed.coordinatorFirst _ _ oldSelected currentSelected
          (List.getElem_mem j.isLt) (List.getElem_mem k.isLt)
          holdSelected hcurrentSelection hselectedSigma
      have holdPayload : oldSelected.view.payload = c.payload := hpayload.trans hcurrentPayload
      have hprior : prior = c.payload.downRecord i := by
        rw [hpriorRecord, holdPayload]
      obtain ⟨oldBirth, holdBirthMem, holdBirth, holdBirthTime, holdBefore⟩ :=
        ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ _ _ _ seed.coordinatorFirst _ oldSelected
          (List.getElem_mem j.isLt) holdSelected
      have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hbirth
      have hbirthEq : oldBirth =
          (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            _ _ _ _).records[b.val] := by
        apply ReferenceAssignmentPayloadChronology.run_records_time_injective
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards _ _ _ _ holdBirthMem (List.getElem_mem b.isLt)
        rw [holdBirthTime, holdPayload, hbirthTime]
      have hbirthBefore :
          ((ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            _ _ _ _).records[b.val]).input.time.val ≤
          ((ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            _ _ _ _).records[j.val]).input.time.val := by
        rw [← hbirthEq, holdBirthTime]
        exact holdBefore
      have hbtime := run_record_time initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ _ _ _ b
      have hjtime := run_record_time initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ _ _ _ j
      have hbj : b.val ≤ j.val := by omega
      have hactualChoice :
          (ReferenceFollowerFixedReply.actualChoice
            ((ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              _ _ _ _).records[k.val]) i).configuration = .ordinary offered memory := by
        rw [← hsender]
        exact hconfiguration
      obtain ⟨F, mu, hinput, hframe, hstatus⟩ :=
        ReferenceFollowerReplyChronology.record_input_to_choice _ i offered memory hactualChoice
      have hlastFrame : offered.lastDown = F.lastDown := congrArg Prod.fst hframe
      have hSFrame : offered.S = F.S := congrArg (fun r => r.2.1) hframe
      have hdeltaFrame : offered.delta = F.delta := congrArg (fun r => r.2.2.1) hframe
      have hqFrame : offered.backlog = F.backlog := congrArg (fun r => r.2.2.2) hframe
      refine ⟨b, j, F, mu, hbj, hjk, hbirth, ?_, hinput, ?_, hreplySigma, hsigma,
        hS.trans hSFrame, hdelta.trans hdeltaFrame, hq.trans hqFrame, hcutoff, hbase⟩
      · simpa only [hprior] using hretained
      · exact hlastFrame.symm.trans (hlast.trans (congrArg some hprior))

end Bandits.Support.ReferenceAcceptedUpAssignmentBirthJoin
