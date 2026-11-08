/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAssignmentMassComposer

import Lean.Elab.Tactic.Omega

/-!
# Historical mass for actual ordinary follower inputs

This module proves the conditional input and choice projections from the
literal complete physical suffix. It keeps the historical installation,
payload, base vector, and retained DOWN event in one witness.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteOrdinaryFollowerMass

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

private abbrev Payload := ReferenceActivePhysicalStep.Payload rate

private abbrev Label := Fin (p.m - 1)

private abbrev Records (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h

private theorem actual_follower_mass_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (row : CompletePublicTable.CompleteRow p) (start n : ℕ)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hComplete : R = ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)
    (runInitial : ReferenceActivePhysicalHorizon.State p rate)
    (runCount : ℕ) (runSpan : start + runCount ≤ p.T)
    (runMode : ReferenceActivePhysicalHorizon.allActiveAtStart runInitial start)
    (runFirst : runInitial.coordinator = .first)
    (hRun : R = (ReferenceActivePhysicalHorizon.run runInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start runCount runSpan runMode).records)
    (hn : n < R.length)
    (hrow : R[n].input.row = row)
    (htime : R[n].input.time.val = start + n)
    (i : Label) (F : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : R[n].input.state.followers i = .ordinary F memory)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : R[n].output.next.followers i = .ordinary next nextMemory)
    (M : DownRecord) (hnextDown : next.lastDown = some M)
    (hcurrent : F.lastDown = some M →
      ∃ (b j : Fin R.length) (P : Payload) (beta : Label → ℕ),
        b.val ≤ j.val ∧ j.val < n ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧
        M = P.downRecord i ∧
        beta i + F.S + F.backlog ≤
          min (start + n)
            (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p ∧
        F.delta ≤ D p) :
    ∃ (b j : Fin R.length) (P : Payload) (beta : Label → ℕ),
      b.val ≤ j.val ∧ j.val ≤ n ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧
      M = P.downRecord i ∧
      beta i + next.S + next.backlog ≤
        min (start + n + 1)
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p ∧
    next.delta ≤ D p := by
  subst R
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let record := R[n]
  let input := record.input
  let prepared := (ReferenceActivePhysicalStep.prepare input).followers.followers i
  let view := (ReferenceActivePhysicalStep.prepare input).coordinator.downView
  let observation := (ReferenceActivePhysicalStep.prepare input).feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hnext' : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    rw [record.output_eq] at hnext
    exact hnext
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hrelease,
    hfinishInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory hnext'
  have hprepareEq : prepared = DeclaredFollowerLocalRound.prepare rate i input.row
      (input.state.activations i) input.time (input.active i) (input.state.followers i) :=
    (ReferenceActivePhysicalStep.prepare input).followers.followers_eq i
  rw [hprepareEq] at hchoice
  obtain ⟨before, beforeMemory, hinput', hstart, hprepareFrame, _hprepareUnoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i input.row
      (input.state.activations i) input.time (input.active i) (input.state.followers i)
      choice choiceMemory hchoice
  have hbeforeEq : before = F ∧ beforeMemory = memory := by
    have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinput.symm.trans hinput')
    exact ⟨hsame.1.symm, hsame.2.symm⟩
  rcases hbeforeEq with ⟨rfl, rfl⟩
  have halignment := (ReferenceActivePhysicalStep.prepare input).follower_alignment i
  have hrecord' : (ReferenceActivePhysicalStep.recordFollower view i input.row
      (input.state.activations i) input.time (input.active i) prepared.arm observation choice).result =
      .ok post := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1,
      halignment.2.2.2] using hrecord
  have hrelease' : DeclaredFollowerLocalRound.releaseAndFinish rate i input.row input.time
      observation choice choiceMemory post = .ok (next, nextMemory) := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1] using hrelease
  have hfinishInput' : (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
      (ReferenceActivePhysicalStep.recordFollower view i input.row (input.state.activations i)
        input.time (input.active i) prepared.arm observation choice).downInput := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1,
      halignment.2.2.2] using hfinishInput
  have hfinishDown' : (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
      (ReferenceActivePhysicalStep.recordFollower view i input.row (input.state.activations i)
        input.time (input.active i) prepared.arm observation choice).down := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1,
      halignment.2.2.2] using hfinishDown
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    i input.row input.time observation choice post next choiceMemory nextMemory hrelease'
  have hnextLast : next.lastDown = post.lastDown := congrArg Prod.fst hframe.1
  have hnextS : next.S = post.S := congrArg (fun r => r.2.1) hframe.1
  have hnextDelta : next.delta = post.delta := congrArg (fun r => r.2.2.1) hframe.1
  have hnextQueue : next.backlog = post.backlog := congrArg (fun r => r.2.2.2) hframe.1
  obtain hpostLast | ⟨logged, cut, raw, accepted, scan, registers, lastService,
      hdownInput, hdown, hcut, haccepted, _hstrict, hacceptedLast⟩ :=
    ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      view i input.row (input.state.activations i) input.time (input.active i)
      prepared.arm observation choice post hrecord'
  · cases hbeforeDown : before.lastDown with
    | none =>
        have hchoiceDown : choice.lastDown = none := by
          have h := congrArg Prod.fst hprepareFrame
          change choice.lastDown = before.lastDown at h
          simpa [hbeforeDown] using h
        have hpostDown : post.lastDown = none := hpostLast.1.trans hchoiceDown
        have hnextDownNone : next.lastDown = none := hnextLast.trans hpostDown
        rw [hnextDownNone] at hnextDown
        cases hnextDown
    | some old =>
      have hchoiceDown : choice.lastDown = some old := by
        have h := congrArg Prod.fst hprepareFrame
        change choice.lastDown = before.lastDown at h
        simpa [hbeforeDown] using h
      have hpostDown : post.lastDown = some old := hpostLast.1.trans hchoiceDown
      have hnextDownOld : next.lastDown = some old := hnextLast.trans hpostDown
      have holdEq : old = M := Option.some.inj (hnextDownOld.symm.trans hnextDown)
      subst old
      obtain ⟨b, j, P, beta, hbj, hjn, hbirth, hbase, hretained, hmessage, hmass, hdelta⟩ :=
        hcurrent hbeforeDown
      have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
        rate rewards C_star C_h source ⟨n, hn⟩ i before beforeMemory hinput' M hbeforeDown
      have htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
          stamp.val + 1 = input.time.val ∧
            beforeMemory.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val input.row stamp⟩ := by
        intro hbusy
        obtain ⟨stamp, hstamp, hread⟩ :=
          ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
            rate rewards C_star C_h source ⟨n, hn⟩ i before beforeMemory hinput' hbusy
        refine ⟨stamp, ?_, ?_⟩
        · simpa [record, input] using hstamp
        · simpa [record, input] using hread
      have hchoicePhase := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
        input.time input.row before choice beforeMemory choiceMemory M hbeforeDown hphase htoken hstart
      have hchoiceS : choice.S = before.S := congrArg (fun r => r.2.1) hprepareFrame
      have hchoiceDelta : choice.delta = before.delta := congrArg (fun r => r.2.2.1) hprepareFrame
      have hchoiceQueue : choice.backlog = before.backlog := congrArg (fun r => r.2.2.2) hprepareFrame
      have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = P.sigma := by
        rw [hmessage]
        apply Fin.ext
        have hf := ActiveFollowerDownAcceptance.downStart_val_add_one p rate (P.downRecord i)
        rw [P.downRecord_fields i] at hf
        exact Nat.add_right_cancel hf
      rw [hstartP, hrow] at hchoicePhase
      by_cases hunoccupied : choice.status = .unoccupied
      · obtain ⟨hreply, _hstatus⟩ := hpostLast.2 hunoccupied
        have hnextReply : ReferenceFollowerReplyChronology.reply next =
            ReferenceFollowerReplyChronology.reply choice := hframe.1.trans hreply
        have hnextChoiceS : next.S = choice.S := by
          have h := congrArg (fun r => r.2.1) hnextReply
          exact h
        have hnextChoiceDelta : next.delta = choice.delta := by
          have h := congrArg (fun r => r.2.2.1) hnextReply
          exact h
        have hnextChoiceQueue : next.backlog = choice.backlog := by
          have h := congrArg (fun r => r.2.2.2) hnextReply
          exact h
        have hmass' : beta i + next.S + next.backlog ≤
            min (start + n + 1)
              (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p := by
          have hmono : min (start + n)
                (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) ≤
              min (start + n + 1)
                (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) :=
            min_le_min (Nat.le_succ _) le_rfl
          calc
            beta i + next.S + next.backlog = beta i + before.S + before.backlog := by
              rw [hnextChoiceS, hnextChoiceQueue, hchoiceS, hchoiceQueue]
            _ ≤ min (start + n)
                (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p := hmass
            _ ≤ min (start + n + 1)
                (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                  (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p :=
              Nat.mul_le_mul_right (D p) hmono
        have hdelta' : next.delta ≤ D p := by
          calc
            next.delta = before.delta := hnextChoiceDelta.trans hchoiceDelta
            _ ≤ D p := hdelta
        exact ⟨b, ⟨j, ⟨P, ⟨beta, hbj, Nat.le_of_lt hjn,
          hbirth, hbase, hretained, hmessage, hmass', hdelta'⟩⟩⟩⟩
      · have hserviceResult : ∃ result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta
            rate.n i input.row (input.state.activations i) input.time observation choice,
          ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
            i input.row (input.state.activations i) input.time observation choice = .success result ∧
          result.output = post := by
          have hc := hrecord'
          rw [ReferenceActivePhysicalStep.recordFollower_result] at hc
          have hflow : DeclaredFollowerLocalRound.recordOrServiceThenDown rate i input.row
              (input.state.activations i) input.time (input.active i) prepared.arm observation choice =
              .ok post := by
            simpa [ReferenceDownReception.loggingThenReferenceDown, hunoccupied] using hc
          unfold DeclaredFollowerLocalRound.recordOrServiceThenDown at hflow
          simp [hunoccupied] at hflow
          cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
              rate.n rate.n_scale i input.row (input.state.activations i) input.time observation choice with
          | failure => simp [hs] at hflow
          | success result =>
              simp only [hs, Except.ok.injEq] at hflow
              exact ⟨result, rfl, hflow⟩
        obtain ⟨result, hservice, hresult⟩ := hserviceResult
        let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
        have htimeInput : input.time.val = start + n := by
          simpa [input, record, R] using htime
        have hcredit : beta i + choice.S + choice.backlog ≤ min input.time.val (u - 1) * D p := by
          have hs := hmass
          rw [← hchoiceS, ← hchoiceQueue] at hs
          rw [← htime] at hs
          simpa [u] using hs
        have hserviceMass := ReferenceAssignmentFollowerMassSteps.service_mass_of_choice_cutoff
          i input.row (input.state.activations i) input.time observation choice result u (beta i)
          hcredit (by simpa [u] using hchoicePhase)
        have hmass' : beta i + next.S + next.backlog ≤ min (start + n + 1) (u - 1) * D p := by
          rw [hnextS, hnextQueue, ← hresult]
          simpa [u, htimeInput] using hserviceMass.1
        have hdelta' : next.delta ≤ D p := by
          rw [hnextDelta, ← hresult]
          exact hserviceMass.2
        refine ⟨b, ?_⟩
        refine ⟨j, ?_⟩
        refine ⟨P, ?_⟩
        refine ⟨beta, ?_⟩
        simpa [u] using ⟨hbj, Nat.le_of_lt hjn, hbirth, hbase, hretained,
          hmessage, hmass', hdelta'⟩
  · have hacceptedEq : accepted = M := by
      have hpost : post.lastDown = some M := hnextLast.symm.trans hnextDown
      exact Option.some.inj (hacceptedLast.symm.trans hpost)
    subst accepted
    have hdiagnosticInput : (record.output.followers i).downInput = some logged := by
      rw [record.output_eq]
      exact hfinishInput'.trans hdownInput
    have hdiagnosticDown : (record.output.followers i).down = some cut := by
      rw [record.output_eq]
      exact hfinishDown'.trans hdown
    have hdiagnostic := ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      record i cut hdiagnosticDown
    obtain ⟨actualChoice, actualMemory, actualLogged, _hconfiguration, _hunoccupied,
      _hlogging, hactualInput, hactualCut⟩ := hdiagnostic
    have hloggedEq : actualLogged = logged := Option.some.inj (hactualInput.symm.trans hdiagnosticInput)
    rw [hloggedEq] at hactualCut
    have hactualAccepted : (ReferenceDownReception.referenceDownCut p view i input.row
        input.time observation rate logged).outcome = .accepted logged post raw M scan registers lastService := by
      rw [← hcut]
      exact haccepted
    obtain ⟨selectedView, hview⟩ :=
      ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
        view i input.row input.time
        observation logged logged post raw M scan registers lastService hactualAccepted
    have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields selectedView i
      input.row input.time observation logged logged post raw M scan registers
      lastService (by simpa [hview] using hactualAccepted)
    have hselected : record.output.preparation.coordinator.selection.map Selection.view =
        some selectedView := by
      have hview' : record.output.preparation.coordinator.downView = some selectedView := by
        rw [record.output_eq]
        exact hview
      simpa only [DispatchCut.downView] using hview'
    cases hselection : record.output.preparation.coordinator.selection with
    | none => simp [hselection] at hselected
    | some selected =>
      have hselectedView : selected.view = selectedView := by
        simpa [hselection] using hselected
      subst selectedView
      have hrecordInRun : record ∈
          (ReferenceActivePhysicalHorizon.run runInitial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            start runCount runSpan runMode).records := by
        rw [← hRun]
        exact List.getElem_mem hn
      obtain ⟨birthRecord, hbirthMem, hbirth, hbirthTime, hbirthBefore⟩ :=
        ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
          runInitial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start runCount runSpan runMode runFirst record selected hrecordInRun
          hselection
      rw [← hRun] at hbirthMem
      obtain ⟨bval, hbval, hbget⟩ := List.mem_iff_getElem.mp hbirthMem
      let b : Fin R.length := ⟨bval, hbval⟩
      have hbrecord : R[b.val] = birthRecord := by simpa [b] using hbget
      have hbirthR : ReferenceAssignmentPayloadPersistence.InstallationBirth
          R[b.val] selected.view.payload := by
        rw [hbrecord]
        exact hbirth
      obtain ⟨beta, hbase, _hqueues, _hassigned, hdownCredit⟩ :=
        ReferenceAssignmentMassComposer.complete_assignment_birth_mass
          rate rewards C_star C_h source b selected.view.payload hbirthR
      have hcredit : beta i + M.val.q ≤ (M.val.sigma - 1) * D p := by
        rw [hfields.1]
        exact hdownCredit i
      have hdiagnosticDown' : (record.output.followers i).down = some cut := hdiagnosticDown
      obtain ⟨_hlast, hmassAccepted, hdeltaAccepted, _hphase⟩ :=
        ReferenceAssignmentFollowerMassSteps.record_accepted_down_mass record i logged cut post raw
          M scan registers lastService (beta i) hcredit hdiagnosticInput hdiagnosticDown' haccepted
      have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = selected.view.payload.sigma := by
        rw [hfields.1]
        apply Fin.ext
        have hf := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
          (selected.view.payload.downRecord i)
        rw [selected.view.payload.downRecord_fields i] at hf
        exact Nat.add_right_cancel hf
      have htimeInput : input.time.val = start + n := by
        simpa [input, record, R] using htime
      rw [hstartP, hrow, htimeInput] at hmassAccepted
      have hcurrentTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source ⟨n, hn⟩
      have hbtime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source b
      have hb_le_n : b.val ≤ n := by
        have hbirthTime' :
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b.val =
            selected.view.payload.sigma.val := by
          have hbt := hbirthTime
          rw [← hbrecord] at hbt
          rw [hbtime] at hbt
          exact hbt
        have hselectedBefore : selected.view.payload.sigma.val ≤
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n := by
          rw [← hcurrentTime]
          exact hbirthBefore
        exact Nat.le_of_add_le_add_left (hbirthTime'.trans_le hselectedBefore)
      have hmassNext : beta i + next.S + next.backlog ≤
          min (start + n + 1)
            (FollowerCutoffScan.firstCutoff p rate.eta.val selected.view.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) * D p := by
        rw [hnextS, hnextQueue]
        exact hmassAccepted
      have hdeltaNext : next.delta ≤ D p := by
        rw [hnextDelta]
        exact hdeltaAccepted
      have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown R[n] i M := by
        exact ⟨logged, cut, post, raw, scan, registers, lastService,
          hdiagnosticInput, hdiagnosticDown, haccepted⟩
      have hmsg : M = selected.view.payload.downRecord i := hfields.1
      refine ⟨b, ?_⟩
      refine ⟨⟨n, hn⟩, ?_⟩
      refine ⟨selected.view.payload, ?_⟩
      refine ⟨beta, ?_⟩
      constructor
      · simpa using hb_le_n
      · constructor
        · rfl
        · constructor
          · simpa [record, b] using hbirthR
          · constructor
            · simpa [record, b] using hbase
            · constructor
              · simpa [record] using hretained
              · constructor
                · exact hmsg
                · constructor
                  · exact hmassNext
                  · exact hdeltaNext

private theorem complete_ordinary_follower_input_mass_at
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (row : CompletePublicTable.CompleteRow p) (start : ℕ)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hComplete : R = ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)
    (runInitial : ReferenceActivePhysicalHorizon.State p rate)
    (runCount : ℕ) (runSpan : start + runCount ≤ p.T)
    (runMode : ReferenceActivePhysicalHorizon.allActiveAtStart runInitial start)
    (runFirst : runInitial.coordinator = .first)
    (hRun : R = (ReferenceActivePhysicalHorizon.run runInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start runCount runSpan runMode).records)
    (hconnected : ReferenceActivePhysicalHorizon.Connected runInitial R
      (ReferenceActivePhysicalHorizon.run runInitial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start runCount runSpan runMode).finalState)
    (hdata : ∀ n (hn : n < R.length),
      R[n].input.row = row ∧ R[n].input.time.val = start + n)
    (hseed : ∀ (i : Label) (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      runInitial.followers i = .ordinary F memory → F.lastDown = none) :
    ∀ n, ∀ (hn : n < R.length),
      ∀ (i : Label) (F : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p) (M : DownRecord),
        (R[n]'hn).input.state.followers i = .ordinary F memory → F.lastDown = some M →
        ∃ (b j : Fin R.length) (P : Payload) (beta : Label → ℕ),
          b.val ≤ j.val ∧ j.val < n ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
          ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧
          M = P.downRecord i ∧
          beta i + F.S + F.backlog ≤
            min (R[n]'hn).input.time.val
              (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (R[n]'hn).input.row) - 1) * D p ∧
          F.delta ≤ D p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn i F memory M hinput hdown
      cases n with
      | zero =>
          have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
            hconnected 0 hn
          have hfirst : R[0].input.state = runInitial := by
            change R[0].input.state = runInitial at hprefix
            exact hprefix
          have hconfiguration : runInitial.followers i = .ordinary F memory := by
            rw [← hfirst]
            exact hinput
          have hnone := hseed i F memory hconfiguration
          rw [hnone] at hdown
          cases hdown
      | succ n =>
          have hnprev : n < R.length := by omega
          have hadj : R[n + 1].input.state = R[n].output.next := by
            have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output
              hconnected n hnprev
            rw [List.drop_eq_getElem_cons (show n + 1 < R.length by omega)] at hdrop
            exact hdrop.1
          have hnext : R[n].output.next.followers i = .ordinary F memory := by
            have hcurrentInput : (R[n + 1]).input.state.followers i = .ordinary F memory := hinput
            rw [hadj] at hcurrentInput
            exact hcurrentInput
          obtain ⟨before, beforeMemory, hbeforeInput, _hstart, _hfreeze, _happlied⟩ :=
            ReferenceFollowerReplyChronology.record_ordinary_chronology
              R[n] i F memory hnext
          have hcurrent : before.lastDown = some M →
              ∃ (b j : Fin R.length) (P : Payload) (beta : Label → ℕ),
                b.val ≤ j.val ∧ j.val < n ∧
                ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
                ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧
                M = P.downRecord i ∧
                beta i + before.S + before.backlog ≤
                min (R[n]'hnprev).input.time.val
                    (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (R[n]'hnprev).input.row) - 1) * D p ∧
                before.delta ≤ D p := by
            intro hbeforeDown
            exact ih n (by omega) hnprev i before beforeMemory M hbeforeInput hbeforeDown
          obtain ⟨hrow, htime⟩ := hdata n hnprev
          have hcurrent' := hcurrent
          rw [htime, hrow] at hcurrent'
          have hstep := actual_follower_mass_step rewards C_star C_h source row start n R
            hComplete runInitial runCount runSpan runMode runFirst hRun hnprev hrow htime
            i before beforeMemory hbeforeInput F memory hnext M hdown hcurrent'
          obtain ⟨b, j, P, beta, hbj, hjle, hbirth, hbase, hretained, hmessage,
            hmass, hdelta⟩ := hstep
          obtain ⟨hrowNext, htimeNext⟩ := hdata (n + 1) (by omega)
          refine ⟨b, ?_⟩
          refine ⟨j, ?_⟩
          refine ⟨P, ?_⟩
          refine ⟨beta, ?_⟩
          constructor
          · exact hbj
          · constructor
            · omega
            · constructor
              · exact hbirth
              · constructor
                · exact hbase
                · constructor
                  · exact hretained
                  · constructor
                    · exact hmessage
                    · constructor
                      · simpa [htimeNext, hrowNext, Nat.add_assoc] using hmass
                      · exact hdelta

/-- An actual ordinary INPUT with a retained DOWN has a historical birth,
base-score vector, and retained acceptance whose same follower component
bounds the exact elapsed input mass. -/
theorem complete_ordinary_follower_input_mass
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary state memory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M) :
    ∃ (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
      (P : ReferenceActivePhysicalStep.Payload rate) (beta : Fin (p.m - 1) → ℕ),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] = some beta ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val] i M ∧
      M = P.downRecord i ∧
      beta i + state.S + state.backlog ≤
        min (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val].input.row) - 1) * D p ∧
      state.delta ≤ D p := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hempty : R = [] := by
        simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch]
      have hk : k.val < ([] : List (ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate))).length := by
        simpa [R, hempty] using k.isLt
      simp at hk
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan seed.activeAtStart
      have hComplete : R = ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h := rfl
      have hRun : R = execution.records := by
        simpa [R, execution] using hrecords
      have hconnected : ReferenceActivePhysicalHorizon.Connected initial R
          execution.finalState := by
        rw [hRun]
        exact execution.connected
      obtain ⟨_hfirst, _hactive, hfollowers⟩ :=
        ReferenceAssignmentFollowerMassSteps.actual_launch_mass_seed
          rate rewards C_star C_h source hc
      have hseed : ∀ (j : Label) (F : ReferencePrelaunchFollower.State p rate.eta)
          (mu : ActiveFollowerLifecycle.LocalMemory p),
          initial.followers j = .ordinary F mu → F.lastDown = none := by
        intro j F mu hconfiguration
        exact (hfollowers j F mu hconfiguration).1
      let row := source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      have hdata : ∀ n (hn : n < R.length),
          R[n].input.row = row ∧ R[n].input.time.val = start + n := by
        intro n hn
        have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨n, hn⟩
        have htime' : R[n].input.time.val = start + n := by
          simpa [R, start] using htime
        have hmem : R[n] ∈ execution.records := by
          rw [← hRun]
          exact List.getElem_mem hn
        obtain ⟨hrows, hselected, _hrewards⟩ :=
          ReferenceActivePhysicalHorizon.run_record_inputs initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            start (p.T - start) hspan seed.activeAtStart R[n] hmem
        have hrow : R[n].input.row = row := by
          change R[n].input.rows R[n].input.selected = _
          rw [hrows, hselected]
        exact ⟨hrow, htime'⟩
      have hresult := complete_ordinary_follower_input_mass_at rewards C_star C_h source
        row start R hComplete initial (p.T - start) hspan seed.activeAtStart
        seed.coordinatorFirst hRun hconnected hdata hseed k.val k.isLt i state memory M
        hinput hdown
      have hrowK := (hdata k.val k.isLt).1
      have htimeK := (hdata k.val k.isLt).2
      simpa [R, hrowK, htimeK, Nat.add_assoc] using hresult

/-- Project the INPUT mass witness to CHOICE through the actual public
INPUT-to-CHOICE reply frame. The historical birth and base vector are reused
unchanged; no second history induction is needed. -/
theorem complete_ordinary_follower_choice_mass
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] i).configuration = .ordinary choice choiceMemory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : choice.lastDown = some M) :
    ∃ (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
      (P : ReferenceActivePhysicalStep.Payload rate) (beta : Fin (p.m - 1) → ℕ),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] = some beta ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val] i M ∧
      M = P.downRecord i ∧
      beta i + choice.S + choice.backlog ≤
        min (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val].input.row) - 1) * D p ∧
      choice.delta ≤ D p := by
  obtain ⟨before, beforeMemory, hinput, hreply, _hunoccupied⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val]
      i choice choiceMemory hchoice
  have hbeforeDown : before.lastDown = some M := by
    have hlast := congrArg Prod.fst hreply
    exact hlast.symm.trans hdown
  obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, hmass, hdelta⟩ :=
    complete_ordinary_follower_input_mass rewards C_star C_h source k i before beforeMemory
      hinput M hbeforeDown
  have hS : choice.S = before.S := congrArg (fun r => r.2.1) hreply
  have hdeltaReply : choice.delta = before.delta := congrArg (fun r => r.2.2.1) hreply
  have hbacklog : choice.backlog = before.backlog := congrArg (fun r => r.2.2.2) hreply
  refine ⟨b, ?_⟩
  refine ⟨j, ?_⟩
  refine ⟨P, ?_⟩
  refine ⟨beta, ?_⟩
  constructor
  · exact hbj
  · constructor
    · exact hjk
    · constructor
      · exact hbirth
      · constructor
        · exact hbase
        · constructor
          · exact hretained
          · constructor
            · exact hmessage
            · constructor
              · calc
                  beta i + choice.S + choice.backlog = beta i + before.S + before.backlog := by
                    rw [hS, hbacklog]
                  _ ≤ _ := hmass
              · rw [hdeltaReply]
                exact hdelta

end Bandits.Support.ReferenceCompleteOrdinaryFollowerMass

end
