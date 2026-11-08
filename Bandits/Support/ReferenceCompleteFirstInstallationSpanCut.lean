/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory

import Lean.Elab.Tactic.Omega

/-!
# The retained first-installation cutoff span

This is an internal structural join on the original complete physical suffix.
It identifies the actual first cutoff segment and the retained selector at a
later chosen record. It does not assert the installation-interval endpoint or
any numerical regret bound.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFirstInstallationSpanCut

open Bandits.Support.ConstructorDimensions

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A retained output and absence of an installation exclude even failed
later sampler invocations on the actual record. -/
private theorem record_parameters_none_of_retained_no_birth
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate)
    (hret : storedPayload record.output.next.coordinator = some payload)
    (hnobirth : ∀ fresh, ¬ InstallationBirth record fresh) :
    ReferenceLaterSamplerParameterMeasurability.parameters? record.input = none := by
  have hp := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch record.input
  change ReferenceLaterSamplerParameterMeasurability.parameters? record.input =
    ReferenceLaterAssignmentFibreStep.dispatchParameters?
      (prepare record.input).coordinator at hp
  have hprepared : record.output.preparation.coordinator =
      (prepare record.input).coordinator := by rw [record.output_eq]; rfl
  rw [← hprepared] at hp
  have hfailure (hnone : record.output.preparation.coordinator.selection = none) : False := by
    have he := ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
      record hnone
    rw [hret] at he
    cases he
  cases hc : record.output.preparation.coordinator with
  | first outcome => simpa only [hc, ReferenceLaterAssignmentFibreStep.dispatchParameters?] using hp
  | live r q base outcome => simpa only [hc, ReferenceLaterAssignmentFibreStep.dispatchParameters?] using hp
  | invalidCollectionCutoff => simpa only [hc, ReferenceLaterAssignmentFibreStep.dispatchParameters?] using hp
  | dagger => simpa only [hc, ReferenceLaterAssignmentFibreStep.dispatchParameters?] using hp
  | collection old ledger clock cutoff outcome =>
      have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
      cases outcome <;>
        simp only [hc, ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          ReferenceLaterAssignmentFibreStep.outcomeParameters?] at hp
      all_goals solve
        | exact hp
        | (exfalso; apply hfailure; simp only [hc, DispatchCut.selection]; done)
        | (simp only [hc] at hbirth; exact False.elim (hnobirth _ hbirth))

/-- A retained live step before the cutoff has the continuing chosen tag. -/
private theorem record_continuing_of_live_retained
    (record : RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : record.input.state.coordinator = .live r q base)
    (payload : Payload rate)
    (hret : storedPayload record.output.next.coordinator = some payload)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest record = true := by
  have hfailure (hnone : record.output.preparation.coordinator.selection = none) : False := by
    have he := ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
      record hnone
    rw [hret] at he
    cases he
  have hdispatch : (prepare record.input).coordinator =
      .live r q base (CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)) := by
    simp only [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hprepared : record.output.preparation.coordinator =
      (prepare record.input).coordinator := by rw [record.output_eq]; rfl
  rw [hdispatch] at hprepared
  cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)
  all_goals have hc := hprepared.trans (congrArg (DispatchCut.live r q base) hd)
  all_goals solve
    | (exfalso; apply hfailure; simp only [hc, DispatchCut.selection]; done)
    | (simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hdispatch, hd] at hcut; cases hcut)
    | exact (by simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest, hc])

/-- A present cutoff initializer comes from the original incoming live
registers and the literal cutoff dispatch. -/
private theorem initialized_choice_live
    (x : RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (I : ReferenceCollectionSegmentExtraction.Initializer p)
    (hc : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hI : c.initializer = some I) :
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      x.state.coordinator = .live r q base ∧
      c.payload = r.payload ∧
      I = ReferenceCollectionSegmentExtraction.cutoffInitializer
        (liveInput x r q base).registers (liveInput x r q base).ownedRegisters base
        (liveInput x r q base).registers.time ∧
      ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
  classical
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · contradiction
  next hn =>
    cases hs : x.state.coordinator with
    | first =>
        have hd := ReferenceActivePhysicalStep.dispatch_first x hs
        change ReferenceCollectionSegmentExtraction.choiceOfCut (dispatch x) = some c at hc
        rw [hd] at hc
        cases CoordinatorRoundDispatch.dispatchFirst (firstInput x) <;>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals contradiction
    | dagger =>
        simp only [prepare, dispatch, hs, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        contradiction
    | collection payload ledger saved =>
        change ReferenceCollectionSegmentExtraction.choiceOfCut (dispatch x) = some c at hc
        simp only [dispatch, hs] at hc
        split at hc
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock payload ledger saved cutoff
          change ReferenceCollectionSegmentExtraction.choiceOfCut
            (.collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput x payload ledger clock cutoff))) = some c at hc
          cases hd : CoordinatorRoundDispatch.dispatchCollection
            (collectionInput x payload ledger clock cutoff) <;>
            simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
          all_goals first
            | contradiction
            | (cases Option.some.inj hc; cases hI)
        · simp only [ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
          contradiction
    | live r q base =>
        have hdispatch : (prepare x).coordinator =
            .live r q base (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          simp only [prepare, dispatch, hs, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hdispatch] at hc
        cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
          simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        cases Option.some.inj hc
        cases Option.some.inj hI
        exact ⟨r, q, base, rfl, rfl, rfl, by
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hdispatch, hd]⟩

/-- An indexed original input up to the first cutoff has the actual
first-live phase invariant. -/
private theorem complete_firstLive_state_at
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hk : k.val ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length) :
    ReferenceFirstLiveConfirmationHistory.FirstLiveState
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).get k).input.state := by
  obtain ⟨hc, span, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h hc)
  have hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro i state memory hi
    have he := (seed.configuration i).symm.trans hi
    cases he
    exact ⟨seed.unoccupied i, seed.lastDown_none i⟩
  have hphase := ReferenceFirstLiveConfirmationHistory.run_firstLive_prefix_state
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    s (p.T - s) (by omega) seed.activeAtStart seed.coordinatorFirst hseed
    k.val (by
      have hbound := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hbound
      exact Nat.le_of_lt hbound) (by rw [← hrecords]; exact hk)
  rw [hrecord]
  exact hphase

/-- The first actual input is the original launch's first phase. -/
private theorem complete_zero_first
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hzero : 0 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[0]'hzero).input.state.coordinator = .first := by
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).length := ⟨0, hzero⟩
  obtain ⟨hc, span, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  rw [List.get_eq_getElem] at hrecord
  rw [hrecord]
  have hspan0 : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 0 ≤ p.T := by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  have hmode : allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z rewards C_star C_h hc).activeAtStart
  change (ReferenceActivePhysicalHorizon.run
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    0 hspan0 hmode).finalState.coordinator = .first
  rw [ReferenceActivePhysicalHorizon.run_zero_final]
  exact (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc).coordinatorFirst

private theorem takeWhile_eq_take_length {α : Type*} (xs : List α) (test : α → Bool) :
    xs.takeWhile test = xs.take (xs.takeWhile test).length := by
  obtain ⟨tail, heq⟩ := List.takeWhile_prefix (l := xs) test
  have ht := congrArg (fun ys : List α => ys.take (xs.takeWhile test).length) heq
  rw [List.take_left] at ht
  exact ht

private theorem takeWhile_first_false {α : Type*} (f : α → Bool)
    (xs : List α) (n : ℕ) (r : α) (hr : xs[n]? = some r)
    (hfalse : f r = false)
    (hearlier : ∀ j < n, ∀ q, xs[j]? = some q → f q = true) :
    (xs.takeWhile f).length = n := by
  induction xs generalizing n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
  | cons head rest ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst r
          simp only [List.takeWhile_cons, hfalse, Bool.false_eq_true,
            ↓reduceIte, List.length_nil]
      | succ n =>
          have hh : f head = true := hearlier 0 (by omega) head rfl
          have ht := ih n (by simpa only [List.getElem?_cons_succ] using hr)
            (fun j hj q hq => hearlier (j + 1) (by omega) q
              (by simpa only [List.getElem?_cons_succ] using hq))
          simpa only [List.takeWhile_cons, hh, ↓reduceIte, List.length_cons]
            using congrArg Nat.succ ht

/-- The first retained installation fixes its actual cutoff span and the
first present later-collection selector on that same physical suffix. -/
theorem internal_complete_first_retained_installation_span_cut
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
    ∀ (b : Fin R.length)
      (_hb : ReferenceCollectionPhaseHistory.laterChosen (R[b.val]'b.isLt).input = true)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (_hcarry0 : ∀ k : Fin R.length, 0 < k.val → k.val ≤ b.val →
        ReferenceAssignmentPayloadPersistence.storedPayload (R.get k).input.state.coordinator =
          some payload ∧
        (k.val < b.val → ∀ fresh,
          ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth (R.get k) fresh)),
    ∃ (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (I : ReferenceCollectionSegmentExtraction.Initializer p)
      (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE)
      (u : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p),
      e = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length ∧
      0 < e ∧ e < b.val ∧
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow R =
        R.take 1 ++ ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z 1 ∧
      e = 1 + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z 1).length ∧
      ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
      R[e]? = some seg.entry ∧ seg.records ≠ [] ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.entry.input.time.val = s + e ∧
      seg.entry.input.state.coordinator = .live rE qE (fun _ => 0) ∧
      rE.payload = payload ∧ seg.context.payload = payload ∧
      ReferenceCollectionSegmentExtraction.choice seg.entry.input = some seg.context ∧
      seg.context.initializer = some I ∧
      (let li := ReferenceActivePhysicalStep.liveInput seg.entry.input rE qE (fun _ => 0)
       I = ReferenceCollectionSegmentExtraction.cutoffInitializer li.registers
         li.ownedRegisters (fun _ => 0) li.registers.time) ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
      I.sigma = payload.sigma.val + 1 ∧ I.cutoff = s + e + 1 ∧
      I.base = (fun _ => 0) ∧ I.assignment.arm = payload.assignment.assigned ∧
      I.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma bits ∧
      u.val = s + e ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt (R[b.val]'b.isLt) =
        some (u, theta) ∧
      (∀ j < b.val, ∀ earlier, R[j]? = some earlier →
        ReferenceLaterSamplerParameterMeasurability.parameters? earlier.input = none) ∧
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z =
        some (u, ((R[b.val]'b.isLt).input.time, theta)) ∧
      z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u (R[b.val]'b.isLt).input.time := by
  classical
  dsimp only
  intro b hb payload hcarry0
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
  let e := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let recordB : RoundRecord (p := p) (rate := rate) := R[b.val]'b.isLt
  have hbR : b.val < R.length := b.isLt
  have hrecordB : R[b.val]? = some recordB := by
    exact List.getElem?_eq_getElem b.isLt
  obtain ⟨old, ledgerB, savedB, hcoordB, _⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty recordB.input hb
  have heb : e < b.val :=
    ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
      rate rewards C_star C_h z b.val recordB hrecordB old ledgerB savedB hcoordB
  obtain ⟨hcross, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z b
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      z rewards C_star C_h + (p.T - s) ≤ p.T := by
    change s + (p.T - s) ≤ p.T
    dsimp only [s]
    omega
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hcross (p.T - s) hspan
  have hRrun : R = epoch.records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h z hcross
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length < p.T - s := by
    have hbBound := b.isLt
    simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hbBound
    rw [← hRrun]
    change e < p.T - s
    omega
  obtain ⟨cut, suffix, rOld, qOld, baseOld, choice, I, seg, hsplit, htime,
      hchoice, hchoicePayload, hinitializer, hchoiceInitializer, hsigmaI,
      hcutoffI, hfreezeI, hfreezeGrid, hbaseI, hassignmentI, hcheckedI,
      hkpos, hu, hgridLower, hgridUpper, hfirstCutoff, hsegmentAt,
      hentry, hcontext, hrecords, hremaining, hpartition, hwindow⟩ :=
    ReferenceFirstCollectionEpochAlignment.actual_first_collection_segment
      rate z rewards C_star C_h (p.T - s) hcross hspan hshort
  change epoch.records = ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records ++ cut :: suffix at hsplit
  rw [← hRrun] at hsplit
  change cut.input.time.val = s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length at htime
  rw [← hRrun] at htime
  change I.cutoff = s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length + 1 at hcutoffI
  rw [← hRrun] at hcutoffI
  change 0 < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length at hkpos
  rw [← hRrun] at hkpos
  change ReferenceCollectionSegmentExtraction.segmentAt epoch.records
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length = some seg at hsegmentAt
  rw [← hRrun] at hsegmentAt
  have hep : 0 < e := hkpos
  have heBound : e < R.length := lt_trans heb b.isLt
  let ke : Fin R.length := ⟨e, heBound⟩
  have hcutAt : R[e]? = some cut := by
    nth_rw 1 [hsplit]
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R ++ cut :: suffix)[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length]? = some cut
    simp only [List.getElem?_append_right (by omega :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length ≤
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length), Nat.sub_self,
      List.getElem?_cons_zero]
  have hentryAt : R[e]? = some seg.entry := by rw [hentry]; exact hcutAt
  have hgetE : R.get ke = seg.entry := (List.getElem?_eq_some_iff.mp hentryAt).2
  have hchoiceSeg : ReferenceCollectionSegmentExtraction.choice seg.entry.input = some seg.context := by
    simpa only [hentry, hcontext] using hchoice
  have hinitSeg : seg.context.initializer = some I := by
    simpa only [hcontext] using hchoiceInitializer
  obtain ⟨rE, qE, baseE, hstateE, hpE, hIE, hcutE⟩ :=
    initialized_choice_live seg.entry.input seg.context I hchoiceSeg hinitSeg
  have hbaseE : baseE = (fun _ => 0) := by
    have heq := congrArg ReferenceCollectionSegmentExtraction.Initializer.base hIE
    exact heq.symm.trans hbaseI
  subst baseE
  have hrPayload : rE.payload = payload := by
    have hcarried := (hcarry0 ke hep (Nat.le_of_lt heb)).1
    rw [hgetE, hstateE] at hcarried
    exact Option.some.inj hcarried
  have hcontextPayload : seg.context.payload = payload := hpE.trans hrPayload
  have hOldPayload : rOld.payload = payload := by
    rw [← hchoicePayload, ← hcontext]
    exact hcontextPayload
  have hret (k : Fin R.length) (hkb : k.val < b.val) :
      storedPayload (R.get k).output.next.coordinator = some payload := by
    have hnextBound : k.val + 1 < R.length := by omega
    let next : Fin R.length := ⟨k.val + 1, hnextBound⟩
    have hnext := (hcarry0 next (by dsimp only [next]; omega)
      (by dsimp only [next]; omega)).1
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z k.val hnextBound
    change storedPayload (R[k.val + 1]).input.state.coordinator = some payload at hnext
    rw [hadj] at hnext
    exact hnext
  have hretE : storedPayload seg.entry.output.next.coordinator = some payload := by
    rw [← hgetE]
    exact hret ke heb
  have hphase : ReferenceCollectionPhaseHistory.CollectionPhase seg.entry.output.next.coordinator := by
    rw [seg.entry.output_eq]
    change ReferenceCollectionPhaseHistory.CollectionPhase
      (prepare seg.entry.input).observeCoordinator.configuration
    rw [ReferenceCollectionSegmentExtraction.choice_tail seg.entry.input seg.context hchoiceSeg]
    exact ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation _ _ _ _ _
  have hcompleted : (ReferenceCollectionSegmentExtraction.extractRound seg.entry).isSome = true := by
    rcases hphase with hdagger | ⟨P, ledger, saved, hcollection⟩
    · simp only [hdagger, storedPayload] at hretE
      cases hretE
    · obtain ⟨completed, hc⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_complete
        seg.entry seg.context P ledger saved hchoiceSeg hcollection
      rw [hc]
      rfl
  have hnonempty : seg.records ≠ [] := by
    rw [← hentry] at hrecords
    rw [hcompleted] at hrecords
    simpa only [↓reduceIte] using hrecords ▸ List.cons_ne_nil _ _
  have htimeE : seg.entry.input.time.val = s + e := by rw [hentry]; exact htime
  have hsigmaPayload : I.sigma = payload.sigma.val + 1 := by
    rw [hIE]
    change rE.payload.sigma.val + 1 = payload.sigma.val + 1
    rw [hrPayload]
  have hfreezePayload : I.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
    simpa only [hOldPayload] using hfreezeGrid
  have hassignmentPayload : I.assignment.arm = payload.assignment.assigned := by
    simpa only [hOldPayload] using hassignmentI
  have hfirst : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma bits := by
    let i : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
    have hf := hfirstCutoff i
    change FollowerCutoffScan.firstCutoff p rate.eta.val rOld.payload.sigma bits =
      s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length + 1 at hf
    rw [← hRrun, hOldPayload] at hf
    exact hcutoffI.trans hf.symm
  have hearlier : ∀ j < b.val, ∀ earlier, R[j]? = some earlier →
      ReferenceLaterSamplerParameterMeasurability.parameters? earlier.input = none := by
    intro j hj earlier hjRecord
    have hjBound : j < R.length := by omega
    have hget : R.get ⟨j, hjBound⟩ = earlier := (List.getElem?_eq_some_iff.mp hjRecord).2
    by_cases hjzero : j = 0
    · subst j
      have hf := complete_zero_first (rate := rate) rewards C_star C_h z hjBound
      have hcoord : earlier.input.state.coordinator = .first := by
        rw [← hget]
        exact hf
      simp only [ReferenceLaterSamplerParameterMeasurability.parameters?,
        ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
    · let kj : Fin R.length := ⟨j, hjBound⟩
      have hnobirth := (hcarry0 kj (by dsimp only [kj]; omega) (by dsimp only [kj]; omega)).2
        (by dsimp only [kj]; exact hj)
      have hretj := hret kj hj
      rw [hget] at hretj hnobirth
      exact record_parameters_none_of_retained_no_birth earlier payload hretj hnobirth
  have hcontinuing (k : Fin R.length) (hkpos : 0 < k.val) (hke : k.val < e) :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest (R.get k) = true := by
    have hstored := (hcarry0 k hkpos (by omega)).1
    have hphase := complete_firstLive_state_at (rate := rate) rewards C_star C_h z k
      (Nat.le_of_lt hke)
    have hprefix : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).IsPrefix R :=
      List.takeWhile_prefix _
    have hmem : R.get k ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := by
      rw [List.get_eq_getElem, ← hprefix.getElem hke]
      exact List.getElem_mem hke
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen (R.get k).input = false := by
      simpa only [Bool.not_eq_true'] using List.mem_takeWhile_imp hmem
    change storedPayload (R.get k).input.state.coordinator = some payload at hstored
    change ReferenceFirstLiveConfirmationHistory.FirstLiveState (R.get k).input.state at hphase
    cases hc : (R.get k).input.state.coordinator with
    | first => rw [hc] at hstored; cases hstored
    | dagger => rw [hc] at hstored; cases hstored
    | collection P ledger saved =>
        unfold ReferenceFirstLiveConfirmationHistory.FirstLiveState at hphase
        rw [hc] at hphase
        exact hphase.elim
    | live r q base =>
        exact record_continuing_of_live_retained (R.get k) r q base hc payload
          (hret k (by omega)) hcut
  have hcutTest : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest seg.entry = false := by
    have hprep : seg.entry.output.preparation.coordinator = (prepare seg.entry.input).coordinator := by
      rw [seg.entry.output_eq]; rfl
    rw [ReferenceCollectionPhaseHistory.cutoffChosen, ← hprep] at hcutE
    cases hc : seg.entry.output.preparation.coordinator with
    | first outcome => simp only [hc, Bool.false_eq_true] at hcutE
    | collection P ledger clock cutoff outcome => simp only [hc, Bool.false_eq_true] at hcutE
    | invalidCollectionCutoff => simp only [hc, Bool.false_eq_true] at hcutE
    | dagger => simp only [hc, Bool.false_eq_true] at hcutE
    | live r q base outcome =>
        cases outcome <;> simp only [hc, Bool.false_eq_true] at hcutE
        simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest, hc]
  have hprefixLen : (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z 1).length = e - 1 := by
    apply takeWhile_first_false _ (R.drop 1) (e - 1) seg.entry
    · simpa only [List.getElem?_drop, Nat.add_sub_of_le hep] using hentryAt
    · exact hcutTest
    · intro j hj earlier hjRecord
      have hglobal : R[1 + j]? = some earlier := by
        simpa only [List.getElem?_drop] using hjRecord
      have hbound : 1 + j < R.length := by omega
      have hg : R.get ⟨1 + j, hbound⟩ = earlier := (List.getElem?_eq_some_iff.mp hglobal).2
      rw [← hg]
      exact hcontinuing ⟨1 + j, hbound⟩ (by simp) (by dsimp only; omega)
  have hprefixEq : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R =
      R.take 1 ++ ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z 1 := by
    calc
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow R = R.take e :=
        takeWhile_eq_take_length R _
      _ = R.take (1 + (e - 1)) := by congr 1; omega
      _ = R.take 1 ++ (R.drop 1).take (e - 1) := List.take_add
      _ = _ := by
        unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rw [takeWhile_eq_take_length]
        change (R.drop 1 |>.takeWhile ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length = e - 1 at hprefixLen
        rw [hprefixLen]
  have hparams := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
    recordB.input hb
  change (ReferenceLaterSamplerParameterMeasurability.parameters? recordB.input).isSome = true at hparams
  rw [← ReferenceFirstCollectionSamplerCall.collectionCallAt_isSome recordB] at hparams
  obtain ⟨⟨u, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hparams
  obtain ⟨P, ledger, saved, hcoord, hcutoff, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec recordB u theta).mp hcall
  have hstoreB := (hcarry0 b (by omega) le_rfl).1
  change storedPayload recordB.input.state.coordinator = some payload at hstoreB
  rw [hcoord] at hstoreB
  have hP : P = payload := Option.some.inj hstoreB
  have hprovenance := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z b
  change (match recordB.input.state.coordinator with
    | .live r _ beta => _
    | .collection P l _ => _
    | .first => _
    | .dagger => _) at hprovenance
  rw [hcoord] at hprovenance
  have hledgerCutoff : ledger.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma bits := by
    simpa only [hP] using hprovenance.2.2.2
  have huval : u.val = s + e := by
    have heq := hledgerCutoff.trans hfirst.symm
    omega
  have hfirstCall : ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z =
      some (u, (recordB.input.time, theta)) :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z
      u recordB.input.time theta).2 ⟨b.val, recordB, hrecordB, rfl, hcall, hearlier⟩
  refine ⟨e, seg, I, rE, qE, u, theta, rfl, hep, heb, hprefixEq, ?_,
    hsegmentAt, hentryAt, hnonempty, hcutE, htimeE, hstateE, hrPayload,
    hcontextPayload, hchoiceSeg, hinitSeg, hIE, ?_, hsigmaPayload, hcutoffI,
    hbaseI, hassignmentPayload, hfreezePayload, hfirst, huval, hcall, hearlier,
    hfirstCall, ?_⟩
  · omega
  · simpa only [hcontext] using hcheckedI
  · change (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z).map
      (fun c => (c.1, c.2.1)) = some (u, recordB.input.time)
    rw [hfirstCall]
    rfl

end Bandits.Support.ReferenceCompleteFirstInstallationSpanCut

end
