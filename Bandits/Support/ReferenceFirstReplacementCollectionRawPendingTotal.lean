/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedWaitingCost
public import Bandits.Support.ReferenceFirstCollectionCalendarPendingTotal

import Lean.Elab.Tactic.Omega

/-!
# Raw first replacement collection chronology

Sources: pinned ZIP4 `06_interruptions.tex:9-14,37-79,246-296,425-437`
and `appendix_a_local_protocol.tex:8-85`.

The raw calendar retains the round whose output first empties pending. Its
boundary is the actual next assignment input or the actual horizon endpoint.
This module makes no assertion about domination by an analytical stopping mask.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionRawPendingTotal

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceCollectionSegmentExtraction
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem prepare_collection {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : RoundInput p rate) (P : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (u : Fin p.T)
    (hu : u.val + 1 = l.cutoff)
    (hs : x.state.coordinator = .collection P l saved) :
    (prepare x).coordinator = .collection P l (collectionClock P l saved u) u
      (CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x P l (collectionClock P l saved u) u)) := by
  have hb : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by have := u.isLt; omega
  have he : (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = u := by
    apply Fin.ext
    dsimp only
    omega
  simp only [prepare, dispatch, hs, dite_eq_left hb, CoordinatorRoundDispatch.dispatch]
  rw [he]
  rfl

/-- Both calendar branches install a later assignment at an empty incoming
collection ledger. This uses no first-collection admissibility specialization. -/
private theorem actual_empty_later {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hs : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.state.coordinator = .collection P l saved)
    (he : l.pending = ∅) :
    ReferenceCollectionPhaseHistory.laterChosen
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]).input = true := by
  let x := ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]).input
  change x.state.coordinator = .collection P l saved at hs
  change ReferenceCollectionPhaseHistory.laterChosen x = true
  by_cases hb : x.time.val + 1 < l.freezeAt
  · obtain ⟨u, hu, core, started, hstart, instruction, ha, _ht, _hk,
        _hsigma, _huNone, consistent, output, hlocal, _hlater,
        clockData, installation, selected, _hprior, _hresult, _hpending,
        _hinstall, hd, _rest⟩ :=
      ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
        rate rewards C_star C_h z k P l saved hs he hb
    rw [ReferenceCollectionPhaseHistory.laterChosen, prepare_collection x P l saved u hu hs, hd]
  · obtain ⟨u, hu, core, _scores, started, hstart, instruction, ha, ht, hk,
        output, hlocal, _hlater, _hscore, _hqueue, _hweight, _hanchor,
        _hqueues, _hdomains, _hbase, _hclock, mass, sampled, _hmass,
        _hsampled, _hvector, selected, hd, hp, _rest⟩ :=
      ReferenceCompleteEmptyCollectionRenewalChoiceDomains.complete_empty_collection_renewal_choice_domains
        rate rewards C_star C_h z k P l saved hs he (by change l.freezeAt ≤ x.time.val + 1; omega)
    rw [ReferenceCollectionPhaseHistory.laterChosen, hp, hd]

/-- The fields which remain fixed throughout a collection. -/
def ledgerContext {rate : ReferenceActivePhysicalStep.RateInput p} (l : Ledger rate) :=
  (l.assignment, l.sigma, l.cutoff, l.freezeAt, l.baseScore)

private def contextSpec {rate : ReferenceActivePhysicalStep.RateInput p}
    (l : Ledger rate) : CoordinatorCollectionLedger.Checked (Ledger rate) → Prop
  | .invalid => True
  | .success out | .rejected out => ledgerContext out = ledgerContext l

private theorem decode_context {rate : ReferenceActivePhysicalStep.RateInput p}
    (l out : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (h : CoordinatorCollectionLedger.decodeUp l i parsed = .success out ∨
      CoordinatorCollectionLedger.decodeUp l i parsed = .rejected out) :
    ledgerContext out = ledgerContext l := by
  have hall : contextSpec l (CoordinatorCollectionLedger.decodeUp l i parsed) := by
    unfold CoordinatorCollectionLedger.decodeUp
    split
    · cases parsed with
      | none =>
        dsimp only
        split
        · rfl
        · trivial
      | some M =>
        dsimp only
        split
        · split
          · split
            · split
              · trivial
              · split
                · split
                  · rfl
                  · trivial
                · trivial
              · trivial
            · trivial
          · trivial
        · split
          · rfl
          · trivial
    · trivial
  rcases h with h | h <;> rw [h] at hall <;> exact hall

private theorem checked_context {rate : ReferenceActivePhysicalStep.RateInput p}
    (l out : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (accepted : Bool)
    (h : CollectionCheckedExecution.checkedRounds l [input] = some ([accepted], out)) :
    ledgerContext out = ledgerContext l := by
  cases hs : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw with
  | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at h
  | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at h
  | success started =>
    have hstart : ledgerContext started = ledgerContext l := by
      unfold CoordinatorCollectionLedger.startRound at hs
      repeat (first | split at hs | dsimp only at hs)
      all_goals first | contradiction | (cases hs; rfl)
    cases hd : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed with
    | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, reduceCtorEq] at h
    | success decoded | rejected decoded =>
      have hdecode : ledgerContext decoded = ledgerContext started :=
        decode_context started decoded input.selectedFollower input.parsed (by first | exact Or.inl hd | exact Or.inr hd)
      cases hf : CoordinatorCollectionLedger.finishRound decoded with
      | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at h
      | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at h
      | success finished =>
        have hfinish := CollectionCheckedExecution.finishRound_success_candidate decoded finished hf
        have heq : finished = out := by
          have hh := h
          simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf,
            Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hh
          exact hh.2
        rw [← heq, hfinish]
        exact hdecode.trans hstart

private theorem actual_continuing {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hs : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.state.coordinator = .collection P l saved)
    (hne : l.pending.Nonempty) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    ∃ cr : CompletedRound rate, extractRound r = some cr ∧
      cr.context.payload = P ∧ cr.context.preLedger = l ∧
      cr.context.initializer = none ∧
      r.output.coordinator.failure = none ∧
      (∃ saved', r.output.next.coordinator = .collection P cr.final saved') ∧
      CoordinatorCollectionLedger.validLedgerCheck cr.final = true ∧
      cr.final.phase = .ready ∧ cr.final.cursor = r.input.time.val + 2 ∧
      ledgerContext cr.final = ledgerContext l ∧
      cr.final.pending = ReferenceCollectionPhaseHistory.eraseEvent l.pending
        (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  obtain ⟨u, hu, core, scores, startedClock, hstartClock, _hframe,
      choiceInputs, snapshot, boundary, _hdispatch, _hchoiceInputs, _hclock,
      _harm, c, hc, _hc, _rest⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h z k P l saved hs hne
  obtain ⟨o, started, decoded, bank, finished, clockFinished,
      hcP, hcl, hci, _hrecordValid, _hrecord, _hfresh, _hstart, _hstartedValid,
      _hstartedPhase, _hstartedCursor, _hcutPos, _hcutCursor, _hcursorT,
      _hcheck, _hreceive, _hbank, _hbankWell, _hbankCheck, _hbankOther,
      _hfinish, _hfinishedCandidate, hvalid, hphase, hcursor, _hgamma,
      _hassign, _hsigma, _hcutoff, _hfreeze, _hbase, _hpending,
      _hcutregs, _hcurrentregs, _hraw, _henabled, _hclockValid, _hclockSigma,
      cutoff, _hclockU, _hcutTime, _hstartTime, _hfinishTime, _hclockFinish,
      _hpost, _hcollectionFinish, hobserve, _rest⟩ :=
    ReferenceCompleteContinuingCollectionReception.actual_continuing_collection_reception_finish
      rate rewards C_star C_h z k P l saved hs c hc
  have hout : r.output.coordinator =
      ⟨.collection P finished clockFinished.clock.lastProposal, bank, none,
        some o, (receiveUp (prepare r.input) started).diagnostic⟩ := by
    rw [r.output_eq]
    exact hobserve
  have hnext : r.output.next.coordinator =
      .collection P finished clockFinished.clock.lastProposal := by
    rw [r.output_eq]
    exact congrArg CoordinatorObservation.configuration hobserve
  obtain ⟨cr, hcr⟩ := actual_collection_round_complete r c P finished
    clockFinished.clock.lastProposal hc hnext
  obtain ⟨hchoice, _htime, hchecked, P', saved', hnext'⟩ :=
    actual_collection_round_checked r cr hcr
  have hcontext : cr.context = c := Option.some.inj (hchoice.symm.trans hc)
  have hfinal : cr.final = finished := by
    rw [hnext] at hnext'
    exact (CoordinatorConfiguration.collection.inj hnext').2.1.symm
  have hpre : cr.context.preLedger = l := hcontext ▸ hcl
  have hframe := checked_context cr.context.preLedger cr.final cr.input cr.accepted hchecked
  obtain ⟨tail, htail, hpending, _hsigma⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame r.input P finished
      clockFinished.clock.lastProposal (by rw [← r.output_eq]; exact hnext)
  have horigin := (ReferenceCollectionPhaseHistory.executedTail_origin htail).2
  have hledger : tail.ledger = l := by
    rcases horigin with hcut | ⟨_hcut, P0, l0, saved0, hstate0, hl0⟩
    · have hcutFalse : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        obtain ⟨u0, hu0, _⟩ :=
          ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
            rate rewards C_star C_h z k P l saved hs
        rw [ReferenceCollectionPhaseHistory.cutoffChosen,
          prepare_collection r.input P l saved u0 hu0 hs]
      rw [hcutFalse] at hcut
      cases hcut.1
    · have hstate := hs
      change r.input.state.coordinator = .collection P l saved at hstate
      rw [hstate] at hstate0
      exact hl0.trans (CoordinatorConfiguration.collection.inj hstate0).2.1.symm
  refine ⟨cr, hcr, hcontext ▸ hcP, hpre, hcontext ▸ hci, ?_,
    ⟨clockFinished.clock.lastProposal, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout]
  · rw [hfinal]
    exact hnext
  · simpa only [hfinal] using hvalid
  · simpa only [hfinal] using hphase
  · simpa only [hfinal] using hcursor
  · simpa only [hpre] using hframe
  · simpa only [hfinal, hledger] using hpending

private theorem actual_lookup {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (r : Record rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n]? = some r) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      r.input.time z = some r := by
  obtain ⟨hn, heq⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨_, _, hprefix⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z ⟨n, hn⟩
  have htime : r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
    rw [← heq]
    change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get ⟨n, hn⟩).input.time.val = _
    rw [hprefix]
    rfl
  have hs : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ r.input.time.val := by omega
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs]
  have hi : r.input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = n := by omega
  rw [hi]
  exact hr

private theorem live_input_of_prepare {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
    (hp : (prepare x).coordinator = .live registers owned base outcome) :
    x.state.coordinator = .live registers owned base := by
  cases hs : x.state.coordinator with
  | first =>
    simp only [prepare, dispatch, hs, CoordinatorRoundDispatch.dispatch] at hp
    contradiction
  | dagger =>
    simp only [prepare, dispatch, hs] at hp
    contradiction
  | collection P l saved =>
    simp only [prepare, dispatch, hs] at hp
    split at hp <;>
      (try simp only [CoordinatorRoundDispatch.dispatch] at hp) <;> contradiction
  | live registers' owned' base' =>
    have hactual : (prepare x).coordinator = .live registers' owned' base'
        (CoordinatorRoundDispatch.dispatchLive (liveInput x registers' owned' base')) := by
      simp only [prepare, dispatch, hs, CoordinatorRoundDispatch.dispatch]
      rfl
    have he := hactual.symm.trans hp
    cases he
    rfl

private theorem live_outcome_of_prepare {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
    (hs : x.state.coordinator = .live registers owned base)
    (hp : (prepare x).coordinator = .live registers owned base outcome) :
    CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base) = outcome := by
  have hactual : (prepare x).coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base)) := by
    simp only [prepare, dispatch, hs, CoordinatorRoundDispatch.dispatch]
    rfl
  have he := hactual.symm.trans hp
  injection he

private theorem completed_length {rate : ReferenceActivePhysicalStep.RateInput p}
    (K : List (Record rate))
    (h : ∀ r ∈ K, (extractRound r).isSome = true) :
    (completed K).length = K.length := by
  induction K with
  | nil => rfl
  | cons r rest ih =>
    have hr := h r (by simp only [List.mem_cons, true_or])
    cases he : extractRound r with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hr
    | some cr =>
      simp only [completed, List.filterMap_cons, he, List.length_cons]
      exact congrArg Nat.succ (ih (fun r hr => h r (List.mem_cons_of_mem _ hr)))

private theorem connected_of_inputs {rate : ReferenceActivePhysicalStep.RateInput p}
    (K : List (Record rate)) (initial : State p rate)
    (h : ∀ j : Fin K.length,
      (K.get j).input.state = endpointState initial (K.take j.val)) :
    ReferenceActivePhysicalHorizon.Connected initial K (endpointState initial K) := by
  induction K generalizing initial with
  | nil => rfl
  | cons r rest ih =>
    refine ⟨h ⟨0, by simp only [List.length_cons]; omega⟩, ?_⟩
    apply ih
    intro j
    exact h ⟨j.val + 1, by simp only [List.length_cons]; omega⟩

private theorem actual_cutoff_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    match r.output.preparation.coordinator with
    | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
      ∃ (c : Choice rate) (a : Initializer p) (cr : CompletedRound rate),
        choice r.input = some c ∧ c.payload = registers.payload ∧
        c.initializer = some a ∧ a.checkedStart rate = .success c.preLedger ∧
        cr.context = c ∧ extractRound r = some cr ∧
        r.output.coordinator.failure = none ∧
        (∃ saved, r.output.next.coordinator = .collection registers.payload cr.final saved) ∧
        c.preLedger.sigma = registers.payload.sigma.val + 1 ∧
        c.preLedger.cutoff = r.input.time.val + 1 ∧
        c.preLedger.freezeAt = (liveRegistersAt registers r.input.time).gridBoundary ∧
        c.preLedger.cursor = r.input.time.val + 1 ∧
        c.preLedger.pending = Finset.univ ∧
        c.preLedger.increment = (fun _ => 0) ∧
        c.preLedger.gammaLoc = (fun _ => 0) ∧
        c.preLedger.rawBuffer = (fun _ _ => none) ∧ c.preLedger.phase = .ready ∧
        CoordinatorCollectionLedger.validLedgerCheck cr.final = true ∧
        cr.final.cursor = r.input.time.val + 2 ∧ cr.final.phase = .ready ∧
        cr.final.pending = Finset.univ ∧ ledgerContext cr.final = ledgerContext c.preLedger
    | _ => True := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  change match r.output.preparation.coordinator with
    | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => _
    | _ => True
  cases hp : r.output.preparation.coordinator with
  | first _ => trivial
  | collection _ _ _ _ _ => trivial
  | dagger => trivial
  | invalidCollectionCutoff => trivial
  | live registers owned base outcome =>
    cases outcome <;> try trivial
    rename_i dispatched hs ledger hi he hd hc hpend hn selected
    have hprepare : (prepare r.input).coordinator = .live registers owned base
        (.cutoffChosen dispatched hs ledger hi he hd hc hpend hn selected) := by
      rw [r.output_eq] at hp
      exact hp
    have hstate := live_input_of_prepare r.input registers owned base _ hprepare
    have hpost := Bandits.Support.complete_live_cutoff_post_choice
      rate rewards C_star C_h z k registers owned base hstate
    dsimp only at hpost
    rw [live_outcome_of_prepare r.input registers owned base _ hstate hprepare] at hpost
    rcases hpost.2 with ⟨_hcommand, _hclock, _hpending, _hassignment,
      _hinit, _hledger, hsigma, hcutoff, hfreeze, hpending, hcursor,
      hincrement, hgamma, hraw, hphase, _hchoiceValid, _hgT, _harm,
      physical, hselection, _hpay, _hpend, _hcut, _hstarted, _harm', _hpend',
      _hcut', _harm'', recording, _hrecord, started, _hstart, hcandidate,
      _hvalidStart, _hphaseStart, _hcursorStart, _hincrementStart,
      _henabled, _hrawStart, _hknown, _hunknown, _hlocal, _hdisabled,
      _hzero, _hbanks, decoded, bank, _hreceive, hdecoded, _hbank,
      finished, clockFinished, diagnostic, _hfinish, hfinishedCandidate,
      hvalid, _hincrementFinish, _hgammaFinish, hcursorFinish, hphaseFinish,
      _hcutregs, _hcurrentregs, _hrawFinish, _hpendingFinish, _hclockFinish,
      _hclockEq, _hclockPending, _hclockCommand, _hdiag, _hdiagInput,
      _hdiagRaw, _hpost, _hobserve, houtput, hnext, _hbankNext⟩
    let c : Choice rate :=
      ⟨registers.payload, sharedLedger ledger, dispatched.startResult,
        (liveRegistersAt registers r.input.time).complementWeights,
        some (cutoffInitializer (liveRegistersAt registers r.input.time)
          (liveOwnedAt registers owned r.input.time) base r.input.time)⟩
    let a := cutoffInitializer (liveRegistersAt registers r.input.time)
      (liveOwnedAt registers owned r.input.time) base r.input.time
    have hchoice : choice r.input = some c := by
      unfold choice
      have hsel : (prepare r.input).coordinator.selection ≠ none := by
        rw [hselection]
        exact Option.some_ne_none _
      rw [ite_eq_right hsel, hprepare]
      rfl
    obtain ⟨cr, hcr⟩ := actual_collection_round_complete r c registers.payload
      finished clockFinished.clock.lastProposal hchoice hnext
    obtain ⟨hchoice', _htime, hchecked, P', saved', hnext'⟩ :=
      actual_collection_round_checked r cr hcr
    have hcontext : cr.context = c := Option.some.inj (hchoice'.symm.trans hchoice)
    have hfinal : cr.final = finished := by
      rw [hnext] at hnext'
      exact (CoordinatorConfiguration.collection.inj hnext').2.1.symm
    have hshared := sharedLedger_fields (rate := rate) ledger
    have hfinalPending : finished.pending = Finset.univ := by
      rw [hfinishedCandidate, hdecoded, hcandidate]
      change (sharedLedger ledger).pending = Finset.univ
      exact hshared.2.2.2.2.2.1.trans hpending
    refine ⟨c, a, cr, hchoice, rfl, rfl,
      choice_initializer r.input c a hchoice rfl, hcontext, hcr, ?_,
      ⟨clockFinished.clock.lastProposal, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [houtput]
    · rw [hfinal]
      exact hnext
    · exact hshared.2.1.trans hsigma
    · exact hshared.2.2.1.trans hcutoff
    · exact hshared.2.2.2.1.trans hfreeze
    · exact hshared.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hcursor
    · exact hshared.2.2.2.2.2.1.trans hpending
    · exact hshared.2.2.2.2.2.2.2.2.1.trans hincrement
    · exact hshared.2.2.2.2.2.2.2.2.2.1.trans hgamma
    · exact hshared.2.2.2.2.2.2.2.2.2.2.1.trans hraw
    · exact hshared.2.2.2.2.2.2.2.2.2.2.2.2.2.trans hphase
    · simpa only [hfinal] using hvalid
    · simpa only [hfinal] using hcursorFinish
    · simpa only [hfinal] using hphaseFinish
    · simpa only [hfinal] using hfinalPending
    · simpa only [hcontext] using
        checked_context cr.context.preLedger cr.final cr.input cr.accepted hchecked

/-- On the unchanged complete source, the first replacement's literal raw
collection has nonempty incoming pending at every calendar cell. The canonical
checked stream has its full raw length and ends at the actual next start or
horizon. No survival, numerical truth, or sampler-law premise is supplied. -/
theorem complete_first_replacement_raw_calendar_pending_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
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
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            ∃ (stream : Segment rate) (initializer : Initializer p),
              segment K = some stream ∧ stream.records = K ∧ stream.remaining = [] ∧
              stream.context.payload = payload ∧ stream.context.initializer = some initializer ∧
              initializer.checkedStart rate = .success stream.context.preLedger ∧
              stream.context.preLedger.sigma = payload.sigma.val + 1 ∧
              stream.context.preLedger.cutoff = u ∧
              stream.context.preLedger.freezeAt = (liveRegistersAt registers cut.input.time).gridBoundary ∧
              stream.context.preLedger.cursor = u ∧
              stream.context.preLedger.pending = Finset.univ ∧
              stream.context.preLedger.increment = (fun _ => 0) ∧
              stream.context.preLedger.gammaLoc = (fun _ => 0) ∧
              stream.context.preLedger.rawBuffer = (fun _ _ => none) ∧
              stream.context.preLedger.phase = .ready ∧
              CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
                initializer.base initializer.outside stream.inputs =
                  .success ⟨stream.context.preLedger, stream.accepted, stream.final⟩ ∧
              (completed K).length = K.length ∧
              (∀ a : Fin K.length,
                let r := K.get a
                (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  payload.sigma.val r.input.time z).Nonempty ∧
                R[c + a.val]? = some r ∧
                ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                  r.input.time z = some r ∧
                r.input.time.val + 1 = u + a.val ∧
                r.input.rows = z.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                r.input.rewards = rewards ∧
                r.output.coordinator.failure = none ∧
                ∃ (cr : CompletedRound rate) (saved : Option (Fin p.T × Bool)),
                  extractRound r = some cr ∧ cr.context.payload = payload ∧
                  r.output.next.coordinator = .collection payload cr.final saved ∧
                  CoordinatorCollectionLedger.validLedgerCheck cr.final = true ∧
                  cr.final.phase = .ready ∧ cr.final.cursor = u + a.val + 1 ∧
                  ledgerContext cr.final = ledgerContext stream.context.preLedger) ∧
              (∃ saved, (endpointState cut.input.state K).coordinator =
                .collection payload stream.final saved) ∧
              match R[c + K.length]? with
              | none => c + K.length = R.length ∧
                  ReferenceCompletePhysicalHistory.completeTerminalState rate z rewards C_star C_h =
                    some (endpointState cut.input.state K)
              | some next => next.input.state = endpointState cut.input.state K ∧
                  ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                  ∃ ledger saved,
                    next.input.state.coordinator = .collection payload ledger saved ∧
                    ledger.pending = ∅
          | _ => True
      | _ => True := by
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  have hS := ReferenceFirstReplacementCollectionSeedEndpoint.complete_first_replacement_collection_seed_endpoint
    rate z rewards C_star C_h
  have hU := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  dsimp only at hB hS hU ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hB hS hU ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hB hS hU
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hB hS hU ⊢
      rcases hU with ⟨_hCL, _hX, hU⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hB hS hU ⊢
        rcases hB with ⟨_hnotContinuing, hB⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hB hS hU
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi he hd hclock hpend hn selectedCut
          dsimp only at hB hS hU ⊢
          let P : Payload rate := installed.registers.payload
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => endpointState cut.output.next (W.take j)
          have hpay : registers.payload = P := hB.1
          obtain ⟨hcLt, hcutEq⟩ := List.getElem?_eq_some_iff.mp hc
          have hD := actual_cutoff_data rate rewards C_star C_h z ⟨c, hcLt⟩
          dsimp only at hD
          rw [hcutEq, hcut] at hD
          dsimp only at hD
          rw [hpay] at hD
          rcases hD with ⟨c0, a0, cr0, hchoice0, hpay0, hinit0, hstart0,
            hcontext0, hcr0, hfail0, ⟨saved0, hnext0⟩, hsigma0, hcutoff0,
            hfreeze0, hcursor0, hpending0, hincrement0, hgamma0, hraw0, hphase0,
            hvalid0, hcursor1, hphase1, hpending1, hcontext1⟩
          rcases hS with ⟨_hwindow, _hE0, hcutTime, _hu, _huT, _hfirst, _hfollowers, hgeometry⟩
          rcases hU with ⟨_hprovenance, _hreceptions, hboundary⟩
          have hget (j : Fin W.length) : R[c + 1 + j.val]? = some (W.get j) :=
            ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get R c j.val j.isLt
          have hgeom (j : Fin W.length) :
              (W.get j).input.state = E j.val ∧
              (W.get j).input.time.val = u + j.val ∧
              (W.get j).input.rows = z.1.2 ∧
              (W.get j).input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
              (W.get j).input.rewards = rewards ∧ E (j.val + 1) = (W.get j).output.next := by
            have h := hgeometry j.val (Nat.le_of_lt j.isLt)
            rw [hget j] at h
            exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
              (h.2.2.2.2.2.1 j.isLt).2⟩
          have hnotLater (j : Fin W.length) :
              ReferenceCollectionPhaseHistory.laterChosen (W.get j).input = false := by
            have hmem : W.get j ∈ W := List.get_mem W j
            have hpred := (List.all_eq_true.mp List.all_takeWhile) (W.get j) hmem
            simpa only [Bool.not_eq_true'] using hpred
          have hnonempty (j : Fin W.length) (l : Ledger rate)
              (saved : Option (Fin p.T × Bool))
              (hstate : (E j.val).coordinator = .collection P l saved) : l.pending.Nonempty := by
            have hs' : (W.get j).input.state.coordinator = .collection P l saved := by
              rw [(hgeom j).1]
              exact hstate
            obtain ⟨hindex, hrecord⟩ := List.getElem?_eq_some_iff.mp (hget j)
            by_contra hempty
            have hlater := actual_empty_later rewards C_star C_h z
              ⟨c + 1 + j.val, hindex⟩ P l saved
              (by rw [hrecord]; exact hs') (Finset.not_nonempty_iff_eq_empty.mp hempty)
            rw [hrecord, hnotLater j] at hlater
            cases hlater
          have hstates (j : ℕ) (hj : j ≤ W.length) :
              ∃ l saved, (E j).coordinator = .collection P l saved ∧
                ledgerContext l = ledgerContext c0.preLedger ∧
                CoordinatorCollectionLedger.validLedgerCheck l = true ∧
                l.phase = .ready ∧ l.cursor = u + j + 1 := by
            induction j with
            | zero =>
              exact ⟨cr0.final, saved0, hnext0, hcontext1, hvalid0, hphase1, hcursor1⟩
            | succ j ih =>
              have hjlt : j < W.length := by omega
              let idx : Fin W.length := ⟨j, hjlt⟩
              obtain ⟨l, saved, hstate, hcontext, _hvalid, _hphase, _hcursor⟩ := ih (by omega)
              obtain ⟨hindex, hrecord⟩ := List.getElem?_eq_some_iff.mp (hget idx)
              have hs' : (W.get idx).input.state.coordinator = .collection P l saved := by
                rw [(hgeom idx).1]
                exact hstate
              have hstep := actual_continuing rewards C_star C_h z
                ⟨c + 1 + j, hindex⟩ P l saved
                (by rw [hrecord]; exact hs') (hnonempty idx l saved hstate)
              dsimp only at hstep
              rw [hrecord] at hstep
              obtain ⟨cr, _hcr, _hP, _hl, _hi, _hfail, ⟨saved', hnext⟩,
                hvalid, hphase, hcursor, hcontext', _hpending⟩ := hstep
              refine ⟨cr.final, saved', ?_, hcontext'.trans hcontext, hvalid, hphase, ?_⟩
              · rw [(hgeom idx).2.2.2.2.2]
                exact hnext
              · rw [hcursor, (hgeom idx).2.1]
                change u + j + 2 = u + (j + 1) + 1
                omega
          have htail (j : Fin W.length) :
              ∃ cr : CompletedRound rate, extractRound (W.get j) = some cr ∧
                cr.context.payload = P ∧ cr.context.initializer = none ∧
                (W.get j).output.coordinator.failure = none ∧
                (∃ saved, (W.get j).output.next.coordinator = .collection P cr.final saved) ∧
                CoordinatorCollectionLedger.validLedgerCheck cr.final = true ∧
                cr.final.phase = .ready ∧ cr.final.cursor = u + j.val + 2 ∧
                ledgerContext cr.final = ledgerContext c0.preLedger ∧
                (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  P.sigma.val (W.get j).input.time z).Nonempty := by
            obtain ⟨l, saved, hstate, hcontext, _hvalid, _hphase, _hcursor⟩ :=
              hstates j.val (Nat.le_of_lt j.isLt)
            have hne := hnonempty j l saved hstate
            have hs' : (W.get j).input.state.coordinator = .collection P l saved := by
              rw [(hgeom j).1]
              exact hstate
            obtain ⟨hindex, hrecord⟩ := List.getElem?_eq_some_iff.mp (hget j)
            have hstep := actual_continuing rewards C_star C_h z
              ⟨c + 1 + j.val, hindex⟩ P l saved (by rw [hrecord]; exact hs') hne
            dsimp only at hstep
            rw [hrecord] at hstep
            obtain ⟨cr, hcr, hP, _hl, hi, hfail, hnext, hvalid, hphase,
              hcursor, hcontext', _hpending⟩ := hstep
            refine ⟨cr, hcr, hP, hi, hfail, hnext, hvalid, hphase, ?_,
              hcontext'.trans hcontext, ?_⟩
            · rw [hcursor, (hgeom j).2.1]
            · rw [ReferenceFirstCollectionPendingObservation.Q,
                actual_lookup rewards C_star C_h z _ _ (hget j)]
              dsimp only
              rw [hs']
              change (if P.sigma.val = P.sigma.val then l.pending else ∅).Nonempty
              rw [ite_eq_left rfl]
              exact hne
          have hcontinuing : W.takeWhile continuing = W := by
            apply List.takeWhile_eq_self_iff.mpr
            intro r hr
            obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
            obtain ⟨cr, hcr, _hP, hi, _rest⟩ := htail j
            simp only [← hj, continuing, hcr, hi, Option.isNone_none]
          have hdropContinuing : W.dropWhile continuing = [] := by
            apply List.dropWhile_eq_nil_iff.mpr
            intro r hr
            exact (List.takeWhile_eq_self_iff.mp hcontinuing) r hr
          let stream : Segment rate := ⟨cut, c0, K, []⟩
          have hsegment : segment K = some stream := by
            simp only [K, ReferenceCollectionSegmentExtraction.segment, hchoice0, Option.map_some, hcr0,
              Option.isSome_some, ↓reduceIte, hcontinuing, hdropContinuing]
            rfl
          have hall : ∀ r ∈ K, (extractRound r).isSome = true := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · rw [hcr0]
              rfl
            · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
              obtain ⟨cr, hcr, _⟩ := htail j
              rw [← hj, hcr]
              rfl
          have hchain : ReferenceActivePhysicalHorizon.Connected cut.input.state K
              (endpointState cut.input.state K) := by
            apply connected_of_inputs
            intro a
            rcases a with ⟨a, ha⟩
            cases a with
            | zero => rfl
            | succ j =>
              have hj : j < W.length := Nat.lt_of_succ_lt_succ ha
              exact (hgeom ⟨j, hj⟩).1
          have hchecked := connected_segment_initialized K cut.input.state
            (endpointState cut.input.state K) stream a0 hchain hsegment hinit0
          obtain ⟨P', savedFinal, hfinal⟩ := completed_endpoint K cut.input.state c0.preLedger
            (by simp only [K, ne_eq, reduceCtorEq, not_false_eq_true]) hall
          obtain ⟨lFinal, savedFinal', hstateFinal, _rest⟩ := hstates W.length le_rfl
          have hendpoint : endpointState cut.input.state K = E W.length := by
            simp only [K, endpointState, List.foldl_cons, E, List.take_length]
          have hfinalP : P' = P := by
            rw [hendpoint, hstateFinal] at hfinal
            exact (CoordinatorConfiguration.collection.inj hfinal).1.symm
          refine ⟨stream, a0, hsegment, rfl, rfl, hpay0, hinit0, hstart0,
            hsigma0, hcutoff0, hfreeze0, hcursor0, hpending0, hincrement0,
            hgamma0, hraw0, hphase0, hchecked, completed_length K hall, ?_,
            ⟨savedFinal, ?_⟩, ?_⟩
          · intro a
            rcases a with ⟨a, ha⟩
            cases a with
            | zero =>
              have hprepare : (prepare cut.input).coordinator = .live registers owned base
                  (.cutoffChosen dispatched hs ledger hi he hd hclock hpend hn selectedCut) := by
                rw [cut.output_eq] at hcut
                exact hcut
              have hstate := live_input_of_prepare cut.input registers owned base _ hprepare
              have hQ : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  P.sigma.val cut.input.time z = Finset.univ := by
                rw [ReferenceFirstCollectionPendingObservation.Q,
                  actual_lookup rewards C_star C_h z c cut hc]
                dsimp only
                rw [hstate]
                simp only [hpay, ReferenceCollectionPhaseHistory.cutoffChosen, hprepare,
                  and_self, ite_true]
              have hQne : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  P.sigma.val cut.input.time z).Nonempty := by
                rw [hQ]
                exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by have := p.two_le_m; omega⟩⟩
              refine ⟨hQne, hc, actual_lookup rewards C_star C_h z c cut hc, rfl,
                ?_, ?_, ?_, hfail0, cr0, saved0, hcr0, ?_, hnext0,
                hvalid0, hphase1, hcursor1, hcontext1⟩
              · exact hB.2.2.2.1
              · exact hB.2.2.2.2.1
              · exact hB.2.2.2.2.2.1
              · rw [hcontext0]
                exact hpay0
            | succ j =>
              have hj : j < W.length := Nat.lt_of_succ_lt_succ ha
              let idx : Fin W.length := ⟨j, hj⟩
              obtain ⟨cr, hcr, hP, _hi, hfail, ⟨saved, hnext⟩, hvalid, hphase,
                hcursor, hcontext, hQ⟩ := htail idx
              have hg := hgeom idx
              refine ⟨hQ, ?_, actual_lookup rewards C_star C_h z _ _ (hget idx), ?_,
                hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hfail,
                cr, saved, hcr, hP, hnext, hvalid, hphase, ?_, hcontext⟩
              · change R[c + (j + 1)]? = some (W.get idx)
                have hi : c + (j + 1) = c + 1 + j := by omega
                rw [hi]
                exact hget idx
              · change (W.get idx).input.time.val + 1 = u + (j + 1)
                rw [hg.2.1]
                change u + j + 1 = u + (j + 1)
                omega
              · change cr.final.cursor = u + (j + 1) + 1
                change cr.final.cursor = u + j + 2 at hcursor
                omega
          · rw [hfinalP] at hfinal
            exact hfinal
          · change match R[c + K.length]? with
              | none => _
              | some next => _
            have hlen : c + K.length = c + 1 + W.length := by simp only [K, List.length_cons]; omega
            rw [hlen]
            cases hgetEnd : R[c + 1 + W.length]? with
            | none =>
              rw [hgetEnd] at hboundary
              exact ⟨hboundary.1, hboundary.2.trans (congrArg some hendpoint.symm)⟩
            | some next =>
              rw [hgetEnd] at hboundary
              obtain ⟨hstate, hlater, l, saved, _hE, hnext, hempty, _haccepted⟩ := hboundary
              exact ⟨hstate.trans hendpoint.symm, hlater, l, saved, hnext, hempty⟩

end Bandits.Support.ReferenceFirstReplacementCollectionRawPendingTotal

end
