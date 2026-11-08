/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCollectionOldDownChronology

import Lean.Elab.Tactic.Omega

/-!
# Original cutoff OLD DOWN pending prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:459-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-191`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106,151-157`.

The source readout sum below retains the original source, the original
complete-suffix cutoff run, the literal kth prechoice mask, and the date
inclusive first-bad gate.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstReplacementCollectionOldDownCallDates
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCollectionOldDownPendingPrefix

abbrev Parameters := ReferenceOriginalCollectionOldDownChronology.Parameters
abbrev RateInput := ReferenceOriginalCollectionOldDownChronology.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalCollectionOldDownChronology.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalCollectionOldDownChronology.GridRewardTable p
abbrev Record {p : Parameters} (rate : RateInput p) :=
  ReferenceOriginalCollectionOldDownChronology.Record (rate := rate)
abbrev DownRecord {p : Parameters} (rate : RateInput p) :=
  ReferenceOriginalCollectionOldDownChronology.DownRecord (rate := rate)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- The number of actual cutoff-run dates through `j` whose physical date is
at or before the inclusive first-bad date. -/
def actualOldDownPrefixLength
    (K : List (Record rate)) (j beta : ℕ) : ℕ :=
  ((K.take j).takeWhile fun r => r.input.time.val + 1 ≤ beta).length

/-- Literal source readout sum for the OLD/pending DOWN selector on the
original cutoff run. The reward readout, kth-C OLD/pending mask, and inclusive
first-bad gate are all evaluated at the same physical date in `K`. -/
def actualOldDownPrefixReadoutSum
    (z : SourceInput p) (K : List (Record rate)) (j beta : ℕ)
    (i : Fin (p.m - 1)) : ℝ :=
  ((K.take (min j K.length)).map fun r =>
    let t := r.input.time
    (if t.val + 1 ≤ beta then (1 : ℝ) else 0) *
      (if ∃ pending : Finset (Fin (p.m - 1)),
          i ∈ pending ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
              rate rewards C_star C_h t i z = some
                (pending, .old)
        then (1 : ℝ) else 0) *
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t z).sum

private theorem connected_history
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (before : List (Record rate))
    (history : ReferenceCollectionPhaseHistory.History before initial) :
    ReferenceCollectionPhaseHistory.History (before ++ records) final := by
  induction records generalizing initial before with
  | nil =>
      change final = initial at chain
      simpa only [List.append_nil, chain] using history
  | cons r rest ih =>
      have hpre : ReferenceCollectionPhaseHistory.History before r.input.state := by
        rw [chain.1]
        exact history
      have hstep := ReferenceCollectionPhaseHistory.history_step hpre
      have hrecord : (⟨r.input, ReferenceActivePhysicalStep.step r.input, rfl⟩ :
          Record rate) = r := by
        cases r with
        | mk input output heq => cases heq; rfl
      rw [hrecord, ← r.output_eq] at hstep
      have htail := ih chain.2 (before ++ [r]) hstep
      simpa only [List.append_assoc, List.singleton_append] using htail

private theorem actual_input_history (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ReferenceCollectionPhaseHistory.History (R.take k.val) R[k.val].input.state := by
  dsimp only
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
      simp at hk
  | some initial =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      obtain ⟨other, hother, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate z rewards C_star C_h hc
      have heq : other = initial := Option.some.inj (hother.symm.trans hlaunch)
      subst other
      have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate z rewards C_star C_h initial hlaunch
      have hpref := ReferenceFollowerReplyChronology.connected_take_to_input hchain k.val k.isLt
      have hzero : ReferenceCollectionPhaseHistory.History [] initial := by
        intro payload ledger saved hcollection
        rw [hfirst] at hcollection
        cases hcollection
      simpa only [List.nil_append] using
        connected_history rate hpref [] hzero

private theorem actual_old_collection_pending (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator = .collection P ledger saved)
    (i : Fin (p.m - 1))
    (hsigma : ledger.sigma = (P.downRecord i).val.sigma)
    (hold : actualOldAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] i (P.downRecord i)) :
    i ∈ ledger.pending := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      R[k.val].input.state.coordinator = some P := by rw [hstate]; rfl
  have hprior := ReferenceOriginalCollectionOldDownChronology.actual_stored_old_prior_up_start_lt
    rate rewards C_star C_h z k P hstored i hold
  obtain ⟨before, cut, during, hrecords, _hcut, _hlater, _hduring,
    hpending, _hnodup, hwitness⟩ :=
    actual_input_history rate rewards C_star C_h z k P ledger saved hstate
  rw [hpending]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  intro hmem
  rw [List.mem_toFinset, ReferenceCollectionPhaseHistory.acceptedLabels,
    List.mem_filterMap] at hmem
  obtain ⟨r, hr, hlabel⟩ := hmem
  obtain ⟨U, hU, hUsigma⟩ := hwitness r hr i hlabel
  have hrprefix : r ∈ R.take k.val := by
    rw [hrecords]
    exact List.mem_append_right before hr
  obtain ⟨n, hn, hnrecord⟩ := List.mem_take_iff_getElem.mp hrprefix
  have hnR : n < R.length := (lt_min_iff.mp hn).2
  have hnk : n < k.val := (lt_min_iff.mp hn).1
  have hU' : ReferenceCollectionPhaseHistory.AcceptedUp R[n].input i U := by
    rw [hnrecord]
    exact hU
  have hlt := hprior ⟨n, hnR⟩ hnk U hU'
  rw [hUsigma, hsigma] at hlt
  exact (Nat.lt_irrefl _ hlt)

private theorem collection_choice_fields
    (r : Record rate) (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    ledger.sigma = P.sigma.val + 1 ∧
      ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
        c.payload = P ∧ c.preLedger = ledger := by
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hsome : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection ≠ none := by
    rw [← hp, hs]
    exact Option.some_ne_none _
  by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock P ledger saved cutoff
    let x := ReferenceActivePhysicalStep.collectionInput r.input P ledger clock cutoff
    have hd : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
        .collection P ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection x) := by
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, dite_eq_left hv, CoordinatorRoundDispatch.dispatch]
      rfl
    cases ho : CoordinatorRoundDispatch.dispatchCollection x with
    | continuing core snapshot boundary scores =>
        have hsigma : ledger.sigma = P.sigma.val + 1 := by
          simpa only [x, ReferenceActivePhysicalStep.collectionInput,
            CoordinatorRoundDispatch.collectionOperationLedger,
            CoordinatorRecorderComplementBridge.sourceStart] using core.ledger_sigma_eq
        refine ⟨hsigma, ⟨P, ledger, snapshot.clockStarted,
          CoordinatorCollectionInteractive.PreObservationInputs.weights x
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩, ?_, rfl, rfl⟩
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [ite_eq_right hsome, hd, ho]
        rfl
    | laterChosen core consistent started hs instruction hi output he data installed chosen =>
        have htrue : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
          simp only [ReferenceCollectionPhaseHistory.laterChosen, hd, ho]
        exact Bool.noConfusion (hn.symm.trans htrue)
    | _ => simp [hd, ho, ReferenceActivePhysicalStep.DispatchCut.selection] at hsome
  · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate, dite_eq_right hv, ReferenceActivePhysicalStep.DispatchCut.selection] at hsome

private theorem choice_next_collection
    (r : Record rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c) :
    ReferenceCollectionPhaseHistory.CollectionPhase r.output.next.coordinator := by
  have htail := ReferenceCollectionSegmentExtraction.choice_tail r.input c hc
  have hout : r.output.next.coordinator =
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare r.input)
        c.payload c.preLedger c.started c.weights).configuration := by
    rw [r.output_eq]
    exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration htail
  rw [hout]
  exact ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation _ _ _ _ _

private theorem connected_collection_inputs
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hphase : ReferenceCollectionPhaseHistory.CollectionPhase initial.coordinator)
    (hn : ∀ r ∈ records, ReferenceCollectionPhaseHistory.laterChosen r.input = false)
    (hselected : ∀ r ∈ records, ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected) :
    ∀ r ∈ records, ReferenceCollectionPhaseHistory.CollectionPhase r.input.state.coordinator := by
  induction records generalizing initial with
  | nil => intro r hr; cases hr
  | cons r rest ih =>
      have hinput : ReferenceCollectionPhaseHistory.CollectionPhase r.input.state.coordinator := by
        rw [chain.1]
        exact hphase
      have hnext : ReferenceCollectionPhaseHistory.CollectionPhase r.output.next.coordinator := by
        rcases hinput with hd | ⟨P, ledger, saved, hc⟩
        · left
          rw [r.output_eq]
          exact (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hd).1
        · obtain ⟨selected, hs⟩ := hselected r List.mem_cons_self
          obtain ⟨_, c, hchoice, _, _⟩ :=
            collection_choice_fields rate r P ledger saved hc (hn r List.mem_cons_self) selected hs
          exact choice_next_collection rate r c hchoice
      intro current hcurrent
      rcases List.mem_cons.mp hcurrent with hhead | hrest
      · simpa only [hhead] using hinput
      · exact ih chain.2 hnext (fun r hr => hn r (List.mem_cons_of_mem _ hr))
          (fun r hr => hselected r (List.mem_cons_of_mem _ hr)) current hrest

private theorem actual_cutoff_coordinate_data
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, ∃ (k : Fin R.length)
          (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
          k.val = e + a.val ∧ R[k.val] = K.get a ∧
          R[k.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = P ∧
          (actualOldAt (K.get a) i (P.downRecord i) → i ∈ selected.view.pendingAtChoice) ∧
          ((∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
              rate rewards C_star C_h (K.get a).input.time z = some data ∧
            data.1 = P ∧ data.2.1 = selected.view.pendingAtChoice) ∨
          (selected.view.pendingAtChoice = ∅ ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
              rate rewards C_star C_h (K.get a).input.time z = none))
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    have hcut' : R[e]'he = cut := rfl
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        have hfixed :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
            rate rewards C_star C_h z e i
        have hinit :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_initialization
            rate rewards C_star C_h z e i
        have hdataCut := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_choice_at
          rate rewards C_star C_h z e he i
        dsimp only at hfixed hinit hdataCut
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hfixed hinit hdataCut
        dsimp only at hfixed hinit hdataCut
        rw [hbranch] at hfixed hinit hdataCut
        dsimp only at hfixed hinit hdataCut
        obtain ⟨c, _birth, hc, hcP, _hstored, hcPending, _rest⟩ := hinit
        obtain ⟨otherC, hotherC, _hotherP, _hword, dataCut, hdataCut, hdP, hdPending, _⟩ := hdataCut
        have hcc : otherC = c := Option.some.inj (hotherC.symm.trans hc)
        subst otherC
        have hpref : K <+: R.drop e := by
          rw [List.drop_eq_getElem_cons he, hcut']
          exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
        have hlen : e + K.length ≤ R.length := by
          have h := hpref.length_le
          simp only [List.length_drop] at h
          omega
        obtain ⟨span, active, hrun⟩ :=
          ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
            (rate := rate) rewards C_star C_h z ⟨e, he⟩ K.length hlen
        have hrun' : (ReferenceActivePhysicalHorizon.run cut.input.state z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
            cut.input.time.val K.length span active).records = K :=
          hrun.trans (List.prefix_iff_eq_take.mp hpref).symm
        have hchain := ReferenceActivePhysicalHorizon.run_connected cut.input.state z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          cut.input.time.val K.length span active
        rw [hrun'] at hchain
        have hphase := ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h z
        dsimp only at hphase
        have hselectedK : ∀ r ∈ K, ∃ physical : ReferenceActivePhysicalStep.Selection r.input,
            r.output.preparation.coordinator.selection = some physical := by
          intro r hr
          obtain ⟨a, ha⟩ := List.mem_iff_get.mp hr
          obtain ⟨k, _hk, hrk, _⟩ := hfixed a
          have hne := (hphase.1 k).2.1
          rw [hrk, ha] at hne
          exact Option.ne_none_iff_exists'.mp hne
        have hnW : ∀ r ∈ W, ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
          intro r hr
          have h := List.mem_takeWhile_imp hr
          cases hn : ReferenceCollectionPhaseHistory.laterChosen r.input with
          | false => rfl
          | true => rw [hn] at h; cases h
        have htail := connected_collection_inputs rate hchain.2
          (choice_next_collection rate cut c hc) hnW
          (fun r hr => hselectedK r (List.mem_cons_of_mem cut hr))
        change ∀ a : Fin K.length, _
        intro a
        obtain ⟨k, hk, hrecord, hselected⟩ := hfixed a
        obtain ⟨physical, hphysical⟩ := Option.ne_none_iff_exists'.mp (hphase.1 k).2.1
        obtain ⟨hP, hstored, _⟩ := hselected physical hphysical
        refine ⟨k, physical, hk, hrecord, hphysical, hP, ?_⟩
        by_cases ha0 : a.val = 0
        · have hhead : R[k.val] = cut := by
            rw [hrecord]
            simp only [List.get_eq_getElem, ha0, K, List.getElem_cons_zero]
          have hp : physical.view.pendingAtChoice = Finset.univ := by
            have hmap := congrArg (fun o => o.map
              (fun s : ReferenceActivePhysicalStep.Selection R[k.val].input =>
                s.view.pendingAtChoice)) hphysical
            have hheadMap := congrArg (fun r : Record rate =>
              r.output.preparation.coordinator.selection.map
                (fun s => s.view.pendingAtChoice)) hhead
            rw [hheadMap, hbranch] at hmap
            simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, dite_true,
              Option.map_some] at hmap
            exact (Option.some.inj hmap).symm.trans hpending
          refine ⟨fun _ => hp ▸ Finset.mem_univ i, Or.inl ⟨dataCut, ?_, hdP.trans hcP, ?_⟩⟩
          · rw [← hrecord, hhead]
            exact hdataCut
          · exact hdPending.trans (hcPending.trans hp.symm)
        · have haW : a.val - 1 < W.length := by
            have ha := a.isLt
            change a.val < W.length + 1 at ha
            omega
          have hrW : K.get a ∈ W := by
            have heq : K.get a = W[a.val - 1] := by
              simp only [List.get_eq_getElem, K]
              rw [List.getElem_cons, dite_eq_right ha0]
            rw [heq]
            exact List.getElem_mem haW
          have hinputPhase := htail (K.get a) hrW
          rw [← hrecord] at hinputPhase
          rcases hinputPhase with hd | ⟨Q, L, saved, hstate⟩
          · exact ((hphase.1 k).1 hd).elim
          have hQP : Q = P := by
            rw [hstate] at hstored
            exact Option.some.inj hstored
          subst Q
          have hn : ReferenceCollectionPhaseHistory.laterChosen R[k.val].input = false := by
            rw [hrecord]
            exact hnW _ hrW
          obtain ⟨hLP, _c, _hc, _hcP, _hcL⟩ :=
            collection_choice_fields rate R[k.val] P L saved hstate hn physical hphysical
          have hp := ReferenceFirstReplacementCollectionOldDownSenderReadiness.collection_selection_pending
            R[k.val] P L saved hstate hn physical hphysical
          have hlookup := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
            rate rewards C_star C_h z k.val k.isLt
          refine ⟨?_, ?_⟩
          · intro hold
            rw [hp.2]
            apply actual_old_collection_pending rate rewards C_star C_h z k P L saved hstate i
            · exact hLP
            · rw [hrecord]
              exact hold
          · by_cases hnonempty : L.pending.Nonempty
            · obtain ⟨_choice, _hchoice, _hpay, _hpend, _hcutoff, _hinit,
                data, hdata, hdataP, hdataPending, _⟩ :=
                ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualCollectionChoice_nonempty
                  rate rewards C_star C_h R[k.val].input.time z R[k.val] hlookup
                  P L saved hstate hnonempty
              left
              refine ⟨data, ?_, hdataP.trans _hpay, ?_⟩
              · rw [← hrecord]
                exact hdata
              · exact hdataPending.trans (_hpend.trans hp.2.symm)
            · right
              have hempty : L.pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
              refine ⟨hp.2.trans hempty, ?_⟩
              rw [← hrecord,
                ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
                  rate rewards C_star C_h _ z _ hlookup]
              simp only [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
                ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate,
                hnonempty, decide_false, Bool.false_eq_true, ite_false]

private theorem source_old_mask_iff
    (z : SourceInput p) (r : Record rate) (P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (pending : Finset (Fin (p.m - 1)))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time z = some r)
    (hpend : actualOldAt r i (P.downRecord i) → i ∈ pending)
    (hdata : (∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h r.input.time z = some data ∧
      data.1 = P ∧ data.2.1 = pending) ∨
      (pending = ∅ ∧ ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h r.input.time z = none)) :
    (∃ q : Finset (Fin (p.m - 1)), i ∈ q ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
        rate rewards C_star C_h r.input.time i z = some (q, .old)) ↔
      actualOldAt r i (P.downRecord i) := by
  rcases hdata with ⟨data, hd, hdP, hdPending⟩ | ⟨hempty, hnone⟩
  · have hstage : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
        rate rewards C_star C_h r.input.time i z =
        some (pending, ReferenceFirstReplacementCollectionPredictableStages.choiceStage r P i) := by
      unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
      rw [hd]
      simp only [Option.map_some, hdP, hdPending]
      apply congrArg some
      apply congrArg (fun stage => (pending, stage))
      simpa only [ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex,
        PublicDiscreteDraws.followerCount] using
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_choiceStage
          rate rewards C_star C_h r.input.time i z r P hr
    constructor
    · rintro ⟨q, _hiq, hq⟩
      rw [hstage] at hq
      exact (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_iff r P i).mp
        (Prod.mk.inj (Option.some.inj hq)).2
    · intro hold
      refine ⟨pending, hpend hold, ?_⟩
      rw [hstage, (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_iff r P i).mpr hold]
  · have hstage : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
        rate rewards C_star C_h r.input.time i z = none := by
      simp only [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage,
        hnone, Option.map_none]
    constructor
    · rintro ⟨q, _hiq, hq⟩
      rw [hstage] at hq
      cases hq
    · intro hold
      have hi := hpend hold
      rw [hempty] at hi
      exact (Finset.notMem_empty i hi).elim

private theorem source_readout_of_old (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (M : DownRecord rate)
    (hold : actualOldAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] i M) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i r.input.time z =
      if ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val
      then 1 else 0 := by
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hr := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
    rate rewards C_star C_h z k.val k.isLt
  obtain ⟨state, memory, choice, _hinput, _hdomain, _hstart, hchoice, hchoiceDomain, hoperation⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z k i
  obtain ⟨old, oldMemory, hOld, hstatus, _hword⟩ := hold
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hchoice.symm.trans hOld)
  have hstatusChoice : choice.status = .unoccupied := heq.1 ▸ hstatus
  have hprepared : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have halign := r.output.preparation.follower_alignment i
  have hgate : ReferenceActiveAffinePositiveTest.downPrefixGate i r.input.row r.input.time
      (.ordinary choice memory) = decide
        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) := by
    simp only [ReferenceActiveAffinePositiveTest.downPrefixGate,
      ReferenceActiveAffinePositiveTest.downReceiverGate, hchoiceDomain.2.1,
      hstatusChoice, hoperation.1, hoperation.2.1, hoperation.2.2, and_true, true_and]
  unfold ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
  rw [hr]
  change (if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive r.input = true then (1 : ℝ) else 0) =
    if ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val then 1 else 0
  by_cases hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i
  · have hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i := by
      rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
      exact hdraw
    have hpositive : ReferenceActiveAffinePositiveTest.downPositive r.input =
        (decide (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) &&
          decide (0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val)) := by
      unfold ReferenceActiveAffinePositiveTest.downPositive
      dsimp only [PublicDiscreteDraws.followerCount]
      rw [hindex, ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix]
      rw [← hprepared]
      have hchoice' : (r.output.preparation.followers.followers i).configuration =
          .ordinary choice memory := hchoice
      rw [halign.1, halign.2.1, halign.2.2.1, hchoice', hgate]
      rfl
    simp [hdraw, hpositive, PublicDiscreteDraws.followerCount]
  · have hnotSelected : ¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time :=
      fun hs => hdraw hs.2
    simp only [hdraw, false_and, hnotSelected, ite_false]

private theorem actual_record_no_physical_failure (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  intro hf
  rcases (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt_iff r).mp hf with
    hc | ⟨i, hi⟩
  · have hnone := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 k |>.2.2.1
    rw [hnone] at hc
    exact Bool.false_ne_true hc
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hnone, _⟩ :=
      ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
        (rate := rate) rewards C_star C_h z k i
    rw [hnone] at hi
    exact Bool.false_ne_true hi

private theorem selected_channel_down_iff
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1)) :
    ReferenceSelectedAffinePairLaw.selectedChannel p (r.input.row.2 r.input.time).1 =
      some (0, i) ↔
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  constructor
  · intro h
    have hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
        PublicDiscreteDraws.downSlot := by
      by_contra hn
      unfold ReferenceSelectedAffinePairLaw.selectedChannel
        ReferenceSelectedAffinePairLaw.channelFromDraws at h
      simp only [ite_eq_right hn] at h
      by_cases hup : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.upSlot
      · simp only [ite_eq_left hup] at h
        have hf := congrArg Prod.fst (Option.some.inj h)
        cases hf
      · simp only [ite_eq_right hup] at h
        cases h
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p
      (r.input.row.2 r.input.time).1 hdown] at h
    exact ⟨hdown, (Prod.mk.inj (Option.some.inj h)).2⟩
  · rintro ⟨hdown, hi⟩
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p
      (r.input.row.2 r.input.time).1 hdown, hi]
    rfl

private theorem old_count_succ
    (K : List (Record rate)) (i : Fin (p.m - 1)) (M : DownRecord rate)
    (j : ℕ) (hj : j < K.length) :
    ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K (j + 1) i M =
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K j i M +
        if ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt
          K i M ⟨j, hj⟩ then 1 else 0 := by
  by_cases hs : ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt
      K i M ⟨j, hj⟩
  · rw [ite_eq_left hs]
    exact ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount_succ_eq_add_one_of_service
      K j i M hj hs
  · rw [ite_eq_right hs, Nat.add_zero]
    unfold ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
      countedOldDownServiceIndices
    apply congrArg List.length
    apply List.filter_congr
    intro a _ha
    apply decide_eq_decide.mpr
    change (a.val < j + 1 ∧
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt K i M a) ↔
      (a.val < j ∧
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt K i M a)
    constructor
    · rintro ⟨ha, hservice⟩
      have hne : a.val ≠ j := by
        intro he
        have heq : a = ⟨j, hj⟩ := Fin.ext he
        exact hs (heq ▸ hservice)
      exact ⟨by omega, hservice⟩
    · rintro ⟨ha, hservice⟩
      exact ⟨by omega, hservice⟩

private theorem date_gated_sum_count
    (K : List (Record rate)) (i : Fin (p.m - 1)) (M : DownRecord rate)
    (beta : ℕ) (f : Record rate → ℝ)
    (hpoint : ∀ a : Fin K.length, f (K.get a) =
      if ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt K i M a
        then 1 else 0)
    (hmono : ∀ a b : Fin K.length, b.val ≤ a.val →
      (K.get b).input.time.val ≤ (K.get a).input.time.val)
    (j : ℕ) :
    ((K.take j).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum =
      (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K
        (actualOldDownPrefixLength rate K j beta) i M : ℝ) := by
  have hbounded : ∀ n : ℕ, n ≤ K.length →
      ((K.take n).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum =
        (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K
          (actualOldDownPrefixLength rate K n beta) i M : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro _hn
        simp only [List.take_zero, List.map_nil, List.sum_nil, actualOldDownPrefixLength,
          List.takeWhile_nil, List.length_nil,
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount,
          countedOldDownServiceIndices, countedOldDownServiceAt, Nat.not_lt_zero,
          false_and, decide_false, List.filter_false, List.length_nil, Nat.cast_zero]
    | succ n ih =>
        intro hn
        have hnK : n < K.length := by omega
        have hih := ih (by omega)
        have hsum : ((K.take (n + 1)).map fun r =>
              if r.input.time.val + 1 ≤ beta then f r else 0).sum =
            ((K.take n).map fun r =>
              if r.input.time.val + 1 ≤ beta then f r else 0).sum +
            (if K[n].input.time.val + 1 ≤ beta then f K[n] else 0) := by
          rw [List.take_succ_eq_append_getElem hnK, List.map_append, List.sum_append]
          simp only [List.map_singleton, List.sum_singleton]
        rw [hsum, hih]
        by_cases hgood : K[n].input.time.val + 1 ≤ beta
        · have hall : ∀ r ∈ K.take (n + 1),
              (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
            intro r hr
            obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
            have hbK : b < K.length := (lt_min_iff.mp hb).2
            have hbn : b ≤ n := by have := (lt_min_iff.mp hb).1; omega
            have htime := hmono ⟨n, hnK⟩ ⟨b, hbK⟩ hbn
            change K[b].input.time.val ≤ K[n].input.time.val at htime
            rw [hbr] at htime
            exact decide_eq_true (by omega)
          have hLn : actualOldDownPrefixLength rate K n beta = n := by
            unfold actualOldDownPrefixLength
            have hallPre : ∀ r ∈ K.take n,
                (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
              intro r hr
              obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
              apply hall r
              exact List.mem_take_iff_getElem.mpr ⟨b,
                lt_min (by have := (lt_min_iff.mp hb).1; omega)
                  (lt_min_iff.mp hb).2, hbr⟩
            rw [(List.takeWhile_eq_self_iff).mpr hallPre]
            simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hnK)]
          have hLsucc : actualOldDownPrefixLength rate K (n + 1) beta = n + 1 := by
            unfold actualOldDownPrefixLength
            rw [(List.takeWhile_eq_self_iff).mpr hall]
            simp only [List.length_take, Nat.min_eq_left hn]
          rw [hLn, hLsucc, old_count_succ rate K i M n hnK, Nat.cast_add]
          rw [ite_eq_left hgood, show f K[n] =
            if ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt
              K i M ⟨n, hnK⟩ then 1 else 0 from hpoint ⟨n, hnK⟩]
          split <;> simp only [Nat.cast_one, Nat.cast_zero]
        · have hL : actualOldDownPrefixLength rate K (n + 1) beta =
              actualOldDownPrefixLength rate K n beta := by
            unfold actualOldDownPrefixLength
            rw [List.take_succ_eq_append_getElem hnK, List.takeWhile_append]
            simp only [List.takeWhile_cons, hgood, decide_false, Bool.false_eq_true,
              ite_false, List.takeWhile_nil, List.append_nil]
            split
            · rename_i hlen
              exact hlen.symm
            · rfl
          rw [hL, ite_eq_right hgood, add_zero]
  have htake : K.take (min j K.length) = K.take j := by
    by_cases hj : j ≤ K.length
    · rw [Nat.min_eq_left hj]
    · have hle : K.length ≤ j := by omega
      rw [Nat.min_eq_right hle, List.take_length, List.take_of_length_le hle]
  have h := hbounded (min j K.length) (Nat.min_le_right _ _)
  simpa only [actualOldDownPrefixLength, htake] using h

/-- An actual OLD coordinate in the retained cutoff run forces every earlier
actual follower choice in that connected run to be ordinary, unoccupied, and
OLD for the same stored payload. The absent and noncutoff branches remain
literal. -/
theorem actual_cutoff_old_ordinary_prefix
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, actualOldAt (K.get a) i M →
          ∀ b : Fin K.length, b.val ≤ a.val →
            ∃ k : Fin R.length, k.val = e + b.val ∧ R[k.val]'k.isLt = K.get b ∧
              ∃ selected : ReferenceActivePhysicalStep.Selection
                  (R[k.val]'k.isLt).input,
                (R[k.val]'k.isLt).output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = P ∧
              actualOldAt (K.get b) i M
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    have hcut' : R[e]'he = cut := rfl
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        have hpref : K <+: R.drop e := by
          rw [List.drop_eq_getElem_cons he, hcut']
          exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
        have hlen : e + K.length ≤ R.length := by
          have h := hpref.length_le
          simp only [List.length_drop] at h
          omega
        let entry : Fin R.length := ⟨e, he⟩
        obtain ⟨span, active, hrun⟩ :=
          ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
            (rate := rate) rewards C_star C_h z entry K.length hlen
        have hrun' : (ReferenceActivePhysicalHorizon.run cut.input.state
            z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
            cut.input.time.val K.length span active).records = K := by
          exact hrun.trans (List.prefix_iff_eq_take.mp hpref).symm
        have hchain := ReferenceActivePhysicalHorizon.run_connected cut.input.state
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          cut.input.time.val K.length span active
        rw [hrun'] at hchain
        have hfixed :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
            rate rewards C_star C_h z e i
        dsimp only at hfixed
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hfixed
        dsimp only at hfixed
        rw [hbranch] at hfixed
        dsimp only at hfixed
        have hphase := ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h z
        dsimp only at hphase
        change ∀ a : Fin K.length, _
        intro a holdA
        obtain ⟨ka, hka, hrecordA, hselectedA⟩ := hfixed a
        have hnotA := (hphase.1 ka).2.1
        obtain ⟨selectedA, hselectionA⟩ := Option.ne_none_iff_exists'.mp hnotA
        rcases hselectedA selectedA hselectionA with
          ⟨hpayloadA, hstoredA, _hcurrentA, _hpriorA, _hawaitedA⟩
        obtain ⟨stateA, memoryA, hchoiceA, hunoccupiedA, hstaleA⟩ := holdA
        have hchoiceA' :
            (ReferenceFollowerFixedReply.actualChoice (R[ka.val]'ka.isLt) i).configuration =
              .ordinary stateA memoryA := by
          rw [hrecordA]
          exact hchoiceA
        have horderA :=
          ReferenceOriginalCollectionOldDownChronology.actual_stored_choice_current_or_older
            rate rewards C_star C_h z ka P hstoredA i stateA memoryA hchoiceA'
        have hstrictA : ReferencePrelaunchFollower.acceptedStart stateA < M.val.sigma :=
          horderA.resolve_left hstaleA
        intro b hba
        obtain ⟨kb, hkb, hrecordB, hselectedB⟩ := hfixed b
        have hnotB := (hphase.1 kb).2.1
        obtain ⟨selectedB, hselectionB⟩ := Option.ne_none_iff_exists'.mp hnotB
        rcases hselectedB selectedB hselectionB with
          ⟨hpayloadB, hstoredB, _hcurrentB, _hpriorB, _hawaitedB⟩
        have hchoiceFields :=
          ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
            rewards C_star C_h z kb selectedB hselectionB
        obtain ⟨statesB, memoriesB, hchoicesB, hoccupiedB, _⟩ := hchoiceFields
        let stateB := statesB i
        let memoryB := memoriesB i
        have hchoiceB :
            (ReferenceFollowerFixedReply.actualChoice (R[kb.val]'kb.isLt) i).configuration =
              .ordinary stateB memoryB := hchoicesB i
        have hmon :=
          (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i
            b.val a.val b.isLt a.isLt hba stateB stateA memoryB memoryA
            (by
              change (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration = _
              rw [← hrecordB]
              exact hchoiceB)
            (by
              change (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration = _
              rw [← hrecordA]
              exact hchoiceA')).1
        have hunoccupiedB : stateB.status = .unoccupied := by
          by_contra hstatus
          have hcurrent := hoccupiedB i hstatus
          have hcurrent' : stateB.lastDown = some M := by
            simpa [stateB, M, hpayloadB] using hcurrent
          have hstartB : ReferencePrelaunchFollower.acceptedStart stateB = M.val.sigma := by
            simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent']
          omega
        have hstaleB : stateB.lastDown ≠ some M := by
          intro hcurrent
          have hstartB : ReferencePrelaunchFollower.acceptedStart stateB = M.val.sigma := by
            simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
          omega
        have hOldB :=
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.actualOldAt_before_of_connected
            hchain i M a b hba stateA stateB memoryA memoryB
            (by
              rw [← hrecordA]
              exact hchoiceA')
            (by
              rw [← hrecordB]
              exact hchoiceB) hunoccupiedB hstrictA
        exact ⟨kb, hkb, hrecordB, selectedB, hselectionB, hpayloadB, hOldB⟩

/-- If the actual cutoff choice already holds this payload's DOWN word, the
same source run has no OLD contribution anywhere in its retained collection
window. -/
theorem actual_cutoff_already_current_has_no_old
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
            .ordinary choice memory →
          choice.lastDown = some M →
          ∀ a : Fin K.length, ¬ actualOldAt (K.get a) i M
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    have hcut' : R[e]'he = cut := rfl
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        have hfixed :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
            rate rewards C_star C_h z e i
        dsimp only at hfixed
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hfixed
        dsimp only at hfixed
        rw [hbranch] at hfixed
        dsimp only at hfixed
        have hphase := ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h z
        dsimp only at hphase
        intro choice memory hchoice hcurrent
        have hnotOld : ∀ a : Fin K.length,
            ¬ actualOldAt (K.get a) i M := by
          intro a
          obtain ⟨k, _hk, hrecord, hselected⟩ := hfixed a
          obtain ⟨selected, hselection⟩ :=
            Option.ne_none_iff_exists'.mp (hphase.1 k).2.1
          rcases hselected selected hselection with
            ⟨_, _, hcutCurrent, _, _⟩
          have hnoAt := hcutCurrent ⟨choice, memory, hchoice, hcurrent⟩
          rw [hrecord] at hnoAt
          exact hnoAt
        exact hnotOld

/-- An actual OLD choice supplies every earlier OLD coordinate, and the
accepted complete-source failure and follower-preservation results exclude
physical failures on that prefix. The existing local replay identity then
identifies the full positive DOWN list with the literal OLD service count. -/
theorem actual_cutoff_old_backward_positive_count
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, actualOldAt (K.get a) i M →
          ∀ j : ℕ, j ≤ a.val + 1 →
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K j i M =
              (ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)).length
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        have hfixed :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
            rate rewards C_star C_h z e i
        dsimp only at hfixed
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hfixed
        dsimp only at hfixed
        rw [hbranch] at hfixed
        dsimp only at hfixed
        have hphase := ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h z
        dsimp only at hphase
        have hback := actual_cutoff_old_ordinary_prefix rate rewards C_star C_h z e i
        dsimp only at hback
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hback
        dsimp only at hback
        rw [hbranch] at hback
        dsimp only at hback
        intro a holdA j hj
        have hjK : j ≤ K.length := by
          change j ≤ (cut :: (R.drop (e + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length
          have ha : a.val < (cut :: (R.drop (e + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length :=
            a.isLt
          omega
        have hold : ∀ b : Fin K.length, b.val < j → actualOldAt (K.get b) i M := by
          intro b hb
          obtain ⟨kb, hkb, hrecordB, selectedB, hselectionB, hpayloadB, hOldB⟩ :=
            hback a holdA b (by omega)
          exact hOldB
        have hfree : ∀ b : Fin K.length, b.val < j →
            ∀ r ∈ K.take b.val,
              ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r := by
          intro b hb r hr
          obtain ⟨n, hn, helem⟩ := List.mem_iff_getElem.mp hr
          have hnj : n < b.val := by
            simp only [List.length_take] at hn
            omega
          have hnK : n < K.length := lt_trans hnj b.isLt
          have hna : n ≤ a.val := by omega
          have hbackB := hback a holdA ⟨n, hnK⟩ hna
          obtain ⟨kn, hkn, hrecordN, selectedN, hselectionN, hpayloadN, _hOldN⟩ := hbackB
          have htake : (K.take b.val)[n] = K[n]'(by omega) := by
            simp only [List.getElem_take]
          have hrK : r = K.get ⟨n, by omega⟩ := by
            have helem' : K[n] = r := by
              rw [← htake]
              exact helem
            simpa only [List.get_eq_getElem] using helem'.symm
          have hrSource : r = R[kn.val]'kn.isLt :=
            hrK.trans hrecordN.symm
          intro hfailure
          rw [hrSource] at hfailure
          rcases (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt_iff
            (R[kn.val]'kn.isLt)).mp hfailure with hcoord | hfollow
          · have hcoordNone := (hphase.1 kn).2.2.1
            have hcoordNone' :
                (R[kn.val]'kn.isLt).output.coordinator.failure = none := hcoordNone
            rw [hcoordNone'] at hcoord
            exact Bool.false_ne_true hcoord
          · obtain ⟨follower, hfollower⟩ := hfollow
            obtain ⟨_, _, _, _, _, _, _, _, _, _, hfollowerNone, _⟩ :=
              ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
                (rate := rate) rewards C_star C_h z kn follower
            have hfollowerNone' :
                ((R[kn.val]'kn.isLt).output.followers follower).failure = none := hfollowerNone
            rw [hfollowerNone'] at hfollower
            exact Bool.false_ne_true hfollower
        exact
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount_eq_actualDownPositives_length
            K i M j hjK hold hfree

/-- Every coordinate before a later actual OLD choice is itself OLD and
pending for the same payload. Every selected DOWN call there is awaited at
its original source date, whether its observation is zero or positive. -/
theorem actual_cutoff_old_pending_prefix
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, actualOldAt (K.get a) i M →
          ∀ b : Fin K.length, b.val ≤ a.val →
            ∃ (k : Fin R.length)
              (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
              k.val = e + b.val ∧ R[k.val] = K.get b ∧
              R[k.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = P ∧ i ∈ selected.view.pendingAtChoice ∧
              actualOldAt (K.get b) i M ∧
              (ActiveFollowerDownAcceptance.downSelected p i R[k.val].input.row R[k.val].input.time →
                ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt rate
                  R[k.val] i (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
                ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownAwaitedAt
                  rate rewards C_star C_h z i
                  (CoordinatorLocalArmChoice.storedDownFlatWord P i) R[k.val].input.time)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        have hback := actual_cutoff_old_ordinary_prefix rate rewards C_star C_h z e i
        have hdata := actual_cutoff_coordinate_data rate rewards C_star C_h z e i
        have hfixed := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
          rate rewards C_star C_h z e i
        dsimp only at hback hdata hfixed
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hback hdata hfixed
        dsimp only at hback hdata hfixed
        rw [hbranch] at hback hdata hfixed
        dsimp only at hback hdata hfixed
        intro a holdA b hba
        obtain ⟨_kb, _hkb, _hrb, _sb, _hsb, _hPb, holdB⟩ := hback a holdA b hba
        obtain ⟨k, physical, hk, hrecord, hphysical, hP, hpend, _hdata⟩ := hdata b
        have hip := hpend holdB
        refine ⟨k, physical, hk, hrecord, hphysical, hP, hip, holdB, ?_⟩
        intro hdown
        obtain ⟨other, hother, hotherRecord, hfields⟩ := hfixed b
        have hotherK : other = k := Fin.ext (hother.trans hk.symm)
        subst other
        obtain ⟨_hP, _hstored, _hcurrent, _hprior, haw⟩ := hfields physical hphysical
        apply haw hip
        · rw [hrecord]
          exact holdB
        · exact hdown

/-- The literal original-source OLD/pending readout equals the actual OLD
service count on the date-inclusive prefix. The count is not capped by the
decoder quota, and the retained original run continues beyond the date gate. -/
theorem actual_cutoff_old_readout_eq_count
    (z : SourceInput p) (e j : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        actualOldDownPrefixReadoutSum rate rewards C_star C_h z K j beta i =
          (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
            K (actualOldDownPrefixLength rate K j beta) i M : ℝ)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
        have hcoord := actual_cutoff_coordinate_data rate rewards C_star C_h z e i
        dsimp only at hcoord
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hcoord
        dsimp only at hcoord
        rw [hbranch] at hcoord
        dsimp only at hcoord
        let f : Record rate → ℝ := fun r =>
          (if ∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
              ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
                rate rewards C_star C_h r.input.time i z = some (pending, .old)
            then (1 : ℝ) else 0) *
            ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
              (rate := rate) rewards C_star C_h i r.input.time z
        have hfree : ∀ a : Fin K.length, ∀ r ∈ K.take a.val,
            ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r := by
          intro a r hr
          obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
          have hbK : b < K.length := (lt_min_iff.mp hb).2
          obtain ⟨k, _selected, _hk, hrecord, _⟩ := hcoord ⟨b, hbK⟩
          have hsource : R[k.val] = r := hrecord.trans hbr
          rw [← hsource]
          exact actual_record_no_physical_failure rate rewards C_star C_h z k
        have hpoint : ∀ a : Fin K.length, f (K.get a) =
            if ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt
              K i M a then 1 else 0 := by
          intro a
          obtain ⟨k, physical, _hk, hrecord, _hphysical, _hP, hpend, hdata⟩ := hcoord a
          have hr := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
            rate rewards C_star C_h z k.val k.isLt
          rw [hrecord] at hr
          have hmask := source_old_mask_iff rate rewards C_star C_h z (K.get a) P i
            physical.view.pendingAtChoice hr hpend hdata
          have hservice :
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt K i M a ↔
              actualOldAt (K.get a) i M ∧
                ActiveFollowerDownAcceptance.downSelected p i (K.get a).input.row (K.get a).input.time ∧
                0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val := by
            unfold ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt
            rw [selected_channel_down_iff rate]
            constructor
            · rintro ⟨hold, hdown, hpositive, _⟩
              exact ⟨hold, hdown, hpositive⟩
            · rintro ⟨hold, hdown, hpositive⟩
              exact ⟨hold, hdown, hpositive, hfree a⟩
          change (if _ then (1 : ℝ) else 0) * _ = _
          simp only [hmask]
          by_cases hold : actualOldAt (K.get a) i M
          · have holdR : actualOldAt R[k.val] i M := by rw [hrecord]; exact hold
            have hread := source_readout_of_old rate rewards C_star C_h z k i M holdR
            dsimp only at hread
            rw [hrecord] at hread
            rw [ite_eq_left hold, one_mul, hread]
            simp only [hservice, hold, true_and]
            rfl
          · have hnservice : ¬
                ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt K i M a :=
              fun hs => hold hs.1
            rw [ite_eq_right hold, zero_mul, ite_eq_right hnservice]
        have hmono : ∀ a b : Fin K.length, b.val ≤ a.val →
            (K.get b).input.time.val ≤ (K.get a).input.time.val := by
          intro a b hba
          by_cases heq : b.val = a.val
          · have hfin : b = a := Fin.ext heq
            rw [hfin]
          · obtain ⟨ka, _sa, hka, hra, _⟩ := hcoord a
            obtain ⟨kb, _sb, hkb, hrb, _⟩ := hcoord b
            have hlt : kb.val < ka.val := by omega
            have htime := (ReferenceFirstReplacementCollectionPureUpWindowCut.complete_records_chronological
              rate z rewards C_star C_h).rel_getElem_of_lt kb.isLt ka.isLt hlt
            rw [hrb, hra] at htime
            exact Nat.le_of_lt htime
        have htake : K.take (min j K.length) = K.take j := by
          by_cases hj : j ≤ K.length
          · rw [Nat.min_eq_left hj]
          · have hle : K.length ≤ j := by omega
            rw [Nat.min_eq_right hle, List.take_length, List.take_of_length_le hle]
        have hform : actualOldDownPrefixReadoutSum rate rewards C_star C_h z K j beta i =
            ((K.take j).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum := by
          unfold actualOldDownPrefixReadoutSum
          rw [htake]
          congr 1
          apply List.map_congr_left
          intro r _hr
          dsimp only [f]
          by_cases ht : r.input.time.val + 1 ≤ beta
          · simp only [ht, ite_true, one_mul]
          · simp only [ht, ite_false, zero_mul]
        exact hform.trans (date_gated_sum_count rate K i M beta f hpoint hmono j)

end Bandits.Support.ReferenceOriginalCollectionOldDownPendingPrefix
