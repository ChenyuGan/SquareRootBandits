/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# First excluded record of a corrected collection segment

The literal segment extractor stops at the first record which is not a
continuing completed collection round.  On the actual corrected-cell source,
the accepted collection history identifies the state at that boundary.  The
source dispatcher and receiver then exclude an old continuing choice there.
This is an internal deterministic execution result; it adds no calendar date
and makes no regret-closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceFirstCorrectedCollectionBoundaryExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem head_dropWhile_false
    (xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (h : (xs.dropWhile ReferenceCollectionSegmentExtraction.continuing).head? = some r) :
    ReferenceCollectionSegmentExtraction.continuing r = false := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      cases hp : ReferenceCollectionSegmentExtraction.continuing a with
      | false =>
          have hneg : ¬ ReferenceCollectionSegmentExtraction.continuing a = true := by
            rw [hp]
            decide
          simp only [List.dropWhile_cons_of_neg hneg, List.head?_cons,
            Option.some.injEq] at h
          cases h
          exact hp
      | true =>
          simp only [List.dropWhile_cons_of_pos hp] at h
          exact ih h

/-- A nonempty segment's first excluded suffix record is precisely outside
the maximal `takeWhile` prefix.  The premise exposes the literal old
`segmentAt` query, while `hboundary` is obtained from the actual boundary
history, never from an invented successor record. -/
private theorem no_choice_at_remaining_head
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate) (hne : seg.records ≠ [])
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (v : ℕ) (hv : v = e + seg.records.length)
    (hvR : v < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hdrop : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop v = seg.remaining)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[v]'hvR).input.state.coordinator = .collection P l saved) :
    ∀ c : Choice rate,
      choice ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[v]'hvR).input ≠ some c := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hsegment := (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
  have hpartition := ReferenceCollectionSegmentExtraction.segmentAt_partition R e seg hseg
  have hliteral : ∃ entry rest,
      R.drop e = entry :: rest ∧
      seg.records = entry :: rest.takeWhile ReferenceCollectionSegmentExtraction.continuing ∧
      seg.remaining = rest.dropWhile ReferenceCollectionSegmentExtraction.continuing := by
    cases hd : R.drop e with
    | nil => simp only [hd, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hsegment
    | cons entry rest =>
        rw [hd] at hsegment
        unfold ReferenceCollectionSegmentExtraction.segment at hsegment
        cases hc : ReferenceCollectionSegmentExtraction.choice entry.input with
        | none => simp only [hc, Option.map_none, reduceCtorEq] at hsegment
        | some c =>
            simp only [hc, Option.map_some] at hsegment
            cases he : ReferenceCollectionSegmentExtraction.extractRound entry with
            | none =>
                simp only [he, Option.isSome_none, Bool.false_eq_true,
                  ↓reduceIte, Option.some.injEq] at hsegment
                have hrecords : seg.records = [] :=
                  congrArg (fun s : Segment rate => s.records) hsegment.symm
                exact False.elim (hne hrecords)
            | some done =>
                simp only [he, Option.isSome_some, ↓reduceIte,
                  Option.some.injEq] at hsegment
                cases hsegment
                exact ⟨entry, rest, rfl, rfl, rfl⟩
  obtain ⟨entry, rest, hdropE, hrecords, hremaining⟩ := hliteral
  have hdropTail : (R.drop e).drop seg.records.length = seg.remaining := by
    rw [← hpartition, List.drop_append_length]
  have hdropWhile : R.drop (e + seg.records.length) =
      rest.dropWhile ReferenceCollectionSegmentExtraction.continuing := by
    calc
      R.drop (e + seg.records.length) = (R.drop e).drop seg.records.length := by
        rw [List.drop_drop]
      _ = seg.remaining := hdropTail
      _ = rest.dropWhile ReferenceCollectionSegmentExtraction.continuing := hremaining
  have hvcons : R.drop v = R[v]'hvR :: R.drop (v + 1) :=
    List.drop_eq_getElem_cons hvR
  have hdropWhileV : R.drop v =
      rest.dropWhile ReferenceCollectionSegmentExtraction.continuing := by
    rw [hv]
    exact hdropWhile
  have hhead : (rest.dropWhile ReferenceCollectionSegmentExtraction.continuing).head? =
      some (R[v]'hvR) := by
    calc
      _ = (R.drop v).head? := congrArg List.head? hdropWhileV.symm
      _ = some (R[v]'hvR) := by rw [hvcons]; rfl
  have hnotContinuing : ReferenceCollectionSegmentExtraction.continuing
      (R[v]'hvR) = false := head_dropWhile_false rest (R[v]'hvR) hhead
  intro c hc
  let k : Fin R.length := ⟨v, hvR⟩
  have hrecv :=
    ReferenceCompleteContinuingCollectionReception.actual_continuing_collection_reception_finish
      rate rewards C_star C_h z k P l saved hstate c hc
  rcases hrecv with ⟨o, started, decoded, bank, finished, clockFinished,
    hpayload, hpre, hinitializer, hlocal, hrecording, hfresh, hstart, hvalidStarted,
    hphaseStarted, hcursorStarted, hcutLower, hcutCursor, hcursorBound,
    hreceiveInput, hreceived, hbank, hbankWellFormed, hbankCheck, hbankFrame,
    hfinish, hfinishCandidate, hvalidFinished, hphaseFinished, hcursorFinished,
    hincrements, hassignment, hsigma, hcutoff, hfreeze, hbase, hpending,
    hcutoffRegisters, hcurrentRegisters, hrawBuffer, henabledHistory,
    hclockValid, hclockSigma, hclockCutoff, hclockU, hcutoffAtTime,
    hstartTimeValid, hfinishTimeValid, hclockFinished, hpostChoice,
    hcollectionFinish, hobserve, hdiagnostic, hmismatch⟩
  have hnext : (R[v]'hvR).output.next.coordinator =
      .collection P finished clockFinished.clock.lastProposal := by
    calc
      (R[v]'hvR).output.next.coordinator =
          (ReferenceActivePhysicalStep.step (R[v]'hvR).input).next.coordinator := by
            rw [(R[v]'hvR).output_eq]
      _ = (prepare (R[v]'hvR).input).observeCoordinator.configuration :=
        (ReferenceActivePhysicalStep.step_next_fields (R[v]'hvR).input).1
      _ = .collection P finished clockFinished.clock.lastProposal := by
        rw [hobserve]
  obtain ⟨done, hdone⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_complete
      (R[v]'hvR) c P finished clockFinished.clock.lastProposal hc hnext
  have hcontext : done.context = c := by
    unfold ReferenceCollectionSegmentExtraction.extractRound at hdone
    rw [hc] at hdone
    exact (ReferenceCollectionSegmentExtraction.extractWith_endpoint
      (R[v]'hvR).input c (R[v]'hvR).output.coordinator done hdone).1
  have hcontinuing : ReferenceCollectionSegmentExtraction.continuing (R[v]'hvR) = true := by
    unfold ReferenceCollectionSegmentExtraction.continuing
    rw [hdone]
    simp [hcontext, hinitializer]
  rw [hcontinuing] at hnotContinuing
  cases hnotContinuing

private theorem collection_later_or_choice
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator = .collection P l saved)
    (hselection : (prepare ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt).input).coordinator.selection ≠ none) :
    laterChosen ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt).input = true ∨
      ∃ c : Choice rate,
        choice ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input = some c := by
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]'k.isLt |>.input
  have hcutoff : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    by_contra hbad
    have hbad' : ¬ (1 ≤ l.cutoff ∧ l.cutoff ≤ p.T) := hbad
    obtain ⟨hinvalid, _⟩ :=
      ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff x P l saved hstate hbad'
    apply hselection
    change (ReferenceActivePhysicalStep.dispatch x).selection ≠ none at hselection
    rw [hinvalid] at hselection
    simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselection
  let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x P l clock cutoff
  have hprepared : (prepare x).coordinator =
      .collection P l clock cutoff (CoordinatorRoundDispatch.dispatchCollection input) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    dsimp [ReferenceActivePhysicalStep.dispatch, x]
    rw [hstate]
    simp only [dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
    rfl
  cases hdispatch : CoordinatorRoundDispatch.dispatchCollection input with
  | continuing core snapshot boundary scores =>
      right
      let c : Choice rate := ⟨P, l, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights input
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff (.continuing core snapshot boundary scores) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simp [hprepareCase, DispatchCut.selection]
      have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [ite_eq_right hselectionX]
        rw [hprepareCase]
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, c, input, clock, cutoff]
      exact ⟨c, hchoice⟩
  | laterChosen core consistent started hstart instruction hinstruction output
      hcons data installed selected =>
      left
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff
            (.laterChosen core consistent started hstart instruction hinstruction
              output hcons data installed selected) := by
        rw [hprepared, hdispatch]
      simp [ReferenceCollectionPhaseHistory.laterChosen, hprepareCase, x]
  | clockFailure failure hstart =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff (.clockFailure failure hstart) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | localFailure started hstart hcore reason =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff (.localFailure started hstart hcore reason) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | coreFailure core started hstart reason =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff (.coreFailure core started hstart reason) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | laterReconstructionFailure core consistent started hstart instruction hinstruction
      reason hlater =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff
            (.laterReconstructionFailure core consistent started hstart instruction hinstruction
              reason hlater) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff
            (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff
            (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX
  | laterChoiceFailure core consistent started hstart instruction hinstruction output hcons data installed reason =>
      have hprepareCase : (prepare x).coordinator =
          .collection P l clock cutoff
            (.laterChoiceFailure core consistent started hstart instruction hinstruction output hcons data installed reason) := by
        rw [hprepared, hdispatch]
      have hselectionX : (prepare x).coordinator.selection ≠ none := by
        simpa [x] using hselection
      rw [hprepareCase] at hselectionX
      simp [DispatchCut.selection] at hselectionX

/-- The literal source queries and deterministic exclusion conclusion at a
corrected collection cutoff. The accepted calendar/readout joins provide the
segment and cutoff evidence for the actual first corrected cutoff. -/
def firstCellCollectionBoundaryExclusionResult
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate) : Prop :=
    segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg ∧
    seg.records ≠ [] ∧
    ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let v := e + seg.records.length
      ∃ saved : Option (Fin p.T × Bool),
        (endpointState seg.entry.input.state seg.records).coordinator =
          .collection seg.context.payload seg.final saved ∧
        seg.final.cursor = s + v + 1 ∧
        (v = R.length ∨ ∃ hv : v < R.length,
          R[v].input.state = endpointState seg.entry.input.state seg.records ∧
          R[v].input.state.coordinator = .collection seg.context.payload seg.final saved ∧
          R[v].input.time.val = s + v ∧ R.drop v = seg.remaining ∧
          ReferenceCollectionPhaseHistory.laterChosen R[v].input = true ∧
          seg.final.pending = ∅ ∧
          (∀ i : Fin (p.m - 1),
            ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e ≤ k.val ∧ k.val < v ∧ R[k.val] ∈ seg.records ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
              U.val.sigma = seg.final.sigma) ∧
          (∀ c : Choice rate, choice R[v].input ≠ some c))

/-- Eliminate the old collection-choice boundary alternative for any literal
nonempty corrected-cell cutoff segment. The source queries are included in
the returned `firstCellCollectionBoundaryExclusionResult`. -/
theorem firstCell_collection_boundary_exclusion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    firstCellCollectionBoundaryExclusionResult rate rewards C_star C_h z e seg := by
  unfold firstCellCollectionBoundaryExclusionResult
  refine ⟨hseg, hne, hcut, ?_⟩
  intro R s v
  have hhistory :=
    ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
      rate rewards C_star C_h u t z hz e seg hseg hne hcut
  rcases hhistory with ⟨hq, hwhole, hpayload, saved, hend, hcursor, during,
    hduring, htake, hnotEntryLater, hduringNotChosen, hpending, hnodup,
    hwitnesses, hboundary⟩
  refine ⟨saved, hend, hcursor, ?_⟩
  rcases hboundary with hhorizon | ⟨hv, hstate, hcoordinator, htime, hdrop, hbranch⟩
  · exact Or.inl hhorizon
  · rcases hbranch with hnotLater | ⟨hlater, hempty, hw⟩
    · have hnoChoice := no_choice_at_remaining_head rewards C_star C_h z e seg hne
        hseg v rfl hv hdrop seg.context.payload seg.final saved hcoordinator
      have hphase :=
        (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h z).1 ⟨v, hv⟩
      have hprepare : (R[v]'hv).output.preparation = prepare (R[v]'hv).input := by
        rw [(R[v]'hv).output_eq]
        rfl
      have hselection : (prepare (R[v]'hv).input).coordinator.selection ≠ none := by
        rw [← hprepare]
        exact hphase.2.1
      have hdispatchChoice := collection_later_or_choice rewards C_star C_h z
        ⟨v, hv⟩ seg.context.payload seg.final saved hcoordinator hselection
      rcases hdispatchChoice with hlater' | ⟨c, hc⟩
      · exact False.elim (Bool.noConfusion (hnotLater.symm.trans hlater'))
      · exact False.elim (hnoChoice c hc)
    · have hnoChoice := no_choice_at_remaining_head rewards C_star C_h z e seg hne
        hseg v rfl hv hdrop seg.context.payload seg.final saved hcoordinator
      exact Or.inr ⟨hv, hstate, hcoordinator, htime, hdrop, hlater, hempty,
        hw, hnoChoice⟩

/-- The calendar/readout joins identify the actual first corrected-cell
collection cutoff (or the horizon) from the original corrected-cell input.
This packages the conditional boundary theorem with those source-derived
segment, nonemptiness, and cutoff queries, so callers do not supply them. -/
theorem firstCell_actual_collection_boundary_exclusion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (hq : t.val + 1 < p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let e := b + 1 + W.length
    e ≤ R.length ∧
      (e = R.length ∨ ∃ (seg : Segment rate),
        firstCellCollectionBoundaryExclusionResult rate rewards C_star C_h z e seg) := by
  intro R b
  obtain ⟨L, c, birth, _hL, _hc, _hprefix, _hLb, _hsBirth, _hb, _hbt,
      _hrows, _hselected, _hrewards, _henabled, _hlater, _hcell, _hout, hcalendar⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hz
  obtain ⟨birth', rout, qout, beta, _hb', _hbt', _hdate, _hrows',
      _hselected', _hrewards', _hbirth, _hsigma, _hlaterBirth, hnext, _htail⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  have hbirthEq : birth' = birth := Option.some.inj (_hb'.symm.trans _hb)
  subst birth'
  obtain ⟨_hsigmaNumerical, _hcalendarTail⟩ := hcalendar rout qout beta hnext
  obtain ⟨hbound, _htimeBound, hreadoutTail⟩ := _htail hq
  obtain ⟨rE, qE, _hpayload, _hinterior, hcase⟩ := hreadoutTail
  constructor
  · exact hbound
  · rcases hcase with hterminal | ⟨he, seg, I, l0, hseg, _hentry,
        _hpay, _hpre, _hinitializer, _hI, _hchecked, _harm, _hsigmaI,
        _hcutoffI, _hfirstCutoff, _hfreeze, _hbase, hcut, hnonempty,
        _hpartition, _htimes, _hqueue⟩
    · exact Or.inl hterminal
    · obtain ⟨during, hrecords⟩ := hnonempty
      have hne : seg.records ≠ [] := by
        rw [hrecords]
        simp
      refine Or.inr ⟨seg, ?_⟩
      exact firstCell_collection_boundary_exclusion rate rewards C_star C_h u t z hz
        (b + 1 + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1)).length) seg hseg hne hcut

end Bandits.Support.ReferenceFirstCorrectedCollectionBoundaryExclusion

end
