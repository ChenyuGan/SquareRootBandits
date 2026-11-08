/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergySum

/-!
# Immediate physical recording after the original first collection call

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`06_interruptions.tex:31-100,246-299,355-426`,
`04_slow_fast_learner.tex:96-188,245-278`, and
`appendix_a_local_protocol.tex:28-79`.

All source arguments below are original source inputs. The first-call branch
is literal; there is no renewal-subtype coercion or renewed assignment draw.
These are internal physical readouts, not a conditional law or regret closure.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedNextPhysicalReadout

variable {p : ConstructorDimensions.Parameters}

local notation "X" => BootstrapPrivateRoundStreams.SourceInput p

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal adjacent calendar cell, with both kinds of outer absence. -/
def nextCell (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  (actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x).bind
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)

/-- Numerical parameters are projections of the actual optional cell. -/
def nextParameters (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  (nextCell rate rewards C_star C_h t hq x).map fun c => (c.enabled, c.rate)

/-- The outer option records presence; the inner option is the physical marker. -/
def nextMarker (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  (nextCell rate rewards C_star C_h t hq x).map fun c => c.recordedArm

private theorem takeWhile_first_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (r : A) (hr : xs[n]? = some r)
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
          have hhead : f head = true := hearlier 0 (by omega) head rfl
          have hrest := ih n
            (by simpa only [List.getElem?_cons_succ] using hr)
            (fun j hj q hq => hearlier (j + 1) (by omega) q
              (by simpa only [List.getElem?_cons_succ] using hq))
          simpa only [List.takeWhile_cons, hhead, ↓reduceIte, List.length_cons]
            using congrArg Nat.succ hrest

/-- The actual first invocation is the first replacement, on the original
source. Earlier absent selectors exclude earlier chosen replacements. -/
theorem firstCell_firstReplacement_record (u t : Fin p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      R[v]? = some r ∧ actualRecord rate rewards C_star C_h t x = some r ∧
      r.input.time = t ∧ ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
  classical
  dsimp only
  obtain ⟨n, r, theta, hr, ht, har, hcall, _hrows, _hselected, _hrewards,
      hearlier, _hrest⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
      rate rewards C_star C_h u t x hx
  obtain ⟨n', r', _theta', _old, _l, _saved, _c, _hr', _ht', har',
      _hcall', _hrows', _hselected', _hrewards', _hcoord', _hcut', _hcursor',
      _hpending', _hregister', _hbound', _hadmissible, hchosen, _hcell⟩ :=
    ReferenceFirstCollectionCorrectedCallAdmissibility.firstCell_corrected_parameters_admissible
      rate rewards C_star C_h u t x hx
  have heq : r' = r := Option.some.inj (har'.symm.trans har)
  subst r'
  obtain ⟨old, ledger, saved, hcoord, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  have hwn : w < n :=
    ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
      rate rewards C_star C_h x n r hr old ledger saved hcoord
  have hn : n < R.length := (List.getElem?_eq_some_iff.mp hr).1
  let tail := R.drop (w + 1)
  have htail : tail[n - (w + 1)]? = some r := by
    simpa only [tail, List.getElem?_drop, Nat.add_sub_of_le (by omega : w + 1 ≤ n)]
      using hr
  have hscan : (tail.takeWhile fun q =>
      !ReferenceCollectionPhaseHistory.laterChosen q.input).length = n - (w + 1) := by
    apply takeWhile_first_false _ tail _ r htail
    · simp only [hchosen, Bool.not_true]
    · intro k hk q hq
      have hget : R[w + 1 + k]? = some q := by
        simpa only [tail, List.getElem?_drop] using hq
      have hnone := hearlier (w + 1 + k) (by omega) q hget
      change ReferenceLaterAssignmentFibreStep.parameters? q.input = none at hnone
      have hfalse : ReferenceCollectionPhaseHistory.laterChosen q.input = false := by
        cases hb : ReferenceCollectionPhaseHistory.laterChosen q.input with
        | false => rfl
        | true =>
            have hpresent := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present q.input hb
            rw [hnone] at hpresent
            cases hpresent
      simp only [hfalse, Bool.not_false]
  have hhead : ((R.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hwindow : (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      1 + (n - (w + 1)) := by
    simp only [ReferenceCollectionPhaseHistory.collectionWindow, List.length_append, hhead]
    exact congrArg (1 + ·) hscan
  have hv : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length = n := by omega
  refine ⟨r, ?_, har, ht, hchosen⟩
  change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some r
  rw [hv]
  exact hr

/-- The successor is the adjacent actual record. All row, private selection,
whole-reward, time and state boundaries are preserved. -/
theorem firstCell_successor_records (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    ∃ r0 r1 : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      R[v]? = some r0 ∧ R[v + 1]? = some r1 ∧
      actualRecord rate rewards C_star C_h t x = some r0 ∧
      actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r1 ∧
      r0.input.time = t ∧ r1.input.time = ⟨t.val + 1, hq⟩ ∧
      r1.input.state = r0.output.next ∧
      r1.input.rows = x.1.2 ∧
      r1.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p x ∧
      r1.input.rewards = rewards ∧
      ReferenceCollectionPhaseHistory.laterChosen r0.input = true := by
  dsimp only
  obtain ⟨r0, h0, ha0, ht0, hchosen⟩ :=
    firstCell_firstReplacement_record rate rewards C_star C_h u t x hx
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  have hclock := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate x rewards C_star C_h v r0 h0
  rw [ht0] at hclock
  change t.val = s + v at hclock
  have hlen : v + 1 < R.length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    change v + 1 < p.T - s
    omega
  let r1 := R[v + 1]
  have h1 : R[v + 1]? = some r1 := List.getElem?_eq_getElem hlen
  have ha1 : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r1 := by
    rw [actualRecord, ite_eq_left (show s ≤ t.val + 1 by omega)]
    have he : t.val + 1 - s = v + 1 := by omega
    change R[t.val + 1 - s]? = some r1
    rw [he]
    exact h1
  have hadj := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_actual_successor
    rate x rewards C_star C_h
  dsimp only at hadj
  dsimp only [R, w, v] at h1
  simp only [h0, h1] at hadj
  obtain ⟨_hc, _hspan0, _hspan1, _hrun0, _hrun1, hstate, _htime⟩ := hadj
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h ⟨t.val + 1, hq⟩ x r1 ha1
  exact ⟨r0, r1, h0, h1, ha0, ha1, ht0, hf.2.2.1, hstate,
    hf.1, hf.2.1, hf.2.2.2, hchosen⟩


private theorem live_baseline_zero
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

/-- A continuing chosen next constructor produces an actual LIVE source
cell and ordinary PREPARE configurations, without assuming tail success. -/
theorem firstCell_next_continuing (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r =
            some cell.input ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some cell.input ∧
        (∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
          SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
          (∀ other, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a → other = owner) ∧
          r.output.preparation.arms.actions owner = a ∧
          r.gridFeedback owner = rewards r.input.time a ∧
          (r.output.ownEntries owner).2.val.val =
            ((rewards r.input.time a).val : ℝ) / (D p : ℝ))
    | _ => True := by
  obtain ⟨r0, r1, h0, h1, _ha0, ha1, _ht0, _ht1, _hstate, _hrows,
      _hselected, _hrewards, hchosen⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have heq : r1 = r := Option.some.inj (ha1.symm.trans hr)
  subst r1
  have h := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_next_continuing_readout
    rate x rewards C_star C_h
  dsimp only at h
  simp only [h0] at h
  have hp : r0.output.preparation = prepare r0.input := by rw [r0.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hb : r0.output.preparation.coordinator <;> simp only [hb, Bool.false_eq_true] at hchosen
  rename_i out
  cases out <;> simp only at hchosen <;> try contradiction
  simp only [hb, h1] at h
  cases hd : r.output.preparation.coordinator <;> try trivial
  rename_i out
  cases out <;> try trivial
  simp only [hd] at h
  obtain ⟨_selected, _hsel, _hpayload, _hsigma, _hlive, _hfollowers,
      cell0, hread, _hcellPayload, _harrival, _howner⟩ := h
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let k : Fin R.length := ⟨v + 1, (List.getElem?_eq_some_iff.mp h1).1⟩
  have hkr : R.get k = r := (List.getElem?_eq_some_iff.mp h1).2
  have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
    rate rewards C_star C_h x k cell0.input (by rw [hkr]; exact hread)
  dsimp only at hphysical
  rw [hkr] at hphysical
  obtain ⟨cell, hcell, _henabled, _hlive, _htrace, _hrows', _hselected',
    _hrewards', _hmarker, _hdown, howner, _⟩ := hphysical
  have hread' : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r = some cell.input := by
    rw [hcell]
    exact hread
  rw [← hcell] at howner
  exact ⟨cell, hread', live_baseline_zero rate r _ cell.input hread', howner⟩

/-- An immediate cutoff produces actual unoccupied PREPARE configurations
and the actual collection readout, including a disabled boundary cell. -/
theorem firstCell_next_cutoff (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.output.preparation.coordinator with
    | .live _ _ _ (.cutoffChosen ..) =>
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r ∧
      ∃ c, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c
    | _ => True := by
  obtain ⟨r0, r1, h0, h1, _ha0, ha1, _ht0, _ht1, _hstate, _hrows,
      _hselected, _hrewards, hchosen⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have heq : r1 = r := Option.some.inj (ha1.symm.trans hr)
  subst r1
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  have h := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate x rewards C_star C_h
  dsimp only at h
  simp only [h0] at h
  have hp : r0.output.preparation = prepare r0.input := by rw [r0.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hb : r0.output.preparation.coordinator <;> simp only [hb, Bool.false_eq_true] at hchosen
  rename_i out
  cases out <;> simp only at hchosen <;> try contradiction
  simp only [hb] at h
  cases hd : r.output.preparation.coordinator <;> try trivial
  rename_i registers owned base out
  cases out <;> try trivial
  have htail : ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v = [] := by
    apply List.takeWhile_eq_nil_iff.mpr
    intro hlen
    have hget : (R.drop (v + 1)).get ⟨0, hlen⟩ = r := by
      have he := List.getElem?_eq_getElem hlen
      have h1local : R[v + 1]? = some r := h1
      simp only [List.getElem?_drop, Nat.add_zero, h1local] at he
      exact (Option.some.inj he).symm
    rw [hget]
    simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hd,
      Bool.false_eq_true, not_false_eq_true]
  dsimp only [R, w, v] at htail
  simp only [htail, List.length_nil, Nat.add_zero, h1, hd] at h
  obtain ⟨_hnoncontinuing, hregisters, _htime, _hindex, _hrows, _hselected,
      _hrewards, _hsigma, hbase, _hcutoff, _hgrid, _htrigger,
      _selected, _hselection, _hpayload, _hpending, _hselectedCutoff, hfollowers⟩ := h
  have ho : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r := by
    intro i
    obtain ⟨old, memory, _hinput, _hdomain, _hbound, _hzero, _haccepted,
      _hoccupied, _hdecision, _hstart, hprepared, _⟩ := hfollowers i
    simp only [hprepared]
  have hs : s < registers.payload.sigma.val := by rw [hregisters]; exact hbase
  have hz : 0 < registers.payload.sigma.val := by omega
  have hdom : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s r).isSome = true :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s r).2
      ⟨ho, by simpa only [hd] using hs⟩
  cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s r with
  | none => simp only [hc, Option.isSome_none, Bool.false_eq_true] at hdom
  | some c =>
    refine ⟨ho, c, rfl, ?_⟩
    unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hc ⊢
    simp only [dite_eq_left ho, hd, dite_eq_left hs, Option.some.injEq] at hc
    simp only [dite_eq_left ho, hd, dite_eq_left hz]
    exact congrArg some hc


private theorem livePostChoice_phase
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (livePostChoice prepared registers owned base started).configuration with
    | .live .. => True
    | .dagger => True
    | _ => False := by
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (liveRecordingInput prepared registers started) with
  | none => simp [livePostChoice, hrecording, coordinatorFailure]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
    | error reason => simp [livePostChoice, hrecording, hservice, coordinatorFailure]
    | ok serviced =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none => simp [livePostChoice, hrecording, hservice, hconfirmation, coordinatorFailure]
      | some pending =>
        cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row
          <;> simp [livePostChoice, hrecording, hservice, hconfirmation, hfinish, coordinatorFailure]

/-- The actual adjacent incoming phase is LIVE or dagger. A post-choice
failure is preserved; it is not an assumed successful tail. -/
theorem firstCell_next_input_phase (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.input.state.coordinator with | .live .. => True | .dagger => True | _ => False := by
  obtain ⟨r0, r1, _h0, _h1, _ha0, ha1, _ht0, _ht1, hstate, _hrows,
      _hselected, _hrewards, hchosen⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have heq : r1 = r := Option.some.inj (ha1.symm.trans hr)
  subst r1
  have hp : r0.output.preparation = prepare r0.input := by rw [r0.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hb : r0.output.preparation.coordinator <;> simp only [hb, Bool.false_eq_true] at hchosen
  rename_i out
  cases out <;> simp only at hchosen <;> try contradiction
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r0
  simp only [hb] at hframes
  have hsel : r0.output.preparation.coordinator.selection ≠ none := by
    simp only [hb, DispatchCut.selection, selectionAt, dite_eq_left hframes.1,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have hnext : r0.output.next.coordinator =
      (livePostChoice r0.output.preparation installed.registers installed.ownedRegisters
        installed.retainedBaseScore started).configuration := by
    have he : r0.output.next.coordinator = r0.output.preparation.observeCoordinator.configuration := by
      rw [r0.output_eq]; rfl
    rw [he]
    unfold PreparedRound.observeCoordinator
    rw [dite_eq_right hsel, hb]
  rw [hstate, hnext]
  exact livePostChoice_phase rate _ _ _ _ _

/-- Exhaustive next dispatch phase, including local failure constructors. -/
theorem firstCell_next_dispatch_phase (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.output.preparation.coordinator with | .live .. => True | .dagger => True | _ => False := by
  have hphase := firstCell_next_input_phase rate rewards C_star C_h u t hq x hx r hr
  have hp : r.output.preparation.coordinator = dispatch r.input := by rw [r.output_eq]; rfl
  rw [hp]
  unfold dispatch
  cases hs : r.input.state.coordinator <;> simp only [hs] at hphase
  · simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive _ <;> trivial
  · trivial

/-- The exact two disjoint readouts at the immediate successor. Every failed
constructor has outer absence in both existing numerical APIs. -/
theorem firstCell_next_readouts (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some cell.input ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none
    | .live _ _ _ (.cutoffChosen ..) =>
      ∃ c, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none
    | _ => ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = none := by
  have hphase := firstCell_next_dispatch_phase rate rewards C_star C_h u t hq x hx r hr
  have hl := firstCell_next_continuing rate rewards C_star C_h u t hq x hx r hr
  have hc := firstCell_next_cutoff rate rewards C_star C_h u t hq x hx r hr
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hphase hl hc ⊢
  · rename_i out
    cases out
    case continuingChosen =>
      obtain ⟨cell, _hread, hz, _howner⟩ := hl
      refine ⟨cell, hz, ?_⟩
      simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hd]
    case cutoffChosen =>
      obtain ⟨_ho, c, _hread, hz⟩ := hc
      refine ⟨c, hz, ?_⟩
      cases hh : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
      | none => rfl
      | some other =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 r ⟨by rw [hh]; rfl, by rw [hz]; rfl⟩)
    all_goals simp [ReferenceFirstCollectionCurrentRetainedGate.cell0,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hd, DispatchCut.selection]
  · simp [ReferenceFirstCollectionCurrentRetainedGate.cell0,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hd, DispatchCut.selection]

open ReferenceFirstCollectionRenewalNextRecordingPriorView

/-- Literal optional tag of the actual adjacent input. -/
def nextTag (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  (actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x).bind fun r => dispatchTag r.input

/-- Literal optional sender view of the actual adjacent PREPARE. -/
def nextDownView (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  (actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x).bind fun r =>
    r.output.preparation.coordinator.downView

/-- The status projection retains dagger absence. -/
def recordStatuses (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :=
  configurationStatus rate (r.output.preparation.followers.followers i).configuration

/-- Optional recording view, using only the actual cell and actual PREPARE.
The absent snapshot code denotes collection, not an absent numerical cell. -/
def recordRecordingView (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  r.output.preparation.coordinator.downView.map fun view =>
    ((ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => (c.enabled, c.rate)), view,
      if isCutoffTag (dispatchTag r.input) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (view.pendingAtChoice, recordStatuses rate r))

/-- No successor record supplies no recording view. -/
def nextRecordingView (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  (actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x).bind (recordRecordingView rate)


private theorem recordTag_eq
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    dispatchTag r.input = match r.output.preparation.coordinator with
      | .live _ _ _ out => some (eraseArm (ReferenceLiveDispatchOutputMeasurability.outcomeData out))
      | _ => none := by
  unfold dispatchTag
  have hd : dispatch r.input = r.output.preparation.coordinator := by rw [r.output_eq]; rfl
  rw [hd]
  cases r.output.preparation.coordinator <;> rfl

/-- A present actual recording view constructs the snapshot and the checked
choice bounds consumed by the existing physical recording map. -/
theorem firstCell_record_kernel (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match recordRecordingView rate r with
    | none => (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map
        (fun c => c.recordedArm) = none
    | some (parameters, view, code) =>
      ∃ (enabled : Bool)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
          r.input.time view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        code = snapshot.map (fun z => (z.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => c.recordedArm) =
          some (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun z => .live view.payload.assignment z)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
            (ContinuousLearningRows.sliceAt r.input.time r.input.row.2)) := by
  have hread := firstCell_next_readouts rate rewards C_star C_h u t hq x hx r hr
  have hphase := firstCell_next_dispatch_phase rate rewards C_star C_h u t hq x hx r hr
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hread hphase
  · rename_i registers owned base out
    cases out
    case cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hstart selected =>
      obtain ⟨c, hC, hL⟩ := hread
      have hdom := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mp
        (by rw [hC]; rfl)
      have hsig : 0 < registers.payload.sigma.val := by simpa only [hd] using hdom.2
      have hvalue : c = ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
          r registers owned base dispatched selected := by
        unfold ReferenceLaterCollectionArrivalReadout.laterCollectionReadout at hC
        simp only [dite_eq_left hdom.1, hd, dite_eq_left hsig, Option.some.injEq] at hC
        exact hC.symm
      simp only [recordRecordingView, DispatchCut.downView, DispatchCut.selection,
        selectionAt, dite_true, Option.map_some, recordTag_eq, hd,
        ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm, isCutoffTag]
      dsimp only [liveRegistersAt, ActiveRoundActions.Follower, Bool.true_eq, ite_true]
      refine ⟨c.enabled, none, selected.choiceInputsValid, ?_, rfl, ?_⟩
      · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL, hC,
          Option.none_or, Option.map_some]
        rw [hvalue]
        rfl
      · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL, hC,
          Option.none_or, Option.map_some]
        rw [hvalue]
        rfl
    case continuingChosen dispatched hs continuation selected =>
      obtain ⟨cell, hL, hC⟩ := hread
      have hview : r.output.preparation.coordinator.downView = some cell.selected.view := by
        simp only [DispatchCut.downView, cell.selection_actual, Option.map_some]
      rw [hd] at hview
      have hrate : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
      simp only [recordRecordingView, hview, Option.map_some, recordTag_eq, hd,
        ReferenceLiveDispatchOutputMeasurability.outcomeData, eraseArm, isCutoffTag]
      simp only [Bool.false_eq_true, ite_false]
      refine ⟨true, some (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states),
        cell.choiceInputsValid, ?_, ?_, ?_⟩
      · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL,
          Option.some_or, Option.map_some, cell.enabled, hrate]
      · simp only [Option.map_some, cell.selected.pending_eq]
        congr 2
        funext i
        simp only [recordStatuses, cell.ordinary i, configurationStatus,
          ReferenceActiveDataOwnership.choiceSnapshot]
      · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL,
          Option.some_or, Option.map_some]
        rw [cell.recordedArm_eq]
        unfold ReferenceFirstWindowNumericalStream.sourceArm
        rw [cell.selected.pending_eq]
        rfl
    all_goals
      simp only [recordRecordingView, hd, DispatchCut.downView, DispatchCut.selection, Option.map_none]
      rw [hread]
      rfl
  · simp only [recordRecordingView, hd, DispatchCut.downView, DispatchCut.selection, Option.map_none]
    rw [hread]
    rfl

/-- Literal consumer interface on the corrected before-old-boundary branch.
The map uses the original selected row's actual adjacent TimeControl slice.
No current control, success, ordinary domain, or recording law is a premise. -/
theorem corrected_next_physical_kernel (_control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t)
    (g : ℕ)
    (_hg : ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g) (_hlt : t.val + 1 < g) :
    match nextRecordingView rate rewards C_star C_h t hq x with
    | none => nextMarker rate rewards C_star C_h t hq x = none
    | some (parameters, view, code) =>
      ∃ (enabled : Bool)
        (snapshot : Option (ActiveRoundActions.Snapshot view.payload.assignment))
        (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
          ⟨t.val + 1, hq⟩ view.complementWeights),
        parameters = some (enabled, view.payload.rate) ∧
        code = snapshot.map (fun z => (z.missing, fun i => some
          (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
        nextMarker rate rewards C_star C_h t hq x = some
          (SnapshotRecordingKernel.recordingMap p
            (snapshot.elim .collection (fun z => .live view.payload.assignment z)) enabled
            rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
            view.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
            (ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
              (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2)) := by
  obtain ⟨r0, r, _h0, _h1, _ha0, ha, _ht0, ht, _hstate, hrows, hselected, _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have h := firstCell_record_kernel rate rewards C_star C_h u t hq x hx r ha
  have hrow : r.input.row = x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x) := by
    simp only [RoundInput.row, hrows, hselected]
  simp only [nextRecordingView, ha, Option.bind_some, nextMarker, nextCell]
  rw [ht, hrow] at h
  exact h


/-- The literal optional parameters come from the actual pre-arm tag and
sender view. Choice validity and ordinary preparation are produced above. -/
theorem firstCell_record_parameters (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => (c.enabled, c.rate)) =
      parametersOfTag rate r.input.time (dispatchTag r.input) r.output.preparation.coordinator.downView := by
  have hread := firstCell_next_readouts rate rewards C_star C_h u t hq x hx r hr
  have hphase := firstCell_next_dispatch_phase rate rewards C_star C_h u t hq x hx r hr
  rw [recordTag_eq]
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hread hphase ⊢
  · rename_i registers owned base out
    cases out
    case cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hstart selected =>
      obtain ⟨c, hC, hL⟩ := hread
      obtain ⟨payload, ledger', started, weights, _out, hcall, _hpost, _hrun,
          _henabled, hclockEnabled, hrate, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hC
      have hdom := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mp
        (by rw [hC]; rfl)
      have hsig : 0 < registers.payload.sigma.val := by simpa only [hd] using hdom.2
      have hcall' : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
          some ⟨registers.payload, sharedLedger ledger, dispatched.startResult,
            (liveRegistersAt registers r.input.time).complementWeights⟩ := by
        simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
          hdom.1, ite_true, hd, hsig]
      have hargs := Option.some.inj (hcall'.symm.trans hcall)
      have hp : registers.payload = payload := congrArg (fun args => args.1) hargs
      have ht : dispatched.startResult = started := congrArg (fun args => args.2.2.1) hargs
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL, hC,
        Option.none_or, Option.map_some, parametersOfTag, Option.bind_some,
        eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData,
        DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true,
        hclockEnabled, hrate, ← hp, ← ht]
      rfl
    case continuingChosen dispatched hs continuation selected =>
      obtain ⟨cell, hL, _hC⟩ := hread
      have hsel := cell.selection_actual
      rw [hd] at hsel
      simp only [DispatchCut.selection, selectionAt, dite_true, Option.some.injEq] at hsel
      have hp := congrArg (fun selected => selected.view.payload) hsel
      have hrate : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hL,
        Option.some_or, Option.map_some, parametersOfTag, Option.bind_some,
        eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData,
        DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true,
        cell.enabled, hrate, ← hp]
      rfl
    all_goals simp only [hread, Option.map_none, parametersOfTag, Option.bind_some,
      eraseArm, ReferenceLiveDispatchOutputMeasurability.outcomeData]
  · simp only [hread, Option.map_none, parametersOfTag, Option.bind_none]

/-- Literal parameter formula at the actual adjacent calendar time. -/
theorem firstCell_nextParameters_eq (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    nextParameters rate rewards C_star C_h t hq x = parametersOfTag rate ⟨t.val + 1, hq⟩
      (nextTag rate rewards C_star C_h t hq x) (nextDownView rate rewards C_star C_h t hq x) := by
  obtain ⟨_r0, r, _h0, _h1, _ha0, ha, _ht0, ht, _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have h := firstCell_record_parameters rate rewards C_star C_h u t hq x hx r ha
  simpa only [nextParameters, nextCell, nextTag, nextDownView, ha, Option.bind_some, ht] using h

/-- The first-cell predicate is constant on equal strict successor prefixes. -/
theorem firstCell_prefix_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (x y : X)
    (hprefix : sourcePrefix control0 (t.val + 1) x = sourcePrefix control0 (t.val + 1) y) :
    x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ↔
      y ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
  have hm := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  rw [sourcePrefixFiltration_succ, MeasurableSpace.measurableSet_comap] at hm
  obtain ⟨s, _hs, heq⟩ := hm
  have hp := congrArg (sourcePrefix control0 t.val) hprefix
  simp only [sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega)] at hp
  rw [← heq]
  change sourcePrefix control0 t.val x ∈ s ↔ sourcePrefix control0 t.val y ∈ s
  rw [hp]

/-- On the actual first cell, the old boundary is the literal incoming
collection-code projection. This retains the original installation. -/
theorem firstCell_oldFreezeAt_eq_incoming (u t : Fin p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t x =
      (incoming rate rewards C_star C_h t x).bind
        (fun code => ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt? rate code.1) := by
  obtain ⟨n, r, theta, hr, ht, ha, hcall, _⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_record rate rewards C_star C_h u t x hx
  obtain ⟨old, ledger, saved, hcoord, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h t x r (List.mem_of_getElem? hr) ht old ledger saved hcoord]
  simp only [incoming, ha, Option.map_some, Option.bind_some,
    ReferenceActivePhysicalStepMeasurability.encodeState, hcoord,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt?]

/-- The literal branch hypotheses survive every equal strict successor
prefix, without a subtype change or a new branch event definition. -/
theorem corrected_branch_prefix_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (x y : X)
    (hprefix : sourcePrefix control0 (t.val + 1) x = sourcePrefix control0 (t.val + 1) y)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (g : ℕ) (hg : ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g) (hlt : t.val + 1 < g) :
    y ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ∧
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t y = some g ∧
      t.val + 1 < g := by
  have hy := (firstCell_prefix_congr rate rewards C_star C_h control0 u t x y hprefix).mp hx
  have hp := congrArg (sourcePrefix control0 t.val) hprefix
  simp only [sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega)] at hp
  have hi : incoming rate rewards C_star C_h t x = incoming rate rewards C_star C_h t y := by
    rw [incoming_factor rate rewards C_star C_h control0 t x,
      incoming_factor rate rewards C_star C_h control0 t y, hp]
  refine ⟨hy, ?_, hlt⟩
  rw [firstCell_oldFreezeAt_eq_incoming rate rewards C_star C_h u t y hy,
    ← hi, ← firstCell_oldFreezeAt_eq_incoming rate rewards C_star C_h u t x hx]
  exact hg


private theorem ordinary_of_view (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hv : r.output.preparation.coordinator.downView = some view) :
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
    ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∀ i, (r.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
  have hl := firstCell_next_continuing rate rewards C_star C_h u t hq x hx r hr
  have hc := firstCell_next_cutoff rate rewards C_star C_h u t hq x hx r hr
  have hp := firstCell_next_dispatch_phase rate rewards C_star C_h u t hq x hx r hr
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hl hc hp hv
  · rename_i out
    cases out <;> try (simp only [DispatchCut.downView, DispatchCut.selection,
      Option.map_none, reduceCtorEq] at hv)
    · obtain ⟨ho, _⟩ := hc
      exact ⟨fun i => (ReferenceLaterCollectionArrivalReadout.actualFollowerParts r ho i).1,
        fun i => (ReferenceLaterCollectionArrivalReadout.actualFollowerParts r ho i).2,
        fun i => (ReferenceLaterCollectionArrivalReadout.actualFollowerParts_spec r ho i).1⟩
    · obtain ⟨cell, _⟩ := hl
      exact ⟨cell.states, cell.memories, cell.ordinary⟩
  · simp only [DispatchCut.downView, DispatchCut.selection, Option.map_none, reduceCtorEq] at hv

/-- Equal original strict prefixes fix the actual incoming state, without
exposing any of the successor TimeControl. -/
theorem nextState_congr (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (hq : t.val + 1 < p.T) (x y : X)
    (hprefix : sourcePrefix control0 (t.val + 1) x = sourcePrefix control0 (t.val + 1) y)
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r)
    (hr' : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ y = some r') :
    r.input.state = r'.input.state := by
  have hi : incoming rate rewards C_star C_h ⟨t.val + 1, hq⟩ x =
      incoming rate rewards C_star C_h ⟨t.val + 1, hq⟩ y := by
    rw [incoming_factor rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩ x,
      incoming_factor rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩ y, hprefix]
  simp only [incoming, hr, hr', Option.map_some, Option.some.injEq] at hi
  exact ReferenceActivePhysicalStepMeasurability.encodeState_injective hi

/-- Strict-prior congruence of the actual tag, sender, optional parameters,
and complete recording view/status code. The comparison source remains X. -/
theorem firstCell_next_prior_congr (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x y : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (hprefix : sourcePrefix control0 (t.val + 1) x = sourcePrefix control0 (t.val + 1) y) :
    nextTag rate rewards C_star C_h t hq x = nextTag rate rewards C_star C_h t hq y ∧
    nextDownView rate rewards C_star C_h t hq x = nextDownView rate rewards C_star C_h t hq y ∧
    nextParameters rate rewards C_star C_h t hq x = nextParameters rate rewards C_star C_h t hq y ∧
    nextRecordingView rate rewards C_star C_h t hq x = nextRecordingView rate rewards C_star C_h t hq y := by
  have hy := (firstCell_prefix_congr rate rewards C_star C_h control0 u t x y hprefix).mp hx
  obtain ⟨_b, r, _h0, _h1, _ha0, hr, _ht0, ht, _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  obtain ⟨_b', r', _h0', _h1', _ha0', hr', _ht0', ht', _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq y hy
  have hs := nextState_congr rate rewards C_star C_h control0 t hq x y hprefix r r' hr hr'
  have htime : r.input.time = r'.input.time := ht.trans ht'.symm
  have hphase := firstCell_next_input_phase rate rewards C_star C_h u t hq x hx r hr
  have htag := dispatchTag_congr r.input r'.input hs htime hphase
  have hv : r.output.preparation.coordinator.downView = r'.output.preparation.coordinator.downView := by
    rw [r.output_eq, r'.output_eq]
    exact downView_congr r.input r'.input hs htime hphase
  have hp : (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (fun c => (c.enabled, c.rate)) =
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r').map (fun c => (c.enabled, c.rate)) := by
    rw [firstCell_record_parameters rate rewards C_star C_h u t hq x hx r hr,
      firstCell_record_parameters rate rewards C_star C_h u t hq y hy r' hr', htime, htag, hv]
  refine ⟨by simpa only [nextTag, hr, hr', Option.bind_some] using htag,
    by simpa only [nextDownView, hr, hr', Option.bind_some] using hv,
    by simpa only [nextParameters, nextCell, hr, hr', Option.bind_some] using hp, ?_⟩
  simp only [nextRecordingView, hr, hr', Option.bind_some]
  cases hview : r.output.preparation.coordinator.downView with
  | none => simp only [recordRecordingView, hview, ← hv, Option.map_none]
  | some view =>
    obtain ⟨sl, ml, hol⟩ := ordinary_of_view rate rewards C_star C_h u t hq x hx r hr view hview
    obtain ⟨sr, mr, hor⟩ := ordinary_of_view rate rewards C_star C_h u t hq y hy r' hr' view
      (hv.symm.trans hview)
    have hstatuses : recordStatuses rate r = recordStatuses rate r' := by
      funext i
      have hol' : ((prepare r.input).followers.followers i).configuration = .ordinary (sl i) (ml i) := by
        rw [← show r.output.preparation = prepare r.input by rw [r.output_eq]; rfl]
        exact hol i
      have hor' : ((prepare r'.input).followers.followers i).configuration = .ordinary (sr i) (mr i) := by
        rw [← show r'.output.preparation = prepare r'.input by rw [r'.output_eq]; rfl]
        exact hor i
      have he := ordinary_preparation_congr r.input r'.input hs htime i (sl i) (sr i) (ml i) (mr i) hol' hor'
      simp only [recordStatuses, hol i, hor i, configurationStatus, he.1]
    simp only [recordRecordingView, ← hv, hview, Option.map_some, htag, hp, hstatuses]

/-- Source-level optional observations of this first-cell question. Outside
that cell both coordinates remain absent, including the no-call branch. -/
def firstCellPrior (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  if x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t then
    (nextParameters rate rewards C_star C_h t hq x, nextRecordingView rate rewards C_star C_h t hq x)
  else (none, none)

/-- Factorization through the existing sourcePrefix, not a new filtration. -/
theorem firstCellPrior_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :
    firstCellPrior rate rewards C_star C_h u t hq x =
      firstCellPrior rate rewards C_star C_h u t hq (sourcePrefix control0 (t.val + 1) x) := by
  have hp : sourcePrefix control0 (t.val + 1) x =
      sourcePrefix control0 (t.val + 1) (sourcePrefix control0 (t.val + 1) x) :=
    (sourcePrefix_sourcePrefix control0 _ _ le_rfl x).symm
  have hm := firstCell_prefix_congr rate rewards C_star C_h control0 u t x _ hp
  by_cases hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
  · have he := firstCell_next_prior_congr rate rewards C_star C_h control0 u t hq x _ hx hp
    simp only [firstCellPrior, hx, hm.mp hx, ite_true, he.2.2.1, he.2.2.2]
  · have hy := mt hm.mpr hx
    simp only [firstCellPrior, hx, hy, ite_false]


/-- Optional actual round input; no input is assigned to an absent record. -/
def actualInput? (q : Fin p.T) (x : X) :=
  (actualRecord rate rewards C_star C_h q x).map fun r => r.input

private theorem measurable_optionBind {A B D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace (Option D)]
    (f : A → Option B) (hf : Measurable f) (g : B → Option D) (hg : Measurable g) :
    Measurable (fun x => (f x).bind g) := by
  have he : Measurable (Equiv.optionEquivSumPUnit B) := comap_measurable _
  have hl : Measurable (Sum.elim g (fun _ : PUnit => (none : Option D))) :=
    measurable_fun_sum hg measurable_const
  convert hl.comp (he.comp hf) using 1
  funext x
  dsimp only [Function.comp_def]
  cases f x <;> rfl

/-- Borelness uses the genuine indexed-input domains and their existing
continuous Borel structure, never a discrete raw-record space. -/
theorem measurable_actualInput? (q : Fin p.T) :
    Measurable (actualInput? rate rewards C_star C_h q) := by
  classical
  let R := fun x : X => ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  have hsome : Measurable (some : RoundInput p rate → Option (RoundInput p rate)) :=
    measurable_comap_iff.mpr measurable_inl
  have hk (k : ℕ) : Measurable (fun x : X => ((R x)[k]?).map fun r => r.input) := by
    apply measurable_of_restrict_of_restrict_compl
      (ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain rate rewards C_star C_h k)
    · have h := hsome.comp
        (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt rate rewards C_star C_h k)
      convert h using 1
      funext x
      change ((R x.val)[k]?).map (fun r => r.input) = some ((R x.val)[k]'x.property).input
      rw [List.getElem?_eq_getElem x.property]
      rfl
    · have heq : (fun x : ↥({x : X | k < (R x).length}ᶜ) =>
          ((R x.val)[k]?).map fun r => r.input) = fun _ => none := by
        funext x
        rw [List.getElem?_eq_none (Nat.le_of_not_gt x.property)]
        rfl
      change Measurable (fun x : ↥({x : X | k < (R x).length}ᶜ) =>
        ((R x.val)[k]?).map fun r => r.input)
      rw [heq]
      exact measurable_const
  have hs := ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart rate rewards C_star C_h
  have hi : Measurable (fun x : X => q.val -
      ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) :=
    (measurable_of_countable fun s : ℕ => q.val - s).comp hs
  have hl := (measurable_from_prod_countable_right
    (f := fun v : ℕ × X => ((R v.2)[v.1]?).map fun r => r.input) hk).comp
      (hi.prodMk measurable_id)
  have hset : MeasurableSet {x : X |
      ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ q.val} :=
    hs (MeasurableSpace.measurableSet_top : MeasurableSet {s : ℕ | s ≤ q.val})
  have hopt : Measurable (fun x : X =>
      if ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h ≤ q.val then
        ((R x)[q.val - ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h]?).map
          (fun r => r.input) else none) := Measurable.ite hset hl measurable_const
  convert hopt using 1
  funext x
  unfold actualInput? actualRecord
  split_ifs <;> rfl

/-- Borel formula in existing input, tag, view and prepared-status APIs. -/
def inputRecordingView (q : Fin p.T) (input : RoundInput p rate) :=
  (dispatch input).downView.map fun view =>
    (parametersOfTag rate q (dispatchTag input) (dispatch input).downView, view,
      if isCutoffTag (dispatchTag input) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (view.pendingAtChoice, fun i =>
        configurationStatus rate ((prepare input).followers.followers i).configuration))

private theorem measurable_inputRecordingView (q : Fin p.T) :
    Measurable (inputRecordingView rate q) := by
  have ht : Measurable (dispatchTag (p := p) (rate := rate)) := measurable_dispatchTag
  have hv := ReferenceActiveStepCompositionMeasurability.measurable_downView (p := p) (rate := rate)
  have hp := (measurable_parametersOfTag rate q).comp (ht.prodMk hv)
  have hs : Measurable (fun input : RoundInput p rate => fun i : Fin (p.m - 1) =>
      configurationStatus rate ((prepare input).followers.followers i).configuration) := by
    apply measurable_pi_iff.mpr
    intro i
    have h := (measurable_preparedStatusCode rate).comp
      (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)
    convert h using 1
    funext input
    exact (preparedStatusCode_eq rate input i).symm
  have hm : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))))
  have hc : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × RoundInput p rate =>
      if isCutoffTag (dispatchTag v.2) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (v.1.pendingAtChoice, fun i =>
        configurationStatus rate ((prepare v.2).followers.followers i).configuration)) :=
    (measurable_of_countable (fun key : Bool ×
      (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))) =>
        if key.1 then none else some key.2)).comp
      ((((measurable_of_countable isCutoffTag).comp ht).comp measurable_snd).prodMk
        ((hm.comp measurable_fst).prodMk (hs.comp measurable_snd)))
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent _
    ((hp.comp measurable_snd).prodMk (measurable_fst.prodMk hc)) _ hv

private theorem firstCell_inputRecordingView (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    nextRecordingView rate rewards C_star C_h t hq x =
      (actualInput? rate rewards C_star C_h ⟨t.val + 1, hq⟩ x).bind
        (inputRecordingView rate ⟨t.val + 1, hq⟩) := by
  obtain ⟨_b, r, _h0, _h1, _ha0, hr, _ht0, ht, _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  simp only [nextRecordingView, actualInput?, hr, Option.map_some, Option.bind_some]
  have hp := firstCell_record_parameters rate rewards C_star C_h u t hq x hx r hr
  have hprep : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
  unfold recordRecordingView inputRecordingView recordStatuses
  rw [hp, ht, hprep]
  rfl

/-- Ambient Borelness of the original first-cell optional parameter/view
pair. No positivity of that cell's source mass is required. -/
theorem measurable_firstCellPrior (u t : Fin p.T) (hq : t.val + 1 < p.T) :
    Measurable (firstCellPrior rate rewards C_star C_h u t hq) := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let I := actualInput? rate rewards C_star C_h q
  have hI := measurable_actualInput? rate rewards C_star C_h q
  have ht := measurable_optionBind I hI dispatchTag measurable_dispatchTag
  have hv := measurable_optionBind I hI (fun input => (dispatch input).downView)
    ReferenceActiveStepCompositionMeasurability.measurable_downView
  have hp := (measurable_parametersOfTag rate q).comp (ht.prodMk hv)
  have hr := measurable_optionBind I hI (inputRecordingView rate q) (measurable_inputRecordingView rate q)
  have heq : firstCellPrior rate rewards C_star C_h u t hq = fun x : X =>
      if x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t then
        (parametersOfTag rate q ((I x).bind dispatchTag)
          ((I x).bind fun input => (dispatch input).downView),
          (I x).bind (inputRecordingView rate q)) else (none, none) := by
    funext x
    by_cases hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
    · simp only [firstCellPrior, hx, ite_true,
        firstCell_nextParameters_eq rate rewards C_star C_h u t hq x hx,
        firstCell_inputRecordingView rate rewards C_star C_h u t hq x hx]
      congr 2
      · simp only [nextTag, I, q, actualInput?, Option.bind_map, Function.comp_def]
      · simp only [nextDownView, I, q, actualInput?, Option.bind_map]
        congr 1
        funext r
        rw [r.output_eq]
        rfl
    · simp only [firstCellPrior, hx, ite_false]
  rw [heq]
  apply Measurable.ite _ (hp.prodMk hr) measurable_const
  simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell, Set.mem_ofPred_eq] using
    ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell rate rewards C_star C_h u t

/-- Borelness in the existing strict-prior source filtration. -/
theorem firstCellPrior_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (firstCellPrior rate rewards C_star C_h u t hq) := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega, sourcePrefixFiltration_succ]
  have h := (measurable_firstCellPrior rate rewards C_star C_h u t hq).comp
    (comap_measurable (sourcePrefix control0 (t.val + 1)))
  convert h using 1
  funext x
  exact firstCellPrior_factor rate rewards C_star C_h control0 u t hq x


/-- The strict prefix retains the entire original call control, hence every
one of its K+1 assignment coordinates, as well as the original private arrays. -/
theorem prefix_retains_call_control (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (x : X) :
    ((sourcePrefix control0 (t.val + 1) x).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 t =
        (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 t := by
  rw [sourcePrefix_control, ite_eq_left (by omega : t.val < t.val + 1)]

/-- Changing the whole current successor control preserves the strict past. -/
theorem sourcePrefix_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (control : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 (t.val + 1)
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩ x control) =
      sourcePrefix control0 (t.val + 1) x := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p x
    · subst row
      simp only [sourcePrefix, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val + 1
      · have hne : v ≠ (⟨t.val + 1, hq⟩ : Fin p.T) := by
          intro h
          exact (Nat.ne_of_lt hv) (congrArg Fin.val h)
        simp only [hv, ite_true, Function.update_of_ne hne]
      · simp only [hv, ite_false]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p x.2.1.2 := hr
      simp only [sourcePrefix, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hr']
  · rfl

/-- Arbitrary replacement of all controls from the successor onward has the
same strict prior. No coordinate of its current TimeControl is exposed. -/
theorem sourcePrefix_replaceSuffix (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 (t.val + 1)
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix x ⟨t.val + 1, hq⟩ suffix) =
      sourcePrefix control0 (t.val + 1) x := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p x
    · subst row
      simp only [sourcePrefix, ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val + 1 <;> simp only [hv, ite_true, ite_false]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p x.2.1.2 := hr
      simp only [sourcePrefix, ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hr']
  · rfl

/-- The actual corrected branch survives arbitrary whole-current-control
replacement; its old threshold and original first-call tags are preserved. -/
theorem corrected_branch_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (g : ℕ) (hg : ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g) (hlt : t.val + 1 < g)
    (control : ContinuousLearningRows.TimeControl p) :
    let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩ x control
    y ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ∧
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t y = some g ∧
      t.val + 1 < g :=
  corrected_branch_prefix_congr rate rewards C_star C_h control0 u t x _
    (sourcePrefix_replaceControl control0 t hq x control).symm hx g hg hlt

/-- Actual optional parameters and the complete recording view/status code
are unchanged by reintegrating the whole successor TimeControl. -/
theorem firstCell_prior_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (control : ContinuousLearningRows.TimeControl p) :
    let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩ x control
    nextParameters rate rewards C_star C_h t hq x = nextParameters rate rewards C_star C_h t hq y ∧
      nextRecordingView rate rewards C_star C_h t hq x = nextRecordingView rate rewards C_star C_h t hq y :=
  (firstCell_next_prior_congr rate rewards C_star C_h control0 u t hq x _ hx
    (sourcePrefix_replaceControl control0 t hq x control).symm).2.2

/-- Present cells, enabled or disabled, have the actual payload's canonical
rate bounds. These are consequences of the constructor, never premises. -/
theorem firstCell_nextParameters_bounds (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (enabled : Bool) (xi : Fin p.K → ℝ)
    (hp : nextParameters rate rewards C_star C_h t hq x = some (enabled, xi)) :
    ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
      nextDownView rate rewards C_star C_h t hq x = some view ∧ xi = view.payload.rate ∧
      (∀ a, CanonicalRecordingRates.beta p rate.eta.val ≤ xi a ∧
        xi a ≤ 1 / (16 * (p.m : ℝ) * (p.K : ℝ))) ∧ (∑ a, xi a) ≤ 1 := by
  rw [firstCell_nextParameters_eq rate rewards C_star C_h u t hq x hx] at hp
  generalize ht : nextTag rate rewards C_star C_h t hq x = tag at hp
  rcases tag with _ | tag
  · cases hp
  rcases tag with _ | tag
  · cases hp
  rcases tag with _ | tag
  · cases hp
  rcases tag with _ | chosen
  · cases hp
  cases hv : nextDownView rate rewards C_star C_h t hq x with
  | none => simp only [parametersOfTag, Option.bind_some, hv, Option.map_none, reduceCtorEq] at hp
  | some view =>
    simp only [parametersOfTag, Option.bind_some, hv, Option.map_some, Option.some.injEq] at hp
    have hxi : xi = view.payload.rate := (Prod.mk.inj hp).2.symm
    refine ⟨view, rfl, hxi, ?_, ?_⟩
    · intro a
      rw [hxi, view.payload.rate_eq_canonical]
      exact ⟨CanonicalRecordingRates.beta_le_xi p rate.eta.property _ a,
        CanonicalRecordingRates.xi_le_one_div_16mK p rate.eta.property rate.sourceCap
          view.payload.anchor view.payload.anchor_pos a⟩
    · rw [hxi, show view.payload.rate = CanonicalRecordingRates.xi p rate.eta.val
        view.payload.anchor from funext view.payload.rate_eq_canonical]
      exact CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
        view.payload.anchor view.payload.anchor_pos

/-- The actual optional successor extended to the terminal date has no
filled successor slot. This extension never searches for a later success. -/
def successorCell? (t : Fin p.T) (x : X) : Option (RecordedQueueRun.RoundInput p.K) :=
  if hq : t.val + 1 < p.T then nextCell rate rewards C_star C_h t hq x else none

/-- At the terminal date there is no q and no successor recording assertion. -/
theorem terminal_successor_absent (t : Fin p.T) (x : X) (ht : t.val + 1 = p.T) :
    (¬ ∃ q : Fin p.T, q.val = t.val + 1) ∧ successorCell? rate rewards C_star C_h t x = none := by
  constructor
  · rintro ⟨q, hq⟩
    have hlt := q.isLt
    omega
  · simp only [successorCell?, ht, lt_self_iff_false, dite_false]

/-- Off the original first-cell question, including no call, its optional
prior observations are absent rather than supplied with a default cell. -/
theorem firstCellPrior_absent (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∉ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    firstCellPrior rate rewards C_star C_h u t hq x = (none, none) := by
  simp only [firstCellPrior, hx, ite_false]


/-- On the actual next cutoff the collection recorder, owner and original
whole-reward identities are produced, including local numerical arrivals. -/
theorem firstCell_next_cutoff_physical (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some r) :
    match r.output.preparation.coordinator with
    | .live _ _ _ (.cutoffChosen ..) =>
      ∃ (c : RecordedQueueRun.RoundInput p.K) (payload : Payload rate)
        (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
        (out : CoordinatorRecordingOperation.Output p),
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall
          (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r =
            some ⟨payload, ledger, started, weights⟩ ∧
        c.rate = payload.rate ∧
        c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
        c.enabled = decide (r.input.time.val + 1 < started.clock.g) ∧
        CoordinatorRecorderComplementBridge.run
          (collectionRecordingInput r.output.preparation payload started weights) = some out ∧
        r.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
        (∀ a, CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (∀ a, ∃! owner : Fin p.m, SnapshotRecordingKernel.owns p .collection owner a) ∧
        ∀ a, c.recordedArm = some a →
          SnapshotRecordingKernel.owns p .collection (ActiveRoundActions.coordinator p.two_le_m) a ∧
          r.actions (ActiveRoundActions.coordinator p.two_le_m) = a ∧
          r.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) = rewards r.input.time a
    | _ => True := by
  have hc := firstCell_next_cutoff rate rewards C_star C_h u t hq x hx r hr
  cases hd : r.output.preparation.coordinator <;> try trivial
  rename_i outcome
  cases outcome <;> try trivial
  simp only [hd] at hc
  obtain ⟨_ho, c, hread, hz⟩ := hc
  obtain ⟨_b, r', _h0, h1, _ha0, ha, _⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  have heq : r' = r := Option.some.inj (ha.symm.trans hr)
  subst r'
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let k : Fin R.length := ⟨v + 1, (List.getElem?_eq_some_iff.mp h1).1⟩
  have hkr : R.get k = r := (List.getElem?_eq_some_iff.mp h1).2
  have hphysical := ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_physical
    rate rewards C_star C_h x k c (by rw [hkr]; exact hread)
  dsimp only at hphysical
  rw [hkr] at hphysical
  obtain ⟨payload, ledger, started, weights, out, hcall, hrun, hdiag, hgate,
      harrival, hrate, hreward, howner⟩ := hphysical
  obtain ⟨_payload', _ledger', started', _weights', _out', hcall', _hpost, _hrun',
      _henabled, hclock, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
      (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r c hread
  have hstarted : started' = started := congrArg (fun args => args.2.2.1)
    (Option.some.inj (hcall'.symm.trans hcall))
  rw [hstarted] at hclock
  refine ⟨c, payload, ledger, started, weights, out, hz, hcall, hrate, hreward,
    hclock, hrun, hdiag, hgate, harrival, ?_, ?_⟩
  · intro a
    obtain ⟨owner, howns⟩ := SnapshotRecordingKernel.exists_ownerSource p .collection a
    exact ⟨owner, howns, fun other hother => SnapshotRecordingKernel.owns_unique p _ a other owner hother howns⟩
  · intro a ha
    obtain ⟨_valid, _hslot, _hrecorder, _hfrozen, howns, haction, _hmask, _hthin,
      hfeedback, _harrival⟩ := howner a ha
    exact ⟨howns, haction, hfeedback⟩

/-- A surviving next input retains the exact original installed payload.
Failure is the separate none alternative, not a replacement payload. -/
theorem firstCell_next_installed_payload (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ birth next : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      actualRecord rate rewards C_star C_h t x = some birth ∧
      actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some next ∧
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ReferenceAssignmentPayloadPersistence.storedPayload next.input.state.coordinator = none ∨
        ReferenceAssignmentPayloadPersistence.storedPayload next.input.state.coordinator =
          some installed.registers.payload
      | _ => False := by
  obtain ⟨birth, next, _h0, _h1, hb, hn, _ht0, _ht1, hstate, _hrows,
      _hselected, _hrewards, hchosen⟩ :=
    firstCell_successor_records rate rewards C_star C_h u t hq x hx
  refine ⟨birth, next, hb, hn, ?_⟩
  have hp : birth.output.preparation = prepare birth.input := by rw [birth.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hd : birth.output.preparation.coordinator <;> simp only [hd, Bool.false_eq_true] at hchosen
  rename_i outcome
  cases outcome <;> simp only at hchosen <;> try contradiction
  rename_i core consistent started hs instruction hi output hlocal clockData installed selection
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames birth
  simp only [hd] at hframes
  have hsel : birth.output.preparation.coordinator.selection ≠ none := by
    simp only [hd, DispatchCut.selection, selectionAt, dite_eq_left hframes.1,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have hnext : birth.output.next.coordinator =
      (livePostChoice birth.output.preparation installed.registers installed.ownedRegisters
        installed.retainedBaseScore started).configuration := by
    have he : birth.output.next.coordinator = birth.output.preparation.observeCoordinator.configuration := by
      rw [birth.output_eq]; rfl
    rw [he]
    unfold PreparedRound.observeCoordinator
    rw [dite_eq_right hsel, hd]
  rw [hstate, hnext]
  exact ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame _ _ _ _ _

/-- The optional prior pair has its literal values on the original first cell. -/
theorem firstCellPrior_eq (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    firstCellPrior rate rewards C_star C_h u t hq x =
      (nextParameters rate rewards C_star C_h t hq x, nextRecordingView rate rewards C_star C_h t hq x) := by
  simp only [firstCellPrior, hx, ite_true]

/-- Canonical payload/real-product recording code, together with the literal
optional parameters and full prepared status/missing code. -/
def firstCellRecordingCode (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :=
  ((firstCellPrior rate rewards C_star C_h u t hq x).2).map fun v =>
    (v.1, recordingViewCode rate v.2.1, v.2.2)

/-- All recording-code coordinates are Borel in the existing strict-prior field. -/
theorem firstCellRecordingCode_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (firstCellRecordingCode rate rewards C_star C_h u t hq) := by
  exact @LaterAssignmentFullOutputMeasurability.measurable_optionMap
    X (sourcePrefixFiltration control0 (t.val + 2)) _ _ _ _ _
    (measurable_fst.prodMk (((measurable_recordingViewCode rate).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))) _
    (measurable_snd.comp (firstCellPrior_measurable rate rewards C_star C_h control0 u t hq))


/-- The original before-old-boundary branch also survives an arbitrary
successor control suffix, with its same old boundary. -/
theorem corrected_branch_replaceSuffix (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (g : ℕ) (hg : ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g) (hlt : t.val + 1 < g)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    let y := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix x ⟨t.val + 1, hq⟩ suffix
    y ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ∧
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t y = some g ∧
      t.val + 1 < g :=
  corrected_branch_prefix_congr rate rewards C_star C_h control0 u t x _
    (sourcePrefix_replaceSuffix control0 t hq x suffix).symm hx g hg hlt

/-- Literal parameter projection as a measurable original-source observation. -/
theorem firstCellParameters_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)] (fun x : X =>
      if x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t then
        nextParameters rate rewards C_star C_h t hq x else none) := by
  have h := measurable_fst.comp (firstCellPrior_measurable rate rewards C_star C_h control0 u t hq)
  convert h using 1
  funext x
  dsimp only [Function.comp_def]
  unfold firstCellPrior
  split_ifs <;> rfl

/-- The canonical recording code factors through exactly the same strict prefix. -/
theorem firstCellRecordingCode_factor (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X) :
    firstCellRecordingCode rate rewards C_star C_h u t hq x =
      firstCellRecordingCode rate rewards C_star C_h u t hq (sourcePrefix control0 (t.val + 1) x) := by
  unfold firstCellRecordingCode
  rw [firstCellPrior_factor rate rewards C_star C_h control0 u t hq x]

/-- No original collection invocation supplies no first-call successor view
or numerical parameter. This does not fill any missing numerical cell. -/
theorem noCall_firstCellPrior (u t : Fin p.T) (hq : t.val + 1 < p.T) (x : X)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h x = none) :
    firstCellPrior rate rewards C_star C_h u t hq x = (none, none) := by
  apply firstCellPrior_absent
  simp only [ReferenceCalendarCollectionCallControlLaw.firstCell, Set.mem_ofPred_eq,
    hcall, Option.map_none, reduceCtorEq, not_false_eq_true]

end Bandits.Support.ReferenceFirstCollectionCorrectedNextPhysicalReadout
