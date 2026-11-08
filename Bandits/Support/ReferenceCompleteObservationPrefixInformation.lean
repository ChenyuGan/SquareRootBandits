/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFirstPhaseObservationRecovery
public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseAdaptation

/-!
# Strict dated prefixes of the actual numerical observation

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:355-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The prefixes below filter literal calendar dates of the existing observation.
They retain absent numerical cells, whole reward and rate vectors, and the
original saved real coordinates. The source-prefix field is an analysis field;
these results do not identify the physical pre-sampler field or prove a law.
The intended consumer is the whole-calendar actual numerical/source-law
strict-past information join.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceCompleteObservationPrefixInformation

variable {p : ConstructorDimensions.Parameters}

/-- Literal strict calendar filtering, including entries with absent cells. -/
def datePrefix (rate : ReferenceActivePhysicalStep.RateInput p)
    (n : ℕ) (omega : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate) :
    ReferenceCompleteFirstPhaseObservationRecovery.OBS rate :=
  omega.filter (fun e => decide (e.1.val < n))

/-- The incoming state coordinate of the actual entry at this calendar date. -/
def incomingDecoder (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T) (omega : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate) :
    Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) :=
  (omega.find? (fun e => e.1 == t)).map (fun e => e.2.1.2.1)

private theorem filter_dates_eq_take {α : Type*} (l : List (Fin p.T × α))
    (s n : ℕ) (hd : ∀ k (hk : k < l.length), (l[k]).1.val = s + k) :
    l.filter (fun e => decide (e.1.val < n)) = l.take (n - s) := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
      have he : e.1.val = s := by
        have h := hd 0 (by simp)
        change e.1.val = s + 0 at h
        simpa only [Nat.add_zero] using h
      have ht : ∀ k (hk : k < l.length), (l[k]).1.val = (s + 1) + k := by
        intro k hk
        have h := hd (k + 1) (by simpa using hk)
        change (l[k]).1.val = s + (k + 1) at h
        omega
      by_cases hs : s < n
      · have hsub : n - s = (n - (s + 1)) + 1 := by omega
        simp only [List.filter_cons, he, hs, decide_true, ite_true,
          hsub, List.take_succ_cons]
        exact congrArg (List.cons e) (ih (s + 1) ht)
      · have hsub : n - s = 0 := by omega
        have hsub' : n - (s + 1) = 0 := by omega
        simp only [List.filter_cons, he, hs, decide_false, Bool.false_eq_true, ite_false,
          hsub, List.take_zero]
        simpa only [hsub', List.take_zero] using ih (s + 1) ht

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

private theorem observation_date (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : ℕ) (hk : k < (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source).length) :
    ((ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source)[k]).1.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k := by
  have h := ReferenceCompleteNumericalBranchObservation.branchCalendar_times rate rewards C_star C_h 0 source
  have hlen := ReferenceCompleteNumericalBranchObservation.branchCalendar_length rate rewards C_star C_h 0 source
  have hk' : k < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    simpa only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation, hlen] using hk
  have hget := congrArg (fun l : List ℕ => l[k]?) h
  change k < (ReferenceCompleteNumericalBranchObservation.branchCalendar
    rate rewards C_star C_h 0 source).length at hk
  simp only [List.getElem?_map, List.getElem?_range' hk', Nat.one_mul] at hget
  rw [List.getElem?_eq_getElem hk] at hget
  exact Option.some.inj hget

/-- Filtering dates below `n` takes exactly the first `n - start` actual
suffix entries, without a future suffix-length tag. -/
theorem datePrefix_eq_take (n : ℕ) (_hn : n ≤ p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    datePrefix rate n (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source) =
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h source).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  exact filter_dates_eq_take _ _ n (observation_date rate rewards C_star C_h source)

/-- The actual strict prefix has this exact length even before launch. -/
theorem datePrefix_length (n : ℕ) (hn : n ≤ p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (datePrefix rate n (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source)).length =
      n - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  rw [datePrefix_eq_take rate rewards C_star C_h n hn, List.length_take,
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar_length]
  exact Nat.min_eq_left (Nat.sub_le_sub_right hn _)

private theorem find_date {α : Type*} (l : List (Fin p.T × α)) (s : ℕ)
    (hd : ∀ k (hk : k < l.length), (l[k]).1.val = s + k) (t : Fin p.T) :
    l.find? (fun e => e.1 == t) = if s ≤ t.val then l[t.val - s]? else none := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
      have he : e.1.val = s := by
        have h := hd 0 (by simp)
        change e.1.val = s + 0 at h
        simpa only [Nat.add_zero] using h
      have ht : ∀ k (hk : k < l.length), (l[k]).1.val = (s + 1) + k := by
        intro k hk
        have h := hd (k + 1) (by simpa using hk)
        change (l[k]).1.val = s + (k + 1) at h
        omega
      by_cases het : e.1 = t
      · have hst : s = t.val := he.symm.trans (congrArg Fin.val het)
        simp [het, hst]
      · have hne : s ≠ t.val := fun h => het (Fin.ext (he.trans h))
        have hb : (e.1 == t) = false := by simp [het]
        rw [List.find?_cons, hb]
        rw [ih (s + 1) ht]
        by_cases hs : s ≤ t.val
        · have hs' : s + 1 ≤ t.val := by omega
          have hsub : t.val - s = (t.val - (s + 1)) + 1 := by omega
          simp only [hs, hs', ite_true, hsub, List.getElem?_cons_succ]
        · have hs' : ¬ s + 1 ≤ t.val := by omega
          simp only [hs, hs', ite_false]

/-- The literal calendar lookup recovers H's existing optional incoming
state, including the present incoming state at the empty strict launch prefix. -/
theorem incomingDecoder_eq_incoming (t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    incomingDecoder rate t (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t source := by
  unfold incomingDecoder
  rw [find_date _ _ (observation_date rate rewards C_star C_h source)]
  unfold ReferenceSourcePrefixHistoryFiltration.incoming ReferenceSourcePrefixHistoryFiltration.actualRecord
  split_ifs <;> simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar,
    List.getElem?_map, Option.map_map, Option.map_none]
  rfl

private theorem prepared_configurations_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time) :
    ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration := by
  intro i
  rw [left.output.preparation.followers.followers_eq i,
    right.output.preparation.followers.followers_eq i]
  change (DeclaredFollowerLocalRound.prepare rate i left.input.row
    (left.input.state.activations i) left.input.time (left.input.active i)
    (left.input.state.followers i)).configuration =
      (DeclaredFollowerLocalRound.prepare rate i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.input.state.followers i)).configuration
  have h := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
    (rate := rate) i (left.input.state.activations i) (left.input.active i)
    (left.input.state.followers i) (row := left.input.row) (otherRow := right.input.row)
    (by simpa only [htime] using hcurrent)
  simpa only [hstate, htime] using congrArg Prod.snd h

private theorem selection_codes_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    left.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      right.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  rw [left.output.preparation.coordinator_eq, right.output.preparation.coordinator_eq]
  exact (ReferenceActiveHorizonMeasurability.roundRecordCode_front left).1.symm.trans
    ((congrArg ReferenceCoordinatorRecorderCallTrace.selection hcode).trans
      (ReferenceActiveHorizonMeasurability.roundRecordCode_front right).1)

private theorem live_numerical_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right)
    (htime : left.input.time = right.input.time)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hconf : ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration) (b : ℕ) :
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout b left).map
        ReferenceCompleteNumericalBranchObservation.encodeNumerical =
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout b right).map
        ReferenceCompleteNumericalBranchObservation.encodeNumerical := by
  have hordinary : ReferenceLaterLiveNumericalReadout.preparedOrdinary left ↔
      ReferenceLaterLiveNumericalReadout.preparedOrdinary right := by
    unfold ReferenceLaterLiveNumericalReadout.preparedOrdinary
    simp only [hconf]
  have hsel := selection_codes_eq rate left right hcode
  cases hl : left.output.preparation.coordinator.selection with
  | none =>
      have hr : right.output.preparation.coordinator.selection = none := by
        exact Option.map_eq_none_iff.mp (by simpa only [hl, Option.map_none] using hsel.symm)
      simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hl, hr, Option.map_none]
  | some sl =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => simp only [hl, hr, Option.map_some, Option.map_none] at hsel; cases hsel
      | some sr =>
          have hv : sl.view = sr.view := congrArg Prod.fst
            (Option.some.inj (by simpa only [hl, hr, Option.map_some] using hsel))
          rcases sl with ⟨vl, stl, pdl, cdl, al, chl⟩
          rcases sr with ⟨vr, str, pdr, cdr, ar, chr⟩
          change vl = vr at hv
          cases hv
          by_cases ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary left
          · have ho' := hordinary.mp ho
            have hstates : ReferenceLaterLiveNumericalReadout.preparedStates left ho =
                ReferenceLaterLiveNumericalReadout.preparedStates right ho' := by
              funext i
              unfold ReferenceLaterLiveNumericalReadout.preparedStates
              simp only [hconf]
            simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hl, hr,
              htime, ho, ho', dite_true]
            by_cases hg : b < vl.payload.sigma.val ∧
                CoordinatorLocalArmChoice.assignmentIsLive vl.payload vl.cutoff right.input.time
            · simp only [hg]
              unfold ReferenceCompleteNumericalBranchObservation.encodeNumerical
                ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates
                ReferenceFirstWindowNumericalStream.sourceCell
              simp only [hstates, hrewards, htime]
              congr 2
              unfold ReferenceFirstWindowNumericalStream.sourceArm
              rw [hcurrent]
            · simp only [hg, ite_false, Option.map_none]
          · have ho' : ¬ ReferenceLaterLiveNumericalReadout.preparedOrdinary right :=
              fun h => ho (hordinary.mpr h)
            simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hl, hr,
              htime, ho, ho', dite_false]

private theorem incoming_live_tag_eq_preparation
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      match record.output.preparation.coordinator with
      | .live _ _ _ _ => true
      | _ => false := by
  rw [record.output.preparation.coordinator_eq]
  cases hc : record.input.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first record.input hc]
      simp [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger record.input hc]
      simp [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]
  | live registers owned base =>
      simp [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch,
        ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator]; rfl
  | collection payload ledger proposal =>
      by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp [ReferenceActivePhysicalStep.dispatch, hc, hv, CoordinatorRoundDispatch.dispatch,
          ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
        rfl
      · simp [ReferenceActivePhysicalStep.dispatch, hc, hv,
          ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator]

private theorem collection_domain_code
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (b : ℕ) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).isSome = true ↔
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ∧
        (match record.output.preparation.coordinator.selection with
        | none => False
        | some selected =>
            ReferenceCoordinatorRecorderCallTrace.live
                (ReferenceActiveHorizonMeasurability.roundRecordCode record)
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false ∧
              (ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate
                  (ReferenceActiveHorizonMeasurability.roundRecordCode record) = false ∨
                b < selected.view.payload.sigma.val)) := by
  rw [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain]
  apply and_congr_right
  intro _
  rw [incoming_live_tag_eq_preparation rate record]
  cases hs : record.output.preparation.coordinator.selection with
  | none =>
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp
      | live registers owned base outcome =>
          cases outcome <;> simp_all [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt]
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp_all [ReferenceActivePhysicalStep.DispatchCut.selection]
      | invalidCollectionCutoff => simp
      | dagger => simp
  | some selected =>
      have hd : (ReferenceActivePhysicalStep.dispatch record.input).selection = some selected := by
        rw [← record.output.preparation.coordinator_eq]
        exact hs
      have hp := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits record selected hd
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp_all
      | live registers owned base outcome =>
          cases outcome <;> simp_all [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt,
            ReferenceLiveDispatchOutputMeasurability.encodeSelection]
          cases hs
          rfl
      | collection payload ledger clock cutoff outcome => cases outcome <;> simp_all
      | invalidCollectionCutoff => simp_all
      | dagger => simp_all

private theorem collection_numerical_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right)
    (htime : left.input.time = right.input.time)
    (hrewards : left.input.rewards = right.input.rewards)
    (hconf : ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration) (b : ℕ) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b left).map
        ReferenceCompleteNumericalBranchObservation.encodeNumerical =
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b right).map
        ReferenceCompleteNumericalBranchObservation.encodeNumerical := by
  have hunocc : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied left ↔
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied right := by
    unfold ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
    simp only [hconf]
  have hsel := selection_codes_eq rate left right hcode
  have hdomain :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b left).isSome = true ↔
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b right).isSome = true := by
    rw [collection_domain_code rate left b, collection_domain_code rate right b]
    apply and_congr hunocc
    cases hl : left.output.preparation.coordinator.selection with
    | none =>
        have hr : right.output.preparation.coordinator.selection = none :=
          Option.map_eq_none_iff.mp (by simpa only [hl, Option.map_none] using hsel.symm)
        simp only [hr]
    | some sl =>
        cases hr : right.output.preparation.coordinator.selection with
        | none => simp only [hl, hr, Option.map_none, Option.map_some] at hsel; cases hsel
        | some sr =>
            have he := Option.some.inj (by simpa only [hl, hr, Option.map_some] using hsel)
            have hv : sl.view = sr.view := congrArg Prod.fst he
            simp only [hcode, he, hv]
  change (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b left).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b right).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
  rw [ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization,
    ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization]
  simp only [hdomain, hcode, htime, hrewards]

/-- All comparisons here are explicit data about two literal records. They
will be discharged from the same actual calendar lookup below. -/
private theorem branch_readout_eq_of_temporal_reads
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (hselected : left.input.selected = right.input.selected)
    (htime : left.input.time = right.input.time)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hpast : ∀ v : Fin p.T, v.val < left.input.time.val →
      (left.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (right.input.row.2 v).1 ContinuousControlSlice.Label.prop) (b : ℕ) :
    ReferenceActiveHorizonMeasurability.roundRecordCode left =
        ReferenceActiveHorizonMeasurability.roundRecordCode right ∧
      ReferenceCompleteNumericalBranchObservation.branchReadout rate b left =
        ReferenceCompleteNumericalBranchObservation.branchReadout rate b right := by
  have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
    left.input right.input hstate hselected htime hrewards hcurrent hpast
  change ReferenceActiveHorizonMeasurability.roundRecordCode left =
    ReferenceActiveHorizonMeasurability.roundRecordCode right at hcode
  have hconf := prepared_configurations_eq rate left right hstate htime hcurrent
  have hlive := live_numerical_eq rate left right hcode htime hrewards hcurrent hconf b
  have hcollection := collection_numerical_eq rate left right hcode htime hrewards hconf b
  refine ⟨hcode, ?_⟩
  unfold ReferenceCompleteNumericalBranchObservation.branchReadout
  simp only [hcode, hlive, hcollection]

private theorem actual_record_fields (t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  · obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
    have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
      rate rewards C_star C_h _ ⟨source, hk⟩
    dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
      List.get_eq_getElem] at hf
    rw [hrecord] at hf
    refine ⟨hf.1, hf.2.1, ?_, hf.2.2.1⟩
    have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h
    have hk' : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h < p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h := by
      simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
    have hget := congrArg (fun l : List ℕ => l[t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h]?) ht
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
      List.getElem?_range' hk', Nat.one_mul] at hget
    rw [List.getElem?_eq_getElem hk, hrecord] at hget
    apply Fin.ext
    have hv := Option.some.inj hget
    simpa only [Nat.add_sub_of_le hs] using hv

private theorem empty_of_not_launchBy (n : ℕ) (hn : n ≤ p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n source) :
    datePrefix rate n
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h source) = [] := by
  have hs : n ≤ ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing with
    | none =>
        have h := (ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
          rate source rewards C_star C_h hc).2.1
        change ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h = p.T at h
        rw [h]
        exact hn
    | some c =>
        by_contra h
        exact hz ⟨by simp only [hc, Option.isSome_some], by omega⟩
  rw [datePrefix_eq_take rate rewards C_star C_h n hn,
    Nat.sub_eq_zero_of_le hs, List.take_zero]

/-- Actual numerical entries dated before `n` are unchanged by replacing
only the selected controls at offsets at least `n`. No whole row or
row-bearing record is equated. Future launches on the absent branch may differ. -/
theorem datePrefix_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)) := by
  by_cases hterminal : p.T ≤ n
  · rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_self control0 n hterminal]
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n source
  · have hs := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
      rate rewards C_star C_h control0 n hn source hz).1
    rw [datePrefix_eq_take rate rewards C_star C_h n hn,
      datePrefix_eq_take rate rewards C_star C_h n hn]
    apply List.ext_getElem
    · simp only [List.length_take, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar_length, hs]
    intro k hk hk'
    have hkbound : k < n - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h := by
      rw [List.length_take] at hk
      exact (lt_min_iff.mp hk).1
    have htbound : ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h + k < n := by omega
    let t : Fin p.T := ⟨ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k, by omega⟩
    have hi : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
      omega
    have hi' : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)
        rewards C_star C_h).length := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, ← hs]
      omega
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k]'hi
    let r' := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)
      rewards C_star C_h)[k]'hi'
    have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t source = some r := by
      unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
      have hle : ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h ≤ t.val := by dsimp [t]; omega
      rw [ite_eq_left hle]
      have hsub : t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h = k := by dsimp [t]; omega
      rw [hsub, List.getElem?_eq_getElem hi]
    have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) = some r' := by
      unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
      have hle : ReferenceCompletePhysicalHistory.physicalStart rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)
          rewards C_star C_h ≤ t.val := by rw [← hs]; dsimp [t]; omega
      rw [ite_eq_left hle]
      have hsub : t.val - ReferenceCompletePhysicalHistory.physicalStart rate
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)
          rewards C_star C_h = k := by rw [← hs]; dsimp [t]; omega
      rw [hsub, List.getElem?_eq_getElem hi']
    have hin : ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h t source =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) := by
      rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 t source,
        ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source),
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
          control0 t.val n (by exact Nat.le_of_lt htbound)]
    unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
    rw [hr, hr', Option.map_some, Option.map_some] at hin
    have hstate : r.input.state = r'.input.state := by
      have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeState (Option.some.inj hin)
      simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using h
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actual_record_fields rate rewards C_star C_h t source r hr
    obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
      actual_record_fields rate rewards C_star C_h t _ r' hr'
    have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
        hselected, hselected', htime, htime',
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
        ite_eq_left (show t.val < n from htbound)]
    have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
        (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
          (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
      intro v hv
      rw [htime] at hv
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
        hselected, hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
        ite_eq_left (hv.trans htbound)]
    have hcompare := branch_readout_eq_of_temporal_reads rate r r' hstate
      (by rw [hselected, hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected])
      (htime.trans htime'.symm) (hrewards.trans hrewards'.symm) hcurrent hpast 0
    simp only [List.getElem_take, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map]
    change (r.input.time, (ReferenceActiveHorizonMeasurability.roundRecordCode r,
        ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r)) =
      (r'.input.time, (ReferenceActiveHorizonMeasurability.roundRecordCode r',
        ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r'))
    exact Prod.ext (htime.trans htime'.symm) (Prod.ext hcompare.1 hcompare.2)
  · have hz' : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) :=
      fun h => hz ((ReferenceSourcePrefixHistoryFiltration.actualLaunchBy_factor
        rate rewards C_star C_h control0 n hn source).mpr h)
    rw [empty_of_not_launchBy rate rewards C_star C_h n hn source hz,
      empty_of_not_launchBy rate rewards C_star C_h n hn _ hz']

private theorem measurable_list_take {Y α : Type*} [MeasurableSpace Y] [MeasurableSpace α]
    (records : Y → List α) (hrecords : Measurable records)
    (n : Y → ℕ) (hn : Measurable n) :
    Measurable (fun x => (records x).take (n x)) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords
  have hlen : Measurable (fun x => min (n x) (records x).length) :=
    (measurable_of_countable (fun v : ℕ × ℕ => min v.1 v.2)).comp
      (hn.prodMk (measurable_fst.comp hc))
  have ht : Measurable (fun x => fun j =>
      ReferenceActiveHorizonMeasurability.listObservationAt ((records x).take (n x)) j) := by
    apply measurable_pi_iff.mpr
    intro j
    have htag := (measurable_pi_apply j).comp (measurable_snd.comp hc)
    have h : Measurable (fun x => if j < n x then
        ReferenceActiveHorizonMeasurability.listObservationAt (records x) j
        else (Sum.inl () : Unit ⊕ α)) :=
      htag.ite (measurableSet_lt (measurable_const (a := j)) hn) measurable_const
    convert h using 1
    funext x
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    rw [List.getElem?_take]
    by_cases hj : j < n x <;> simp only [hj, ite_true, ite_false]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk ht using 1
  funext x
  exact Prod.ext List.length_take rfl

/-- The literal strict dated observation is measurable in H at index `n+1`.
This includes both actual optional numerical readouts and the whole state code;
it asserts no physical-field identification or conditional probability law. -/
theorem datePrefix_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (fun source : BootstrapPrivateRoundStreams.SourceInput p => datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source)) := by
  have htake := measurable_list_take _
    (ReferenceCompleteNumericalBranchObservation.measurable_completeBranchObservation
      rate rewards C_star C_h)
    (fun source => n - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h)
    ((measurable_of_countable (fun s : ℕ => n - s)).comp
      (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h))
  have hambient : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      datePrefix rate n (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h source)) := by
    simpa only [datePrefix_eq_take rate rewards C_star C_h n hn] using htake
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have h := hambient.comp (comap_measurable
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n))
  convert h using 1
  funext source
  exact datePrefix_factor rate rewards C_star C_h control0 n hn source

end Bandits.Support.ReferenceCompleteObservationPrefixInformation
