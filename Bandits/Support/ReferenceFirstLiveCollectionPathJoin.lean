/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition
public import Bandits.Support.ReferenceActualCollectionNonrenewedEndpointFibreJoin

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# First-LIVE prefix and actual collection path join

The literal first actual nonrenewed collection event produces its canonical
first-cut indices, whole first LIVE prefix, original numerical word, old
payload and actual triggering residual. The whole prefix and sampled
collection path have strict current-control and used-auxiliary locality.
The shared-trigger equality is literal. The joint-law construction is internal;
no manuscript closure follows from this module. No source theorem or regret closure is claimed.

Sources: ZIP4 `06_interruptions.tex:376-426`,
`04_slow_fast_learner.tex:142-215,323-390`,
`appendix_a_local_protocol.tex:28-79`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds
open Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition
open Bandits.Support.ReferenceActualCollectionNonrenewedEndpointFibreJoin
open Bandits.Support.ReferenceActualCollectionHiddenRefreshPath
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceFirstLiveOverflowReadout

namespace Bandits.Support.ReferenceFirstLiveCollectionPathJoin

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Source (p : ConstructorDimensions.Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev AuxiliaryArray (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
abbrev Cell (p : ConstructorDimensions.Parameters) (rate : RateInput p) := LogicalCell p rate

/-- The unnormalized source event of the first actual nonrenewed collection call and its computed clear
PRE-overflow numerical prefix. -/
public def firstLiveCollectionEvent (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set (Source p) :=
  ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t ∩
    (ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
      rate rewards C_star C_h t ∩
      {z | ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false})

section Common

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) (u t : Fin p.T)

local notation "E_nr" => firstLiveCollectionEvent rate rewards C_star C_h u t
local notation "pastAt" => calendarPast rate rewards C_star C_h
local notation "wordAt" => collectionWord rate rewards C_star C_h
local notation "payloadAt" => oldPayload rate rewards C_star C_h
local notation "samplePathAt" => sampledArrayPath rate rewards C_star C_h
local notation "coordinatesAt" => actualCoordinateIndex rate rewards C_star C_h
local notation "stateAt" => collectionState rate rewards C_star C_h
local notation "triggerAt" => triggerInput rate rewards C_star C_h

private theorem actualRecord_suffixFacts (z : Source p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      t z = some record) :
    record ∈ completeSuffixRecords rate z rewards C_star C_h ∧ record.input.time = t := by
  let start := physicalStart rate z rewards C_star C_h
  have hstart : start ≤ t.val := by
    by_cases hs : start ≤ t.val
    · exact hs
    · have hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = none := by
        simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hs]
      rw [hnone] at hrecord
      cases hrecord
  have hlookup : (completeSuffixRecords rate z rewards C_star C_h)[t.val - start]? = some record := by
    simpa [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hstart] using hrecord
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h (t.val - start) record hlookup
  refine ⟨List.mem_of_getElem? hlookup, ?_⟩
  apply Fin.ext
  omega

private theorem actualNonrenewedCollectionCall_iff_oldFreeze :
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
        rate rewards C_star C_h t =
      {z | (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z).isSome = true ∧
        ∃ g, ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
          rate rewards C_star C_h t z = some g ∧ t.val + 1 < g} := by
  ext z
  constructor
  · intro hcall
    rcases hcall with ⟨hpresent, record, hrecord, hstate⟩
    have hfacts := actualRecord_suffixFacts rate rewards C_star C_h t z record hrecord
    cases hcoord : record.input.state.coordinator with
    | collection payload ledger saved =>
        have hfreeze := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
          rate rewards C_star C_h t z record hfacts.1 hfacts.2 payload ledger saved hcoord
        refine ⟨hpresent, ledger.freezeAt, hfreeze, ?_⟩
        simpa only [hcoord, hfacts.2] using hstate
    | first => simp [hcoord] at hstate
    | live registers owned base => simp [hcoord] at hstate
    | dagger => simp [hcoord] at hstate
  · rintro ⟨hpresent, g, hfreeze, hgt⟩
    cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none =>
        have hcall : ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h t z = none := by
          simp [ReferenceCalendarCollectionCallControlLaw.callAt, hrecord]
        simp [hcall] at hpresent
    | some record =>
        cases hselector : ReferenceFirstCollectionSamplerCall.collectionCallAt record with
        | none =>
            have hcall : ReferenceCalendarCollectionCallControlLaw.callAt
                rate rewards C_star C_h t z = none := by
              simp [ReferenceCalendarCollectionCallControlLaw.callAt, hrecord, hselector]
            simp [hcall] at hpresent
        | some call =>
            have hcall : ReferenceCalendarCollectionCallControlLaw.callAt
                rate rewards C_star C_h t z = some call := by
              simp [ReferenceCalendarCollectionCallControlLaw.callAt, hrecord, hselector]
            have hfacts := actualRecord_suffixFacts rate rewards C_star C_h t z record hrecord
            obtain ⟨payload, ledger, saved, hcoord, _, _⟩ :=
              (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec
                record call.1 call.2).mp hselector
            have hfreeze' := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
              rate rewards C_star C_h t z record hfacts.1 hfacts.2 payload ledger saved hcoord
            have hledger : ledger.freezeAt = g := Option.some.inj (hfreeze'.symm.trans hfreeze)
            refine ⟨by simp [hcall], record, hrecord, ?_⟩
            rw [hcoord]
            have htimeValue : record.input.time.val = t.val := congrArg Fin.val hfacts.2
            omega

/-- Membership keeps the actual call and readout as event-local facts. -/
theorem firstLiveCollectionEvent_facts (z : Source p) (hz : z ∈ E_nr) :
    z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t ∧
      ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
        rate rewards C_star C_h t z ∧
      ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false := by
  exact hz

/-- The actual-call cell identifies the first selector and supplies the absence of every earlier actual
selector, independently of later success. -/
theorem firstLiveCollectionEvent_firstCall (z : Source p) (hz : z ∈ E_nr) :
    ∃ (theta : AssignmentParameterFibreKernel.Theta p) (n : ℕ)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z =
        some (u, (t, theta)) ∧
      (completeSuffixRecords rate z rewards C_star C_h)[n]? = some record ∧
      record.input.time = t ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt record = some (u, theta) ∧
      ∀ j < n, ∀ earlier : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        (completeSuffixRecords rate z rewards C_star C_h)[j]? = some earlier →
        ReferenceLaterSamplerParameterMeasurability.parameters? earlier.input = none := by
  have hfirst := (firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz).1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) at hfirst
  obtain ⟨⟨cutoff, date, theta⟩, hcall, hproject⟩ := Option.map_eq_some_iff.mp hfirst
  rcases Prod.mk.inj hproject with ⟨rfl, rfl⟩
  obtain ⟨n, record, hrecord, htime, hselector, hearlier⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
      (rate := rate) rewards C_star C_h z cutoff date theta).mp hcall
  exact ⟨theta, n, record, hcall, hrecord, htime, hselector, hearlier⟩

/-- The first-call observer fixes the first LIVE boundary, not an arbitrary later cutoff. This uses the
accepted actual-prefix coverage theorem. -/
theorem firstLiveCollectionEvent_dates (z : Source p) (hz : z ∈ E_nr) :
    physicalStart rate z rewards C_star C_h ≤ u.val ∧ u.val < t.val ∧
      u.val = physicalStart rate z rewards C_star C_h +
        wholeFirstLiveLength rate rewards C_star C_h z := by
  have hfirst := (firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz).1
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hfirst
  exact ⟨hsu, hut, hu⟩

/-- The same ledger at the first actual selector identifies the canonical zero-based prefix indices. In
particular the LIVE scan excludes the cutoff record at `u`, whereas collection starts with that record.
-/
theorem firstLiveCollectionEvent_canonicalPrefixCell (z : Source p) (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    e = wholeFirstLiveLength rate rewards C_star C_h z ∧ 0 < e ∧ e < b ∧
      ∃ hcell : z ∈ collectionPrefixCell rate rewards C_star C_h e b,
      ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
        (theta : AssignmentParameterFibreKernel.Theta p),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some record ∧
        ReferenceFirstCollectionSamplerCall.collectionCallAt record = some (u, theta) ∧
        record.input.state.coordinator = .collection (payloadAt e b z hcell) ledger saved ∧
        ledger.cutoff = u.val + 1 := by
  dsimp only
  obtain ⟨theta, n, record, _hfirst, hlookup, htime, hselector, _hearlier⟩ :=
    firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z hz
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h n record hlookup
  have htimeValue := congrArg Fin.val htime
  have hstart : physicalStart rate z rewards C_star C_h ≤ t.val := by
    omega
  have hindex : t.val - physicalStart rate z rewards C_star C_h = n := by
    omega
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record := by
    simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart, ite_true, hindex, hlookup]
  obtain ⟨_hcell, hnr, hclear⟩ := firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz
  obtain ⟨e, b, record', _u', _theta', hcell, hactual', _hcall, hdate, ledger, saved, hstate, hcutoff⟩ :=
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_prefixCell
      rate rewards C_star C_h t z hnr hclear
  have hsame : record' = record := Option.some.inj (hactual'.symm.trans hactual)
  subst record'
  obtain ⟨payload', ledger', saved', hstate', hcutoff', _hparameters⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec record u theta).mp hselector
  have hledger : ledger = ledger' :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj (hstate.symm.trans hstate')).2.1
  have hcut : ledger.cutoff = u.val + 1 := hledger ▸ hcutoff'
  have he : e = u.val - physicalStart rate z rewards C_star C_h := by omega
  have hb : b = t.val - physicalStart rate z rewards C_star C_h := by omega
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hcell
  obtain ⟨hsu, hut, hwhole⟩ := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz
  have heb : e < b := by omega
  have hewhole : e = wholeFirstLiveLength rate rewards C_star C_h z := by omega
  subst e
  subst b
  exact ⟨hewhole, by omega, heb, hcell, record, ledger, saved, theta, hactual, hselector, hstate, hcut⟩

/-- Equivalent intrinsic support, expressed with the accepted old-freeze observer and the actual
numerical PRE readout. -/
theorem firstLiveCollectionEvent_eq_correctedCell :
    E_nr =
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t ∩
      {z | ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z = some o ∧ o.2.1 = false} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hfirst, hnr, hclear⟩ := firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz
    rw [actualNonrenewedCollectionCall_iff_oldFreeze] at hnr
    exact ⟨⟨hfirst, hnr.2⟩, hclear⟩
  · rintro ⟨⟨hfirst, hfreeze⟩, hclear⟩
    obtain ⟨n, record, theta, _hlookup, _htime, hactual, hselector, _⟩ :=
      ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
        rate rewards C_star C_h u t z hfirst
    have hcall : ReferenceCalendarCollectionCallControlLaw.callAt
        rate rewards C_star C_h t z = some (u, theta) := by
      simp only [ReferenceCalendarCollectionCallControlLaw.callAt, hactual, Option.bind_some, hselector]
    have hnr : ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
        rate rewards C_star C_h t z := by
      rw [actualNonrenewedCollectionCall_iff_oldFreeze]
      exact ⟨by simp only [hcall, Option.isSome_some], hfreeze⟩
    exact ⟨hfirst, hnr, hclear⟩

/-- Borel support on the original full source; null cells are not removed. -/
theorem measurableSet_firstLiveCollectionEvent :
    MeasurableSet (E_nr) := by
  rw [firstLiveCollectionEvent_eq_correctedCell]
  apply (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
    rate rewards C_star C_h u t).inter
  have hkeep := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
    (fun o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K => !o.2.1)
    ((measurable_of_countable Bool.not).comp (measurable_fst.comp measurable_snd))).comp
      ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
        rate rewards C_star C_h t.val).mono le_rfl le_top)
  have hset := (measurableSet_singleton true).preimage hkeep
  convert hset using 1
  ext z
  cases hr : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h t.val z with
  | none => simp [ReferenceCollectionOutcomeMeasurability.optionalElim, hr]
  | some o =>
      rcases o with ⟨registers, overflow, history⟩
      cases overflow <;> simp [ReferenceCollectionOutcomeMeasurability.optionalElim, hr]

/-- At the actual first call every LIVE cell has already occurred. The calendar observer therefore
retains the whole first LIVE chronological list. -/
theorem firstLiveCollectionEvent_calendarPast (z : Source p) (a : AuxiliaryArray p) (hz : z ∈ E_nr) :
    pastAt (z, a) t.val = firstLiveChronologicalPrefix rate rewards C_star C_h (z, a) ∧
    (pastAt (z, a) t.val).length = u.val - physicalStart rate z rewards C_star C_h := by
  obtain ⟨hsu, hut, hu⟩ := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz
  have heq : pastAt (z, a) t.val = firstLiveChronologicalPrefix rate rewards C_star C_h (z, a) := by
    rw [calendarPast_eq_take_elapsed]
    apply List.take_of_length_le
    rw [firstLiveChronologicalPrefix_length]
    dsimp only [Prod.fst]
    omega
  refine ⟨heq, ?_⟩
  rw [heq, firstLiveChronologicalPrefix_length]
  dsimp only [Prod.fst]
  omega

/-- The original collection word has precisely the whole original LIVE word as its prefix. Membership
supplies all coverage; no word is assumed. -/
theorem firstLiveCollectionEvent_word_prefix (z : Source p) (hz : z ∈ E_nr)
    (hcell : z ∈ collectionPrefixCell rate rewards C_star C_h
      (u.val - physicalStart rate z rewards C_star C_h)
      (t.val - physicalStart rate z rewards C_star C_h)) :
    (wordAt _ _ z hcell).take (u.val - physicalStart rate z rewards C_star C_h) =
      wholeFirstLiveCells rate rewards C_star C_h z := by
  have hfirst := (firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz).1
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, _htotal,
    _hpending, _hrecord, _hchoice, _hDlen, _hDzero, _hDread, hLD, hPast,
    hlen, _hcoverage, _hprefix, hsplit, _hstart⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hfirst
  have hcorrected := (firstLiveCollectionEvent_eq_correctedCell rate rewards C_star C_h u t) ▸ hz
  obtain ⟨L', c, hPast', _hc, hinputs, hlen'⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_initial_inputs
      rate rewards C_star C_h u t z
      hcorrected.1
  have hLL : L' = L := Option.some.inj (hPast'.symm.trans hPast)
  subst L'
  let s := physicalStart rate z rewards C_star C_h
  let b := t.val - s
  have hb : b < (completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [completeSuffixRecords_length]
    have ht := t.isLt
    omega
  have hword := actualOriginalWord_prefix rate rewards C_star C_h z
    (collectionPrefixCell_launch rate rewards C_star C_h _ _ z hcell) (b + 1) (by omega)
  have hdate : s + (b + 1) = t.val + 1 := by dsimp [b, s]; omega
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h (s + (b + 1)) z = some ((wordAt _ _ z hcell).take (b + 1)) at hword
  rw [hdate, hinputs] at hword
  have htake := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.take b)
    (Option.some.inj hword).symm
  have hLb : L.length = b := hlen
  simp only [List.take_take, Nat.min_eq_left (Nat.le_succ b),
    List.take_append, hLb, Nat.sub_self, List.take_zero, List.append_nil] at htake
  have htake' : (wordAt _ _ z hcell).take b = L := by
    simpa only [← hLb, List.take_length] using htake
  have hsplitU := hsplit u le_rfl hut.le
  rw [Nat.sub_self, List.take_zero, List.append_nil] at hsplitU
  have heB : u.val - s ≤ b := by dsimp [b]; omega
  rw [← htake', List.take_take, Nat.min_eq_left heB] at hsplitU
  have hwhole : wholeFirstLiveCells rate rewards C_star C_h z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T - s) hs := by
    simp only [wholeFirstLiveCells, generatedBoundary, generatedInput, hc, dite_true, s]
  exact hsplitU.trans hwhole.symm

private theorem selectedPayload_congr {rate : RateInput p}
    {r s : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrs : r = s) (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s) :
    a.selected.view.payload = b.selected.view.payload := by
  subst s
  have hselected := Option.some.inj (a.selection_actual.symm.trans b.selection_actual)
  exact congrArg (fun selected => selected.view.payload) hselected

/-- Every selected LIVE payload is the old payload retained at this first cutoff, including the entire
assignment, anchor, and initial DOWN queues. -/
theorem firstLiveCollectionEvent_payload (z : Source p) (hz : z ∈ E_nr)
    (hcell : z ∈ collectionPrefixCell rate rewards C_star C_h
      (u.val - physicalStart rate z rewards C_star C_h)
      (t.val - physicalStart rate z rewards C_star C_h))
    (k : Fin (wholeFirstLiveWindow rate rewards C_star C_h z).length) :
    (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem k.isLt)).selected.view.payload =
      payloadAt _ _ z hcell := by
  have hfirst := (firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz).1
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hfirst
  let count := p.T - physicalStart rate z rewards C_star C_h
  have hR := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hc
  have hW : wholeFirstLiveWindow rate rewards C_star C_h z =
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hc count hs := by
    unfold wholeFirstLiveWindow ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← hR]
  have hshort' : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hc count hs).length < count := by
    have hE := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h z hc
    rw [← hW]
    simpa only [wholeFirstLiveWindow, hE] using hshort
  obtain ⟨cut, suffix, r, q, base, dispatched, hstart, ledger, hinit, hledger,
    hdomain, hclock, hpending, hnoAssignment, selected, recording, hcut, _hrecords,
    _hphysical, _htime, _hrows, _hselected, _hrewards, _hsigma, _hn, _hbase,
    hstate, _hprep, _hu, _huBound, _huGrid, _hledgerCut, _hwpos, hpayloads, _htail⟩ :=
    ReferenceFirstCutoffKnownNumericalState.actual_first_cutoff_known_numerical_state
      rate z rewards C_star C_h hc count hs hshort'
  have he := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).1
  have hlen : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hc count hs).length =
      u.val - physicalStart rate z rewards C_star C_h := by
    rw [← hW]
    exact he.symm
  have hcutR : (completeSuffixRecords rate z rewards C_star C_h)[u.val - physicalStart
        rate z rewards C_star C_h]? = some cut := by
    rw [hR, ← hlen]
    exact (List.getElem?_eq_getElem _).trans (congrArg some hcut.symm)
  have hp := oldPayload_eq rate rewards C_star C_h _ _ z hcell r.payload (by
      simp only [cutoffPayload?, hcutR, Option.bind_some, hstate])
  let j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hc count hs).length := ⟨k.val, by rw [← hW]; exact k.isLt⟩
  have hr : (wholeFirstLiveWindow rate rewards C_star C_h z)[k.val] =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hc count hs)[j.val] := by
    simp only [hW, j]
  exact (selectedPayload_congr hr (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem k.isLt))
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate z rewards C_star C_h hc count hs j)).trans ((hpayloads j).trans hp.symm)

/-- Event membership supplies the canonical prefix-cell proof itself. -/
theorem firstLiveCollectionEvent_prefixMembership (z : Source p) (hz : z ∈ E_nr) :
    z ∈ collectionPrefixCell rate rewards C_star C_h (u.val - physicalStart rate z rewards C_star C_h)
      (t.val - physicalStart rate z rewards C_star C_h) :=
  (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).2.2.2.choose

private theorem collectionState_clear_before (e b : ℕ) (z : Source p)
    (hcell : z ∈ collectionPrefixCell rate rewards C_star C_h e b) (k : ℕ) (hk : k ≤ b) :
    (stateAt e b z hcell k).overflow = false := by
  have hb := collectionWord_bound rate rewards C_star C_h e b z hcell
  have hclear := collectionWord_retained rate rewards C_star C_h e b z hcell
  unfold collectionState at hclear ⊢
  cases ho : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((wordAt e b z hcell).take k)).overflow with
  | false => rfl
  | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        _ _ k (hk.trans hb)).mp ho
      have hlast := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        _ _ b hb).mpr (hfirst.trans hk)
      rw [hclear] at hlast
      cases hlast

/-- The actual final LIVE update has a clear PRE-state and a true physical proposal. Its residual uses
the original numerical trigger, old anchor and precisely the label-one scalar at `u-1`; the detecting
POST update is retained. -/
theorem firstLiveCollectionEvent_trigger (z : Source p) (a : AuxiliaryArray p) (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ (k : Fin (wholeFirstLiveWindow rate rewards C_star C_h z).length) (q : Fin p.T),
      k.val = e - 1 ∧ q.val + 1 = u.val ∧
      (stateAt e b z hcell (e - 1)).overflow = false ∧
      let entry := (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[k.val]'(by
          rw [firstLiveChronologicalPrefix_length]
          exact k.isLt)
      entry.time = q ∧ entry.proposal = true ∧
      entry.nextSlowSet = residualDraw rate (stateAt e b z hcell (e - 1)) (triggerAt e b z hcell)
        (payloadAt e b z hcell).anchor
        (payloadAt e b z hcell).anchor_pos (a (q, 1)) := by
  dsimp only
  let s := physicalStart rate z rewards C_star C_h
  let e := u.val - s
  let b := t.val - s
  let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
  obtain ⟨he, hpos, heb, _⟩ := firstLiveCollectionEvent_canonicalPrefixCell
    rate rewards C_star C_h u t z hz
  have he' : e = (wholeFirstLiveWindow rate rewards C_star C_h z).length := he
  let k : Fin (wholeFirstLiveWindow rate rewards C_star C_h z).length := ⟨e - 1, by omega⟩
  let r := (wholeFirstLiveWindow rate rewards C_star C_h z)[k.val]
  let cell := wholeLiveCell rate rewards C_star C_h z r (List.getElem_mem k.isLt)
  have hword := firstLiveCollectionEvent_word_prefix rate rewards C_star C_h u t z hz hcell
  change (wordAt e b z hcell).take e = wholeFirstLiveCells rate rewards C_star C_h z at hword
  have hstate : stateAt e b z hcell (e - 1) =
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((wholeFirstLiveCells rate rewards C_star C_h z).take k.val) := by
    unfold collectionState
    rw [← hword, List.take_take, Nat.min_eq_left (by dsimp [k]; omega)]
  have hinput : cell.input = triggerAt e b z hcell := by
    have hget := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs[k.val]?) hword
    rw [List.getElem?_take, ite_eq_left (by dsimp [k]; omega), List.getElem?_eq_getElem (by
        have hbound := collectionWord_bound rate rewards C_star C_h e b z hcell
        dsimp [k]; omega), List.getElem?_eq_getElem (by
        rw [wholeFirstLiveCells_length]
        exact k.isLt)] at hget
    exact (wholeLiveCell_input_eq rate rewards C_star C_h z k).trans (Option.some.inj hget).symm
  have hpayload := firstLiveCollectionEvent_payload rate rewards C_star C_h u t z hz hcell k
  have hclear := collectionState_clear_before rate rewards C_star C_h e b z hcell (e - 1) (by omega)
  have hgeometry := wholeLiveCell_geometry rate rewards C_star C_h z k
  have hdate : r.input.time.val + 1 = u.val := by
    have hsu := (firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz).1
    have htime : r.input.time.val = s + k.val := hgeometry.2.2.1
    dsimp [k, e, s] at htime ⊢
    omega
  obtain ⟨stamp, hstamp, hprop⟩ :=
    collectionPrefixCell_trigger_proposal rate rewards C_star C_h e b z hcell
  have hstampEq : stamp = r.input.time := by
    apply Fin.ext
    change stamp.val + 1 = s + e at hstamp
    have hsu := (firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz).1
    dsimp [e, s] at hstamp
    omega
  rw [hstampEq] at hprop
  have hendpoint := firstLiveChronologicalPrefix_finite_window_endpoint_triggering_residual
      rate rewards C_star C_h z a k (hstate ▸ hclear) hprop
  refine ⟨k, r.input.time, rfl, hdate, hclear, ?_, hendpoint.2.2.1, ?_⟩
  · exact firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h z a k
  · have hnext := hendpoint.2.2.2.1
    rw [← hstate, hinput] at hnext
    simpa only [hpayload] using hnext

/-- Literal equality of the two accepted inverse-CDF samplers, at the same state, numerical update,
anchor and scalar. -/
theorem residualDraw_eq_sampleResidual
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) (x : ContinuousControlSlice.Scalar) :
    residualDraw rate state round anchor hanchor x = DeferredRefreshUniformKernels.sampleResidual p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor x := rfl

/-- The entire past's final LIVE cell and the original deferred path share one literal triggering scalar.
There is no independent redraw. -/
theorem firstLiveCollectionEvent_last_next (z : Source p) (a : AuxiliaryArray p) (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ hlast : e - 1 < (pastAt (z, a) t.val).length, ((pastAt (z, a) t.val)[e - 1]'hlast).nextSlowSet =
        samplePathAt e b z hcell (b - e) le_rfl a 0 := by
  dsimp only
  let s := physicalStart rate z rewards C_star C_h
  let e := u.val - s
  let b := t.val - s
  let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
  obtain ⟨k, q, hk, hq, _hclear, _htime, _hprop, hnext⟩ :=
    firstLiveCollectionEvent_trigger rate rewards C_star C_h u t z a hz
  have hpos := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).2.1
  have hpast := firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z a hz
  have hlast : e - 1 < (calendarPast
      rate rewards C_star C_h (z, a) t.val).length := by rw [hpast.2]; change e - 1 < e; omega
  refine ⟨hlast, ?_⟩
  have hnext' := hnext
  simp only [hk] at hnext'
  simp only [hpast.1]
  rw [hnext', residualDraw_eq_sampleResidual]
  unfold sampledArrayPath
  rw [sampledPath_zero]
  unfold triggerSampler
  congr 1
  have hindex := actualCoordinateIndex_trigger rate rewards C_star C_h e b z hcell (b - e) le_rfl
  have hdate : (actualCoordinateIndex
      rate rewards C_star C_h e b z hcell (b - e) le_rfl (.inl ())).1 = q := by
    apply Fin.ext
    rw [hindex.1]
    have hsu := (firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz).1
    dsimp [e, s]
    omega
  change a (q, 1) = a _
  rw [show actualCoordinateIndex
      rate rewards C_star C_h e b z hcell (b - e) le_rfl (.inl ()) = (q, 1) from
    Prod.ext hdate hindex.2]

private theorem actualLookup_fields
    (z : Source p) (j : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (completeSuffixRecords rate z rewards C_star C_h)[j]? = some r) :
    r.input.rows = z.1.2 ∧ r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards := by
  have hj := (List.getElem?_eq_some_iff.mp hr).1
  have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
    rate rewards C_star C_h j ⟨z, hj⟩
  have heq : (completeSuffixRecords rate z rewards C_star C_h)[j]'hj = r :=
    Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hr)
  dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt, List.get_eq_getElem] at hf
  rw [heq] at hf
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-- A first call's actual numerical word strictly before its date is fixed by the original source
controls strictly before that date. The proof compares actual records using the accepted nonread
identities, without a supplied path-locality assumption. -/
theorem firstCall_prefixInputs_suffix (z : Source p) (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h t.val
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix) =
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h t.val z := by
  let z' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix
  obtain ⟨active, hlaunch, hs, hstart, hlaunch'⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_launch_of_firstCollectionCall
      rate rewards C_star C_h z u t theta suffix hcall
  obtain ⟨n, hdate, hrecords⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_records_of_firstCollectionCall
      rate rewards C_star C_h z u t theta suffix hcall
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
  have hcross' := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z' rewards C_star C_h).mp (by rw [hlaunch']; rfl)
  have hla : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := ⟨hcross, hs⟩
  have hlb : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z' := ⟨hcross', by rw [hstart]; exact hs⟩
  have hn : t.val - physicalStart rate z rewards C_star C_h = n := by omega
  have hnR : n ≤ (completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [completeSuffixRecords_length]
    have ht := t.isLt
    omega
  have hnR' : n ≤ (completeSuffixRecords rate z' rewards C_star C_h).length := by
    rw [completeSuffixRecords_length, hstart]
    simpa only [completeSuffixRecords_length] using hnR
  have hmaps : ((completeSuffixRecords
      rate z' rewards C_star C_h).take n).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
      ((completeSuffixRecords rate z rewards C_star C_h).take n).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, Nat.min_eq_left hnR, Nat.min_eq_left hnR']
    · intro j hj hj'
      have hjn : j < n := by simpa only [List.length_map, List.length_take, Nat.min_eq_left hnR'] using hj
      obtain ⟨a, b, ha, hb, hstate, htime⟩ := hrecords j hjn.le
      obtain ⟨hrowsA, hselectedA, hrewardsA⟩ := actualLookup_fields rate rewards C_star C_h z j a ha
      obtain ⟨hrowsB, hselectedB, hrewardsB⟩ := actualLookup_fields rate rewards C_star C_h z' j b hb
      have htimeA := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
        rate z rewards C_star C_h j a ha
      have hbefore : a.input.time.val < t.val := by omega
      have hcurrent : a.input.row.2 a.input.time = b.input.row.2 b.input.time := by
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hrowsA, hrowsB,
          hselectedA, hselectedB, z',
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_selected, ← htime]
        exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
          z t a.input.time suffix hbefore).symm
      have hpast : ∀ v : Fin p.T, v.val < a.input.time.val →
          (a.input.row.2 v).1 ContinuousControlSlice.Label.prop =
          (b.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
        intro v hv
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hrowsA, hrowsB,
          hselectedA, hselectedB, z',
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_selected]
        rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
          z t v suffix (by omega)]
      have hcompare := ReferenceFirstCollectionAssignmentStepNonRead.compare_of_current
        a b hstate (by rw [hselectedA, hselectedB]; rfl) htime
        (hrewardsA.trans hrewardsB.symm) hcurrent hpast
      have haVal : (completeSuffixRecords rate z rewards C_star C_h)[j]'(hjn.trans_le hnR) = a :=
        Option.some.inj ((List.getElem?_eq_getElem _).symm.trans ha)
      have hbVal : (completeSuffixRecords rate z' rewards C_star C_h)[j]'(hjn.trans_le hnR') = b :=
        Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hb)
      simpa only [List.getElem_map, List.getElem_take, haVal, hbVal] using hcompare.2.2.2.symm
  unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rw [ite_eq_left hlb, ite_eq_left hla]
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords, hstart, hn]
  exact congrArg (List.mapM id) hmaps

/-- The literal event, including its computed PRE-clear test, is preserved when current and future
controls of this same source are replaced. -/
theorem firstLiveCollectionEvent_suffix_forward (z : Source p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hz : z ∈ E_nr) :
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix ∈ E_nr := by
  obtain ⟨theta, n, r, hcall, _⟩ := firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z hz
  have hsupport := (firstLiveCollectionEvent_eq_correctedCell rate rewards C_star C_h u t) ▸ hz
  rw [firstLiveCollectionEvent_eq_correctedCell]
  refine ⟨⟨(ReferenceFirstCollectionRenewalPastLocality.actualCollectionCallCell_iff_replaceSelectedControlSuffix
    rate rewards C_star C_h z u t suffix).mp hsupport.1.1, ?_⟩, ?_⟩
  · rw [← ReferenceFirstCollectionRenewalPastLocality.oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z u t theta suffix hcall]
    exact hsupport.1.2
  · change ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h t.val
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix) = some o ∧
      o.2.1 = false
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rw [firstCall_prefixInputs_suffix rate rewards C_star C_h u t z theta suffix hcall]
    exact hsupport.2

/-- Event invariance is two-sided and does not require positive event mass. -/
theorem firstLiveCollectionEvent_suffix_iff (z : Source p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    z ∈ E_nr ↔
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix ∈ E_nr := by
  constructor
  · exact firstLiveCollectionEvent_suffix_forward rate rewards C_star C_h u t z suffix
  · intro hz
    have h := firstLiveCollectionEvent_suffix_forward rate rewards C_star C_h u t _
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 hz
    rw [ReferenceFirstCollectionRenewalPastLocality.replaceSelectedControlSuffix_restore] at h
    exact h

/-- The same first-call suffix comparison preserves the entire consumed numerical word and whole old
payload. The unchanged prefix is established before any sampled-path locality is used. -/
theorem firstLiveCollectionEvent_suffix_word (z : Source p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let z' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ hcell' : z' ∈ collectionPrefixCell rate rewards C_star C_h e b, (wordAt e b z' hcell').take b =
        (wordAt e b z hcell).take b ∧
      payloadAt e b z' hcell' = payloadAt e b z hcell := by
  dsimp only
  let s := physicalStart rate z rewards C_star C_h
  let e := u.val - s
  let b := t.val - s
  let z' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix
  let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
  obtain ⟨theta, n, record, hcall, _⟩ :=
    firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z hz
  obtain ⟨active, hlaunch, hs, hstart, hlaunch'⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_launch_of_firstCollectionCall
      rate rewards C_star C_h z u t theta suffix hcall
  have hz' := firstLiveCollectionEvent_suffix_forward rate rewards C_star C_h u t z suffix hz
  have hcell' := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z' hz'
  rw [hstart] at hcell'
  refine ⟨hcell', ?_, ?_⟩
  · have hraw := firstCall_prefixInputs_suffix rate rewards C_star C_h u t z theta suffix hcall
    have hleft := actualOriginalWord_prefix rate rewards C_star C_h z'
      (collectionPrefixCell_launch rate rewards C_star C_h e b z' hcell') b hcell'.2.1
    have hright := actualOriginalWord_prefix rate rewards C_star C_h z
      (collectionPrefixCell_launch rate rewards C_star C_h e b z hcell) b hcell.2.1
    have hdate : s + b = t.val := by dsimp [s, b]; omega
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (physicalStart rate z' rewards C_star C_h + b) z' = some
        ((wordAt e b z' hcell').take b) at hleft
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + b) z = some ((wordAt e b z hcell).take b) at hright
    rw [hstart, hdate] at hleft
    rw [hdate] at hright
    exact Option.some.inj (hleft.symm.trans (hraw.trans hright))
  · obtain ⟨j, hdate, hrecords⟩ :=
      ReferenceFirstCollectionRenewalPastLocality.actual_records_of_firstCollectionCall
        rate rewards C_star C_h z u t theta suffix hcall
    have he : e ≤ j := by
      have hdates := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz
      dsimp [e, s]
      omega
    obtain ⟨a, b', ha, hb, hstate, _htime⟩ := hrecords e he
    have hcut : cutoffPayload? rate rewards C_star C_h e z' =
        cutoffPayload? rate rewards C_star C_h e z := by
      unfold cutoffPayload?
      rw [hb, ha]
      simp only [Option.bind_some]
      rw [← hstate]
    obtain ⟨_hi, r, _q, _base, _hstate, _hcutoff, _hbefore, hpayload⟩ :=
      collectionPrefixCell_live rate rewards C_star C_h e b z hcell
    exact (oldPayload_eq rate rewards C_star C_h e b z' hcell' r.payload (hcut.trans hpayload)).trans
      (oldPayload_eq rate rewards C_star C_h e b z hcell r.payload hpayload).symm

/-- All fields of the whole LIVE past depend on only its actual final residual scalar. Every label-zero
coordinate remains free to be retained. -/
theorem firstLiveCollectionEvent_calendarPast_auxiliary_ext (z : Source p) (a a' : AuxiliaryArray p)
    (hz : z ∈ E_nr)
    (haa : ∀ q : Fin p.T, q.val + 1 = u.val → a (q, 1) = a' (q, 1)) :
    pastAt (z, a) t.val = pastAt (z, a') t.val := by
  rw [(firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z a hz).1, (firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z a' hz).1]
  obtain ⟨k, q, hk, hq, _hclear, htime, _⟩ :=
    firstLiveCollectionEvent_trigger rate rewards C_star C_h u t z a hz
  have he := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).1
  have hlast : k.val + 1 = (wholeFirstLiveWindow rate rewards C_star C_h z).length := by
    change _ = wholeFirstLiveLength rate rewards C_star C_h z
    have hpos := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).2.1
    omega
  apply firstLiveChronologicalPrefix_last_auxiliary_ext rate rewards C_star C_h z a a' k hlast
  have hphysical := firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h z a k
  have hrtime := hphysical.symm.trans htime
  rw [hrtime]
  exact haa q hq

/-- Strict current-control locality of the complete calendar past, with all original private arrays and
unread earlier coordinates retained. -/
theorem calendarPast_replace_current (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : Source p) (a : AuxiliaryArray p) (c : ContinuousLearningRows.TimeControl p) :
    calendarPast rate rewards C_star C_h
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c, a) t.val =
      calendarPast rate rewards C_star C_h (z, a) t.val := by
  rw [calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val t.isLt.le _ a,
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current,
    ← calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val t.isLt.le z a]

/-- The actual hidden path is unchanged by replacing current and future controls of the same physical
source. Its inherited word and anchor are proved equal first; the existing path recurrences then compare
every entry. -/
theorem firstLiveCollectionEvent_suffix_path (z : Source p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let z' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ hcell' : z' ∈ collectionPrefixCell rate rewards C_star C_h e b,
      ∀ (n : ℕ) (hn : n ≤ b - e) (a : AuxiliaryArray p),
      samplePathAt e b z' hcell' n hn a =
      samplePathAt e b z hcell n hn a := by
  dsimp only
  let s := physicalStart rate z rewards C_star C_h
  let e := u.val - s
  let b := t.val - s
  let z' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix
  let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
  obtain ⟨hcell', hword, hpayload⟩ :=
    firstLiveCollectionEvent_suffix_word rate rewards C_star C_h u t z suffix hz
  change (wordAt e b z' hcell').take b = (wordAt e b z hcell).take b at hword
  obtain ⟨theta, _n, _record, hcall, _⟩ :=
    firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z hz
  obtain ⟨_active, _hlaunch, _hs, hstart, _hlaunch'⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_launch_of_firstCollectionCall
      rate rewards C_star C_h z u t theta suffix hcall
  change physicalStart rate z' rewards C_star C_h = physicalStart rate z rewards C_star C_h at hstart
  change payloadAt e b z' hcell' = payloadAt e b z hcell at hpayload
  have hstate (j : ℕ) (hj : j ≤ b) :
      stateAt e b z' hcell' j =
      stateAt e b z hcell j := by
    have ht := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.take j) hword
    simp only [List.take_take, Nat.min_eq_left hj] at ht
    exact congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)) ht
  have hbound := collectionWord_bound rate rewards C_star C_h e b z hcell
  have hbound' := collectionWord_bound rate rewards C_star C_h e b z' hcell'
  have hinput (j : ℕ) (hj : j < b) :
      (wordAt e b z' hcell')[j]'(hj.trans_le hbound') =
      (wordAt e b z hcell)[j]'(hj.trans_le hbound) := by
    have ht := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs[j]?) hword
    simp only [List.getElem?_take, ite_eq_left hj, List.getElem?_eq_getElem (hj.trans_le hbound'),
      List.getElem?_eq_getElem (hj.trans_le hbound)] at ht
    exact Option.some.inj ht
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hcell
  have heb := hcell.1
  refine ⟨hcell', ?_⟩
  change ∀ (n : ℕ) (hn : n ≤ b - e) (a : AuxiliaryArray p), samplePathAt e b z' hcell' n hn a =
    samplePathAt e b z hcell n hn a
  intro n hn a
  have hcoords : actualPrefixCoordinates rate rewards C_star C_h e b ⟨z', hcell'⟩ n hn a =
      actualPrefixCoordinates rate rewards C_star C_h e b ⟨z, hcell⟩ n hn a := by
    unfold actualPrefixCoordinates actualCoordinateIndex cutoffDate prefixDate
    simp only [DeferredRefreshUniformEvaluator.coordinateIndex,
      DeferredRefreshUniformEvaluator.triggerIndex, DeferredRefreshUniformEvaluator.stepIndex, hstart]
  unfold sampledArrayPath
  rw [hcoords]
  funext j
  induction j using Fin.induction with
  | zero =>
      rw [sampledPath_zero, sampledPath_zero]
      unfold triggerSampler
      rw [hstate (e - 1) (by omega)]
      have ht : triggerAt e b z' hcell' = triggerAt e b z hcell := hinput (e - 1) (by omega)
      rw [ht]
      simp only [hpayload]
  | succ i ih =>
      rw [sampledPath_succ, sampledPath_succ]
      unfold transitionSampler
      rw [hstate (e + i.val) (by have hi := i.isLt; omega), ih]
      have ht : windowInput rate rewards C_star C_h e b z' hcell' ⟨i.val, by have hi := i.isLt; omega⟩ =
          windowInput rate rewards C_star C_h e b z hcell ⟨i.val, by have hi := i.isLt; omega⟩ :=
        hinput (e + i.val) (by have hi := i.isLt; omega)
      rw [ht]
      simp only [hpayload]

private theorem replaceSourceControl_eq_suffix
     (z : Source p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t
        (Function.update (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t c) := by
  classical
  unfold ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
  rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  apply Prod.ext
  · refine Prod.ext rfl ?_
    apply congrArg (Function.update z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
    refine Prod.ext rfl ?_
    funext v
    by_cases hv : v.val < t.val
    · have hne : v ≠ t := by intro h; subst v; omega
      simp only [hv, ite_true, Function.update_of_ne hne]
    · simp only [hv, ite_false]
  · rfl

/-- The exact unnormalized event is invariant under replacing the current whole control of this same
source. -/
theorem firstLiveCollectionEvent_replace_current_iff
     (z : Source p) (c : ContinuousLearningRows.TimeControl p) :
    z ∈ E_nr ↔ ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E_nr := by
  rw [replaceSourceControl_eq_suffix]
  exact firstLiveCollectionEvent_suffix_iff rate rewards C_star C_h u t z _

/-- Joint strict current-control locality of the WHOLE chronological past and the SAME original sampled
collection path, before any law is asserted. -/
theorem firstLiveCollectionEvent_replace_current_pair
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (z : Source p) (a : AuxiliaryArray p) (c : ContinuousLearningRows.TimeControl p)
    (hz : z ∈ firstLiveCollectionEvent rate rewards C_star C_h u t) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ hcell' : z' ∈ collectionPrefixCell rate rewards C_star C_h e b,
      (calendarPast rate rewards C_star C_h (z', a) t.val,
        sampledArrayPath rate rewards C_star C_h e b z' hcell' (b - e) le_rfl a) =
      (calendarPast rate rewards C_star C_h (z, a) t.val,
        sampledArrayPath rate rewards C_star C_h e b z hcell (b - e) le_rfl a) := by
  dsimp only
  rw [replaceSourceControl_eq_suffix]
  obtain ⟨hcell', hpath⟩ := firstLiveCollectionEvent_suffix_path rate rewards C_star C_h u t z
    (Function.update (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t c) hz
  refine ⟨hcell', Prod.ext ?_ (hpath _ le_rfl a)⟩
  change calendarPast rate rewards C_star C_h
    (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t
      (Function.update (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t c), a) t.val =
    calendarPast rate rewards C_star C_h (z, a) t.val
  rw [← replaceSourceControl_eq_suffix]
  exact calendarPast_replace_current rate rewards C_star C_h control0 t z a c

/-- The literal consumed addresses are the single trigger at `u-1`, then both labels at each date
`u+i<t`. In particular date `t` is unused. -/
theorem firstLiveCollectionEvent_used_addresses (z : Source p) (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    let index := coordinatesAt e b z hcell (b - e) le_rfl
    b - e = t.val - u.val ∧ (index (.inl ())).1.val + 1 = u.val ∧ (index (.inl ())).2 = 1 ∧
      (∀ i : Fin (b - e), (index (.inr (.inl i))).1.val = u.val + i.val ∧ (index (.inr (.inl i))).2 = 0 ∧
        (index (.inr (.inr i))).1.val = u.val + i.val ∧
        (index (.inr (.inr i))).2 = 1) ∧
      ∀ i, (index i).1.val < t.val := by
  dsimp only
  let s := physicalStart rate z rewards C_star C_h
  let e := u.val - s
  let b := t.val - s
  let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
  obtain ⟨hsu, hut, _⟩ := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z hz
  have hpos := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z hz).2.1
  have htrigger := actualCoordinateIndex_trigger rate rewards C_star C_h e b z hcell (b - e) le_rfl
  have hstep := actualCoordinateIndex_step rate rewards C_star C_h e b z hcell (b - e) le_rfl
  have hlength : b - e = t.val - u.val := by dsimp [b, e, s]; omega
  refine ⟨hlength, ?_, htrigger.2, ?_, ?_⟩
  · rw [htrigger.1]
    dsimp [e, s]
    omega
  · intro i
    obtain ⟨h0, hl0, h1, hl1⟩ := hstep i
    refine ⟨?_, hl0, ?_, hl1⟩
    · rw [h0]
      dsimp [e, s]
      omega
    · rw [h1]
      dsimp [e, s]
      omega
  · intro i
    cases i with
    | inl v =>
        cases v
        rw [htrigger.1]
        dsimp [e, s]
        omega
    | inr i =>
        cases i with
        | inl i =>
            rw [(hstep i).1]
            have hi := i.isLt
            dsimp [b, e, s] at hi ⊢
            omega
        | inr i =>
            rw [(hstep i).2.2.1]
            have hi := i.isLt
            dsimp [b, e, s] at hi ⊢
            omega

/-- Joint auxiliary locality keeps exactly the trigger and subsequent pairs used by the actual path.
Every other auxiliary coordinate may change. -/
theorem firstLiveCollectionEvent_pair_auxiliary_ext (z : Source p) (a a' : AuxiliaryArray p)
    (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    (∀ i, a (coordinatesAt e b z hcell (b - e) le_rfl i) =
      a' (coordinatesAt e b z hcell (b - e) le_rfl i)) →
    (pastAt (z, a) t.val, samplePathAt e b z hcell (b - e) le_rfl a) =
    (pastAt (z, a') t.val, samplePathAt e b z hcell (b - e) le_rfl a') := by
  dsimp only
  intro hused
  refine Prod.ext ?_ (sampledArrayPath_eq_of_used_entries
    rate rewards C_star C_h _ _ z _ _ le_rfl a a' hused)
  change pastAt (z, a) t.val = pastAt (z, a') t.val
  apply firstLiveCollectionEvent_calendarPast_auxiliary_ext rate rewards C_star C_h u t z a a' hz
  intro q hq
  have haddress := firstLiveCollectionEvent_used_addresses rate rewards C_star C_h u t z hz
  have heq : coordinatesAt (u.val - physicalStart rate z rewards C_star C_h)
      (t.val - physicalStart rate z rewards C_star C_h)
      z (firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz)
      _ le_rfl (.inl ()) = (q, 1) := by
    apply Prod.ext
    · apply Fin.ext
      exact Nat.add_right_cancel (haddress.2.1.trans hq.symm)
    · exact haddress.2.2.1
  simpa only [heq] using hused (.inl ())

/-- The strict current-control comparison retains the actual numerical word through the call and the
entire old payload, including its anchor and DOWN queue seed. Both are produced from event membership on
the same source. -/
theorem firstLiveCollectionEvent_replace_current_word
     (z : Source p) (c : ContinuousLearningRows.TimeControl p)
    (hz : z ∈ E_nr) :
    let s := physicalStart rate z rewards C_star C_h
    let e := u.val - s
    let b := t.val - s
    let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c
    let hcell := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z hz
    ∃ hcell' : z' ∈ collectionPrefixCell rate rewards C_star C_h e b, (wordAt e b z' hcell').take b =
        (wordAt e b z hcell).take b ∧
      payloadAt e b z' hcell' = payloadAt e b z hcell := by
  dsimp only
  rw [replaceSourceControl_eq_suffix]
  exact firstLiveCollectionEvent_suffix_word rate rewards C_star C_h u t z _ hz

/-- Null support has zero restricted source mass; no normalization or positivity of the event is
required. -/
theorem firstLiveCollectionEvent_restrict_eq_zero_iff :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (E_nr) = 0 ↔
      BootstrapPrivateRoundStreams.sourceInputLaw p (E_nr) = 0 :=
  Measure.restrict_eq_zero

end Common

section Joint

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) (u t : Fin p.T)

/-- The literal event domain, retaining the full original source. -/
abbrev EventSource := {z : Source p // z ∈ firstLiveCollectionEvent rate rewards C_star C_h u t}
abbrev Path := Fin (t.val - u.val + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m
abbrev Innovations := ContinuousControlSlice.Scalar ×
  (Fin (t.val - u.val) → ContinuousControlSlice.Scalar)

/-- Unnormalized restriction, expressed on its Borel subtype. -/
def eventSourceLaw : Measure (EventSource rate rewards C_star C_h u t) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val

theorem eventSourceLaw_map :
    (eventSourceLaw rate rewards C_star C_h u t).map Subtype.val =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstLiveCollectionEvent rate rewards C_star C_h u t) :=
  map_comap_subtype_coe (measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t) _

/-- The subtype product is exactly the original unnormalized event restriction. -/
theorem eventProductLaw_map :
    ((eventSourceLaw rate rewards C_star C_h u t).prod (auxiliaryUniformLaw p)).map
      (Prod.map (Subtype.val : EventSource rate rewards C_star C_h u t → Source p) id) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod (auxiliaryUniformLaw p)).restrict
        (firstLiveCollectionEvent rate rewards C_star C_h u t ×ˢ Set.univ) := by
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    eventSourceLaw_map, Measure.map_id, Measure.restrict_prod_eq_prod_univ]

/-- The original path, with its event-proved length written in calendar coordinates. -/
def collectionPath (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) : Path u t :=
  let s := physicalStart rate z.val rewards C_star C_h
  sampledArrayPath rate rewards C_star C_h (u.val - s) (t.val - s) z.val
    (firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property)
    (t.val - u.val) (by
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      dsimp [s]; omega) a

/-- The unique triggering date on the nonempty event. -/
def triggerDate : Fin p.T := ⟨u.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩

def triggerSource (z : EventSource rate rewards C_star C_h u t) :
    LiveCalendarSource rate rewards C_star C_h (triggerDate u) :=
  ⟨z.val, (currentCellGate_iff rate rewards C_star C_h (triggerDate u) z.val).mpr (by
    have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
    have hp := (firstLiveCollectionEvent_canonicalPrefixCell
      rate rewards C_star C_h u t z.val z.property).2.1
    change _ ≤ u.val - 1 ∧ u.val - 1 - _ < wholeFirstLiveLength rate rewards C_star C_h z.val
    omega)⟩

/-- All complete earlier cells retain their source-determined values. The last cell keeps the actual
fields before refresh and uses the path's initial set. -/
def joinedPast (z : EventSource rate rewards C_star C_h u t) (D : Path u t) :
    List (Cell p rate) :=
  let e := u.val - physicalStart rate z.val rewards C_star C_h
  (calendarPast
    rate rewards C_star C_h (z.val, ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection) t.val).take (e - 1) ++
    [liveCalendarCellWithNext rate rewards C_star C_h (triggerDate u)
      (triggerSource rate rewards C_star C_h u t z) (D 0)]

/-- Independent coordinates are fed to the existing sampler, using the original label-zero entry at every
collection date. -/
def explicitPath (z : EventSource rate rewards C_star C_h u t)
    (a0 : LabelZeroArray p) (v : Innovations u t) : Path u t :=
  let s := physicalStart rate z.val rewards C_star C_h
  sampledPath rate rewards C_star C_h (u.val - s) (t.val - s) z.val
    (firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property)
    (t.val - u.val) (by
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      dsimp [s]; omega)
    (v.1, fun i => (a0 ⟨u.val + i.val, by
      have hi := i.isLt
      have ht := t.isLt
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      omega⟩, v.2 i))

/-- Extract exactly one trigger and the later label-one coordinates. -/
def innovations (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    Innovations u t :=
  (a (triggerDate u, 1), fun i => a (⟨u.val + i.val, by
    have hi := i.isLt; have ht := t.isLt
    have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
    omega⟩, 1))

private theorem cell_eq_of_before_next {rate : RateInput p} (c d : Cell p rate)
    (hb : c.beforeRefreshFields = d.beforeRefreshFields) (hn : c.nextSlowSet = d.nextSlowSet) :
    c = d := by
  cases c
  cases d
  simp_all only [ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell.beforeRefreshFields,
    Prod.mk.injEq]

theorem collectionPath_explicit (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    collectionPath rate rewards C_star C_h u t z a =
      explicitPath rate rewards C_star C_h u t z (labelZero a)
        (innovations rate rewards C_star C_h u t z a) := by
  dsimp only [collectionPath, explicitPath]
  unfold sampledArrayPath
  congr 1
  unfold actualPrefixCoordinates innovations labelZero
  dsimp only
  apply Prod.ext <;> dsimp only
  · apply congrArg a
    apply Prod.ext
    · apply Fin.ext
      have h := actualCoordinateIndex_trigger rate rewards C_star C_h _ _ z.val
        (firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property)
        (t.val - u.val) (by
          have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
          omega)
      rw [h.1]
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      dsimp [triggerDate]; omega
    · rfl
  · funext i
    apply Prod.ext <;> dsimp only
    all_goals apply congrArg a; apply Prod.ext
    · apply Fin.ext
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      change _ + (u.val - _) + i.val = u.val + i.val
      omega
    · rfl
    · apply Fin.ext
      have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
      change _ + (u.val - _) + i.val = u.val + i.val
      omega
    · rfl

/-- Reconstruct the WHOLE actual calendar past from the same sampled path. -/
theorem joinedPast_actual (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    joinedPast rate rewards C_star C_h u t z (collectionPath rate rewards C_star C_h u t z a) =
      calendarPast rate rewards C_star C_h (z.val, a) t.val := by
  let s := physicalStart rate z.val rewards C_star C_h
  let e := u.val - s
  have hc := firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z.val z.property
  have hp := firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z.val a z.property
  have hp0 := firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z.val
    ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection z.property
  have he : (wholeFirstLiveWindow rate rewards C_star C_h z.val).length = e := hc.1.symm
  have hpos : 0 < e := hc.2.1
  obtain ⟨hlast, hseed⟩ := firstLiveCollectionEvent_last_next
    rate rewards C_star C_h u t z.val a z.property
  have hseed' : ((firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a))[e - 1]'(by
        rw [firstLiveChronologicalPrefix_length]
        change e - 1 < wholeFirstLiveLength rate rewards C_star C_h z.val
        rw [← hc.1]
        change e - 1 < e
        omega)).nextSlowSet =
      collectionPath rate rewards C_star C_h u t z a 0 := by
    simpa only [hp.1, collectionPath, sampledArrayPath, sampledPath_zero, actualPrefixCoordinates,
      actualCoordinateIndex,
      DeferredRefreshUniformEvaluator.coordinateIndex] using hseed
  have hi : (liveCalendarIndex rate rewards C_star C_h (triggerDate u)
      (triggerSource rate rewards C_star C_h u t z)).val = e - 1 := by
    change u.val - 1 - s = u.val - s - 1
    omega
  have hb := liveCalendarCellWithNext_beforeRefresh rate rewards C_star C_h (triggerDate u)
    (triggerSource rate rewards C_star C_h u t z) a
    (collectionPath rate rewards C_star C_h u t z a 0)
  simp only [liveCalendarEntry, hi] at hb
  have hcell := cell_eq_of_before_next _ _ hb.symm hseed'
  have hbound : e - 1 < (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a)).length := by
    simpa only [hp.1] using hlast
  change (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a))[e - 1]'hbound =
      liveCalendarCellWithNext rate rewards C_star C_h (triggerDate u)
        (triggerSource rate rewards C_star C_h u t z)
        (collectionPath rate rewards C_star C_h u t z a 0) at hcell
  have htake := firstLiveChronologicalPrefix_take_auxiliary_ext
    rate rewards C_star C_h z.val a ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
    (e - 1) (by rw [he]; omega)
  dsimp only [joinedPast]
  rw [hp0.1]
  change _ ++ [_] = _
  rw [← htake, ← hcell, List.take_append_getElem]
  have hlen : (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a)).length = e := by
    rw [firstLiveChronologicalPrefix_length]
    exact he
  rw [show e - 1 + 1 = e by omega, ← hlen, List.take_length, hp.1]

/-- The literal joint observable retains original z and every label-zero entry. -/
def actualJoin (w : EventSource rate rewards C_star C_h u t × AuxiliaryArray p) :
    Source p × (LabelZeroArray p × (List (Cell p rate) × Path u t)) :=
  (w.1.val, (labelZero w.2, (calendarPast rate rewards C_star C_h (w.1.val, w.2) t.val,
      collectionPath rate rewards C_star C_h u t w.1 w.2)))

/-- Explicit source/a0/shared-trigger/remaining-label-one construction. -/
def explicitJoin (z : EventSource rate rewards C_star C_h u t) (v : LabelZeroArray p × Innovations u t) :
    Source p × (LabelZeroArray p × (List (Cell p rate) × Path u t)) :=
  let D := explicitPath rate rewards C_star C_h u t z v.1 v.2
  (z.val, (v.1, (joinedPast rate rewards C_star C_h u t z D, D)))

theorem actualJoin_explicit (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    actualJoin rate rewards C_star C_h u t (z, a) = explicitJoin rate rewards C_star C_h u t z
        (labelZero a, innovations rate rewards C_star C_h u t z a) := by
  simp only [actualJoin, explicitJoin, ← collectionPath_explicit, joinedPast_actual]

/-- Joint Borelness is obtained on the countable physical-start sections; no path-measurability premise
is supplied. -/
theorem measurable_collectionPath :
    Measurable (fun w : EventSource rate rewards C_star C_h u t × AuxiliaryArray p =>
      collectionPath rate rewards C_star C_h u t w.1 w.2) := by
  let pieces (s : ℕ) : Set (EventSource rate rewards C_star C_h u t × AuxiliaryArray p) :=
    {w | physicalStart rate w.1.val rewards C_star C_h = s}
  have hs (s : ℕ) : MeasurableSet (pieces s) := measurableSet_eq_fun
      ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h).comp (measurable_subtype_coe.comp measurable_fst)) measurable_const
  have hm (s : ℕ) : Measurable (fun w : pieces s =>
      collectionPath rate rewards C_star C_h u t w.val.1 w.val.2) := by
    by_cases hsu : s ≤ u.val
    · by_cases hut : u.val ≤ t.val
      · have hn : t.val - u.val ≤ (t.val - s) - (u.val - s) := by omega
        let f : pieces s → PrefixSource
            rate rewards C_star C_h (u.val - s) (t.val - s) × AuxiliaryArray p :=
          fun w => (⟨w.val.1.val, by
            have h := firstLiveCollectionEvent_prefixMembership
              rate rewards C_star C_h u t w.val.1.val w.val.1.property
            have hstart : physicalStart rate w.val.1.val rewards C_star C_h = s := w.property
            simpa only [hstart] using h⟩, w.val.2)
        have hf : Measurable f :=
          ((measurable_subtype_coe.comp (measurable_fst.comp measurable_subtype_coe)).subtype_mk).prodMk
            (measurable_snd.comp measurable_subtype_coe)
        convert (measurable_sampledArrayPath_joint
          rate rewards C_star C_h (u.val - s) (t.val - s) (t.val - u.val) hn).comp hf using 1
        funext w
        have hstart : physicalStart rate w.val.1.val rewards C_star C_h = s := w.property
        dsimp only [Function.comp_def, f, collectionPath]
        congr 1 <;> omega
      · have : IsEmpty (pieces s) := ⟨fun w => hut
          (firstLiveCollectionEvent_dates rate rewards C_star C_h u t w.val.1.val w.val.1.property).2.1.le⟩
        exact measurable_of_empty _
    · have : IsEmpty (pieces s) := ⟨fun w => hsu (by
        have h := (firstLiveCollectionEvent_dates
          rate rewards C_star C_h u t w.val.1.val w.val.1.property).1
        rwa [w.property] at h)⟩
      exact measurable_of_empty _
  intro B hB
  have heq : (fun w : EventSource rate rewards C_star C_h u t × AuxiliaryArray p =>
      collectionPath rate rewards C_star C_h u t w.1 w.2) ⁻¹' B =
      ⋃ s : ℕ, Subtype.val '' ((fun w : pieces s =>
        collectionPath rate rewards C_star C_h u t w.val.1 w.val.2) ⁻¹' B) := by
    ext w
    constructor
    · intro hw
      exact Set.mem_iUnion.mpr ⟨_, ⟨⟨w, rfl⟩, hw, rfl⟩⟩
    · intro hw
      obtain ⟨s, v, hv, rfl⟩ := Set.mem_iUnion.mp hw
      exact hv
  rw [heq]
  exact MeasurableSet.iUnion (fun s => (hs s).subtype_image (hm s hB))

theorem measurable_actualJoin : Measurable (actualJoin rate rewards C_star C_h u t) := by
  have hsource := measurable_subtype_coe.comp
    (measurable_fst : Measurable (Prod.fst : EventSource rate rewards C_star C_h u t × AuxiliaryArray p → _))
  have hH := (ReferenceFirstLiveActualRefreshTestLaw.measurable_calendarPast
    rate rewards C_star C_h t).comp (hsource.prodMk measurable_snd)
  exact hsource.prodMk (((measurable_labelZero p).comp measurable_snd).prodMk
    (hH.prodMk (measurable_collectionPath rate rewards C_star C_h u t)))

/-- Restore just the used coordinates, retaining all a0 and filling unused label-one entries with the
same trigger. Their values are never consumed. -/
def assembleAuxiliary (v : LabelZeroArray p × Innovations u t) : AuxiliaryArray p :=
  fun q => if q.2 = 0 then v.1 q.1 else if h : u.val ≤ q.1.val ∧ q.1.val < t.val then
      v.2.2 ⟨q.1.val - u.val, by omega⟩ else v.2.1

theorem measurable_assembleAuxiliary : Measurable (assembleAuxiliary (p := p) u t) := by
  apply Measurable.of_eval
  intro q
  unfold assembleAuxiliary
  split_ifs
  · exact (measurable_pi_apply q.1).comp measurable_fst
  · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
  · exact measurable_fst.comp measurable_snd

theorem assembleAuxiliary_coordinates (z : EventSource rate rewards C_star C_h u t)
    (v : LabelZeroArray p × Innovations u t) :
    labelZero (assembleAuxiliary u t v) = v.1 ∧
      innovations rate rewards C_star C_h u t z (assembleAuxiliary u t v) = v.2 := by
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  have hp := (firstLiveCollectionEvent_canonicalPrefixCell
    rate rewards C_star C_h u t z.val z.property).2.1
  constructor
  · funext q
    simp only [labelZero, assembleAuxiliary, ite_true]
  · apply Prod.ext
    · dsimp only [innovations, assembleAuxiliary, triggerDate]
      rw [ite_eq_right (by decide), dite_eq_right (by omega)]
    · funext i
      have hi := i.isLt
      dsimp only [innovations, assembleAuxiliary]
      rw [ite_eq_right (by decide), dite_eq_left (by omega)]
      apply congrArg v.2.2
      apply Fin.ext
      simp only [Nat.add_sub_cancel_left]

theorem explicitJoin_assembled (z : EventSource rate rewards C_star C_h u t)
    (v : LabelZeroArray p × Innovations u t) :
    explicitJoin rate rewards C_star C_h u t z v =
      actualJoin rate rewards C_star C_h u t (z, assembleAuxiliary u t v) := by
  rw [actualJoin_explicit]
  have h := assembleAuxiliary_coordinates rate rewards C_star C_h u t z v
  rw [h.1, h.2]

theorem measurable_explicitJoin :
    Measurable (fun w : EventSource rate rewards C_star C_h u t ×
      (LabelZeroArray p × Innovations u t) => explicitJoin rate rewards C_star C_h u t w.1 w.2) := by
  have hm := (measurable_actualJoin rate rewards C_star C_h u t).comp
    (measurable_fst.prodMk ((measurable_assembleAuxiliary u t).comp measurable_snd))
  simpa only [Function.comp_def, ← explicitJoin_assembled] using hm

/-- The retained a0 has its original Pi law. -/
theorem labelZeroLaw_eq_pi : labelZeroLaw p =
    Measure.pi (fun _ : Fin p.T => ContinuousControlSlice.scalarLaw) := by
  change (Measure.pi (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
    ContinuousControlSlice.scalarLaw)).map (fun a : AuxiliaryArray p => fun i : Fin p.T => a (i, 0)) = _
  have hi := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => ContinuousControlSlice.scalarLaw)
    (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hm := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i : Fin p.T => (measurable_pi_apply (i, (0 : Fin 2))).aemeasurable)
    (hi.precomp (fun _ _ h => (Prod.mk.inj h).1))
  have hcoord (q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) :
      (Measure.pi (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
        ContinuousControlSlice.scalarLaw)).map (fun a => a q) = ContinuousControlSlice.scalarLaw :=
    (measurePreserving_eval (fun _ => ContinuousControlSlice.scalarLaw) q).map_eq
  simpa only [hcoord] using hm

/-- Full a0 and the single shared trigger/later residual coordinates have one product law. No pair
containing a retained seed is resampled. -/
theorem coordinates_measurePreserving (z : EventSource rate rewards C_star C_h u t) :
    MeasurePreserving (fun a : AuxiliaryArray p =>
      (labelZero a, innovations rate rewards C_star C_h u t z a))
      (auxiliaryUniformLaw p)
      ((labelZeroLaw p).prod (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw)))) := by
  classical
  let index : (Fin p.T ⊕ (Unit ⊕ Fin (t.val - u.val))) →
      ReferenceFirstCollectionAuxiliarySeeds.Coordinate p :=
    Sum.elim (fun q => (q, 0)) (Sum.elim (fun _ => (triggerDate u, 1)) (fun i => (⟨u.val + i.val, by
        have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
        have hi := i.isLt; have ht := t.isLt; omega⟩, 1)))
  have hd := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  have hp := (firstLiveCollectionEvent_canonicalPrefixCell
    rate rewards C_star C_h u t z.val z.property).2.1
  have hinj : Function.Injective index := by
    intro i j hij
    have hv := congrArg (fun q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => q.1.val) hij
    have hl := congrArg (fun q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => q.2) hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Fin.ext hv)
      | inr j => cases j <;> cases hl
    | inr i =>
      cases j with
      | inl j => cases i <;> cases hl
      | inr j =>
        cases i with
        | inl i =>
          cases j with
          | inl j => rfl
          | inr j => dsimp [index, triggerDate] at hv; omega
        | inr i =>
          cases j with
          | inl j => dsimp [index, triggerDate] at hv; omega
          | inr j =>
            apply congrArg (fun k : Fin (t.val - u.val) => Sum.inr (Sum.inr k))
            exact Fin.ext (by dsimp [index] at hv; omega)
  have hi := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => ContinuousControlSlice.scalarLaw)
    (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hselect : MeasurePreserving (fun a : AuxiliaryArray p => fun i => a (index i))
      (auxiliaryUniformLaw p)
      (Measure.pi (fun _ : Fin p.T ⊕ (Unit ⊕ Fin (t.val - u.val)) =>
        ContinuousControlSlice.scalarLaw)) := by
    refine ⟨Measurable.of_eval (fun _ => measurable_pi_apply _), ?_⟩
    have hm := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun i => (measurable_pi_apply (index i)).aemeasurable) (hi.precomp hinj)
    have hcoord (q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) :
        (Measure.pi (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
          ContinuousControlSlice.scalarLaw)).map (fun a => a q) = ContinuousControlSlice.scalarLaw :=
      (measurePreserving_eval (fun _ => ContinuousControlSlice.scalarLaw) q).map_eq
    simpa only [auxiliaryUniformLaw, hcoord] using hm
  have houter := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin p.T ⊕ (Unit ⊕ Fin (t.val - u.val)) => ContinuousControlSlice.scalarLaw)
  have hinner := measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw)
  have hunit := measurePreserving_piUnique (fun _ : Unit => ContinuousControlSlice.scalarLaw)
  have h := ((MeasurePreserving.id (Measure.pi
      (fun _ : Fin p.T => ContinuousControlSlice.scalarLaw))).prod
        ((hunit.prod (MeasurePreserving.id _)).comp hinner)).comp (houter.comp hselect)
  rw [labelZeroLaw_eq_pi]
  convert h using 1
  rfl

instance eventSourceLaw_finite : IsFiniteMeasure (eventSourceLaw rate rewards C_star C_h u t) := by
  unfold eventSourceLaw
  infer_instance

/-- Every bounded Borel joint test is integrable under the original restricted product law, including
null and absent cells. -/
theorem integrable_actualJoin_test
    (Phi : Source p × (LabelZeroArray p × (List (Cell p rate) × Path u t)) → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ v, ‖Phi v‖ ≤ B) :
    Integrable (fun w => Phi (actualJoin rate rewards C_star C_h u t w))
      ((eventSourceLaw rate rewards C_star C_h u t).prod (auxiliaryUniformLaw p)) :=
  Integrable.of_bound (hPhi.comp (measurable_actualJoin rate rewards C_star C_h u t)).aestronglyMeasurable
    B (Filter.Eventually.of_forall (fun _ => hB _))

/-- The explicit right-hand joint test is integrable on the full product. -/
theorem integrable_explicitJoin_test
    (Phi : Source p × (LabelZeroArray p × (List (Cell p rate) × Path u t)) → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ v, ‖Phi v‖ ≤ B) :
    Integrable (fun w => Phi (explicitJoin rate rewards C_star C_h u t w.1 w.2))
      ((eventSourceLaw rate rewards C_star C_h u t).prod
        ((labelZeroLaw p).prod (ContinuousControlSlice.scalarLaw.prod
          (Measure.pi (fun _ : Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw))))) :=
  Integrable.of_bound
    (hPhi.comp (measurable_explicitJoin rate rewards C_star C_h u t)).aestronglyMeasurable
    B (Filter.Eventually.of_forall (fun _ => hB _))

/-- The unnormalized joint identity retains original z, ALL a0, the WHOLE first-LIVE history and the SAME
collection path. The trigger x is used once for both the history's last next set and D(0). -/
theorem bounded_joint_test (Phi : Source p × (LabelZeroArray p × (List (Cell p rate) × Path u t)) → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ v, ‖Phi v‖ ≤ B) :
    ∫ w, Phi (actualJoin rate rewards C_star C_h u t w)
      ∂((eventSourceLaw rate rewards C_star C_h u t).prod (auxiliaryUniformLaw p)) =
    ∫ z, ∫ a0, ∫ x, ∫ y, Phi (explicitJoin rate rewards C_star C_h u t z (a0, (x, y)))
      ∂(Measure.pi (fun _ : Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw))
      ∂ContinuousControlSlice.scalarLaw ∂(labelZeroLaw p)
      ∂(eventSourceLaw rate rewards C_star C_h u t) := by
  rw [integral_prod _ (integrable_actualJoin_test rate rewards C_star C_h u t Phi hPhi B hB)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  let F := fun v : LabelZeroArray p × Innovations u t =>
    Phi (explicitJoin rate rewards C_star C_h u t z v)
  have hF : Measurable F := hPhi.comp
    ((measurable_explicitJoin rate rewards C_star C_h u t).comp (measurable_const.prodMk measurable_id))
  have hi : Integrable F ((labelZeroLaw p).prod (ContinuousControlSlice.scalarLaw.prod
      (Measure.pi (fun _ : Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw)))) :=
    Integrable.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall (fun _ => hB _))
  have hc := coordinates_measurePreserving rate rewards C_star C_h u t z
  calc
    _ = ∫ v, F v ∂((labelZeroLaw p).prod (ContinuousControlSlice.scalarLaw.prod
        (Measure.pi (fun _ : Fin (t.val - u.val) => ContinuousControlSlice.scalarLaw)))) := by
      rw [← hc.map_eq, integral_map hc.measurable.aemeasurable hF.aestronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => congrArg Phi (actualJoin_explicit
        rate rewards C_star C_h u t z a))
    _ = _ := by
      rw [integral_prod _ hi]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a0
      have hsection : Measurable (fun v : Innovations u t => F (a0, v)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      exact integral_prod _ (Integrable.of_bound hsection.aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun _ => hB _)))

end Joint

end Bandits.Support.ReferenceFirstLiveCollectionPathJoin

end
