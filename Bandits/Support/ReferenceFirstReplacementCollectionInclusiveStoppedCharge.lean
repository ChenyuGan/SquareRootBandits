/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay
public import Bandits.Support.ReferenceFirstCorrectedPhysicalQueueSiteAttribution
public import Bandits.Support.ReferenceFirstReplacementCollectionGlobalDecoderCharge

import Mathlib.Tactic

/-!
# Inclusive stopped charge for the first replacement collection

The stop test below uses the complete original launch based strict past and
retains its detecting update.  The selected collection remains the actual
first replacement list from the global decoder charge producer.

The third accepted direct dependency is
`Bandits.Support.ReferenceCompleteInstallationOutsideCalendarReplay`, SHA-256
`1fd7dac9326d7d01712adf4bd22325ff8a182e76fd69c7338cfe6992af29fa32`.
Its current dependency admission is recorded at
`private-audit-archive/turn-00983-inclusive-dependency-admission.json`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionInclusiveStoppedCharge

variable {p : Parameters}

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "R" z:max =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "K" z:max =>
  ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z

local notation "s₀" z:max =>
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "v₀" z:max =>
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
local notation "c₀" z:max =>
  v₀ z + 1 + List.length (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail (R z) (v₀ z))

open ReferenceCollectionSegmentExtraction


private theorem laterChosen_not_continuing
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    continuing r = false := by
  have hc : choice r.input = none := by
    unfold choice
    split
    · rfl
    · unfold ReferenceCollectionPhaseHistory.laterChosen at hr
      cases hd : (prepare r.input).coordinator with
      | collection _ _ _ _ outcome => cases outcome <;> simp_all [choiceOfCut]
      | first _ => simp_all
      | live _ _ _ outcome => cases outcome <;> simp_all
      | dagger => simp_all
      | invalidCollectionCutoff => simp_all
  simp only [continuing, extractRound, hc, Option.bind_none]

private theorem takeWhile_boundary_false {α : Type*} (f : α → Bool)
    (xs : List α) (r : α) (hr : xs[(xs.takeWhile f).length]? = some r) :
    f r = false := by
  induction xs with
  | nil => simp at hr
  | cons x xs ih =>
    cases hx : f x with
    | false =>
      simp only [List.takeWhile_cons, hx, Bool.false_eq_true, ↓reduceIte,
        List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hr
      exact hr ▸ hx
    | true =>
      apply ih
      simpa only [List.takeWhile_cons, hx, ↓reduceIte, List.length_cons,
        List.getElem?_cons_succ] using hr

private theorem takeWhile_same_boundary {α : Type*} (f g : α → Bool)
    (xs : List α)
    (hleft : (xs.takeWhile f).takeWhile g = xs.takeWhile f)
    (hstop : ∀ r, xs[(xs.takeWhile f).length]? = some r → g r = false) :
    xs.takeWhile g = xs.takeWhile f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | false =>
      have hg := hstop x (by simp [hf])
      simp [hf, hg]
    | true =>
      have hg : g x = true := by
        cases hg : g x with
        | true => rfl
        | false => simp [hf, hg] at hleft
      have htail : (xs.takeWhile f).takeWhile g = xs.takeWhile f := by
        simpa only [List.takeWhile_cons, hf, hg, ↓reduceIte, List.cons.injEq,
          true_and] using hleft
      have hstop' : ∀ r, xs[(xs.takeWhile f).length]? = some r → g r = false := by
        intro r hr
        apply hstop r
        simpa only [List.takeWhile_cons, hf, ↓reduceIte, List.length_cons,
          List.getElem?_cons_succ] using hr
      simpa only [List.takeWhile_cons, hf, hg, ↓reduceIte] using
        congrArg (List.cons x) (ih htail hstop')

private theorem actual_segment_records_eq_raw
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hc : (R z)[c₀ z]? = some cut)
    (hk : K z = cut :: ((R z).drop (c₀ z + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input))
    (stream seg : Segment rate)
    (hstream : segment (K z) = some stream) (hrecords : stream.records = K z)
    (hseg : segmentAt (R z) (c₀ z) = some seg) :
    seg.records = K z ∧ seg.remaining = (R z).drop (c₀ z + (K z).length) ∧
      seg.context = stream.context ∧ seg.entry = cut := by
  have hdrop : (R z).drop (c₀ z) = cut :: (R z).drop (c₀ z + 1) := by
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hc
    simpa only [he] using List.drop_eq_getElem_cons hi
  have hs := (segmentAt_branch _ _ seg hseg).1
  rw [hdrop] at hs
  rw [hk] at hstream hrecords
  unfold ReferenceCollectionSegmentExtraction.segment at hstream hs
  cases hchoice : choice cut.input with
  | none => simp only [hchoice, Option.map_none, reduceCtorEq] at hstream
  | some choice₀ =>
    simp only [hchoice, Option.map_some] at hstream hs
    split at hstream
    next hex =>
      cases Option.some.inj hstream
      have htail :
          ((((R z).drop (c₀ z + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).takeWhile continuing) =
          ((R z).drop (c₀ z + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
        exact (List.cons.inj hrecords).2
      have hfull := takeWhile_same_boundary
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) continuing
        ((R z).drop (c₀ z + 1)) htail (by
          intro r hr
          have hf := takeWhile_boundary_false
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            ((R z).drop (c₀ z + 1)) r hr
          exact laterChosen_not_continuing rate r (by simpa using hf))
      simp only [hex, ↓reduceIte] at hs
      cases Option.some.inj hs
      have hrec :
          cut :: List.takeWhile continuing ((R z).drop (c₀ z + 1)) = K z := by
        rw [hfull, hk]
      refine ⟨hrec, ?_, rfl, rfl⟩
      have hpart := segmentAt_partition (R z) (c₀ z) _ hseg
      change (cut :: List.takeWhile continuing ((R z).drop (c₀ z + 1))) ++
        List.dropWhile continuing ((R z).drop (c₀ z + 1)) = _ at hpart
      rw [hrec] at hpart
      have hd := congrArg (List.drop (K z).length) hpart
      simpa only [List.drop_left, List.drop_drop, Nat.add_comm] using hd

    next hex =>
      cases Option.some.inj hstream
      simp only [reduceCtorEq] at hrecords

private theorem reached_raw_segment
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (birth cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : (R z)[v₀ z]? = some birth) (hborn : (ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth).isSome = true)
    (hc : (R z)[c₀ z]? = some cut) (hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true) :
    ∃ stream : Segment rate, segment (K z) = some stream ∧ stream.records = K z := by
  have h := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_reached_execution
    rate rewards C_star C_h control0 z
  change (match (R z)[v₀ z]? with
    | none => True
    | some _ => _) at h
  rw [hb] at h
  cases hd : birth.output.preparation.coordinator with
  | collection _ _ _ _ outcome =>
    cases outcome <;> simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hd, Option.isSome_none,
      Bool.false_eq_true] at hborn
    next =>
      simp only [hd] at h
      change (match (R z)[c₀ z]? with | none => True | some _ => _) at h
      rw [hc] at h
      cases he : cut.output.preparation.coordinator with
      | live _ _ _ outcome =>
        cases outcome <;> simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, he, Bool.false_eq_true] at hcut
        next =>
          simp only [he] at h
          obtain ⟨_, stream, _, hs, hr, _⟩ := h
          exact ⟨stream, hs, hr⟩
      | first _ => simp [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, he] at hcut
      | collection _ _ _ _ _ => simp [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, he] at hcut
      | dagger => simp [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, he] at hcut
      | invalidCollectionCutoff => simp [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, he] at hcut
  | first _ => simp [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hd] at hborn
  | live _ _ _ _ => simp [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hd] at hborn
  | dagger => simp [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hd] at hborn
  | invalidCollectionCutoff => simp [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hd] at hborn

private theorem continuingPrefix_eq_tail
    (z : BootstrapPrivateRoundStreams.SourceInput p) (b : ℕ) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1) =
      ReferenceFirstReplacementLiveFollowerPrefix.continuingTail (R z) b := by
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
  congr 1
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | collection _ _ _ _ _ => rfl
  | dagger => rfl
  | invalidCollectionCutoff => rfl

/-- Complete launch-based numerical words for the literal first replacement
collection. The only branch condition is that this actual collection is
nonempty. All coverage, initialization and queue records are produced from
the original source, including a renewed replacement birth. -/
theorem complete_original_collection_words
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ (Npre Dword : List (RecordedQueueRun.RoundInput p.K))
      (seg : Segment rate) (I : Initializer p),
      Npre.length = c₀ z ∧ Dword.length = (K z).length ∧
      segmentAt (R z) (c₀ z) = some seg ∧ seg.records = K z ∧
      seg.remaining = (R z).drop (c₀ z + (K z).length) ∧
      seg.context.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
      I.cutoff = s₀ z + c₀ z + 1 ∧
      ((R z).take (c₀ z)).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        Npre.map some ∧
      (K z).map (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout (s₀ z)) =
        Dword.map some ∧
      (∀ a : Fin p.K,
        CollectionKnownQueueContinuation.inputQueueRecords seg.context.preLedger a seg.inputs =
          (K z).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) ∧
        (K z).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
          ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a Dword) ∧
      (∀ h, h ≤ c₀ z →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s₀ z + h) z = some (Npre.take h)) ∧
      (∀ j, j ≤ (K z).length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s₀ z + c₀ z + j) z =
            some (Npre ++ Dword.take j)) ∧
      ((R z).take (c₀ z + (K z).length)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = (Npre ++ Dword).map some ∧
      (∀ cell ∈ Npre ++ Dword, cell.enabled = false → cell.recordedArm = none ∧
        ∀ a, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a = 0) ∧
      I.sigma = s₀ z + v₀ z + 1 ∧
      ∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        (R z)[v₀ z]? = some birth ∧ birth.input.time.val = s₀ z + v₀ z := by
  have hraw := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_eq
    rate rewards C_star C_h z
  change K z = (match (R z)[v₀ z]? with | none => [] | some _ => _) at hraw
  cases hb : (R z)[v₀ z]? with
  | none => simp only [hb] at hraw; exact False.elim (hne hraw)
  | some birth =>
    simp only [hb] at hraw
    by_cases hborn : (ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth).isSome = true
    · simp only [hborn, ↓reduceIte] at hraw
      change K z = (match (R z)[c₀ z]? with | none => [] | some _ => _) at hraw
      cases hc : (R z)[c₀ z]? with
      | none => simp only [hc] at hraw; exact False.elim (hne hraw)
      | some cut =>
        simp only [hc] at hraw
        by_cases hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true
        · simp only [hcut, ↓reduceIte] at hraw
          have hv := (List.getElem?_eq_some_iff.mp hb).1
          have hcLt := (List.getElem?_eq_some_iff.mp hc).1
          let b : Fin (R z).length := ⟨v₀ z, hv⟩
          have hlater : ReferenceCollectionPhaseHistory.laterChosen (R z)[b.val].input = true := by
            rw [(List.getElem?_eq_some_iff.mp hb).2]
            exact (ReferenceFirstReplacementCollectionPendingFoundation.birthPayload_isSome birth).symm.trans hborn
          obtain ⟨P0, rb, qb, beta, cell, native, hPlen, hPslots, hPprefix,
            _hinit, _hpost, _hbirth, _hstrict, _hbase, _hcell, _hnative,
            _hpay, _henabled, _hPbirth, _hbirthSlots, _hseed, _hdown, hrest⟩ :=
            ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
              rate rewards C_star C_h z b hlater
          dsimp only at hrest
          rcases hrest with hterminal | ⟨k, C, hk, _hstate, hcont⟩
          · have hvc : v₀ z + 1 ≤ c₀ z := Nat.le_add_right _ _
            change v₀ z + 1 = (R z).length at hterminal
            omega
          · have hW : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z k.val =
                ReferenceFirstReplacementLiveFollowerPrefix.continuingTail (R z) (v₀ z) := by
              rw [hk]
              exact continuingPrefix_eq_tail rate rewards C_star C_h z (v₀ z)
            rw [hW, hk] at hcont
            rcases hcont with ⟨_hClen, _hCmap, _htimes, _heR, _heT, hHlen,
              hHprefix, hHslots, _hHdisabled, _hcounts, rE, qE, _hrE,
              _hlast, _hincoming, _hvalues, halt⟩
            change (P0 ++ [cell] ++ C).length = c₀ z at hHlen
            change c₀ z = (R z).length ∨ _ at halt
            rcases halt with hterminal | ⟨he, seg, I, l0, Dword, hseg, _hentry,
              _hpayload, hl0, hI, _hIdef, hIstart, _hassignment, _hsigma,
              hcutoff, _hfirstCutoff, _hfreeze, _hbeta, _hcutChosen, _hcons,
              _hpartition, _hexit, _hchecked, hDlen, hDmap, hphysical, hE⟩
            · omega
            · change segmentAt (R z) (c₀ z) = some seg at hseg
              obtain ⟨stream, hstream, hstreamRecords⟩ :=
                reached_raw_segment rate rewards C_star C_h control0 z birth cut hb hborn hc hcut
              obtain ⟨hrecords, hremaining, _hcontext, _hcutEntry⟩ :=
                actual_segment_records_eq_raw rate rewards C_star C_h z cut hc hraw
                  stream seg hstream hstreamRecords hseg
              rcases hE with ⟨_hElen, _hEtake, _hvR, _hvT, _hRtake, hEprefix,
                hEslots, hEdisabled, _hledgerCounts, _hfinal⟩
              let H := P0 ++ [cell] ++ C
              change H.length = c₀ z at hHlen
              change (∀ h, v₀ z + 1 ≤ h → h ≤ c₀ z →
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s₀ z + h) z = some (H.take h)) at hHprefix
              change (∀ h, v₀ z + 1 ≤ h → h ≤ c₀ z + seg.records.length →
                ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                  rate rewards C_star C_h (s₀ z + h) z =
                    some ((H ++ Dword).take h)) at hEprefix
              have htakeP (h : ℕ) (hh : h ≤ v₀ z) : H.take h = P0.take h := by
                dsimp only [H]
                rw [List.take_append_of_le_length (by
                  simp only [List.length_append, List.length_singleton]
                  change P0.length = v₀ z at hPlen
                  omega), List.take_append_of_le_length (by
                  change P0.length = v₀ z at hPlen
                  omega)]
              have hprefix (h : ℕ) (hh : h ≤ c₀ z) :
                  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                    rate rewards C_star C_h (s₀ z + h) z = some (H.take h) := by
                by_cases hvh : h ≤ v₀ z
                · rw [htakeP h hvh]
                  exact hPprefix h hvh
                · exact hHprefix h (by omega) hh
              refine ⟨H, Dword, seg, I, hHlen, ?_, hseg, hrecords, hremaining,
                hI, ?_, hcutoff, hHslots, ?_, ?_, hprefix, ?_, ?_, hEdisabled, ?_, ?_⟩
              · exact hDlen.trans (congrArg List.length hrecords)
              · rw [hl0]; exact hIstart
              · rwa [hrecords] at hDmap
              · intro a
                simpa only [hl0, hrecords] using hphysical a
              · intro j hj
                have hp := hEprefix (c₀ z + j) (by omega) (by rw [hrecords]; omega)
                have htake : (H ++ Dword).take (c₀ z + j) = H ++ Dword.take j := by
                  rw [List.take_append, List.take_of_length_le (by omega), hHlen,
                    Nat.add_sub_cancel_left]
                rw [← Nat.add_assoc] at hp
                simpa only [htake] using hp
              · simpa only [hrecords] using hEslots
              · have hbSigma : rb.payload.sigma.val = (R z)[b.val].input.time.val := by
                  unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at _hbirth
                  split at _hbirth <;> first | exact _hbirth.2 | contradiction
                rw [(List.getElem?_eq_some_iff.mp hb).2] at hbSigma
                rw [_hsigma, hbSigma]
                exact congrArg (fun n => n + 1)
                  (ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
                    rate z rewards C_star C_h (v₀ z) birth hb)
              · exact ⟨birth, rfl,
                  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
                    rate z rewards C_star C_h (v₀ z) birth hb⟩
        · simp only [hcut, Bool.false_eq_true, ↓reduceIte] at hraw
          exact False.elim (hne hraw)
    · simp only [hborn] at hraw
      exact False.elim (hne hraw)

private theorem original_record_time
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (R z).length) :
    (R z)[i.val].input.time.val = s₀ z + i.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hi : i.val < p.T - s₀ z := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact i.isLt
  have hget := congrArg (fun values : List ℕ => values[i.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hi, Nat.one_mul] at hget
  exact Option.some.inj hget

/-- One complete original calendar word through all of K, with every source
slot and every launch prefix retained. The rows, selected J, reward table and
dates are the original physical inputs. -/
theorem complete_original_calendar
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧ E.length ≤ (R z).length ∧
      (∀ h, h ≤ E.length → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h)) ∧
      (∀ i : Fin E.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          (R z)[i.val]? = some r ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some E[i.val] ∧
          r.input.rows = z.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          r.input.rewards = rewards ∧ r.input.time.val = s₀ z + i.val) ∧
      ∀ j : Fin (K z).length, (R z)[c₀ z + j.val]? = some (K z)[j.val] ∧
        (K z)[j.val].input.time.val = s₀ z + c₀ z + j.val := by
  obtain ⟨Npre, Dword, seg, I, hNlen, hDlen, hseg, hrecords, _hremaining,
    _hI, _hIstart, _hcutoff, _hNslots, _hDslots, _hphysical, hpre, hcol,
    hslots, _hdisabled⟩ := complete_original_collection_words
      rate rewards C_star C_h control0 z hne
  let E := Npre ++ Dword
  have hlen : E.length = c₀ z + (K z).length := by
    simp only [E, List.length_append, hNlen, hDlen]
  have hslotsLen := congrArg List.length hslots
  simp only [List.length_map, List.length_take, List.length_append, hNlen, hDlen] at hslotsLen
  have hbound : E.length ≤ (R z).length := by omega
  have hprefix (h : ℕ) (hh : h ≤ E.length) :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h) := by
    by_cases hc : h ≤ c₀ z
    · have ht : E.take h = Npre.take h :=
        List.take_append_of_le_length (by omega)
      rw [ht]
      exact hpre h hc
    · have hj : h - c₀ z ≤ (K z).length := by omega
      have hp := hcol (h - c₀ z) hj
      have hdate : s₀ z + c₀ z + (h - c₀ z) = s₀ z + h := by omega
      have ht : E.take h = Npre ++ Dword.take (h - c₀ z) := by
        rw [show E = Npre ++ Dword from rfl, List.take_append,
          List.take_of_length_le (by omega), hNlen]
      rw [ht]
      rw [hdate] at hp
      exact hp
  refine ⟨E, hlen, hbound, hprefix, ?_, ?_⟩
  · intro i
    have hiR : i.val < (R z).length := lt_of_lt_of_le i.isLt hbound
    let ri : Fin (R z).length := ⟨i.val, hiR⟩
    have hsource := ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_inputs
      rate rewards C_star C_h z ri
    have hi : i.val < c₀ z + (K z).length := by omega
    have he := congrArg (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[i.val]?) hslots
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt hi,
      List.getElem?_eq_getElem hiR, List.getElem?_eq_getElem i.isLt,
      Option.map_some, Option.map_some] at he
    refine ⟨(R z)[i.val], List.getElem?_eq_getElem hiR,
      Option.some.inj he, hsource.1, hsource.2.1, hsource.2.2,
      original_record_time rate rewards C_star C_h z ri⟩
  · intro j
    have hpart := segmentAt_partition (R z) (c₀ z) seg hseg
    rw [hrecords] at hpart
    have hget := congrArg (fun xs => xs[j.val]?) hpart
    rw [List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt,
      List.getElem?_drop] at hget
    have hjR : c₀ z + j.val < (R z).length := by omega
    have htime := original_record_time rate rewards C_star C_h z ⟨c₀ z + j.val, hjR⟩
    have hr : (R z)[c₀ z + j.val] = (K z)[j.val] :=
      (List.getElem?_eq_some_iff.mp hget.symm).2
    refine ⟨hget.symm, ?_⟩
    rw [hr, ← Nat.add_assoc] at htime
    exact htime

/-- Every cell of the produced original word has its literal source
meaning. LIVE uses the actual selected assignment, all prepared follower
statuses and whole row, so unoccupied assigned arms are evaluated even when
unread. COLLECTION uses the actual coordinator recorder on every arm. -/
theorem complete_original_source_cells
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧
      (∀ h, h ≤ E.length → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h)) ∧
      ∀ i : Fin E.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          (R z)[i.val]? = some r ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some E[i.val] ∧
          r.input.rows = z.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          r.input.rewards = rewards ∧ r.input.time.val = s₀ z + i.val ∧
          ((∃ (selected : Selection r.input)
              (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
              r.output.preparation.coordinator.selection = some selected ∧
              E[i.val] = ReferenceFirstWindowNumericalStream.sourceCell r
                selected.view.payload selected.view.pendingAtChoice
                (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
                selected.view.complementWeights selected.view.cutoff
                (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
              E[i.val].enabled = true ∧ E[i.val].rate = selected.view.payload.rate ∧
              E[i.val].reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
              ∀ a, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) E[i.val] a =
                if ReferenceFirstWindowNumericalStream.sourceArm r selected.view.payload
                    selected.view.pendingAtChoice
                    (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
                    selected.view.complementWeights selected.view.cutoff
                    (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) = some a then
                  Nat.floor ((rate.n : ℝ) * (((rewards r.input.time a).val : ℝ) / (D p : ℝ)) /
                    selected.view.payload.rate a) else 0) ∨
            ∃ (payload : Payload rate) (ledger : Ledger rate)
              (started : CoordinatorPhaseClock.StartRoundResult p)
              (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
              (out : CoordinatorRecordingOperation.Output p),
              ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
                some ⟨payload, ledger, started, weights⟩ ∧
              CoordinatorRecorderComplementBridge.run
                (collectionRecordingInput r.output.preparation payload started weights) = some out ∧
              r.coordinatorDiagnostics.recording = some out ∧ out.gateArm = E[i.val].recordedArm ∧
              E[i.val].enabled = collectionEnabled ledger r.input.time ∧
              E[i.val].rate = payload.rate ∧
              E[i.val].reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
              ∀ a, CoordinatorCollectionLedger.localArrival
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) E[i.val] a) := by
  obtain ⟨E, hlen, _hbound, hprefix, hsource, _hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  refine ⟨E, hlen, hprefix, ?_⟩
  intro i
  obtain ⟨r, hr, hcell, hrows, hJ, hreward, htime⟩ := hsource i
  refine ⟨r, hr, hcell, hrows, hJ, hreward, htime, ?_⟩
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some cell =>
    have heq : cell = E[i.val] := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl,
        Option.or, Option.some.injEq] using hcell
    subst cell
    obtain ⟨selected, ho, hs, _hbase, _hlive, hinput⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 r E[i.val] hl
    refine Or.inl ⟨selected, ho, hs, hinput, ?_, ?_, ?_, ?_⟩
    · rw [hinput]; rfl
    · rw [hinput]; rfl
    · rw [hinput]
      change (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) = _
      rw [hreward]
    · intro a
      rw [hinput, ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival, hreward]
  | none =>
    have hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some E[i.val] := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.or] using hcell
    obtain ⟨payload, ledger, started, weights, out, hcall, _hdiag, hrun,
      henabled, _hfreeze, hrate, hrewards, hrecording, hgate, harrival⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r E[i.val] hc
    refine Or.inr ⟨payload, ledger, started, weights, out, hcall, hrun,
      hrecording, hgate, henabled, hrate, ?_, harrival⟩
    rwa [hreward] at hrewards

/-- The initial LIVE part of the same complete word retains the accepted
physical source-cell certificates, rather than replacing them by a new queue
seed or by acquired coordinator stores. -/
theorem complete_initial_live_source_cells
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧
      (∀ h, h ≤ E.length → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h)) ∧
      ∀ i : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)).length,
        ∃ (hi : i.val < E.length)
          (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
          (R z)[i.val]? = some r ∧ native.input = E[i.val] := by
  obtain ⟨E, hlen, _hbound, hprefix, hsource, _hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hl
    exact hne (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_of_no_launch
      rate rewards C_star C_h z hl)
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp (Option.ne_none_iff_isSome.mp hlaunch)
  let count := p.T - s₀ z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hs
  have hW : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z) := by
    unfold W ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc]
  have hp : W <+: R z := by
    rw [hW]
    exact List.takeWhile_prefix _
  obtain ⟨_seed, _hstart, hlive⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hc
  refine ⟨E, hlen, hprefix, ?_⟩
  intro i
  have hwv : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)).length ≤ v₀ z :=
    Nat.le_add_right _ _
  have hvc : v₀ z + 1 ≤ c₀ z := Nat.le_add_right _ _
  have hiE : i.val < E.length := by omega
  let j : Fin W.length := ⟨i.val, by rw [hW]; exact i.isLt⟩
  let record := W[j.val]
  let native := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z rewards C_star C_h hc count hs j
  obtain ⟨hiR, _hdate, _hnum, _hnumNone, _harrival, _harrivalNone, hread, _hnone, _⟩ := hlive j
  have hlookup : (R z)[i.val]? = some record := by
    rw [List.getElem?_eq_getElem hiR]
    exact congrArg some (hp.getElem j.isLt).symm
  obtain ⟨r, hr, hcell, _⟩ := hsource ⟨i.val, hiE⟩
  have heqR : r = record := Option.some.inj (hr.symm.trans hlookup)
  subst r
  have hnread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some native.input := by
    rw [← ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
      rate z rewards C_star C_h hc count hs j]
    exact hread
  have hncell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some native.input := by
    unfold ReferenceFirstCollectionCurrentRetainedGate.cell0
    rw [hnread]
    rfl
  exact ⟨hiE, record, native, hlookup, Option.some.inj (hncell.symm.trans hcell)⟩

/-- On every actual later-LIVE readout of the produced whole word, the
all-arm partition is the accepted physical one. Unoccupied followers contribute
the true-assignment saved-record calculation even when no queue is stored. -/
theorem complete_later_live_all_arm_source
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧ ∃ hbound : E.length ≤ (R z).length,
      (∀ h, h ≤ E.length → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h)) ∧
      ∀ i : Fin E.length,
        let r := (R z)[i.val]'(lt_of_lt_of_le i.isLt hbound)
        ReferenceLaterLiveNumericalReadout.laterLiveReadout (s₀ z) r = some E[i.val] →
        ∀ a : Fin p.K,
          ∃ native : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
            native.input = E[i.val] ∧
            ((a ∉ native.selected.view.payload.slowSet.1 ∧
              ∃ out, r.output.coordinator.recording = some out ∧
                ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                  (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                  some (RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) E[i.val] a)) ∨
              ∃ follower : Fin (p.m - 1),
                native.selected.view.payload.assignment.assigned follower = a ∧
                (∀ other, native.selected.view.payload.assignment.assigned other = a → other = follower) ∧
                (if (native.states follower).status = .unoccupied then
                  ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                    r native.selected.view.payload follower
                else ActiveFollowerQueueOperation.rawArrival rate.eta follower r.input.row r.input.time
                  (native.selected.view.payload.downRecord follower)
                  (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m follower)).2) =
                  RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) E[i.val] a) := by
  obtain ⟨E, hlen, hbound, hprefix, _hsource, _hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  refine ⟨E, hlen, hbound, hprefix, ?_⟩
  intro i
  dsimp only
  intro hread a
  obtain ⟨native, hinput, _howner, hpartition⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
      rate rewards C_star C_h z ⟨i.val, lt_of_lt_of_le i.isLt hbound⟩ E[i.val] hread a
  exact ⟨native, hinput, hpartition⟩

/-- The actual queue word on the original launch to date strict past. -/
def originalPrefixInputs (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h t.val z

/-- A date of the literal first replacement collection retained through the
strict past decoder and all arm calendar queue tests. -/
def stoppedDate (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) : Prop :=
  ∃ r ∈ K z, r.input.time = t ∧
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ∧
    ∃ N, originalPrefixInputs rate rewards C_star C_h t z = some N ∧
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N

/-- The finite charge on exactly the literal stopped dates. -/
def Cstop (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t : Fin p.T, if stoppedDate rate rewards C_star C_h z t then
    (min p.m (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t) : ℝ)
    else 0

private theorem map_take_eq_range_getElemBind {α β : Type*}
    (xs : List α) (f : α → Option β) (n : ℕ) (hn : n ≤ xs.length) :
    (xs.take n).map f = (List.range n).map (fun k => (xs[k]?).bind f) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hn]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa using hi₂
    have hiXs : i < xs.length := lt_of_lt_of_le hi hn
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    rw [List.getElem?_eq_getElem hiXs]
    rfl

/-- The public stopped gate and the numerical prefix use the same original
strict past; neither restarts the queue at the replacement birth. -/
theorem originalPrefixInputs_eq_pastCells?
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    originalPrefixInputs rate rewards C_star C_h t z =
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hlen : t.val - s ≤ records.length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  have hs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z = s := rfl
  unfold originalPrefixInputs
  unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    ReferenceFirstCollectionCurrentRetainedGate.pastCells?
    ReferenceFirstCollectionCurrentRetainedGate.pastSlots
  rw [hs]
  by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · simp only [ite_eq_left hlaunch]
    congr 1
    change (records.take (t.val - s)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
      (List.range (t.val - s)).map (fun k =>
        (records[k]?).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))
    exact map_take_eq_range_getElemBind records
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) (t.val - s) hlen
  · simp only [ite_eq_right hlaunch]

/-- The mathematical calendar queue agrees with the unstopped numerical
replay for every arm, also on disabled rows. -/
theorem calendarQueue_eq_unstoppedReplay
    (N : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) (a : Fin p.K) :
    ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate N h a =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) N h a := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  unfold ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue
    UnstoppedRecordedQueueComparison.unstoppedReplay
  have hrec (xs : List (RecordedQueueRun.RoundInput p.K))
      (state : ℕ × ℕ) :
      QueueReplay.replay (4 * q.n) state
          (xs.map (fun c => (c.enabled,
            RecordedQueueRun.quantizedArrival q c a))) =
        QueueReplay.replay (4 * q.n) state
          (xs.map (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord q c a)) := by
    induction xs generalizing state with
    | nil => rfl
    | cons c xs ih =>
        simp only [List.map_cons, QueueReplay.replay, List.foldl_cons]
        by_cases hc : c.enabled
        · simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hc]
          exact ih _
        · simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hc,
            QueueReplay.transition]
          exact ih _
  exact hrec (N.take h) (0, 0)

/-- The raw queue safety test is exactly the false overflow flag on its
complete stopped-machine run. -/
private theorem literalQueueSafe_iff_run_not_overflow
    (N : List (RecordedQueueRun.RoundInput p.K)) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N ↔
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  change (∀ h, h ≤ N.length → ∀ a : Fin p.K,
      32 * (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate N h a).2 ≤ D p) ↔
    (RecordedQueueRun.run q N).overflow = false
  have hrep := calendarQueue_eq_unstoppedReplay rate N
  have hrun := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    q N N.length (by rfl)
  have htake : N.take N.length = N := List.take_of_length_le (le_refl _)
  have hrun' : (RecordedQueueRun.run q N).overflow = true ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix q N ≤ N.length := by
    simpa only [htake] using hrun
  constructor
  · intro hall
    cases hov : (RecordedQueueRun.run q N).overflow with
    | false => rfl
    | true =>
        have hk := hrun'.mp hov
        obtain ⟨a, ha⟩ := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q N hk
        have hs := hall _ hk a
        rw [hrep] at hs
        change 32 * (UnstoppedRecordedQueueComparison.unstoppedReplay q N
          (UnstoppedRecordedQueueComparison.firstOverflowPrefix q N) a).2 ≤ q.D at hs
        omega
  · intro hfalse h hh a
    have hfull : N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix q N := by
      by_contra hn
      have hover := hrun'.mpr (Nat.le_of_not_gt hn)
      rw [hfalse] at hover
      cases hover
    by_cases hz : h = 0
    · subst h
      rw [ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue_zero]
      exact Nat.zero_le _
    · have hn := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        q N h (by omega) hh (by omega)
      have hsafe : ¬ 32 * (UnstoppedRecordedQueueComparison.unstoppedReplay q N h a).2 > q.D :=
        fun hc => hn ⟨a, hc⟩
      have hsafe' : 32 * (UnstoppedRecordedQueueComparison.unstoppedReplay q N h a).2 ≤ q.D :=
        Nat.le_of_not_gt hsafe
      rw [← hrep] at hsafe'
      change 32 * (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate N h a).2 ≤ D p at hsafe'
      exact hsafe'

/-- The least crossing is tested on the whole launch prefix. Its sentinel
means no crossing in this word, with no assertion about later physical dates. -/
theorem literalQueueSafe_take_iff_before_first
    (E : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) (hh : h ≤ E.length) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (E.take h) ↔
      h < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) E := by
  rw [literalQueueSafe_iff_run_not_overflow]
  have hover := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) E h hh
  cases hf : (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (E.take h)).overflow with
  | false =>
    have hn : ¬ UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) E ≤ h := by
      intro hn
      have ht := hover.mpr hn
      rw [hf] at ht
      cases ht
    simp only [true_iff]
    exact Nat.lt_of_not_ge hn
  | true =>
    have hn := hover.mp hf
    simp only [Bool.true_eq_false, false_iff]
    omega

/-- Collection service inherits the launch-zero queue of the entire past.
This identity holds for every arm, including queues absent from physical stores. -/
theorem calendarQueue_append_inherited
    (P Dword : List (RecordedQueueRun.RoundInput p.K)) (j : ℕ) (a : Fin p.K) :
    ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate (P ++ Dword)
        (P.length + j) a =
      QueueReplay.replay (4 * rate.n)
        (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate P P.length a)
        (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (Dword.take j)) := by
  unfold ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue
    ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.map_append, QueueReplay.replay_append, List.take_length]

/-- The integer postqueue test is exactly the source normalized overflow
threshold, using the existing rate scaling. -/
theorem calendarQueue_overflow_iff_normalized
    (E : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) (a : Fin p.K) :
    D p < 32 * (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate E h a).2 ↔
      ((ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate E h a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
  exact (RecordedQueueRun.overflowCutoff_iff
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) _).symm

/-- Safety of a produced strict-past word tests every earlier postqueue;
it is stronger than checking only the current backlog after it may drain. -/
theorem literalQueueSafe_take_iff_all_past
    (E : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) (hh : h ≤ E.length) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (E.take h) ↔
      ∀ k, k ≤ h → ∀ a : Fin p.K,
        32 * (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate E k a).2 ≤ D p := by
  have hqueue (k : ℕ) (hk : k ≤ h) (a : Fin p.K) :
      ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate (E.take h) k a =
        ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate E k a := by
    unfold ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue
    rw [List.take_take, Nat.min_eq_left hk]
  unfold ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe
  rw [List.length_take, Nat.min_eq_left hh]
  constructor
  · intro hs k hk a
    rw [← hqueue k hk a]
    exact hs k hk a
  · intro hs k hk a
    rw [hqueue k hk a]
    exact hs k hk a

/-- Every date in the decoder-safe raw prefix is a raw selected record with
the corresponding global strict-past decoder safety. -/
private theorem mem_decoderSafePrefix_iff_rawK_safe
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r ∈ ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.decoderSafePrefix
        rate rewards C_star C_h z (K z) ↔
      r ∈ K z ∧ ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z r.input.time.val := by
  apply ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.mem_decoderSafePrefix_iff
  exact (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_order
    rate rewards C_star C_h z).imp (fun h => Nat.le_of_lt h)

/-- On a present original prefix, the gate's overflow flag is exactly the
all-arm strict-past replay test. -/
private theorem H_iff_literalQueueSafe
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some N) :
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N := by
  unfold ReferenceFirstCollectionCurrentRetainedGate.H
  simp only [Set.mem_ofPred_eq]
  rw [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hN]
  simp only [Option.map_some]
  constructor
  · rintro ⟨v, hv, hflag⟩
    have heq := Option.some.inj hv
    subst v
    change (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false at hflag
    exact (literalQueueSafe_iff_run_not_overflow rate N).2 hflag
  · intro hs
    refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N), rfl, ?_⟩
    change (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false
    exact (literalQueueSafe_iff_run_not_overflow rate N).1 hs

/-- Exact restriction of the global first decoder/calendar stop to the
selected raw replacement collection. The queue side uses the original full
launch based strict past, and the decoder side uses the global source test. -/
theorem stoppedDate_iff_literalCalendar_and_H
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    stoppedDate rate rewards C_star C_h z t ↔
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar
          rate rewards C_star C_h z t ∧
        z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t := by
  constructor
  · rintro ⟨r, hr, htime, hsafe, N, hN, hqueue⟩
    have hsafeR : ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z r.input.time.val := by
      rw [htime]
      exact hsafe
    constructor
    · exact ⟨r, (mem_decoderSafePrefix_iff_rawK_safe rate rewards C_star C_h z r).2
        ⟨hr, hsafeR⟩, htime⟩
    · have hpast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some N := by
        calc
          _ = originalPrefixInputs rate rewards C_star C_h t z :=
            (originalPrefixInputs_eq_pastCells? rate rewards C_star C_h t z).symm
          _ = some N := hN
      exact (H_iff_literalQueueSafe rate rewards C_star C_h t z N hpast).2 hqueue
  · rintro ⟨⟨r, hr, htime⟩, hH⟩
    have hr' := (mem_decoderSafePrefix_iff_rawK_safe rate rewards C_star C_h z r).1 hr
    have hsafeT : ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val := by
      rw [← htime]
      exact hr'.2
    cases hpast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z with
    | none =>
        have hread := hH
        unfold ReferenceFirstCollectionCurrentRetainedGate.H at hread
        obtain ⟨v, hv, _⟩ := hread
        rw [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hpast] at hv
        cases hv
    | some N =>
        have hqueue := (H_iff_literalQueueSafe rate rewards C_star C_h t z N hpast).1 hH
        have hinputs : originalPrefixInputs rate rewards C_star C_h t z = some N :=
          (originalPrefixInputs_eq_pastCells? rate rewards C_star C_h t z).trans hpast
        exact ⟨r, hr'.1, htime, hsafeT, N, hinputs, hqueue⟩

private theorem stoppedDate_at_produced_prefix
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (E : List (RecordedQueueRun.RoundInput p.K))
    (j : Fin (K z).length)
    (hdate : (K z)[j.val].input.time.val = s₀ z + c₀ z + j.val)
    (hp : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s₀ z + c₀ z + j.val) z =
        some (E.take (c₀ z + j.val))) :
    stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
      ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z (K z)[j.val].input.time.val ∧
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (E.take (c₀ z + j.val)) := by
  have hinput : originalPrefixInputs rate rewards C_star C_h
      (K z)[j.val].input.time z = some (E.take (c₀ z + j.val)) := by
    unfold originalPrefixInputs
    rw [hdate]
    exact hp
  constructor
  · rintro ⟨r, hr, ht, hs, N, hN, hq⟩
    have he : N = E.take (c₀ z + j.val) := Option.some.inj (hN.symm.trans hinput)
    exact ⟨hs, he ▸ hq⟩
  · rintro ⟨hs, hq⟩
    exact ⟨(K z)[j.val], List.getElem_mem j.isLt, rfl, hs,
      E.take (c₀ z + j.val), hinput, hq⟩

/-- The complete original source calendar is restricted by the global first
decoder/calendar-overflow stop. The queue endpoint is a prefix sentinel, and
all tests are strict-past: the update at the first crossing is included. -/
theorem complete_inclusive_stopped_calendar
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧ E.length ≤ (R z).length ∧
      (∀ h, h ≤ E.length → ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + h) z = some (E.take h)) ∧
      (∀ j : Fin (K z).length,
        (R z)[c₀ z + j.val]? = some (K z)[j.val] ∧
        (K z)[j.val].input.time.val = s₀ z + c₀ z + j.val ∧
        originalPrefixInputs rate rewards C_star C_h (K z)[j.val].input.time z =
          some (E.take (c₀ z + j.val)) ∧
        (E.take (c₀ z + j.val)).length = c₀ z + j.val ∧
        (stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
          (∀ f : Fin p.T, f.val < (K z)[j.val].input.time.val →
            ¬ ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.E
              rate rewards C_star C_h z f) ∧
          ∀ h, h ≤ c₀ z + j.val → ∀ a : Fin p.K,
            32 * (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate E h a).2 ≤ D p) ∧
        (stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
          (K z)[j.val].input.time.val + 1 <
              ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint rate rewards C_star C_h z ∧
          c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) E)) ∧
      (∀ j : Fin (K z).length,
        c₀ z + j.val + 1 = UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) E →
        (stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
          ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
            rate rewards C_star C_h z (K z)[j.val].input.time.val) ∧
        ∀ l : Fin (K z).length, j.val < l.val →
          ¬ stoppedDate rate rewards C_star C_h z (K z)[l.val].input.time) ∧
      (E.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) E →
        ∀ j : Fin (K z).length,
          stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
            ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
              rate rewards C_star C_h z (K z)[j.val].input.time.val) := by
  obtain ⟨E, hlen, hbound, hprefix, _hsource, hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  have hp (j : Fin (K z).length) :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + c₀ z + j.val) z =
          some (E.take (c₀ z + j.val)) := by
    have h := hprefix (c₀ z + j.val) (by omega)
    simpa only [← Nat.add_assoc] using h
  have hst (j : Fin (K z).length) :=
    stoppedDate_at_produced_prefix rate rewards C_star C_h z E j (hindex j).2 (hp j)
  have hsafe (j : Fin (K z).length) :
      ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
          rate rewards C_star C_h z (K z)[j.val].input.time.val ↔
        (K z)[j.val].input.time.val + 1 <
          ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint
            rate rewards C_star C_h z :=
    ReferenceFirstCollectionLiteralStoppedCharge.noEarlierLiteralFailure_iff_endpoint
      rate rewards C_star C_h z (K z)[j.val].input.time
  have hcut (j : Fin (K z).length) :
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (E.take (c₀ z + j.val)) ↔
        c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) E :=
    literalQueueSafe_take_iff_before_first rate E _ (by omega)
  refine ⟨E, hlen, hbound, hprefix, ?_, ?_, ?_⟩
  · intro j
    refine ⟨(hindex j).1, (hindex j).2, ?_, ?_, ?_, ?_⟩
    · unfold originalPrefixInputs
      rw [(hindex j).2]
      exact hp j
    · exact List.length_take_of_le (by omega)
    · rw [hst j, literalQueueSafe_take_iff_all_past rate E _ (by omega)]
      rfl
    · rw [hst j, hsafe j, hcut j]
  · intro j hfirst
    constructor
    · rw [hst j, hcut j]
      have hj : c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) E := by omega
      simp only [hj, and_true]
    · intro l hjl hl
      have hsafeQ := (hcut l).mp ((hst l).mp hl).2
      omega
  · intro hnone j
    rw [hst j, hcut j]
    have hj : c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) E := by omega
    simp only [hj, and_true]

/-- Each ordinary completed collection update is the next actual input of
the complete launch word. This applies to the detecting row itself; neither
birth nor cutoff resets the mathematical all-arm queues. -/
theorem complete_collection_updates
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ (Npre Dword : List (RecordedQueueRun.RoundInput p.K)),
      Npre.length = c₀ z ∧ ∃ hDlen : Dword.length = (K z).length,
      ∀ j : Fin (K z).length,
        let cell := Dword[j.val]'(by rw [hDlen]; exact j.isLt)
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s₀ z + c₀ z + j.val) z =
            some (Npre ++ Dword.take j.val) ∧
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s₀ z + c₀ z + j.val + 1) z =
            some ((Npre ++ Dword.take j.val) ++ [cell]) ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout (s₀ z)
          (K z)[j.val] = some cell ∧
        (∀ a : Fin p.K,
          ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate (Npre ++ Dword)
              (c₀ z + j.val) a =
            QueueReplay.replay (4 * rate.n)
              (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate Npre (c₀ z) a)
              (ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate a (Dword.take j.val)) ∧
          ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate (Npre ++ Dword)
              (c₀ z + j.val + 1) a =
            QueueReplay.transition (4 * rate.n)
              (ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue rate (Npre ++ Dword)
                (c₀ z + j.val) a)
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
        (stoppedDate rate rewards C_star C_h z (K z)[j.val].input.time ↔
          ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
              rate rewards C_star C_h z (K z)[j.val].input.time.val ∧
          c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) (Npre ++ Dword)) := by
  obtain ⟨Npre, Dword, seg, I, hNlen, hDlen, _hseg, _hrecords, _hremaining,
    _hI, _hstart, _hcutoff, _hNslots, hDmap, _hphysical, _hpre, hcol,
    _hslots, _hdisabled⟩ := complete_original_collection_words
      rate rewards C_star C_h control0 z hne
  obtain ⟨_E, _hElen, _hEbound, _hprefix, _hsource, hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  refine ⟨Npre, Dword, hNlen, hDlen, ?_⟩
  intro j
  dsimp only
  have hj : j.val < Dword.length := by omega
  have hi : c₀ z + j.val < (Npre ++ Dword).length := by
    simp only [List.length_append]
    omega
  have hcell : (Npre ++ Dword)[c₀ z + j.val] = Dword[j.val] := by
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega
  have htake : (Npre ++ Dword).take (c₀ z + j.val) = Npre ++ Dword.take j.val := by
    rw [List.take_append, List.take_of_length_le (by omega), hNlen, Nat.add_sub_cancel_left]
  have hread := congrArg (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[j.val]?) hDmap
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem j.isLt,
    List.getElem?_eq_getElem hj, Option.map_some, Option.map_some] at hread
  refine ⟨hcol j.val (by omega), ?_, Option.some.inj hread, ?_, ?_⟩
  · have hp := hcol (j.val + 1) (by omega)
    rw [← List.take_append_getElem hj] at hp
    simpa only [← Nat.add_assoc, List.append_assoc] using hp
  · intro a
    constructor
    · simpa only [hNlen] using calendarQueue_append_inherited rate Npre Dword j.val a
    · have hu := ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue_succ
        rate (Npre ++ Dword) (c₀ z + j.val) hi a
      rw [hcell] at hu
      rw [hu]
      cases he : Dword[j.val].enabled <;> rfl
  · have hp := hcol j.val (by omega)
    rw [← htake] at hp
    rw [stoppedDate_at_produced_prefix rate rewards C_star C_h z (Npre ++ Dword)
      j (hindex j).2 hp, literalQueueSafe_take_iff_before_first rate _ _ (by omega)]

/-- An actual first decoder failure is retained exactly when no queue
crossing preceded it. Later selected rows are excluded, also for simultaneous
queue and decoder detection and for a detecting final physical date. -/
theorem first_decoder_failure_on_collection
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hne : K z ≠ []) :
    ∃ E : List (RecordedQueueRun.RoundInput p.K),
      E.length = c₀ z + (K z).length ∧
      ∀ j : Fin (K z).length,
        let f := (K z)[j.val].input.time
        ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.E rate rewards C_star C_h z f →
        ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
          rate rewards C_star C_h z f.val →
        (stoppedDate rate rewards C_star C_h z f ↔
          c₀ z + j.val < UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) E) ∧
        ∀ l : Fin (K z).length, j.val < l.val →
          ¬ stoppedDate rate rewards C_star C_h z (K z)[l.val].input.time := by
  obtain ⟨E, hlen, _hbound, hprefix, _hsource, hindex⟩ :=
    complete_original_calendar rate rewards C_star C_h control0 z hne
  refine ⟨E, hlen, ?_⟩
  intro j
  dsimp only
  intro hfail hsafe
  have hp (l : Fin (K z).length) :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s₀ z + c₀ z + l.val) z =
          some (E.take (c₀ z + l.val)) := by
    simpa only [← Nat.add_assoc] using hprefix (c₀ z + l.val) (by omega)
  constructor
  · rw [stoppedDate_at_produced_prefix rate rewards C_star C_h z E j (hindex j).2 (hp j),
      literalQueueSafe_take_iff_before_first rate E _ (by omega)]
    simp only [hsafe, true_and]
  · intro l hjl hstopped
    have hsl := ((stoppedDate_at_produced_prefix rate rewards C_star C_h z E l
      (hindex l).2 (hp l)).mp hstopped).1
    exact hsl (K z)[j.val].input.time (by rw [(hindex j).2, (hindex l).2]; omega) hfail

/-- Empty selected collections have no stopped dates or charge. This does
not assert absence of decoder failures or overflow elsewhere in physical play. -/
theorem empty_collection
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hK : K z = []) :
    (∀ t, ¬ stoppedDate rate rewards C_star C_h z t) ∧ Cstop rate rewards C_star C_h z = 0 := by
  have hs (t : Fin p.T) : ¬ stoppedDate rate rewards C_star C_h z t := by
    rintro ⟨r, hr, _⟩
    rw [hK] at hr
    exact List.not_mem_nil hr
  refine ⟨hs, ?_⟩
  unfold Cstop
  simp only [hs, ite_false, Finset.sum_const_zero]

/-- The stopped date event is Borel in the original continuous source. -/
theorem stoppedDate_borel
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      stoppedDate rate rewards C_star C_h z t} := by
  have hH : MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t} :=
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _)
      _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
        rate rewards C_star C_h control0 t)
  rw [show {z : BootstrapPrivateRoundStreams.SourceInput p |
      stoppedDate rate rewards C_star C_h z t} =
      {z | ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar
        rate rewards C_star C_h z t} ∩
        {z | z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t} by
    ext z
    exact (stoppedDate_iff_literalCalendar_and_H rate rewards C_star C_h z t)]
  exact (ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar_borel
    rate rewards C_star C_h control0 t).inter hH

/-- Reindexing the literal stopped record definition gives the finite
calendar sum over the source decoder and queue stop tests. -/
theorem Cstop_eq_calendar_sum
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Cstop rate rewards C_star C_h z =
      ∑ t : Fin p.T,
        if ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar
              rate rewards C_star C_h z t ∧
            z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t then
          (min p.m (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t) : ℝ)
        else 0 := by
  unfold Cstop
  apply Finset.sum_congr rfl
  intro t _
  simp only [stoppedDate_iff_literalCalendar_and_H rate rewards C_star C_h z t]

/-- The exact stopped charge is nonnegative and is bounded by the accepted
global decoder charge. -/
theorem Cstop_bounds
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ Cstop rate rewards C_star C_h z ∧
      Cstop rate rewards C_star C_h z ≤
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z := by
  rw [Cstop_eq_calendar_sum rate rewards C_star C_h z,
    ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec_eq_calendar_sum]
  constructor
  · apply Finset.sum_nonneg
    intro t _
    split
    · exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_rfl
  · apply Finset.sum_le_sum
    intro t _
    by_cases hcal : ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar
        rate rewards C_star C_h z t
    · by_cases hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
          rate rewards C_star C_h t
      · simp [hcal, hH]
      · simp only [hcal, hH, and_false, ite_false]
        exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · simp [hcal]

/-- Measurability of the exact stopped capped charge on the whole original
source carrier. -/
theorem Cstop_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (Cstop rate rewards C_star C_h) := by
  unfold Cstop
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite
  · exact stoppedDate_borel rate rewards C_star C_h control0 t
  · exact measurable_const
  · exact measurable_const

/-- The same stopped charge read directly from the actual decoder-safe raw
records selected by the first-replacement producer. -/
def stoppedActualRawRecordSum (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  let D := ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.decoderSafePrefix
    rate rewards C_star C_h z (K z)
  (D.map fun r =>
    if z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h r.input.time then
      (min p.m (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        rewards r.input.time) : ℝ)
    else 0).sum

/-- The literal calendar sum equals the stopped capped charge on the actual
raw records retained by the source decoder. -/
theorem Cstop_eq_stoppedActualRawRecordSum
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Cstop rate rewards C_star C_h z =
      stoppedActualRawRecordSum rate rewards C_star C_h z := by
  let D := ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.decoderSafePrefix
    rate rewards C_star C_h z (K z)
  let dates := D.map (fun r => r.input.time)
  let weight : Fin p.T → ℝ := fun t =>
    min p.m (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t)
  let stoppedWeight : Fin p.T → ℝ := fun t =>
    if z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t
    then weight t else 0
  have hD : D.Pairwise (fun a b => a.input.time.val < b.input.time.val) :=
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_order
      rate rewards C_star C_h z).sublist (List.takeWhile_sublist _)
  have hnodup : dates.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    apply List.pairwise_map.mpr
    exact hD.imp (fun h he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  have he (t : Fin p.T) : t ∈ dates.toFinset ↔
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar
        rate rewards C_star C_h z t := by
    simp only [dates, List.mem_toFinset, List.mem_map,
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.literalCalendar, D]
  have heStop (t : Fin p.T) :
      (t ∈ dates.toFinset ∧
        z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t) ↔
        stoppedDate rate rewards C_star C_h z t := by
    rw [he]
    exact (stoppedDate_iff_literalCalendar_and_H rate rewards C_star C_h z t).symm
  have hsum :
      (dates.map stoppedWeight).sum =
        ∑ t : Fin p.T, if t ∈ dates.toFinset then stoppedWeight t else 0 := by
    calc
      _ = ∑ t ∈ dates.toFinset, stoppedWeight t :=
        (List.sum_toFinset stoppedWeight hnodup).symm
      _ = _ := (Finset.sum_ite_mem_eq dates.toFinset stoppedWeight).symm
  have hmap : D.map (fun r =>
      if z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h r.input.time
      then weight r.input.time else 0) = dates.map stoppedWeight := by
    simp [dates, stoppedWeight, weight, List.map_map, Function.comp_def]
  have hraw : stoppedActualRawRecordSum rate rewards C_star C_h z =
      ∑ t : Fin p.T, if stoppedDate rate rewards C_star C_h z t then weight t else 0 := by
    unfold stoppedActualRawRecordSum
    change (D.map (fun r =>
      if z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h r.input.time
      then weight r.input.time else 0)).sum = _
    rw [hmap]
    calc
      _ = ∑ t : Fin p.T, if t ∈ dates.toFinset then stoppedWeight t else 0 := hsum
      _ = ∑ t : Fin p.T, if stoppedDate rate rewards C_star C_h z t then weight t else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases hm : t ∈ dates.toFinset <;>
          by_cases hh : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
            rate rewards C_star C_h t
        · have hs := heStop t
          have hst : stoppedDate rate rewards C_star C_h z t := hs.mp ⟨hm, hh⟩
          simp [hm, hh, hst, stoppedWeight, weight]
        · have hs := heStop t
          have hst : ¬ stoppedDate rate rewards C_star C_h z t := by
            intro hst
            exact hh ((hs.mpr hst).2)
          simp [hm, hh, hst, stoppedWeight, weight]
        · have hs := heStop t
          have hst : ¬ stoppedDate rate rewards C_star C_h z t := by
            intro hst
            exact hm ((hs.mpr hst).1)
          simp [hm, hst, stoppedWeight, weight]
        · have hs := heStop t
          have hst : ¬ stoppedDate rate rewards C_star C_h z t := by
            intro hst
            exact hm ((hs.mpr hst).1)
          simp [hm, hst, stoppedWeight, weight]
  rw [Cstop_eq_calendar_sum rate rewards C_star C_h z]
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp [weight, stoppedDate_iff_literalCalendar_and_H]
    _ = stoppedActualRawRecordSum rate rewards C_star C_h z := hraw.symm

end Bandits.Support.ReferenceFirstReplacementCollectionInclusiveStoppedCharge

end
