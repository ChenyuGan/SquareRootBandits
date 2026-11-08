/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPureUpWindowCut

import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# Physical location of the second replacement UP completion

Sources: `sources/zip4/manuscript/05_binary_transport.tex:27-55`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`, and
`sources/zip4/manuscript/06_interruptions.tex:110-177,277-284,477-481`.

Least-prefix counting locates the same final positive of the second window.
The physical index is reconstructed from the records, independently of the
decoder replay index. No acceptance conclusion is asserted here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionPureUpDecisionLocation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_positive_length_le_one
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length ≤ 1 := by
  classical
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
  | some d =>
      by_cases hs : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
      · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ite_eq_left hs, AffineBatchDecoder.positiveAt]
        split <;> simp
      · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hs]

private theorem retained_positive_length_le
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).length ≤
      records.length := by
  induction records with
  | nil => simp [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
  | cons r rest ih =>
      have h := record_positive_length_le_one r i
      simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
        List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      omega

private theorem positive_member_input
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (i : Fin (p.m - 1))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hd : r.output.coordinator.up = some d)
    (he : entry ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) :
    d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
      entry.time = d.input.time ∧ entry.sample = d.input.affineSample := by
  classical
  have hs : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i := by
    by_contra h
    simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, h] at he
  have heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput d.input) := by
    by_contra h
    simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hs,
      AffineBatchDecoder.positiveAt, ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
      h] at he
  have hentry : entry =
      AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
        (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
    simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
      ite_eq_left hs, AffineBatchDecoder.positiveAt,
      ReferenceCoordinatorUpDecoderReplay.constantInputTrace] at he
    change entry ∈ (if AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput d.input) then [_] else []) at he
    rw [ite_eq_left heligible] at he
    exact List.mem_singleton.mp he
  refine ⟨hs, heligible, ?_, ?_⟩
  · rw [hentry]
    rfl
  · rw [hentry]
    rfl

private theorem positive_member_time
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : entry ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) :
    entry.time = r.input.time := by
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd] at he
  | some d =>
      have hentry := positive_member_input r d i entry hd he
      obtain ⟨_, _, _, _, htime, _⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
      exact hentry.2.2.1.trans htime

private theorem chronological_time_unique
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (r t : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ records) (ht : t ∈ records)
    (htime : r.input.time = t.input.time) : r = t := by
  obtain ⟨a, ha, hra⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨b, hb, htb⟩ := List.mem_iff_getElem.mp ht
  have hab : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := hchronological.rel_getElem_of_lt ha hb hlt
      rw [hra, htb, htime] at h
      omega
    · have h := hchronological.rel_getElem_of_lt hb ha hgt
      rw [htb, hra, htime] at h
      omega
  subst b
  exact hra.symm.trans htb

private theorem physical_positives_eq_retained
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val)) :
    ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives records i =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i :=
  ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
    records i hchronological

/-- A least physical prefix attaining a positive count ends in one positive.
Its last decision timestamp and record membership identify the same entry and
record, without any injectivity assumption on decoder-bank states. -/
private theorem least_prefix_final_positive
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (m need skip : ℕ)
    (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (hm : 0 < m) (hbound : m ≤ records.length)
    (hcount : (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
      (records.take m) i).length = need)
    (hleast : ∀ n : ℕ, n < m →
      (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
        (records.take n) i).length < need)
    (hlast : last ∈
      (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
        (records.take m) i).drop skip)
    (hdecision : AffineBatchDecoder.decisionTime
      ((ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
        (records.take m) i).drop skip) = some last.time)
    (hr : r ∈ records.take m) (hrtime : r.input.time = last.time) :
    need ≤ m ∧ records[m - 1]? = some r ∧
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [last] := by
  classical
  let positives := ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
    (records.take m) i
  let before := ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
    (records.take (m - 1)) i
  have hcountBound := retained_positive_length_le (records.take m) i
  rw [← physical_positives_eq_retained _ i hchronological.take] at hcountBound
  have hneed : need ≤ m := by
    rw [hcount, List.length_take_of_le hbound] at hcountBound
    exact hcountBound
  have hindex : m - 1 < records.length := by omega
  let finalRecord := records[m - 1]
  have hprevious : before.length < need := hleast (m - 1) (by omega)
  have hstep : positives = before ++
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries finalRecord i := by
    dsimp only [positives, before]
    rw [physical_positives_eq_retained _ i hchronological.take,
      physical_positives_eq_retained _ i hchronological.take]
    have hm' : m = (m - 1) + 1 := by omega
    rw [hm', List.take_succ_eq_append_getElem hindex]
    simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
      List.flatMap_append, List.flatMap_singleton]
    rfl
  have hsingleLength :
      (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries finalRecord i).length = 1 := by
    have hle := record_positive_length_le_one finalRecord i
    have hc : positives.length = need := hcount
    rw [hstep, List.length_append] at hc
    omega
  obtain ⟨entry, hsingle⟩ := List.length_eq_one_iff.mp hsingleLength
  have hpositive : positives = before ++ [entry] := by rw [hstep, hsingle]
  have hskip : skip < positives.length := by
    have hnonempty : positives.drop skip ≠ [] := List.ne_nil_of_mem hlast
    have hlen : 0 < (positives.drop skip).length := List.length_pos_iff.mpr hnonempty
    simp only [List.length_drop] at hlen
    omega
  have hlastTime : last.time = entry.time := by
    have hdec := hdecision
    change ((positives.drop skip).map AffineBatchDecoder.Entry.time).getLast? =
      some last.time at hdec
    rw [List.getLast?_map, List.getLast?_drop, ite_eq_right (by omega), hpositive] at hdec
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.map_some, Option.some.injEq] using hdec.symm
  have hentryTime : entry.time = finalRecord.input.time :=
    positive_member_time finalRecord i entry (by rw [hsingle]; simp)
  have hfinalMem : finalRecord ∈ records.take m := by
    apply List.mem_iff_getElem.mpr
    refine ⟨m - 1, ?_, ?_⟩
    · rw [List.length_take_of_le hbound]
      omega
    · simp only [List.getElem_take]
      rfl
  have hrfinal : r = finalRecord := chronological_time_unique (records.take m)
    hchronological.take r finalRecord hr hfinalMem (hrtime.trans (hlastTime.trans hentryTime))
  have hlastMem : last ∈ positives := List.mem_of_mem_drop hlast
  dsimp only [positives] at hlastMem
  rw [physical_positives_eq_retained _ i hchronological.take] at hlastMem
  obtain ⟨origin, horigin, hlastOrigin⟩ := List.mem_flatMap.mp hlastMem
  have horiginTime := positive_member_time origin i last hlastOrigin
  have horiginEq : origin = finalRecord := chronological_time_unique (records.take m)
    hchronological.take origin finalRecord horigin hfinalMem
      (horiginTime.symm.trans (hlastTime.trans hentryTime))
  rw [horiginEq, hsingle, List.mem_singleton] at hlastOrigin
  refine ⟨hneed, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mpr ⟨hindex, hrfinal.symm⟩
  · rw [hrfinal, hsingle, hlastOrigin]

/-- Locate the same final positive of the actual second pure UP window.
All physical, source-address, and reception-gate facts are produced from the
original complete execution. The local count and saved-call conditions are
the ones supplied by the admitted pure-window cut's exact-threshold branch. -/
theorem complete_first_replacement_collection_pure_up_decision_location
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let _s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _installed _) =>
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            ∀ (i : Fin (p.m - 1)) (b m : ℕ)
              (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
              (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
              (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
              b ≤ K.length → 0 < m → m ≤ (K.drop b).length →
              let channel := (Z b).upDecoderBank i
              let Q := AffineBatchDecoder.quota p
              let need := Q - channel.pending.length + Q
              let positive := ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                ((K.drop b).take m) i
              let window := positive.drop (Q - channel.pending.length)
              positive.length = need →
              (∀ n : ℕ, n < m →
                (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                  ((K.drop b).take n) i).length < need) →
              last ∈ window → AffineBatchDecoder.decisionTime window = some last.time →
              r ∈ (K.drop b).take m → r.input.time = last.time →
              r.output.coordinator.up = some d →
              2 ≤ m ∧
              ∃ k : Fin K.length,
                k.val = b + m - 1 ∧ 0 < k.val ∧ K.get k = r ∧
                (K.drop b)[m - 1]? = some r ∧ R[c + k.val]? = some r ∧
                r.input.time.val + 1 = u + k.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧ r.input.state = Z k.val ∧
                r.input.state = E (k.val - 1) ∧
                ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [last] ∧
                d.input.selectedFollower = i ∧
                ReferenceActivePhysicalStep.upSenderIndex r.input = i ∧
                d.input.time = r.input.time ∧ last.sample = d.input.affineSample ∧
                d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
                AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
                CoordinatorUpReception.receptionGate d.input ∧
                d.input.slot = PublicDiscreteDraws.upSlot ∧
                PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                  PublicDiscreteDraws.upSlot ∧
                i ∈ d.input.ledger.pending
          | _ => True
      | _ => True := by
  classical
  have hP :=
    ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
      rate source rewards C_star C_h
  dsimp only at hP ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hP ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hP ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hP ⊢
      obtain ⟨_, _, hP⟩ := hP
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hP ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hP ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hP ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          have hcalendar : ∀ q : Fin K.length,
              (K.get q).input.time.val + 1 = cut.input.time.val + 1 + q.val := hP.1
          have hZ : Z 0 = cut.input.state ∧
              (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
              (∀ q : Fin K.length, (K.get q).input.state = Z q.val ∧
                (K.get q).output.next = Z (q.val + 1)) := hP.2.1
          clear hP
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          have hchronR :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.complete_records_chronological
              rate source rewards C_star C_h
          have hchronK : K.Pairwise
              (fun earlier later => earlier.input.time.val < later.input.time.val) :=
            List.Pairwise.sublist hKprefix.sublist hchronR.drop
          obtain ⟨initial, active, _, _, _, hInvInitial, _, hfull, hRuns⟩ :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
              rate source rewards C_star C_h c cut hc K hKprefix
          change R = (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            (p.T - s) _ active).records at hfull
          intro i b m last r d hbK hm hbound
          let channel := (Z b).upDecoderBank i
          let Q := AffineBatchDecoder.quota p
          let need := Q - channel.pending.length + Q
          intro hcount hleast hlast hdecision hr hrtime hd
          have hInv : ReferenceUpDecoderBankInvariant.upBankInvariant (Z b) := by
            obtain ⟨span, _, hend⟩ := hRuns b hbK
            change (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + b) span active).finalState = Z b at hend
            rw [← hend]
            exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + b) span active hInvInitial
          have hpending : channel.pending.length < Q := (hInv.1 i).1
          have hQ : 0 < Q := AffineBatchDecoder.quota_pos p
          have hneed : 2 ≤ need := by dsimp only [need]; omega
          obtain ⟨hneedm, hlookup, hsingle⟩ := least_prefix_final_positive
            (K.drop b) i m need (Q - channel.pending.length) last r hchronK.drop
            hm hbound hcount hleast hlast hdecision hr hrtime
          have hmTwo : 2 ≤ m := by omega
          have hkbound : b + m - 1 < K.length := by
            change m ≤ (K.drop b).length at hbound
            simp only [List.length_drop] at hbound
            omega
          let k : Fin K.length := ⟨b + m - 1, hkbound⟩
          have hkpos : 0 < k.val := by dsimp only [k]; omega
          have hKget : K.get k = r := by
            obtain ⟨hmi, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
            rw [List.getElem_drop] at heq
            have hindex : b + (m - 1) = k.val := by dsimp only [k]; omega
            simpa only [hindex, List.get_eq_getElem] using heq
          have hRlookup : R[c + k.val]? = some r := by
            have heq := hKprefix.getElem k.isLt
            rw [List.getElem_drop] at heq
            apply List.getElem?_eq_some_iff.mpr
            refine ⟨?_, ?_⟩
            · have hlength := hKprefix.length_le
              simp only [List.length_drop] at hlength
              omega
            · exact heq.symm.trans (by simpa only [List.get_eq_getElem] using hKget)
          have hrK : r ∈ K :=
            List.mem_of_mem_drop (List.mem_of_mem_take hr)
          have hrR : r ∈ R := List.mem_of_mem_drop (hKprefix.subset hrK)
          have hsourceInputs : r.input.rows = source.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              r.input.rewards = rewards := by
            rw [hfull] at hrR
            exact ReferenceActivePhysicalHorizon.run_record_inputs initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (p.T - s) _ active r hrR
          have htime : r.input.time.val + 1 = cut.input.time.val + 1 + k.val := by
            simpa only [hKget] using hcalendar k
          have hstate : r.input.state = Z k.val := by
            simpa only [hKget] using (hZ.2.2 k).1
          have hcontinuing : r.input.state = E (k.val - 1) := by
            rw [hstate]
            have hWbound : k.val - 1 ≤ W.length := by
              have hki := k.isLt
              change k.val < W.length + 1 at hki
              omega
            have hindex : k.val = (k.val - 1) + 1 := by omega
            calc
              Z k.val = Z ((k.val - 1) + 1) := congrArg Z hindex
              _ = E (k.val - 1) := hZ.2.1 (k.val - 1) hWbound
          obtain ⟨hselected, heligible, _, hsample⟩ :=
            positive_member_input r d i last hd (by rw [hsingle]; simp)
          obtain ⟨savedLedger, _, _, hbank, hdtime, _, hselectedActual,
              hsampleActual, hslot, _⟩ :=
            ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
          have hsender : ReferenceActivePhysicalStep.upSenderIndex r.input = i :=
            hselectedActual.symm.trans hselected
          have hphysicalSample : d.input.affineSample =
              (r.input.row.2 r.input.time).2 (1, i) := by
            change d.input.affineSample =
              (r.input.row.2 r.input.time).2
                (1, CoordinatorUpMeasurability.selectedChannelFollower
                  (r.input.row.2 r.input.time)) at hsampleActual
            have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
                (r.input.row.2 r.input.time) = i := hsender
            rw [hchannel] at hsampleActual
            exact hsampleActual
          have hgate : CoordinatorUpReception.receptionGate d.input :=
            (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput_eligible_iff d).mp
              heligible |>.1
          have hslotUp : d.input.slot = PublicDiscreteDraws.upSlot := hgate.2.1
          have hphysicalSlot : PublicDiscreteDraws.slotDraw
              (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot :=
            hslot.symm.trans hslotUp
          have hpendingAtCall : i ∈ d.input.ledger.pending := by
            rw [← hselected]
            exact hgate.2.2
          exact ⟨hmTwo, k, rfl, hkpos, hKget, hlookup, hRlookup, htime,
            hsourceInputs.1, hsourceInputs.2.1, hsourceInputs.2.2, hstate, hcontinuing,
            hsingle, hselected, hsender, hdtime, hsample, hbank, hphysicalSample,
            heligible, hgate, hslotUp, hphysicalSlot, hpendingAtCall⟩

end Bandits.Support.ReferenceFirstReplacementCollectionPureUpDecisionLocation

end
