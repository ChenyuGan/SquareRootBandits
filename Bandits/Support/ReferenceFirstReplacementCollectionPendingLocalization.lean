/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPendingFoundation

/-!
# Converse localization of first replacement collection pending observations

Sources: `06_interruptions.tex:180-239,246-349,425-431,459-487`,
`05_binary_transport.tex:20-55,180-240`, and
`appendix_a_local_protocol.tex:92-157` in the pinned ZIP4 manuscript.
The physical calendar and all exceptional records are retained.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionPendingLocalization

open ReferenceFirstReplacementCollectionPendingFoundation
open ReferenceActivePhysicalStep
open ReferenceFirstReplacementLiveFollowerPrefix
open _root_.Bandits.Support.ReferenceCollectionPhaseHistory hiding Record


variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

private theorem dispatch_live_origin (x : RoundInput p rate) :
    match dispatch x with
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True := by
  unfold dispatch
  cases x.state.coordinator with
  | first => trivial
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;> rfl
  | collection payload ledger saved =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_left hc]
        cases CoordinatorRoundDispatch.dispatchCollection
          (collectionInput x payload ledger
            (collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
            ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_right hc]
  | dagger => trivial

private theorem advance_live_frame (r : Record (rate := rate))
    (phase : PastPhase rate)
    (hin : ∀ payload, phase = .replacementLive payload →
      r.input.state.coordinator = .dagger ∨
        ∃ registers owned base, r.input.state.coordinator = .live registers owned base ∧
          registers.payload = payload) :
    ∀ payload, advance phase r = .replacementLive payload →
      r.output.next.coordinator = .dagger ∨
        ∃ registers owned base, r.output.next.coordinator = .live registers owned base ∧
          registers.payload = payload := by
  have hout : r.output.next.coordinator =
      r.output.preparation.observeCoordinator.configuration := by
    rw [r.output_eq]
    rfl
  intro payload hp
  cases phase with
  | firstLive => simp only [advance] at hp; split at hp <;> contradiction
  | firstCollection =>
      simp only [advance] at hp
      cases hb : birthPayload r with
      | none => simp only [hb] at hp; contradiction
      | some born =>
          simp only [hb, PastPhase.replacementLive.injEq] at hp
          subst payload
          unfold birthPayload at hb
          cases hd : r.output.preparation.coordinator with
          | collection old ledger clock cutoff outcome =>
              cases outcome <;> simp only [hd] at hb <;> try contradiction
              rename_i core consistent started hstart instruction hi output hcons data installed selected
              have he : installed.registers.payload = born := Option.some.inj hb
              rw [hout, observeCoordinator_collection_equation _ _ _ _ _ _ hd]
              split
              · exact Or.inl rfl
              · rcases ReferenceFirstLiveConfirmationHistory.livePostChoice_frame
                    r.input r.output.preparation installed.registers installed.ownedRegisters
                    installed.retainedBaseScore started with hf | ⟨next, owned, hf, hpay, _⟩
                · exact Or.inl hf
                · exact Or.inr ⟨next, owned, installed.retainedBaseScore, hf, hpay.trans he⟩
          | first _ => simp only [hd] at hb; contradiction
          | live _ _ _ _ => simp only [hd] at hb; contradiction
          | invalidCollectionCutoff => simp only [hd] at hb; contradiction
          | dagger => simp only [hd] at hb; contradiction
  | replacementLive old =>
      simp only [advance] at hp
      split at hp
      · rename_i hcont
        have he : old = payload := PastPhase.replacementLive.inj hp
        subst payload
        have horigin := dispatch_live_origin r.input
        rw [← r.output.preparation.coordinator_eq] at horigin
        unfold isContinuingChosen at hcont
        cases hd : r.output.preparation.coordinator with
        | live registers owned base outcome =>
            rw [hd] at horigin
            cases outcome <;> simp only [hd, Bool.false_eq_true] at hcont
            rename_i dispatched hc selected hselected
            have hpay : registers.payload = old := by
              rcases hin old rfl with hdagger | ⟨next, q, b, hnext, hpayload⟩
              · rw [horigin] at hdagger; contradiction
              · rw [horigin] at hnext
                cases hnext
                exact hpayload
            rw [hout, observeCoordinator_live_equation _ _ _ _ _ hd]
            split
            · exact Or.inl rfl
            · rcases ReferenceFirstLiveConfirmationHistory.livePostChoice_frame
                  r.input r.output.preparation (liveRegistersAt registers r.input.time)
                  (liveOwnedAt registers owned r.input.time) base dispatched.startResult with
                  hf | ⟨next, q, hf, hpayload, _⟩
              · exact Or.inl hf
              · exact Or.inr ⟨next, q, base, hf, hpayload.trans hpay⟩
        | first _ => simp only [hd, Bool.false_eq_true] at hcont
        | collection _ _ _ _ _ => simp only [hd, Bool.false_eq_true] at hcont
        | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hcont
        | dagger => simp only [hd, Bool.false_eq_true] at hcont
      · split at hp <;> contradiction
  | replacementCollection old u =>
      simp only [advance] at hp
      split at hp <;> contradiction
  | closed => contradiction

private theorem connected_scan_live_frame
    (R : List (Record (rate := rate))) (initial final : State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial R final) (phase : PastPhase rate)
    (hin : ∀ payload, phase = .replacementLive payload →
      initial.coordinator = .dagger ∨
        ∃ registers owned base, initial.coordinator = .live registers owned base ∧
          registers.payload = payload) :
    ∀ payload, scan R phase = .replacementLive payload →
      final.coordinator = .dagger ∨
        ∃ registers owned base, final.coordinator = .live registers owned base ∧
          registers.payload = payload := by
  induction R generalizing initial phase with
  | nil =>
      change final = initial at hchain
      subst final
      exact hin
  | cons r R ih =>
      obtain ⟨hr, ht⟩ := hchain
      apply ih r.output.next ht (advance phase r)
      apply advance_live_frame r phase
      simpa only [hr] using hin

private theorem scan_closed (R : List (Record (rate := rate))) :
    scan R .closed = .closed := by
  induction R with
  | nil => rfl
  | cons r R ih => exact ih

private theorem take_prefix {α : Type*} (A B : List α) (h : A <+: B) :
    B.take A.length = A := by
  obtain ⟨D, rfl⟩ := h
  simp only [List.take_left]

private theorem drop_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.drop j = r :: R.drop (j + 1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hr
  simpa only [he] using List.drop_eq_getElem_cons hj

private theorem take_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.take (j + 1) = R.take j ++ [r] := by
  rw [List.take_add_one, hr]
  rfl

private theorem takeWhile_boundary {α : Type*} (test : α → Bool) (R : List α)
    (j : ℕ) (r : α) (hr : R[j]? = some r)
    (hj : (R.takeWhile test).length = j) : test r = false := by
  induction R generalizing j with
  | nil => simp at hr
  | cons q R ih =>
      cases ht : test q with
      | false =>
          have hz : j = 0 := by simpa [ht] using hj.symm
          rw [hz] at hr
          have he : q = r := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using hr
          exact he ▸ ht
      | true =>
          cases j with
          | zero => simp [ht] at hj
          | succ j =>
              apply ih j (by simpa using hr)
              simpa [ht] using hj

private theorem advance_rank (phase : PastPhase rate) (r : Record (rate := rate)) :
    (phaseSummary phase).1 ≤ (phaseSummary (advance phase r)).1 := by
  cases phase with
  | firstLive => simp only [advance]; split <;> simp only [phaseSummary] <;> omega
  | firstCollection =>
      simp only [advance]
      cases birthPayload r <;> simp only [phaseSummary] <;> omega
  | replacementLive payload =>
      simp only [advance]
      split
      · exact le_rfl
      · split <;> simp only [phaseSummary] <;> omega
  | replacementCollection payload u => simp only [advance]; split <;> simp only [phaseSummary] <;> omega
  | closed => exact le_rfl

private theorem scan_rank (R : List (Record (rate := rate))) (phase : PastPhase rate) :
    (phaseSummary phase).1 ≤ (phaseSummary (scan R phase)).1 := by
  induction R generalizing phase with
  | nil => exact le_rfl
  | cons r R ih => exact (advance_rank phase r).trans (ih (advance phase r))

private theorem scan_prefix_rank (A B : List (Record (rate := rate))) (h : A <+: B) :
    (phaseSummary (scan A)).1 ≤ (phaseSummary (scan B)).1 := by
  obtain ⟨D, rfl⟩ := h
  rw [scan_append]
  exact scan_rank D (scan A)

private theorem take_prefix_take {α : Type*} (R : List α) (i j : ℕ) (h : i ≤ j) :
    R.take i <+: R.take j := by
  have ht : (R.take j).take i = R.take i := by rw [List.take_take, Nat.min_eq_left h]
  rw [← ht]
  exact List.take_prefix _ _

private theorem birth_index_bounds (R : List (Record (rate := rate))) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (collectionWindow R w).length
    v ≤ R.length ∧
      (∀ birth, R[v]? = some birth → laterChosen birth.input = true) ∧
      (phaseSummary (scan (R.take v))).1 ≤ 1 := by
  dsimp only
  let A := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R
  let w := A.length
  have hwle : w ≤ R.length := (List.takeWhile_prefix _).length_le
  by_cases hw : w < R.length
  · let cut := R[w]'hw
    have hcut : R[w]? = some cut := List.getElem?_eq_getElem hw
    let W := (R.drop (w + 1)).takeWhile (fun r => !laterChosen r.input)
    have hc : collectionWindow R w = cut :: W := by
      unfold collectionWindow
      rw [drop_lookup R w cut hcut]
      rfl
    have hW : W.length ≤ R.length - (w + 1) := by
      simpa only [List.length_drop] using (show W <+: R.drop (w + 1) from List.takeWhile_prefix _).length_le
    refine ⟨?_, ?_, ?_⟩
    · change w + (collectionWindow R w).length ≤ R.length
      rw [hc, List.length_cons]
      omega
    · intro birth hb
      change R[w + (collectionWindow R w).length]? = some birth at hb
      rw [hc, List.length_cons] at hb
      have hlookup : (R.drop (w + 1))[W.length]? = some birth := by
        rw [List.getElem?_drop]
        convert hb using 1
        congr 1
        omega
      have ht := takeWhile_boundary (fun r : Record (rate := rate) => !laterChosen r.input)
        (R.drop (w + 1)) W.length birth hlookup rfl
      simpa only [Bool.not_eq_false'] using ht
    · rw [scan_before_birth R hw]
      exact Nat.le_refl 1
  · have hwEq : w = R.length := by omega
    have hA : A = R := by
      have ht := take_prefix A R (List.takeWhile_prefix _)
      change R.take w = A at ht
      rw [hwEq, List.take_length] at ht
      exact ht.symm
    have hc : collectionWindow R w = [] := by
      simp only [collectionWindow, hwEq, List.drop_length, List.take_nil,
        List.drop_eq_nil_of_le (by omega : R.length ≤ R.length + 1),
        List.takeWhile_nil, List.append_nil]
    have hv : w + (collectionWindow R w).length = R.length := by rw [hc]; simpa using hwEq
    refine ⟨by rw [hv], ?_, ?_⟩
    · intro birth hb
      change R[w + (collectionWindow R w).length]? = some birth at hb
      rw [hv, List.getElem?_length] at hb
      contradiction
    · change (phaseSummary (scan (R.take (w + (collectionWindow R w).length)))).1 ≤ 1
      rw [hv, List.take_length, ← hA, scan_firstLiveWindow]
      exact Nat.zero_le 1

private theorem actual_scan_live_incoming
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : ℕ)
    (r : Record (rate := rate))
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j]? = some r)
    (payload : ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate))
    (hphase : scan ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take j) = .replacementLive payload) :
    r.input.state.coordinator = .dagger ∨
      ∃ registers owned base, r.input.state.coordinator = .live registers owned base ∧
        registers.payload = payload := by
  have hj := (List.getElem?_eq_some_iff.mp hr).1
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hl
      have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
        rate z rewards C_star C_h
      rw [hs, Nat.sub_self] at hlen
      omega
  | some active =>
      have hc := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate z rewards C_star C_h active hl
      have ht := ReferenceFollowerReplyChronology.connected_take_to_input hc j hj
      rw [(List.getElem?_eq_some_iff.mp hr).2] at ht
      exact connected_scan_live_frame _ active r.input.state ht .firstLive
        (by intro payload hp; contradiction) payload hphase

private theorem continuing_not_cutoff (r : Record (rate := rate))
    (hr : isContinuingChosen r = true) : isCutoff r = false := by
  unfold isContinuingChosen at hr
  unfold isCutoff
  cases hd : r.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome <;> simp_all only [Bool.false_eq_true]
  | first _ => simp only [hd, Bool.false_eq_true] at hr
  | collection _ _ _ _ _ => simp only [hd, Bool.false_eq_true] at hr
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hr
  | dagger => simp only [hd, Bool.false_eq_true] at hr

private theorem raw_nonempty_data
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hP : (Praw rate rewards C_star C_h n z).Nonempty) :
    ∃ (hn : n < p.T) (payload : ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate))
      (u : ℕ) (r : Record (rate := rate)),
      payloadOnset rate rewards C_star C_h n z = some (payload, u) ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z = some r ∧
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h payload.sigma.val ⟨n, hn⟩ z).Nonempty ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
        n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r ∧
      2 ≤ (phaseSummary (pastPhase rate rewards C_star C_h n z)).1 ∧
      (phaseSummary (pastPhase rate rewards C_star C_h n z)).1 < 4 := by
  by_cases hn : n < p.T
  · cases ho : payloadOnset rate rewards C_star C_h n z with
    | none => simp only [Praw, dite_eq_left hn, ho, Finset.not_nonempty_empty] at hP
    | some pair =>
        obtain ⟨payload, u⟩ := pair
        have hQ : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
            payload.sigma.val ⟨n, hn⟩ z).Nonempty := by
          simpa only [Praw, dite_eq_left hn, ho] using hP
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
        | none => simp only [ReferenceFirstCollectionPendingObservation.Q, hr, Finset.not_nonempty_empty] at hQ
        | some r =>
            have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n := by
              by_contra hs
              simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_right hs] at hr
              contradiction
            have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
                n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r := by
              simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs] using hr
            refine ⟨hn, payload, u, r, rfl, hr, hQ, hs, hlookup, ?_⟩
            unfold payloadOnset at ho
            cases he : pastPhase rate rewards C_star C_h n z <;>
              simp_all only [phaseSummary, reduceCtorEq, Nat.reduceLeDiff, Nat.reduceLT, and_self]
  · simp only [Praw, dite_eq_right hn, Finset.not_nonempty_empty] at hP

private theorem raw_support_indices
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hP : (Praw rate rewards C_star C_h n z).Nonempty) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (collectionWindow R w).length
    let tail := continuingTail R v
    let c := v + 1 + tail.length
    ∃ birth cut, R[v]? = some birth ∧ (birthPayload birth).isSome = true ∧
      R[c]? = some cut ∧ isCutoff cut = true ∧ c ≤ n - s ∧
      n - s < c + 1 + ((R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)).length := by
  obtain ⟨hn, observed, onset, r, honset, hactual, hQ, hs, hlookup, hlower, hupper⟩ :=
    raw_nonempty_data rewards C_star C_h z n hP
  rw [pastPhase_eq_scan] at hlower hupper
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let j := n - s
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (collectionWindow R w).length
  let tail := continuingTail R v
  let c := v + 1 + tail.length
  change R[j]? = some r at hlookup
  change 2 ≤ (phaseSummary (scan (R.take j))).1 at hlower
  change (phaseSummary (scan (R.take j))).1 < 4 at hupper
  have hj : j < R.length := (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨hvle, hborn, hvRank⟩ := birth_index_bounds R
  change v ≤ R.length at hvle
  change (phaseSummary (scan (R.take v))).1 ≤ 1 at hvRank
  have hvj : v < j := by
    by_contra h
    have hrank := scan_prefix_rank (R.take j) (R.take v) (take_prefix_take R j v (by omega))
    omega
  have hv : v < R.length := by omega
  let birth := R[v]'hv
  have hb : R[v]? = some birth := List.getElem?_eq_getElem hv
  have hbornTag : (birthPayload birth).isSome = true := by
    rw [birthPayload_isSome]
    exact hborn birth hb
  obtain ⟨payload, hp⟩ : ∃ payload, birthPayload birth = some payload := by
    cases he : birthPayload birth with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hbornTag
    | some payload => exact ⟨payload, rfl⟩
  have hbefore : scan (R.take c) = .replacementLive payload :=
    scan_before_replacement_cut R birth payload hb hp
  have hcurrentCut : ∀ pp, scan (R.take j) = .replacementLive pp → isCutoff r = true := by
    intro pp hphase
    have hframe := actual_scan_live_incoming rewards C_star C_h z j r hlookup pp hphase
    rcases hframe with hdagger | ⟨registers, owned, base, hstate, _⟩
    · simp only [ReferenceFirstCollectionPendingObservation.Q, hactual, hdagger,
        Finset.not_nonempty_empty] at hQ
    · by_contra hcut
      have hfalse : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        rw [← isCutoff_eq]
        exact Bool.eq_false_iff.mpr hcut
      simp only [ReferenceFirstCollectionPendingObservation.Q, hactual, hstate,
        hfalse, Bool.false_eq_true, and_false, ↓reduceIte, Finset.not_nonempty_empty] at hQ
  have hcj : c ≤ j := by
    by_contra h
    have hjc : j ≤ c := by omega
    have hrank := scan_prefix_rank (R.take j) (R.take c) (take_prefix_take R j c hjc)
    rw [hbefore] at hrank
    have hphase : ∃ pp, scan (R.take j) = .replacementLive pp := by
      cases he : scan (R.take j) with
      | replacementLive pp => exact ⟨pp, rfl⟩
      | firstLive => simp only [he, phaseSummary] at hlower; omega
      | firstCollection => simp only [he, phaseSummary] at hlower; omega
      | replacementCollection pp u => simp only [he, phaseSummary] at hrank; omega
      | closed => simp only [he, phaseSummary] at hrank; omega
    obtain ⟨pp, hphase⟩ := hphase
    have hcut := hcurrentCut pp hphase
    let k : Fin tail.length := ⟨j - (v + 1), by dsimp only [c] at h; omega⟩
    have hk := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
    have hkindex : v + 1 + k.val = j := by dsimp only [k]; omega
    rw [hkindex, hlookup] at hk
    have he : tail.get k = r := (Option.some.inj hk).symm
    have hcont := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem R v
      (tail.get k) (List.get_mem tail k)
    rw [he] at hcont
    rw [continuing_not_cutoff r hcont] at hcut
    contradiction
  have hc : c < R.length := by omega
  let cut := R[c]'hc
  have hcutlookup : R[c]? = some cut := List.getElem?_eq_getElem hc
  have hnoncont : isContinuingChosen cut = false := by
    have hget : (R.drop (v + 1))[tail.length]? = some cut := by
      rw [List.getElem?_drop]
      exact hcutlookup
    exact takeWhile_boundary isContinuingChosen (R.drop (v + 1)) tail.length cut hget rfl
  have hcut : isCutoff cut = true := by
    by_contra hbad
    have hfalse : isCutoff cut = false := Bool.eq_false_iff.mpr hbad
    by_cases heq : j = c
    · have her : r = cut := by rw [heq, hcutlookup] at hlookup; exact (Option.some.inj hlookup).symm
      have hflag := hcurrentCut payload (by simpa only [heq] using hbefore)
      rw [her, hfalse] at hflag
      contradiction
    · have hclosed : scan (R.take (c + 1)) = .closed := by
        rw [take_lookup R c cut hcutlookup, scan_append, hbefore]
        simp only [scan_cons, scan_nil, advance, hnoncont, hfalse,
          Bool.false_eq_true, ↓reduceIte]
      have hrank := scan_prefix_rank (R.take (c + 1)) (R.take j)
        (take_prefix_take R (c + 1) j (by omega))
      rw [hclosed] at hrank
      change 4 ≤ (phaseSummary (scan (R.take j))).1 at hrank
      omega
  let W := (R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)
  let e := c + 1 + W.length
  have hafter : scan (R.take (c + 1)) = .replacementCollection payload (cut.input.time.val + 1) := by
    rw [take_lookup R c cut hcutlookup, scan_append, hbefore]
    simp only [scan_cons, scan_nil, advance, hnoncont, hcut, Bool.false_eq_true, ↓reduceIte]
  have hend : scan (R.take e) = .replacementCollection payload (cut.input.time.val + 1) := by
    change scan (R.take ((c + 1) + W.length)) = _
    rw [List.take_add, take_prefix W (R.drop (c + 1)) (List.takeWhile_prefix _),
      scan_append, hafter]
    apply scan_collection
    intro q hq
    simpa only [Bool.not_eq_true'] using List.mem_takeWhile_imp hq
  have hje : j < e := by
    by_contra hbad
    have he : e < R.length := by omega
    let next := R[e]'he
    have hnext : R[e]? = some next := List.getElem?_eq_getElem he
    have hnextTag : laterChosen next.input = true := by
      have hget : (R.drop (c + 1))[W.length]? = some next := by
        rw [List.getElem?_drop]
        exact hnext
      have ht := takeWhile_boundary (fun r : Record (rate := rate) => !laterChosen r.input)
        (R.drop (c + 1)) W.length next hget rfl
      simpa only [Bool.not_eq_false'] using ht
    by_cases heq : j = e
    · have her : r = next := by rw [heq, hnext] at hlookup; exact (Option.some.inj hlookup).symm
      obtain ⟨old, ledger, saved, hstate, hempty⟩ := laterChosen_pending_empty next.input hnextTag
      rw [← her] at hstate
      simp only [ReferenceFirstCollectionPendingObservation.Q, hactual, hstate, hempty] at hQ
      split at hQ <;> exact Finset.not_nonempty_empty hQ
    · have hclosed : scan (R.take (e + 1)) = .closed := by
        rw [take_lookup R e next hnext, scan_append, hend]
        simp only [scan_cons, scan_nil, advance, hnextTag, ↓reduceIte]
      have hrank := scan_prefix_rank (R.take (e + 1)) (R.take j)
        (take_prefix_take R (e + 1) j (by omega))
      rw [hclosed] at hrank
      change 4 ≤ (phaseSummary (scan (R.take j))).1 at hrank
      omega
  exact ⟨birth, cut, hb, hbornTag, hcutlookup, hcut, hcj, hje⟩

private theorem complete_record_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (j : ℕ) (r : Record (rate := rate))
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j]? = some r) :
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j := by
  have hj := (List.getElem?_eq_some_iff.mp hr).1
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have ht := congrArg (fun times : List ℕ => times[j]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h)
  simp only [List.getElem?_map, hr, Option.map_some] at ht
  rw [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' (by omega), Nat.one_mul] at ht
  exact Option.some.inj ht

/-- All-calendar converse for the literal masked pending set. Every absent or
nonmatching physical birth/cutoff branch is false under nonemptiness. The
coordinate belongs to the complete collection, including detecting records. -/
theorem complete_first_replacement_pending_localization
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ),
    (P_repl rate rewards C_star C_h control0 n z).Nonempty →
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (collectionWindow R w).length
    let tail := continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => False
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => False
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let K := cut :: (R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)
            ∃ a : Fin K.length, n = u - 1 + a.val ∧
              (K.get a).input.time.val = n ∧
              payloadOnset rate rewards C_star C_h n z = some (payload, u)
          | _ => False
      | _ => False := by
  intro z n hP
  have hraw : (Praw rate rewards C_star C_h n z).Nonempty := by
    obtain ⟨i, hi⟩ := hP
    exact ⟨i, (Finset.mem_filter.mp hi).1⟩
  have hsupport := raw_support_indices rewards C_star C_h z n hraw
  have hforward := complete_first_replacement_pending_coordinates rate rewards C_star C_h control0 z
  dsimp only at hsupport hforward ⊢
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (collectionWindow R w).length
  let tail := continuingTail R v
  let c := v + 1 + tail.length
  obtain ⟨birth, cut, hb, hborn, hc, hcut, hlo, hhi⟩ := hsupport
  change R[v]? = some birth at hb
  change R[c]? = some cut at hc
  change c ≤ n - s at hlo
  change n - s < c + 1 + ((R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)).length at hhi
  rw [hb] at hforward ⊢
  dsimp only at hforward ⊢
  cases hbirth : birth.output.preparation.coordinator with
  | first _ => simp only [birthPayload, hbirth, Option.isSome_none, Bool.false_eq_true] at hborn
  | live _ _ _ _ => simp only [birthPayload, hbirth, Option.isSome_none, Bool.false_eq_true] at hborn
  | dagger => simp only [birthPayload, hbirth, Option.isSome_none, Bool.false_eq_true] at hborn
  | invalidCollectionCutoff => simp only [birthPayload, hbirth, Option.isSome_none, Bool.false_eq_true] at hborn
  | collection old ledger clock cutoff outcome =>
      rw [hbirth] at hforward
      cases outcome <;> try (simp only [birthPayload, hbirth, Option.isSome_none, Bool.false_eq_true] at hborn)
      rename_i core consistent started hstart instruction hi output hconsistent clockData installed selected
      dsimp only [collectionInput] at hforward ⊢
      rw [hc] at hforward ⊢
      dsimp only at hforward ⊢
      cases hcutprep : cut.output.preparation.coordinator with
      | first _ => simp only [isCutoff, hcutprep, Bool.false_eq_true] at hcut
      | collection _ _ _ _ _ => simp only [isCutoff, hcutprep, Bool.false_eq_true] at hcut
      | dagger => simp only [isCutoff, hcutprep, Bool.false_eq_true] at hcut
      | invalidCollectionCutoff => simp only [isCutoff, hcutprep, Bool.false_eq_true] at hcut
      | live registers owned base result =>
          rw [hcutprep] at hforward
          cases result <;> try (simp only [isCutoff, hcutprep, Bool.false_eq_true] at hcut)
          dsimp only at hforward ⊢
          let u := cut.input.time.val + 1
          let K := cut :: (R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)
          have htime := complete_record_time rewards C_star C_h z c cut hc
          change cut.input.time.val = s + c at htime
          have hns : s ≤ n := by
            obtain ⟨_, _, _, _, _, _, _, hs, _⟩ := raw_nonempty_data rewards C_star C_h z n hraw
            exact hs
          change ∃ a : Fin K.length, n = u - 1 + a.val ∧
            (K.get a).input.time.val = n ∧
            payloadOnset rate rewards C_star C_h n z = some (installed.registers.payload, u)
          let a : Fin K.length := ⟨n - s - c, by
            dsimp only [K]
            simp only [List.length_cons]
            omega⟩
          have hcoord : n = u - 1 + a.val := by dsimp only [u, a]; omega
          have honset := (hforward a).1
          have hprefix : K <+: R.drop c := collection_prefix R c cut hc
          have hget : R[c + a.val]? = some (K.get a) := by
            obtain ⟨rest, hrest⟩ := hprefix
            rw [← List.getElem?_drop, ← hrest, List.getElem?_append_left a.isLt]
            exact List.getElem?_eq_getElem a.isLt
          have hatime := complete_record_time rewards C_star C_h z (c + a.val) (K.get a) hget
          change (K.get a).input.time.val = s + (c + a.val) at hatime
          refine ⟨a, hcoord, ?_, ?_⟩
          · exact hatime.trans (by dsimp only [a]; omega)
          · change payloadOnset rate rewards C_star C_h (u - 1 + a.val) z =
              some (installed.registers.payload, u) at honset
            rw [← hcoord] at honset
            exact honset

end Bandits.Support.ReferenceFirstReplacementCollectionPendingLocalization

end
