/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport
public import Bandits.Support.ReferenceFirstCollectionLiteralStoppedCharge

/-!
# Global decoder-safe charge of the first replacement collection

The records are those of the original continuous source. Safety tests all
strictly earlier literal decoder failures, retaining a detecting update.
Sources: `06_interruptions.tex:425-437,459-487`,
`appendix_a_local_protocol.tex:28-85,141-157`, and
`05_binary_transport.tex:20-55,180-240` in `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep ReferenceFirstReplacementCollectionPendingFoundation
open ReferenceFirstCollectionUpConditionalService (positiveRewardCount)
open ReferenceFirstCollectionRoundEndObservation (g)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionGlobalDecoderCharge

variable {p : Parameters}

/-- The literal nested birth/cutoff selector on the unchanged physical suffix. -/
def rawK (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : List (Record (rate := rate)) :=
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  match R[v]? with
  | none => []
  | some birth => match birth.output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
      match R[c]? with
      | none => []
      | some cut => match cut.output.preparation.coordinator with
        | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
          cut :: (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        | _ => []
    | _ => []

/-- Equivalent constructor tests, retaining the actual records and dates. -/
theorem rawK_eq (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    rawK rate rewards C_star C_h z =
      match R[v]? with
      | none => []
      | some birth => if (birthPayload birth).isSome then
          match R[c]? with
          | none => []
          | some cut => if isCutoff cut then
              cut :: (R.drop (c + 1)).takeWhile
                (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            else []
        else [] := by
  unfold rawK
  dsimp only
  split
  · rfl
  · rename_i birth hb
    cases hd : birth.output.preparation.coordinator with
    | collection _ _ _ _ outcome =>
      cases outcome <;> simp [birthPayload, hd]
      split
      · rfl
      · rename_i cut hc
        cases he : cut.output.preparation.coordinator with
        | live _ _ _ outcome => cases outcome <;> simp [isCutoff, he]
        | first _ => simp [isCutoff, he]
        | collection _ _ _ _ _ => simp [isCutoff, he]
        | dagger => simp [isCutoff, he]
        | invalidCollectionCutoff => simp [isCutoff, he]
    | first _ => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    | live _ _ _ _ => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    | dagger => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    | invalidCollectionCutoff => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- A retained actual record has the specified whole finite calendar date. -/
def literalCalendar (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) : Prop :=
  ∃ r ∈ ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.decoderSafePrefix rate rewards C_star C_h z (rawK rate rewards C_star C_h z),
    r.input.time = t

/-- Capped charge of the globally safe literal collection prefix. -/
def Cdec (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.cappedCharge rate rewards C_star C_h z (rawK rate rewards C_star C_h z)

variable (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

private theorem rawK_sublist (z : BootstrapPrivateRoundStreams.SourceInput p) :
    List.Sublist (rawK rate rewards C_star C_h z)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) := by
  rw [rawK_eq]
  split
  · exact List.nil_sublist _
  · split
    · split
      · exact List.nil_sublist _
      · rename_i birth hb hborn cut hc
        split
        · exact (collection_prefix _ _ cut hc).sublist.trans (List.drop_sublist _ _)
        · exact List.nil_sublist _
    · exact List.nil_sublist _

private theorem complete_order (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).Pairwise
      (fun a b => a.input.time.val < b.input.time.val) := by
  rw [← List.pairwise_map]
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
  exact List.pairwise_lt_range' _ (by decide)

/-- No physical date occurs twice in the selected collection. -/
theorem rawK_order (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (rawK rate rewards C_star C_h z).Pairwise
      (fun a b => a.input.time.val < b.input.time.val) :=
  (complete_order rate rewards C_star C_h z).sublist (rawK_sublist rate rewards C_star C_h z)

private theorem reached_support
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (birth cut : Record (rate := rate))
    (hb : let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some birth)
    (hborn : (birthPayload birth).isSome = true)
    (hc : let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
      R[v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length]? = some cut)
    (hcut : isCutoff cut = true) :
    (∀ r ∈ ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.decoderSafePrefix rate rewards C_star C_h z (rawK rate rewards C_star C_h z),
      (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew rate rewards C_star C_h control0 r.input.time.val z).Nonempty) ∧
    Cdec rate rewards C_star C_h z ≤ ∑ n ∈ Finset.range p.T,
      if (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0 := by
  have h := ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.complete_first_replacement_literal_decoder_safe_support_and_charge
    rate rewards C_star C_h control0 z
  dsimp only at hb hc h
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  have hk : rawK rate rewards C_star C_h z = cut :: (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
    rw [rawK_eq]
    simp only [R, w, v, c, hb, hborn, hc, hcut, ↓reduceIte]
  rw [hb] at h
  dsimp only at h
  cases hd : birth.output.preparation.coordinator with
  | collection _ _ _ _ outcome =>
    rw [hd] at h
    cases outcome <;> simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true] at hborn
    dsimp only [collectionInput] at h ⊢
    rw [hc] at h
    dsimp only at h
    cases he : cut.output.preparation.coordinator with
    | live _ _ _ outcome =>
      rw [he] at h
      cases outcome <;> simp only [isCutoff, he, Bool.false_eq_true] at hcut
      dsimp only at h
      dsimp only [Cdec]
      rw [hk]
      refine ⟨?_, h.2.2.2.2.2⟩
      intro r hr
      have hfilter := h.2.2.2.1
      rw [hfilter] at hr
      obtain ⟨hr, hs⟩ := List.mem_filter.mp hr
      obtain ⟨a, ha⟩ := List.mem_iff_get.mp hr
      have hs' : ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe rate rewards C_star C_h z r.input.time.val := of_decide_eq_true hs
      have hh := h.2.2.1 a
      rw [ha] at hh
      simpa only [← hh.1] using (hh.2 (hh.1 ▸ hs')).2.2
    | first _ => simp only [isCutoff, he, Bool.false_eq_true] at hcut
    | collection _ _ _ _ _ => simp only [isCutoff, he, Bool.false_eq_true] at hcut
    | dagger => simp only [isCutoff, he, Bool.false_eq_true] at hcut
    | invalidCollectionCutoff => simp only [isCutoff, he, Bool.false_eq_true] at hcut
  | first _ => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true] at hborn
  | live _ _ _ _ => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true] at hborn
  | dagger => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true] at hborn
  | invalidCollectionCutoff => simp only [birthPayload, hd, Option.isSome_none, Bool.false_eq_true] at hborn

open ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport
open ReferenceFirstReplacementCollectionAwaitedTaskSupport

/-- Support and domination on every original source, including empty selectors. -/
theorem rawK_support_and_charge (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (∀ r ∈ decoderSafePrefix rate rewards C_star C_h z (rawK rate rewards C_star C_h z),
      (Pnew rate rewards C_star C_h control0 r.input.time.val z).Nonempty) ∧
    Cdec rate rewards C_star C_h z ≤ ∑ n ∈ Finset.range p.T,
      if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0 := by
  by_cases hk : rawK rate rewards C_star C_h z = []
  · constructor
    · simp only [hk, decoderSafePrefix, List.takeWhile_nil, List.not_mem_nil, false_implies, implies_true]
    · simp only [Cdec, cappedCharge, hk, decoderSafePrefix, List.takeWhile_nil, List.map_nil, List.sum_nil]
      apply Finset.sum_nonneg
      intro n _
      split
      · exact (ReferenceFirstCollectionRoundEndObservation.g_mem_Icc rewards n z).1
      · exact le_refl _
  · have he := rawK_eq rate rewards C_star C_h z
    dsimp only at he
    split at he
    · exact (hk he).elim
    · rename_i birth hb
      split at he
      · rename_i hborn
        split at he
        · exact (hk he).elim
        · rename_i cut hc
          split at he
          · rename_i hcut
            exact reached_support rate rewards C_star C_h control0 z birth cut hb hborn hc hcut
          · exact (hk he).elim
      · exact (hk he).elim

/-- Exact domination by the new supported-date charge used by waiting. -/
theorem Cdec_le_supportedCharge (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Cdec rate rewards C_star C_h z ≤ ∑ n ∈ Finset.range p.T,
      if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0 :=
  (rawK_support_and_charge rate rewards C_star C_h control0 z).2

private theorem supported_record_mem_rawK
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (hP : (Pnew rate rewards C_star C_h control0 t.val z).Nonempty) :
    ∃ r ∈ rawK rate rewards C_star C_h z, r.input.time = t := by
  have h := complete_first_replacement_awaited_pending_localization
    rate rewards C_star C_h control0 z t.val hP
  unfold rawK
  dsimp only at h ⊢
  split at h
  · exact h.elim
  · rename_i birth hb
    rw [hb]
    dsimp only
    cases hd : birth.output.preparation.coordinator with
    | collection _ _ _ _ outcome =>
      rw [hd] at h
      cases outcome <;> try contradiction
      dsimp only [collectionInput] at h ⊢
      split at h
      · exact h.elim
      · rename_i cut hc
        rw [hc]
        dsimp only
        cases he : cut.output.preparation.coordinator with
        | live _ _ _ outcome =>
          rw [he] at h
          cases outcome <;> try contradiction
          dsimp only at h ⊢
          obtain ⟨a, _, ha, _⟩ := h
          exact ⟨_, List.get_mem _ a, Fin.ext ha⟩
        | first _ => simp only [he] at h
        | collection _ _ _ _ _ => simp only [he] at h
        | dagger => simp only [he] at h
        | invalidCollectionCutoff => simp only [he] at h
    | first _ => simp only [hd] at h
    | live _ _ _ _ => simp only [hd] at h
    | dagger => simp only [hd] at h
    | invalidCollectionCutoff => simp only [hd] at h

/-- A date is retained exactly when globally safe and supported by the same
actual first replacement assignment. -/
theorem literalDateKept_iff_safe_Pnew (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    literalCalendar rate rewards C_star C_h z t ↔
      Safe rate rewards C_star C_h z t.val ∧
      (Pnew rate rewards C_star C_h control0 t.val z).Nonempty := by
  have hord := (rawK_order rate rewards C_star C_h z).imp (fun h => Nat.le_of_lt h)
  constructor
  · rintro ⟨r, hr, ht⟩
    have hs := (mem_decoderSafePrefix_iff rate rewards C_star C_h z _ hord r).mp hr
    have hp := (rawK_support_and_charge rate rewards C_star C_h control0 z).1 r hr
    rw [ht] at hs hp
    exact ⟨hs.2, hp⟩
  · rintro ⟨hs, hp⟩
    obtain ⟨r, hr, ht⟩ := supported_record_mem_rawK rate rewards C_star C_h control0 z t hp
    refine ⟨r, (mem_decoderSafePrefix_iff rate rewards C_star C_h z _ hord r).mpr ⟨hr, ?_⟩, ht⟩
    simpa only [ht] using hs

/-- Each retained calendar event is Borel in the original continuous source. -/
theorem literalCalendar_borel (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      literalCalendar rate rewards C_star C_h z t} := by
  have he : {z : BootstrapPrivateRoundStreams.SourceInput p |
      literalCalendar rate rewards C_star C_h z t} =
      {z | ReferenceFirstCollectionLiteralStoppedCharge.noEarlierLiteralFailure rate rewards C_star C_h z t} ∩
      ⋃ i : Fin (p.m - 1), {z | i ∈ Pnew rate rewards C_star C_h control0 t.val z} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      literalDateKept_iff_safe_Pnew rate rewards C_star C_h control0,
      Safe, E, ReferenceFirstCollectionLiteralStoppedCharge.noEarlierLiteralFailure, Finset.Nonempty]
  rw [he]
  apply (ReferenceFirstCollectionLiteralStoppedCharge.noEarlierLiteralFailure_borel rate rewards C_star C_h t).inter
  apply MeasurableSet.iUnion
  intro i
  exact ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _) _
    (Pnew_mem_measurable rate rewards C_star C_h control0 t.val i)

/-- Exact finite-calendar reindexing, without any assumption on record-space
measurability. Each physical date contributes at most once. -/
theorem Cdec_eq_calendar_sum (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Cdec rate rewards C_star C_h z = ∑ t : Fin p.T,
      if literalCalendar rate rewards C_star C_h z t then
        (min p.m (positiveRewardCount rewards t) : ℝ) else 0 := by
  let D := decoderSafePrefix rate rewards C_star C_h z (rawK rate rewards C_star C_h z)
  let dates := D.map (fun r => r.input.time)
  let weight : Fin p.T → ℝ := fun t => min p.m (positiveRewardCount rewards t)
  have hD : D.Pairwise (fun a b => a.input.time.val < b.input.time.val) :=
    (rawK_order rate rewards C_star C_h z).sublist (List.takeWhile_sublist _)
  have hnodup : dates.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    apply List.pairwise_map.mpr
    exact hD.imp (fun h he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  have he (t : Fin p.T) : t ∈ dates.toFinset ↔ literalCalendar rate rewards C_star C_h z t := by
    simp only [dates, List.mem_toFinset, List.mem_map, literalCalendar, D]
  calc
    Cdec rate rewards C_star C_h z = (dates.map weight).sum := by
      simp only [Cdec, cappedCharge, dates, weight, D, List.map_map, Function.comp_def]
    _ = ∑ t ∈ dates.toFinset, weight t := (List.sum_toFinset weight hnodup).symm
    _ = ∑ t : Fin p.T, if t ∈ dates.toFinset then weight t else 0 :=
      (Finset.sum_ite_mem_eq dates.toFinset weight).symm
    _ = _ := by simp only [he, weight]

/-- Borel measurability follows from the exact supported-date characterization. -/
theorem Cdec_measurable (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (Cdec rate rewards C_star C_h) := by
  have he : Cdec rate rewards C_star C_h = fun z => ∑ t : Fin p.T,
      if literalCalendar rate rewards C_star C_h z t then
        (min p.m (positiveRewardCount rewards t) : ℝ) else 0 := by
    funext z
    exact Cdec_eq_calendar_sum rate rewards C_star C_h z
  rw [he]
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite (literalCalendar_borel rate rewards C_star C_h control0 t)
    measurable_const measurable_const

/-- A deterministic bound on the original literal capped charge. -/
theorem Cdec_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ Cdec rate rewards C_star C_h z ∧
      Cdec rate rewards C_star C_h z ≤ (p.m : ℝ) * p.T := by
  rw [Cdec_eq_calendar_sum]
  constructor
  · apply Finset.sum_nonneg
    intro t _
    split
    · exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_refl _
  · calc
      _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        split
        · exact min_le_left _ _
        · exact Nat.cast_nonneg _
      _ = (p.m : ℝ) * p.T := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_comm]

private theorem takeWhile_boundary {α : Type*} (test : α → Bool) (R : List α)
    (r : α) (hr : R[(R.takeWhile test).length]? = some r) : test r = false := by
  induction R with
  | nil => simp only [List.takeWhile_nil, List.length_nil, List.getElem?_nil] at hr; contradiction
  | cons q R ih =>
    cases ht : test q with
    | false =>
      simp only [List.takeWhile_cons, ht, Bool.false_eq_true, ↓reduceIte, List.length_nil,
        List.getElem?_cons_zero, Option.some.injEq] at hr
      exact hr ▸ ht
    | true =>
      apply ih
      simpa only [List.takeWhile_cons, ht, ↓reduceIte, List.length_cons,
        List.getElem?_cons_succ] using hr

private theorem drop_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.drop j = r :: R.drop (j + 1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hr
  simpa only [he] using List.drop_eq_getElem_cons hj

private theorem take_of_prefix {α : Type*} (A B : List α) (h : A <+: B) :
    B.take A.length = A := by
  obtain ⟨C, rfl⟩ := h
  exact List.take_left

/-- The initial collection endpoint cannot conceal a non-birth constructor.
If no endpoint record remains, the first live or collection window has consumed
the entire suffix, including empty initialization/terminal suffixes. -/
theorem birth_endpoint (R : List (Record (rate := rate))) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    v ≤ R.length ∧
      (R[v]? = none → v = R.length ∧
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R = R ∨
          w < R.length ∧ ReferenceCollectionPhaseHistory.collectionWindow R w = R.drop w)) ∧
      (∀ birth, R[v]? = some birth → (birthPayload birth).isSome = true) := by
  let A := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R
  let w := A.length
  let W := (R.drop (w + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  have hwle : w ≤ R.length := (List.takeWhile_prefix _).length_le
  by_cases hw : w < R.length
  · let cut := R[w]'hw
    have hc : R[w]? = some cut := List.getElem?_eq_getElem hw
    have hC : ReferenceCollectionPhaseHistory.collectionWindow R w = cut :: W := by
      unfold ReferenceCollectionPhaseHistory.collectionWindow
      rw [drop_lookup R w cut hc]
      rfl
    have hW : W.length ≤ R.length - (w + 1) := by
      simpa only [List.length_drop] using
        (show W <+: R.drop (w + 1) from List.takeWhile_prefix _).length_le
    have hvle : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length ≤ R.length := by
      rw [hC, List.length_cons]
      omega
    refine ⟨hvle, ?_, ?_⟩
    · intro hn
      change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = none at hn
      have hv : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length = R.length := by
        have h := List.getElem?_eq_none_iff.mp hn
        omega
      refine ⟨hv, Or.inr ⟨hw, ?_⟩⟩
      have hp := ReferenceFirstReplacementCollectionPendingFoundation.collection_prefix R w cut hc
      change cut :: W <+: R.drop w at hp
      have hlen : (cut :: W).length = (R.drop w).length := by
        rw [List.length_drop]
        rw [hC] at hv
        omega
      rw [hC]
      exact hp.eq_of_length hlen
    · intro birth hb
      change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some birth at hb
      rw [birthPayload_isSome]
      have hg : (R.drop (w + 1))[W.length]? = some birth := by
        rw [List.getElem?_drop]
        rw [hC, List.length_cons] at hb
        convert hb using 1; congr 1; omega
      have ht := takeWhile_boundary
        (fun r : Record (rate := rate) => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        (R.drop (w + 1)) birth hg
      simpa only [Bool.not_eq_false'] using ht
  · have hwEq : w = R.length := by omega
    have hA : A = R := by
      have ht := take_of_prefix A R (List.takeWhile_prefix _)
      change R.take w = A at ht
      rw [hwEq, List.take_length] at ht
      exact ht.symm
    have hC : ReferenceCollectionPhaseHistory.collectionWindow R w = [] := by
      simp only [ReferenceCollectionPhaseHistory.collectionWindow, hwEq, List.drop_length,
        List.take_nil, List.drop_eq_nil_of_le (by omega : R.length ≤ R.length + 1),
        List.takeWhile_nil, List.append_nil]
    have hv : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length = R.length := by
      rw [hC, List.length_nil, Nat.add_zero, hwEq]
    refine ⟨by rw [hv], fun _ => ⟨hv, Or.inl hA⟩, ?_⟩
    intro birth hb
    change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some birth at hb
    rw [hv, List.getElem?_length] at hb
    contradiction

private def LiveFrame (payload : ReferenceActivePhysicalStep.Payload rate) (state : State p rate) : Prop :=
  state.coordinator = .dagger ∨ ∃ registers owned base,
    state.coordinator = .live registers owned base ∧ registers.payload = payload

private theorem birth_output_frame (birth : Record (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (hb : birthPayload birth = some payload) :
    LiveFrame rate payload birth.output.next := by
  have hout : birth.output.next.coordinator =
      birth.output.preparation.observeCoordinator.configuration := by rw [birth.output_eq]; rfl
  cases hd : birth.output.preparation.coordinator with
  | collection old ledger clock cutoff outcome =>
    cases outcome <;> simp only [birthPayload, hd] at hb <;> try contradiction
    rename_i core consistent started hstart instruction hi output hcons data installed selected
    have hp : installed.registers.payload = payload := Option.some.inj hb
    unfold LiveFrame
    rw [hout, observeCoordinator_collection_equation _ _ _ _ _ _ hd]
    split
    · exact Or.inl rfl
    · rcases ReferenceFirstLiveConfirmationHistory.livePostChoice_frame
        birth.input birth.output.preparation installed.registers installed.ownedRegisters
        installed.retainedBaseScore started with hf | ⟨next, owned, hf, hpay, _⟩
      · exact Or.inl hf
      · exact Or.inr ⟨next, owned, installed.retainedBaseScore, hf, hpay.trans hp⟩
  | first _ => simp only [birthPayload, hd] at hb; contradiction
  | live _ _ _ _ => simp only [birthPayload, hd] at hb; contradiction
  | dagger => simp only [birthPayload, hd] at hb; contradiction
  | invalidCollectionCutoff => simp only [birthPayload, hd] at hb; contradiction

private theorem actual_live_dispatch (r : Record (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers) (base : Fin (p.m - 1) → ℕ)
    (hs : r.input.state.coordinator = .live registers owned base) :
    r.output.preparation.coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base)) := by
  rw [preparation_eq]
  change dispatch r.input = _
  simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch]
  rfl

private theorem continuing_output_frame (r : Record (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (hin : LiveFrame rate payload r.input.state)
    (hcont : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true) :
    LiveFrame rate payload r.output.next := by
  rcases hin with hdagger | ⟨registers, owned, base, hs, hp⟩
  · exact Or.inl (by rw [r.output_eq]; exact (step_coordinator_dagger r.input hdagger).1)
  · have hd := actual_live_dispatch rate r registers owned base hs
    have hout : r.output.next.coordinator =
        r.output.preparation.observeCoordinator.configuration := by rw [r.output_eq]; rfl
    unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen at hcont
    rw [hd] at hcont
    rw [observeCoordinator_live_equation _ _ _ _ _ hd] at hout
    cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) <;>
      simp only [ho, Bool.false_eq_true] at hcont
    rename_i dispatched hstart continuation selected
    rw [ho] at hout
    split at hout
    · exact Or.inl hout
    · rcases ReferenceFirstLiveConfirmationHistory.livePostChoice_frame r.input r.output.preparation
        (liveRegistersAt registers r.input.time) (liveOwnedAt registers owned r.input.time)
        base dispatched.startResult with hf | ⟨next, q, hf, hpay, _⟩
      · exact Or.inl (hout.trans hf)
      · exact Or.inr ⟨next, q, base, hout.trans hf, hpay.trans hp⟩

private theorem connected_continuing_frame (R : List (Record (rate := rate)))
    (initial final : State p rate) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial R final)
    (hin : LiveFrame rate payload initial)
    (hcont : ∀ r ∈ R, ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true) :
    LiveFrame rate payload final := by
  induction R generalizing initial with
  | nil => change final = initial at hchain; exact hchain ▸ hin
  | cons r R ih =>
    obtain ⟨hr, ht⟩ := hchain
    apply ih r.output.next ht
    · apply continuing_output_frame rate r payload
      · exact hr ▸ hin
      · exact hcont r (List.mem_cons_self ..)
    · exact fun q hq => hcont q (List.mem_cons_of_mem r hq)

private theorem noncontinuing_noncutoff_dagger (r : Record (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (hin : LiveFrame rate payload r.input.state)
    (hcont : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = false)
    (hcut : isCutoff r = false) : r.output.next.coordinator = .dagger := by
  rcases hin with hd | ⟨registers, owned, base, hs, _⟩
  · rw [r.output_eq]
    exact (step_coordinator_dagger r.input hd).1
  · have he := actual_live_dispatch rate r registers owned base hs
    have hout : r.output.next.coordinator =
        r.output.preparation.observeCoordinator.configuration := by rw [r.output_eq]; rfl
    unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen at hcont
    unfold isCutoff at hcut
    rw [he] at hcont hcut
    rw [observeCoordinator_live_equation _ _ _ _ _ he] at hout
    cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) <;>
      simp only [ho, Bool.true_eq_false] at hcont hcut
    all_goals rw [ho] at hout; split at hout <;> exact hout

private theorem continuing_not_cutoff (r : Record (rate := rate))
    (h : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true) : isCutoff r = false := by
  unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen at h
  unfold isCutoff
  cases hd : r.output.preparation.coordinator with
  | live _ _ _ outcome => cases outcome <;> simp_all only [Bool.false_eq_true]
  | first _ => simp only [hd, Bool.false_eq_true] at h
  | collection _ _ _ _ _ => simp only [hd, Bool.false_eq_true] at h
  | dagger => simp only [hd, Bool.false_eq_true] at h
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at h

private theorem dagger_not_cutoff (r : Record (rate := rate))
    (hs : r.input.state.coordinator = .dagger) : isCutoff r = false := by
  unfold isCutoff
  rw [preparation_eq]
  rw [(prepare r.input).coordinator_eq, dispatch_dagger r.input hs]

/-- Actual physical absence and endpoint characterization for the search after
the same installed birth. The first noncontinuing record has the same payload
or an incoming dagger. If it is not the cutoff, it enters absorbing dagger;
no subsequent physical date can hide a cutoff of this assignment. -/
theorem replacement_search_endpoint (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    ∀ (birth : Record (rate := rate)) (payload : ReferenceActivePhysicalStep.Payload rate),
      R[v]? = some birth → birthPayload birth = some payload →
      c ≤ R.length ∧
      (R[c]? = none → c = R.length ∧ tail = R.drop (v + 1) ∧
        ∀ r ∈ R.drop (v + 1), isCutoff r = false) ∧
      (∀ cut, R[c]? = some cut →
        (cut.input.state.coordinator = .dagger ∨
          ∃ registers owned base, cut.input.state.coordinator = .live registers owned base ∧
            registers.payload = payload) ∧
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen cut = false ∧
        (isCutoff cut = false → cut.output.next.coordinator = .dagger ∧
          ∀ r ∈ R.drop (c + 1), r.input.state.coordinator = .dagger ∧ isCutoff r = false)) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  let c := v + 1 + tail.length
  intro birth payload hb hp
  change R[v]? = some birth at hb
  have hv : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have htail : tail <+: R.drop (v + 1) := List.takeWhile_prefix _
  have htailLen : tail.length ≤ R.length - (v + 1) := by
    simpa only [List.length_drop] using htail.length_le
  have hcle : c ≤ R.length := by dsimp only [c]; omega
  refine ⟨hcle, ?_, ?_⟩
  · intro hn
    change R[c]? = none at hn
    have hc : c = R.length := by
      have hh := List.getElem?_eq_none_iff.mp hn
      omega
    have ht : tail = R.drop (v + 1) := by
      apply htail.eq_of_length
      simp only [List.length_drop]
      dsimp only [c] at hc
      omega
    refine ⟨hc, ht, ?_⟩
    intro r hr
    rw [← ht] at hr
    exact continuing_not_cutoff rate r
      (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem R v r hr)
  · intro cut hc
    change R[c]? = some cut at hc
    have hlookup : (R.drop (v + 1))[tail.length]? = some cut := by
      rw [List.getElem?_drop]
      exact hc
    have hnoncont : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen cut = false :=
      takeWhile_boundary ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
        (R.drop (v + 1)) cut hlookup
    have hframe : LiveFrame rate payload cut.input.state := by
      cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
      | none =>
        have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
          rate z rewards C_star C_h hl
        have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
        change R.length = _ at hlen
        rw [hs, Nat.sub_self] at hlen
        omega
      | some active =>
        have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate z rewards C_star C_h active hl
        have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output hchain v hv
        rw [(List.getElem?_eq_some_iff.mp hb).2] at hdrop
        have hidx := (List.getElem?_eq_some_iff.mp hlookup).1
        have htake := ReferenceFollowerReplyChronology.connected_take_to_input hdrop tail.length hidx
        rw [(List.getElem?_eq_some_iff.mp hlookup).2] at htake
        rw [take_of_prefix tail (R.drop (v + 1)) htail] at htake
        exact connected_continuing_frame rate tail birth.output.next cut.input.state payload htake
          (birth_output_frame rate birth payload hp)
          (fun r hr => ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem R v r hr)
    refine ⟨hframe, hnoncont, ?_⟩
    intro hcut
    have hdagger := noncontinuing_noncutoff_dagger rate cut payload hframe hnoncont hcut
    refine ⟨hdagger, ?_⟩
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none =>
      have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hl
      have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
      change R.length = _ at hlen
      rw [hs, Nat.sub_self] at hlen
      omega
    | some active =>
      have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate z rewards C_star C_h active hl
      have hcLt := (List.getElem?_eq_some_iff.mp hc).1
      have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output hchain c hcLt
      rw [(List.getElem?_eq_some_iff.mp hc).2] at hdrop
      have habsorb := (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hdrop hdagger).2
      intro r hr
      have hd := habsorb r hr
      exact ⟨hd, dagger_not_cutoff rate r hd⟩

/-- Honest empty-search alternatives. The birth endpoint is always an actual
later-chosen birth when present; the remaining two alternatives are characterized
physically by `replacement_search_endpoint`, including absorbing failure. -/
theorem rawK_absence_cases (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    rawK rate rewards C_star C_h z = [] ↔
      R[v]? = none ∨ ∃ birth payload, R[v]? = some birth ∧ birthPayload birth = some payload ∧
        (R[c]? = none ∨ ∃ cut, R[c]? = some cut ∧ isCutoff cut = false) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  have hborn := (birth_endpoint rate R).2.2
  rw [rawK_eq]
  cases hb : R[v]? with
  | none => simp only [reduceCtorEq, false_and, exists_false, true_or]
  | some birth =>
    have htag : (birthPayload birth).isSome = true := hborn birth hb
    obtain ⟨payload, hp⟩ : ∃ payload, birthPayload birth = some payload := by
      cases he : birthPayload birth with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at htag
      | some payload => exact ⟨payload, rfl⟩
    cases hc : R[c]? with
    | none => simp [hp]
    | some cut => cases hd : isCutoff cut <;> simp [hp, hd]

/-- Exhausted initialization and a terminal launch both have no suffix dates. -/
theorem rawK_of_terminal_start (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    rawK rate rewards C_star C_h z = [] := by
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  rw [hs, Nat.sub_self] at hlen
  have hR := List.length_eq_zero_iff.mp hlen
  have hsub := rawK_sublist rate rewards C_star C_h z
  rw [hR] at hsub
  exact List.sublist_nil.mp hsub

/-- A launch that never occurs contributes no physical suffix or replacement
collection; the generated initialization history is not repurposed as a birth. -/
theorem rawK_of_no_launch (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none) :
    rawK rate rewards C_star C_h z = [] :=
  rawK_of_terminal_start rate rewards C_star C_h z
    (ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T rate z rewards C_star C_h hl)

open ReferenceCollectionSegmentExtraction

/-- The selected raw list has the same complete checked execution, installed
payload, initialized ledger, original rows and dates, and next-birth/horizon
endpoint as the accepted literal construction. No analytical clipping is applied
to this physical stream. The absent branches are characterized above. -/
theorem rawK_reached_execution (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := rawK rate rewards C_star C_h z
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut => match cut.output.preparation.coordinator with
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            K = cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) ∧
            (∃ (stream : Segment rate) (initializer : Initializer p),
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
                  ReferenceFirstReplacementCollectionRawPendingTotal.ledgerContext cr.final =
                    ReferenceFirstReplacementCollectionRawPendingTotal.ledgerContext stream.context.preLedger) ∧
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
                    ledger.pending = ∅)
          | _ => True
      | _ => True := by
  have h := complete_first_replacement_literal_decoder_safe_support_and_charge
    rate rewards C_star C_h control0 z
  dsimp only at h ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at h ⊢
    cases hd : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hd] at h
      cases outcome <;> try trivial
      dsimp only [collectionInput] at h ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at h ⊢
        cases he : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live _ _ _ outcome =>
          rw [he] at h
          cases outcome <;> try trivial
          dsimp only at h ⊢
          dsimp only [R, w, v, c] at hb hc
          have hk := rawK_eq rate rewards C_star C_h z
          simp only [hb, birthPayload, hd, hc, isCutoff, he, ↓reduceIte] at hk
          refine ⟨hk, ?_⟩
          rw [hk]
          exact h.1

end Bandits.Support.ReferenceFirstReplacementCollectionGlobalDecoderCharge
