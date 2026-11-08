/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCompositeQuota

/-!
# First replacement: strict-past awaited support on the original calendar

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-240,354-431`,
`06_interruptions.tex:110-177,246-296,425-437,459-487`, and
`appendix_a_local_protocol.tex:8-85,92-108,141-157`.

The safety support below retains a detecting update. Its physical-failure
predicate is not identified with source all-arm overflow. The service reads
unmasked actual observations, including inherited decoder banks.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceFirstReplacementCollectionPendingFoundation
open ReferenceFirstReplacementCollectionOldDownCallDates
open ReferenceFirstReplacementCollectionStoppedPureUpQuota
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedTaskSupport

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

variable (rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- The actual physical/original-UP event at one unchanged source date. -/
def stopAt (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source (p := p)) : Prop :=
  ∃ r, actualRecord rate rewards C_star C_h t z = some r ∧
    (physicalFailureAt r ∨
      ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
        (rate := rate) rewards C_star C_h control0 z i t)

/-- Scan only completed dates at or after the same one-based onset. -/
def pastStopFlag (u n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Bool :=
  decide (∃ t : Fin p.T, t.val < n ∧ u ≤ t.val + 1 ∧
    stopAt rate rewards C_star C_h control0 i t z)

/-- New decoder-faithful support, distinct from the previous common-stop support. -/
def Pnew (n : ℕ) (z : Source (p := p)) : Finset (Fin (p.m - 1)) :=
  (Praw rate rewards C_star C_h n z).filter fun i =>
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n z = false ∧
    match payloadOnset rate rewards C_star C_h n z with
    | none => False
    | some (_, u) => pastStopFlag rate rewards C_star C_h control0 u n i z = false

/-- Exact membership with the literal strict-past failure mask. -/
theorem mem_Pnew_iff (n : ℕ) (z : Source (p := p)) (i : Fin (p.m - 1)) :
    i ∈ Pnew rate rewards C_star C_h control0 n z ↔
      i ∈ Praw rate rewards C_star C_h n z ∧
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n z = false ∧
      ∃ payload u, payloadOnset rate rewards C_star C_h n z = some (payload, u) ∧
        ¬ ∃ t : Fin p.T, t.val < n ∧ u ≤ t.val + 1 ∧
          ∃ r, actualRecord rate rewards C_star C_h t z = some r ∧
            (physicalFailureAt r ∨
              ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
                (rate := rate) rewards C_star C_h control0 z i t) := by
  cases ho : payloadOnset rate rewards C_star C_h n z with
  | none => simp [Pnew, ho]
  | some pair =>
      rcases pair with ⟨payload, u⟩
      simp only [Pnew, Finset.mem_filter, ho, pastStopFlag, decide_eq_false_iff_not]
      simp only [stopAt]
      simp

theorem Pnew_subset_Praw (n : ℕ) (z : Source (p := p)) :
    Pnew rate rewards C_star C_h control0 n z ⊆ Praw rate rewards C_star C_h n z :=
  Finset.filter_subset _ _

@[simp] theorem Pnew_of_onset_none (n : ℕ) (z : Source (p := p))
    (h : payloadOnset rate rewards C_star C_h n z = none) :
    Pnew rate rewards C_star C_h control0 n z = ∅ := by
  simp [Pnew, h]

@[simp] theorem Pnew_of_horizon_le (n : ℕ) (hn : p.T ≤ n) (z : Source (p := p)) :
    Pnew rate rewards C_star C_h control0 n z = ∅ := by
  simp only [Pnew, Praw_of_horizon_le rate rewards C_star C_h n hn z,
    Finset.filter_empty]

/-- A literal original UP event has its actual record on the same launch stratum. -/
private theorem up_event_record (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source (p := p))
    (h : ReferenceFirstReplacementCollectionCommonStopObservation.U
      rate rewards C_star C_h control0 i t z) :
    ∃ r, actualRecord rate rewards C_star C_h t z = some r := by
  obtain ⟨q, s, hs, hz, _⟩ := h
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s :=
    hz.2.2
  have hl := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q t s hs control0 i ⟨z, hz⟩
  have hle : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val :=
    hstart ▸ hs
  rw [actualRecord_on_launch rate rewards C_star C_h t z _ hl hle]
  exact ⟨_, rfl⟩

private theorem stopAt_iff (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source (p := p)) :
    stopAt rate rewards C_star C_h control0 i t z ↔
      (∃ r, actualRecord rate rewards C_star C_h t z = some r ∧ physicalFailureAt r) ∨
      ReferenceFirstReplacementCollectionCommonStopObservation.U
        rate rewards C_star C_h control0 i t z := by
  constructor
  · rintro ⟨r, hr, hf | hu⟩
    · exact Or.inl ⟨r, hr, hf⟩
    · exact Or.inr hu
  · rintro (⟨r, hr, hf⟩ | hu)
    · exact ⟨r, hr, Or.inl hf⟩
    · obtain ⟨r, hr⟩ := up_event_record rate rewards C_star C_h control0 i t z hu
      exact ⟨r, hr, Or.inr hu⟩

/-- Only accepted record-code reconstruction is needed for physical failures. -/
private theorem physical_event_factor (n : ℕ) (t : Fin p.T) (ht : t.val < n)
    (z : Source (p := p)) :
    (∃ r, actualRecord rate rewards C_star C_h t z = some r ∧ physicalFailureAt r) ↔
      ∃ r, actualRecord rate rewards C_star C_h t (sourcePrefix control0 n z) = some r ∧
        physicalFailureAt r := by
  have hcode := ReferenceFirstReplacementCollectionCommonStopObservation.actualRecordCode_factor
    rate rewards C_star C_h control0 n t ht z
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none =>
      cases hr' : actualRecord rate rewards C_star C_h t (sourcePrefix control0 n z) with
      | none => simp
      | some r' => simp [hr, hr'] at hcode
  | some r =>
      cases hr' : actualRecord rate rewards C_star C_h t (sourcePrefix control0 n z) with
      | none => simp [hr, hr'] at hcode
      | some r' =>
          have he : ReferenceActiveHorizonMeasurability.roundRecordCode r =
              ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
            simpa only [hr, hr', Option.map_some, Option.some.injEq] using hcode
          have hrec := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r
          have hrec' := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r'
          have hc : r.output.coordinator = r'.output.coordinator :=
            hrec.2.1.symm.trans (he ▸ hrec'.2.1)
          have hf : r.output.followers = r'.output.followers := by
            funext k
            exact (hrec.2.2.1 k).symm.trans (he ▸ hrec'.2.2.1 k)
          simp only [Option.some.injEq, exists_eq_left', physicalFailureAt, hc, hf]

/-- Exact strict-past factorization; the original UP event retains its own launch strata. -/
theorem pastStopFlag_factor (u n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    pastStopFlag rate rewards C_star C_h control0 u n i z =
      pastStopFlag rate rewards C_star C_h control0 u n i (sourcePrefix control0 n z) := by
  have hstop : ∀ t : Fin p.T, t.val < n →
      (stopAt rate rewards C_star C_h control0 i t z ↔
        stopAt rate rewards C_star C_h control0 i t (sourcePrefix control0 n z)) := by
    intro t ht
    rw [stopAt_iff, stopAt_iff]
    apply or_congr (physical_event_factor rate rewards C_star C_h control0 n t ht z)
    have h := ReferenceFirstReplacementCollectionCommonStopObservation.U_factor
      rate rewards C_star C_h control0 i t (sourcePrefix control0 n z)
    rw [sourcePrefix_sourcePrefix control0 (t.val + 1) n (by omega)] at h
    exact (ReferenceFirstReplacementCollectionCommonStopObservation.U_factor
      rate rewards C_star C_h control0 i t z).trans h.symm
  unfold pastStopFlag
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨t, ht, hu, h⟩
    exact ⟨t, ht, hu, (hstop t ht).mp h⟩
  · rintro ⟨t, ht, hu, h⟩
    exact ⟨t, ht, hu, (hstop t ht).mpr h⟩

private theorem stopAt_borel (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : Source (p := p) | stopAt rate rewards C_star C_h control0 i t z} := by
  have heq : {z : Source (p := p) | stopAt rate rewards C_star C_h control0 i t z} =
      {z | ∃ r, actualRecord rate rewards C_star C_h t z = some r ∧ physicalFailureAt r} ∪
      {z | ReferenceFirstReplacementCollectionCommonStopObservation.U
        rate rewards C_star C_h control0 i t z} := by
    ext z
    exact stopAt_iff rate rewards C_star C_h control0 i t z
  rw [heq]
  exact (ReferenceFirstReplacementCollectionCommonStopObservation.actualPhysicalFailure_borel
    rate rewards C_star C_h t).union
      (ReferenceFirstReplacementCollectionCommonStopObservation.U_borel
        rate rewards C_star C_h control0 i t)

/-- The literal finite strict-past flag is adapted on every natural date. -/
theorem pastStopFlag_adapted (u n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[sourcePrefixFiltration control0 (n + 1)]
      (pastStopFlag rate rewards C_star C_h control0 u n i) := by
  have hm : Measurable (pastStopFlag rate rewards C_star C_h control0 u n i) := by
    apply measurable_to_bool
    change MeasurableSet {z : Source (p := p) |
      pastStopFlag rate rewards C_star C_h control0 u n i z = true}
    simp only [pastStopFlag, decide_eq_true_eq, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro t
    by_cases ht : t.val < n
    · by_cases hu : u ≤ t.val + 1
      · simpa only [ht, hu, true_and] using stopAt_borel rate rewards C_star C_h control0 i t
      · simp [hu]
    · simp [ht]
  have he : pastStopFlag rate rewards C_star C_h control0 u n i =
      pastStopFlag rate rewards C_star C_h control0 u n i ∘ sourcePrefix control0 n := by
    funext z
    exact pastStopFlag_factor rate rewards C_star C_h control0 u n i z
  rw [he, sourcePrefixFiltration_succ, measurable_iff_comap_le, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hm.comap_le

/-- Mask monotonicity is asserted with the same onset, not across an incoming reset. -/
theorem pastStopFlag_mono (u a b : ℕ) (hab : a ≤ b) (i : Fin (p.m - 1))
    (z : Source (p := p)) :
    pastStopFlag rate rewards C_star C_h control0 u a i z = true →
      pastStopFlag rate rewards C_star C_h control0 u b i z = true := by
  simp only [pastStopFlag, decide_eq_true_eq]
  rintro ⟨t, ht, hu, h⟩
  exact ⟨t, ht.trans_le hab, hu, h⟩

/-- Membership is adapted in the original continuous prefix filtration. -/
theorem Pnew_mem_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | i ∈ Pnew rate rewards C_star C_h control0 n z} := by
  have heq : {z : Source (p := p) | i ∈ Pnew rate rewards C_star C_h control0 n z} =
      {z | i ∈ Praw rate rewards C_star C_h n z} ∩
      ({z | ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n z = false} ∩
      ⋃ b : ℕ, ⋃ u : ℕ,
        {z | pendingCode rate rewards C_star C_h n z = some (b, u)} ∩
        {z | pastStopFlag rate rewards C_star C_h control0 u n i z = false}) := by
    ext z
    simp only [Pnew, Finset.mem_filter, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      pendingCode_eq]
    cases ho : payloadOnset rate rewards C_star C_h n z with
    | none => simp
    | some pair => rcases pair with ⟨payload, u⟩; simp
  rw [heq]
  have hraw := (Praw_measurable rate rewards C_star C_h control0 n)
    (Set.to_countable {s : Finset (Fin (p.m - 1)) | i ∈ s}).measurableSet
  exact hraw.inter ((measurableSet_eq_fun
    (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_adapted
      rate rewards C_star C_h control0 n) measurable_const).inter
    (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun u =>
      ((pendingCode_measurable rate rewards C_star C_h control0 n)
        (measurableSet_singleton (some (b, u)))).inter
      (measurableSet_eq_fun (pastStopFlag_adapted rate rewards C_star C_h control0 u n i)
        measurable_const)))

/-- Actual strict-past factorization of the complete support. -/
theorem Pnew_factor (n : ℕ) (z : Source (p := p)) :
    Pnew rate rewards C_star C_h control0 n z =
      Pnew rate rewards C_star C_h control0 n (sourcePrefix control0 n z) := by
  ext i
  have h := Pnew_mem_measurable rate rewards C_star C_h control0 n i
  rw [sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  change z ∈ {z | i ∈ Pnew rate rewards C_star C_h control0 n z} ↔
    sourcePrefix control0 n z ∈ {z | i ∈ Pnew rate rewards C_star C_h control0 n z}
  rw [← he]
  change sourcePrefix control0 n z ∈ B ↔
    sourcePrefix control0 n (sourcePrefix control0 n z) ∈ B
  rw [sourcePrefix_sourcePrefix control0 n n le_rfl]

-- Reconstruct the raw scan converse locally: the old masked-support converse
-- does not apply to the newly admitted dates.
variable {rate rewards C_star C_h control0}

open ReferenceActivePhysicalStep
open ReferenceFirstReplacementLiveFollowerPrefix
open _root_.Bandits.Support.ReferenceCollectionPhaseHistory hiding Record

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

/-- Nonempty new support belongs to the same actual first replacement birth,
cutoff and installed payload. All absent branches are excluded by the actual scan. -/
theorem complete_first_replacement_awaited_pending_localization
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ),
    (Pnew rate rewards C_star C_h control0 n z).Nonempty →
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


/-- OLD and current-reply FORMED cannot hold in the same physical choice. -/
theorem actualOldAt_not_replyFormedAt (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    actualOldAt r i M → ¬ replyFormedAt r i M := by
  rintro ⟨state, memory, hc, _hs, hne⟩ ⟨other, otherMemory, hd, _ht, he⟩
  have hstate := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans hd)).1
  subst other
  exact hne he

/-- Unmasked OLD and FORMED service from the very same actual record and payload. -/
def recordServiceParts (r : Record (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) : ℕ × ℕ :=
  (if actualOldAt r i (payload.downRecord i) then
      ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive r i else 0,
    if replyFormedAt r i (payload.downRecord i) then
      ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive r i else 0)

/-- The sum is binary by the actual configuration, with no clipping or success test. -/
theorem recordServiceParts_sum_le_one (r : Record (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    (recordServiceParts r payload i).1 + (recordServiceParts r payload i).2 ≤ 1 := by
  have hd := ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive_le_one r i
  have hu := ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive_le_one r i
  by_cases ho : actualOldAt r i (payload.downRecord i)
  · have hf := actualOldAt_not_replyFormedAt r i (payload.downRecord i) ho
    simpa only [recordServiceParts, ite_eq_left ho, ite_eq_right hf, Nat.add_zero] using hd
  · simp only [recordServiceParts, ite_eq_right ho, Nat.zero_add]
    split_ifs <;> omega

variable (rate rewards C_star C_h control0)

/-- Literal natural-date contributions on the new support. Every absent or
terminal branch contributes zero; saved UP entries keep their actual content. -/
def serviceParts (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) : ℕ × ℕ :=
  if i ∈ Pnew rate rewards C_star C_h control0 n z then
    if hn : n < p.T then
      match payloadOnset rate rewards C_star C_h n z,
        actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
      | some (payload, _), some r => recordServiceParts r payload i
      | _, _ => (0, 0)
    else (0, 0)
  else (0, 0)

/-- Inclusive task service; the two physical stages are added without clipping. -/
def service (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) : ℕ :=
  (serviceParts rate rewards C_star C_h control0 i n z).1 +
    (serviceParts rate rewards C_star C_h control0 i n z).2

/-- New binary readout, using the new support and the unmasked actual contributions. -/
def x (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) : Bool :=
  decide (0 < service rate rewards C_star C_h control0 i n z)

/-- OLD positive natural dates through the physical horizon. -/
def oldPositiveDates (i : Fin (p.m - 1)) (z : Source (p := p)) : Finset ℕ :=
  (Finset.range p.T).filter fun n => 0 < (serviceParts rate rewards C_star C_h control0 i n z).1

/-- FORMED positives include the actual saved UP entry, with no receiver-success test. -/
def formedPositiveDates (i : Fin (p.m - 1)) (z : Source (p := p)) : Finset ℕ :=
  (Finset.range p.T).filter fun n => 0 < (serviceParts rate rewards C_star C_h control0 i n z).2

/-- Positive dates of the new binary service on the same natural calendar. -/
def servicePositiveDates (i : Fin (p.m - 1)) (z : Source (p := p)) : Finset ℕ :=
  (Finset.range p.T).filter fun n => x rate rewards C_star C_h control0 i n z = true

@[simp] theorem serviceParts_of_not_mem (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p))
    (hi : i ∉ Pnew rate rewards C_star C_h control0 n z) :
    serviceParts rate rewards C_star C_h control0 i n z = (0, 0) := by
  simp only [serviceParts, ite_eq_right hi]

@[simp] theorem serviceParts_of_horizon_le (i : Fin (p.m - 1)) (n : ℕ) (hn : p.T ≤ n)
    (z : Source (p := p)) : serviceParts rate rewards C_star C_h control0 i n z = (0, 0) := by
  simp only [serviceParts, Pnew_of_horizon_le rate rewards C_star C_h control0 n hn z,
    Finset.notMem_empty, ↓reduceIte]

/-- At a retained record the definition reads the same actual payload and both stages. -/
theorem serviceParts_at_record (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source (p := p))
    (payload : ReferenceActivePhysicalStep.Payload rate) (u : ℕ) (r : Record (rate := rate))
    (hi : i ∈ Pnew rate rewards C_star C_h control0 t.val z)
    (hp : payloadOnset rate rewards C_star C_h t.val z = some (payload, u))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    serviceParts rate rewards C_star C_h control0 i t.val z = recordServiceParts r payload i := by
  simp only [serviceParts, ite_eq_left hi, dite_eq_left t.isLt, hp, hr]

theorem service_le_one (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) :
    service rate rewards C_star C_h control0 i n z ≤ 1 := by
  unfold service serviceParts
  split_ifs
  · split
    · exact recordServiceParts_sum_le_one _ _ _
    · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The Boolean readout equals the literal unmasked sum, rather than clipping it. -/
theorem service_eq_indicator (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) :
    service rate rewards C_star C_h control0 i n z =
      if x rate rewards C_star C_h control0 i n z then 1 else 0 := by
  have h := service_le_one rate rewards C_star C_h control0 i n z
  simp only [x, decide_eq_true_eq]
  split_ifs <;> omega

/-- Every positive new service is supported; no larger-support old service is used. -/
theorem mem_Pnew_of_x (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p))
    (hx : x rate rewards C_star C_h control0 i n z = true) :
    i ∈ Pnew rate rewards C_star C_h control0 n z := by
  by_contra hi
  simp only [x, service, serviceParts_of_not_mem rate rewards C_star C_h control0 i n z hi,
    Nat.add_zero, lt_self_iff_false, decide_false, Bool.false_eq_true] at hx

/-- The two natural-date stage sets are disjoint by physical choice exclusivity. -/
theorem disjoint_positiveDates (i : Fin (p.m - 1)) (z : Source (p := p)) :
    Disjoint (oldPositiveDates rate rewards C_star C_h control0 i z)
      (formedPositiveDates rate rewards C_star C_h control0 i z) := by
  rw [Finset.disjoint_left]
  intro n ho hf
  have hold := (Finset.mem_filter.mp ho).2
  have hformed := (Finset.mem_filter.mp hf).2
  have hbound := service_le_one rate rewards C_star C_h control0 i n z
  unfold service at hbound
  omega

/-- Exact disjoint-union description, preserving all zero-feedback dates. -/
theorem servicePositiveDates_eq_union (i : Fin (p.m - 1)) (z : Source (p := p)) :
    servicePositiveDates rate rewards C_star C_h control0 i z =
      oldPositiveDates rate rewards C_star C_h control0 i z ∪
        formedPositiveDates rate rewards C_star C_h control0 i z := by
  ext n
  simp only [servicePositiveDates, Finset.mem_filter, x, decide_eq_true_eq]
  simp only [oldPositiveDates, formedPositiveDates, Finset.mem_filter, Finset.mem_union, service,
    Nat.add_pos_iff_pos_or_pos, and_or_left]

/-- Exact PhaseServiceWaiting count identity for the new support and new readout. -/
theorem N_eq_card_prefix (i : Fin (p.m - 1)) (H : ℕ) (z : Source (p := p)) :
    PhaseServiceWaiting.N (Pnew rate rewards C_star C_h control0)
      (x rate rewards C_star C_h control0) i H z =
      ((servicePositiveDates rate rewards C_star C_h control0 i z).filter
        (fun n => n < H)).card := by
  have hcount : PhaseServiceWaiting.N (Pnew rate rewards C_star C_h control0)
      (x rate rewards C_star C_h control0) i H z =
      ((Finset.range H).filter fun n => x rate rewards C_star C_h control0 i n z = true).card := by
    rw [PhaseServiceWaiting.N, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hx : x rate rewards C_star C_h control0 i n z = true
    · simp only [hx, and_true, ↓reduceIte,
        ite_eq_left (mem_Pnew_of_x rate rewards C_star C_h control0 i n z hx)]
    · simp only [hx, Bool.not_eq_true] at *
      simp only [Bool.false_eq_true, and_false, ↓reduceIte]
  rw [hcount]
  congr 1
  ext n
  simp only [servicePositiveDates, Finset.mem_filter, Finset.mem_range]
  have hlt : x rate rewards C_star C_h control0 i n z = true → n < p.T := by
    intro hx
    have hi := mem_Pnew_of_x rate rewards C_star C_h control0 i n z hx
    by_contra hn
    rw [Pnew_of_horizon_le rate rewards C_star C_h control0 n (by omega) z] at hi
    exact Finset.notMem_empty i hi
  constructor
  · rintro ⟨hn, hx⟩
    exact ⟨⟨hlt hx, hx⟩, hn⟩
  · rintro ⟨⟨_, hx⟩, hn⟩
    exact ⟨hn, hx⟩

/-- Every natural-calendar prefix is bounded by the terminal positive-date count. -/
theorem N_le_terminal_card (i : Fin (p.m - 1)) (H : ℕ) (z : Source (p := p)) :
    PhaseServiceWaiting.N (Pnew rate rewards C_star C_h control0)
      (x rate rewards C_star C_h control0) i H z ≤
      (servicePositiveDates rate rewards C_star C_h control0 i z).card := by
  rw [N_eq_card_prefix]
  exact Finset.card_filter_le _ _

variable {rate rewards C_star C_h control0}

private theorem linked_dagger_forward
    (K : List (Record (rate := rate))) (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ a : Fin K.length,
      (K.get a).input.state = Z a.val ∧ (K.get a).output.next = Z (a.val + 1))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ K.length)
    (hd : (Z a).coordinator = .dagger) : (Z b).coordinator = .dagger := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    simpa only [ha] using hd
  | succ b ih =>
    by_cases he : a = b + 1
    · simpa only [he] using hd
    · have hprev := ih (by omega) (by omega)
      let idx : Fin K.length := ⟨b, by omega⟩
      have hl := hlinks idx
      have hin : (K.get idx).input.state.coordinator = .dagger := by rw [hl.1]; exact hprev
      have hout := (ReferenceActivePhysicalStep.step_coordinator_dagger (K.get idx).input hin).1
      rw [← (K.get idx).output_eq, hl.2] at hout
      exact hout

private theorem raw_pending_law
    (z : Source (p := p)) (payload : ReferenceActivePhysicalStep.Payload rate)
    (K : List (Record (rate := rate))) (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hactual : ∀ a : Fin K.length, actualRecord rate rewards C_star C_h
      (K.get a).input.time z = some (K.get a))
    (hlinks : ∀ a : Fin K.length,
      (K.get a).input.state = Z a.val ∧ (K.get a).output.next = Z (a.val + 1))
    (hzero : ∀ a : Fin K.length, a.val = 0 →
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get a).input.time z = Finset.univ)
    (hstate : ∀ a : Fin K.length, 0 < a.val →
      (K.get a).input.state.coordinator = .dagger ∨ ∃ ledger saved,
        (K.get a).input.state.coordinator = .collection payload ledger saved ∧
        ledger.pending = Finset.univ \
          (acceptedLabels (K.take a.val)).toFinset) :
    (∀ a b : Fin K.length, a.val ≤ b.val →
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get b).input.time z ⊆
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get a).input.time z) ∧
    (∀ (a b : Fin K.length) (i : Fin (p.m - 1)), b.val < a.val →
      i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get a).input.time z → ¬ acceptanceAt (K.get b) i) := by
  have hread : ∀ a : Fin K.length, 0 < a.val →
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get a).input.time z = ∅ ∧ (Z a.val).coordinator = .dagger) ∨
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        payload.sigma.val (K.get a).input.time z =
          Finset.univ \
            (acceptedLabels (K.take a.val)).toFinset := by
    intro a ha
    rcases hstate a ha with hd | ⟨ledger, saved, hc, hp⟩
    · exact Or.inl ⟨by simp only [ReferenceFirstCollectionPendingObservation.Q, hactual a, hd],
        by rw [← (hlinks a).1]; exact hd⟩
    · exact Or.inr (by simp only [ReferenceFirstCollectionPendingObservation.Q, hactual a, hc,
        ↓reduceIte, hp])
  constructor
  · intro a b hab i hi
    by_cases ha : a.val = 0
    · rw [hzero a ha]
      exact Finset.mem_univ i
    rcases hread b (by omega) with ⟨he, _⟩ | he
    · rw [he] at hi
      exact (Finset.notMem_empty i hi).elim
    rcases hread a (by omega) with ⟨_, hd⟩ | hea
    · have hdb := linked_dagger_forward K Z hlinks a.val b.val hab (Nat.le_of_lt b.isLt) hd
      have hinput : (K.get b).input.state.coordinator = .dagger := by rw [(hlinks b).1]; exact hdb
      simp only [ReferenceFirstCollectionPendingObservation.Q, hactual b, hinput,
        Finset.notMem_empty] at hi
    · rw [he] at hi
      rw [hea]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
      intro hm
      apply (Finset.mem_sdiff.mp hi).2
      apply List.mem_toFinset.mpr
      exact ((List.take_sublist_take_left hab).filterMap
        (fun r : Record (rate := rate) => acceptedLabel r.input)).subset
          (List.mem_toFinset.mp hm)
  · intro a b i hba hi ha
    rcases hread a (by omega) with ⟨he, _⟩ | he
    · rw [he] at hi
      exact Finset.notMem_empty i hi
    rw [he] at hi
    apply (Finset.mem_sdiff.mp hi).2
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    refine ⟨K.get b, ?_, (acceptanceAt_iff _ _).mp ha⟩
    exact List.mem_take_iff_getElem.mpr ⟨b.val, by omega, rfl⟩

-- The existential below is eliminated only inside proofs. Its witnesses are
-- constructed from the literal canonical birth, cutoff and K, never chosen as
-- an alternative execution or as a replacement for inherited banks.
private theorem actual_calendar_data
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (z : Source (p := p)) :
    (∀ n, Pnew rate rewards C_star C_h control0 n z = ∅) ∨
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate) (u : ℕ)
      (K : List (Record (rate := rate))),
      (∀ n, (Pnew rate rewards C_star C_h control0 n z).Nonempty →
        ∃ a : Fin K.length, n = u - 1 + a.val) ∧
      (∀ a : Fin K.length,
        (K.get a).input.time.val = u - 1 + a.val ∧
        payloadOnset rate rewards C_star C_h (u - 1 + a.val) z = some (payload, u) ∧
        actualRecord rate rewards C_star C_h (K.get a).input.time z = some (K.get a) ∧
        Praw rate rewards C_star C_h (u - 1 + a.val) z =
          ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
            payload.sigma.val (K.get a).input.time z) ∧
      (∀ a b : Fin K.length, a.val ≤ b.val →
        Praw rate rewards C_star C_h (u - 1 + b.val) z ⊆
          Praw rate rewards C_star C_h (u - 1 + a.val) z) ∧
      (∀ (a b : Fin K.length) (i : Fin (p.m - 1)), b.val < a.val →
        i ∈ Praw rate rewards C_star C_h (u - 1 + a.val) z →
          ¬ acceptanceAt (K.get b) i) ∧
      (∀ (i : Fin (p.m - 1)) (j : ℕ), j ≤ K.length →
        let h := ReferenceFirstReplacementCollectionAwaitedCompositeQuota.safetyPrefixLength
          K z rewards C_star C_h control0 i j
        ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
          K h i (payload.downRecord i) +
          (formedPositiveEntries (K.take h) i (payload.downRecord i)).length ≤
            4 * AffineBatchDecoder.quota p) := by
  have hL := fun n => complete_first_replacement_awaited_pending_localization
    rate rewards C_star C_h control0 z n
  have hN := complete_first_replacement_pending_coordinates rate rewards C_star C_h control0 z
  have hQ := ReferenceFirstReplacementCollectionAwaitedCompositeQuota.complete_first_replacement_collection_awaited_composite_quota
    rate rewards C_star C_h control0 z
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  have hZ := ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
    rate z rewards C_star C_h
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  dsimp only at hL hN hQ hR hZ hB
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (collectionWindow R w).length
  set c := v + 1 + (continuingTail R v).length
  have hempty : (∀ n, ¬ (Pnew rate rewards C_star C_h control0 n z).Nonempty) →
      ∀ n, Pnew rate rewards C_star C_h control0 n z = ∅ :=
    fun h n => Finset.not_nonempty_iff_eq_empty.mp (h n)
  cases hb : R[v]? with
  | none => exact Or.inl (hempty fun n hn => by simpa only [hb] using hL n hn)
  | some birth =>
    rw [hb] at hN hQ hR hZ hB
    dsimp only at hN hQ hR hZ hB
    cases hbirth : birth.output.preparation.coordinator <;>
      try exact Or.inl (hempty fun n hn => by simpa only [hb, hbirth] using hL n hn)
    rename_i old ledger clock cutoff outcome
    rw [hbirth] at hN hQ hR hZ hB
    cases outcome <;>
      try exact Or.inl (hempty fun n hn => by simpa only [hb, hbirth] using hL n hn)
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    dsimp only [collectionInput] at hN hQ hR hZ hB
    obtain ⟨_, _, hR⟩ := hR
    obtain ⟨_, _, hZ⟩ := hZ
    cases hc : R[c]? with
    | none => exact Or.inl (hempty fun n hn => by simpa only [hb, hbirth, hc] using hL n hn)
    | some cut =>
      rw [hc] at hN hQ hR hZ hB
      dsimp only at hN hQ hR hZ hB
      obtain ⟨_, hB⟩ := hB
      cases hcut : cut.output.preparation.coordinator <;>
        try exact Or.inl (hempty fun n hn => by simpa only [hb, hbirth, hc, hcut] using hL n hn)
      rename_i registers owned base outcome
      rw [hcut] at hN hQ hR hZ hB
      cases outcome <;>
        try exact Or.inl (hempty fun n hn => by simpa only [hb, hbirth, hc, hcut] using hL n hn)
      rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
      dsimp only at hN hQ hR hZ hB
      let payload := installed.registers.payload
      let u := cut.input.time.val + 1
      let W := (R.drop (c + 1)).takeWhile (fun r => !laterChosen r.input)
      let K := cut :: W
      let Z := fun n => ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take n)
      have hct := complete_record_time rewards C_star C_h z c cut hc
      change cut.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + c at hct
      obtain ⟨hactual, initial, active, hlaunch, hseed, hquota⟩ := hQ
      have hcoord : ∀ a : Fin K.length,
          (K.get a).input.time.val = u - 1 + a.val ∧
          payloadOnset rate rewards C_star C_h (u - 1 + a.val) z = some (payload, u) ∧
          actualRecord rate rewards C_star C_h (K.get a).input.time z = some (K.get a) ∧
          Praw rate rewards C_star C_h (u - 1 + a.val) z =
            ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
              payload.sigma.val (K.get a).input.time z := by
        intro a
        refine ⟨?_, (hN a).1, (hN a).2.1, (hN a).2.2.1⟩
        have ht := (hactual a).2.1
        change (K.get a).input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + c + a.val at ht
        dsimp only [u]
        omega
      obtain ⟨_, hlinks, _, _⟩ := hZ
      have hzero : ∀ a : Fin K.length, a.val = 0 →
          ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
            payload.sigma.val (K.get a).input.time z = Finset.univ := by
        intro a ha
        have he : K.get a = cut := by simp [K, List.get_eq_getElem, ha]
        rw [he]
        have hin := dispatch_live_origin cut.input
        rw [← cut.output.preparation.coordinator_eq, hcut] at hin
        have hflag : cutoffChosen cut.input = true := by
          rw [← isCutoff_eq]
          simp only [isCutoff, hcut]
        have hr := (hcoord ⟨0, by simp [K]⟩).2.2.1
        change actualRecord rate rewards C_star C_h cut.input.time z = some cut at hr
        simp only [ReferenceFirstCollectionPendingObservation.Q, hr, hin, hB.1, hflag,
          payload, and_true, ↓reduceIte]
      have hstate : ∀ a : Fin K.length, 0 < a.val →
          (K.get a).input.state.coordinator = .dagger ∨ ∃ ledger saved,
            (K.get a).input.state.coordinator = .collection payload ledger saved ∧
            ledger.pending = Finset.univ \
              (acceptedLabels (K.take a.val)).toFinset := by
        intro a ha
        have he : a.val = (a.val - 1) + 1 := by omega
        have ht : (K.get a).input.state =
            ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take (a.val - 1)) := by
          rw [(hlinks.2.2 a).1]
          conv_lhs => rw [he]
          rfl
        rw [ht]
        rcases hR.1 (a.val - 1) (by change a.val - 1 ≤ W.length; have hlen := a.isLt; change a.val < W.length + 1 at hlen; omega)
          with hd | ⟨l, saved, hl, _, _, hp⟩
        · exact Or.inl hd
        · refine Or.inr ⟨l, saved, hl, ?_⟩
          have heK : K.take a.val = cut :: W.take (a.val - 1) := by
            conv_lhs => rw [he]
            rfl
          rw [heK]
          exact hp
      obtain ⟨hmono, hno⟩ := raw_pending_law z payload K Z (fun a => (hcoord a).2.2.1)
        hlinks.2.2 hzero hstate
      refine Or.inr ⟨payload, u, K, ?_, hcoord, ?_, ?_, ?_⟩
      · intro n hn
        have hh := hL n hn
        simp only [hb, hbirth, hc, hcut] at hh
        obtain ⟨a, ha, _⟩ := hh
        exact ⟨a, ha⟩
      · intro a b hab
        rw [(hcoord a).2.2.2, (hcoord b).2.2.2]
        exact hmono a b hab
      · intro a b i hba hi
        rw [(hcoord a).2.2.2] at hi
        exact hno a b i hba hi
      · intro i j hj
        obtain ⟨base0, memory0, span0, _hbase, _hrun, _hend, _hzero, _hneed, _hthreshold, hbound⟩ := hquota i
        exact (hbound j hj).2.2

variable (rate rewards C_star C_h control0)

/-- Shrinking begins only after an actual nonempty supported date. -/
theorem Pnew_shrinking_after_supported (z : Source (p := p)) {s n t : ℕ}
    (hsn : s ≤ n) (hnt : n ≤ t)
    (hstart : (Pnew rate rewards C_star C_h control0 s z).Nonempty) :
    Pnew rate rewards C_star C_h control0 t z ⊆ Pnew rate rewards C_star C_h control0 n z := by
  rcases actual_calendar_data rate rewards C_star C_h control0 z with hempty |
    ⟨payload, u, K, hloc, hcoord, hmono, _hno, _hquota⟩
  · rw [hempty t]
    exact Finset.empty_subset _
  obtain ⟨a, ha⟩ := hloc s hstart
  intro i hi
  obtain ⟨b, hb⟩ := hloc t ⟨i, hi⟩
  let d : Fin K.length := ⟨n - (u - 1), by have := b.isLt; omega⟩
  have hnd : n = u - 1 + d.val := by dsimp only [d]; omega
  have hdb : d.val ≤ b.val := by dsimp only [d]; omega
  obtain ⟨hraw, hflag, oldPayload, oldU, honset, hstop⟩ :=
    (mem_Pnew_iff rate rewards C_star C_h control0 t z i).mp hi
  have heq : (oldPayload, oldU) = (payload, u) :=
    Option.some.inj (honset.symm.trans (by rw [hb]; exact (hcoord b).2.1))
  cases heq
  apply (mem_Pnew_iff rate rewards C_star C_h control0 n z i).mpr
  refine ⟨?_, ?_, payload, u, ?_, ?_⟩
  · rw [hnd]
    apply hmono d b hdb
    simpa only [hb] using hraw
  · rw [ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure] at hflag ⊢
    exact fun v hv => hflag v (hv.trans_le hnt)
  · rw [hnd]
    exact (hcoord d).2.1
  · rintro ⟨v, hv, hu, r, hr, hf⟩
    exact hstop ⟨v, hv.trans_le hnt, hu, r, hr, hf⟩

/-- Once support has begun, emptiness cannot be followed by a new pending task. -/
theorem Pnew_no_resurrection (z : Source (p := p)) {s n t : ℕ}
    (hsn : s ≤ n) (hnt : n ≤ t)
    (hstart : (Pnew rate rewards C_star C_h control0 s z).Nonempty)
    (hempty : Pnew rate rewards C_star C_h control0 n z = ∅) :
    Pnew rate rewards C_star C_h control0 t z = ∅ := by
  have h := Pnew_shrinking_after_supported rate rewards C_star C_h control0 z hsn hnt hstart
  rw [hempty] at h
  exact Finset.subset_empty.mp h

variable {rate rewards C_star C_h control0}

open ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity
open ReferenceFirstReplacementCollectionAwaitedCompositeQuota

private theorem oldCount_eq_card
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    oldDownCount K j i M = (oldDownServiceFinset K j i M).card := by
  have hn : (countedOldDownServiceIndices K j i M).Nodup :=
    (List.nodup_finRange K.length).filter _
  calc
    oldDownCount K j i M = ((countedOldDownServiceIndices K j i M).toFinset).card := by
      exact (List.toFinset_card_of_nodup hn).symm
    _ = (oldDownServiceFinset K j i M).card := by
      simp [countedOldDownServiceIndices, countedOldDownServiceAt,
        oldDownServiceFinset, oldDownServiceAt, List.toFinset_filter, List.toFinset_finRange]

private theorem card_le_coordinates (S : Finset ℕ) (b : ℕ)
    {len : ℕ} (A : Finset (Fin len))
    (h : ∀ n ∈ S, ∃ a ∈ A, n = b + a.val) : S.card ≤ A.card := by
  have hc : S.card ≤ (A.image Fin.val).card := by
    apply Finset.card_le_card_of_injOn (fun n => n - b)
    · intro n hn
      obtain ⟨a, ha, ht⟩ := h n hn
      exact Finset.mem_image.mpr ⟨a, ha, by change a.val = n - b; omega⟩
    · intro n hn m hm he
      obtain ⟨a, _, ha⟩ := h n hn
      obtain ⟨c, _, hc⟩ := h m hm
      change n - b = m - b at he
      omega
  simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hc

private theorem formed_card_le_entries (K : List (Record (rate := rate)))
    (h : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    (Finset.univ.filter fun a : Fin K.length => a.val < h ∧ replyFormedAt (K.get a) i M ∧
      0 < ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive (K.get a) i).card ≤
        (formedPositiveEntries (K.take h) i M).length := by
  have hsum : ∀ (L : List (Record (rate := rate))) (j : ℕ),
      (formedPositiveEntries (L.take j) i M).length =
        ∑ a : Fin L.length, if a.val < j then
          if replyFormedAt (L.get a) i M then
            ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive (L.get a) i else 0
          else 0 := by
    intro L
    induction L with
    | nil => intro j; simp [formedPositiveEntries]
    | cons r rs ih =>
      intro j
      cases j with
      | zero => simp [formedPositiveEntries]
      | succ j =>
        simp only [List.take_succ_cons, formedPositiveEntries, List.flatMap_cons, List.length_append]
        change (if replyFormedAt r i M then _ else []).length +
          (formedPositiveEntries (rs.take j) i M).length = _
        rw [ih j]
        simp [Fin.sum_univ_succ, ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive]
        split_ifs with hf <;> simp only [hf, ↓reduceIte, List.length_nil]
  rw [hsum, Finset.card_filter]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a.val < h <;> by_cases hf : replyFormedAt (K.get a) i M <;>
    by_cases hp : 0 < ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive (K.get a) i <;>
    simp only [ha, hf, hp, and_true, and_false, ↓reduceIte] <;> omega

variable (rate rewards C_star C_h control0)

/-- Terminal supported positives obey the same original inclusive composite quota. -/
theorem card_servicePositiveDates_le (i : Fin (p.m - 1)) (z : Source (p := p)) :
    (servicePositiveDates rate rewards C_star C_h control0 i z).card ≤
      4 * AffineBatchDecoder.quota p := by
  rcases actual_calendar_data rate rewards C_star C_h control0 z with hempty |
    ⟨payload, u, K, hloc, hcoord, _hmono, hno, hquota⟩
  · have he : servicePositiveDates rate rewards C_star C_h control0 i z = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hi := mem_Pnew_of_x rate rewards C_star C_h control0 i n z (Finset.mem_filter.mp hn).2
      rw [hempty n] at hi
      exact Finset.notMem_empty i hi
    simp only [he, Finset.card_empty, Nat.zero_le]
  let h := safetyPrefixLength K z rewards C_star C_h control0 i K.length
  have hsafe : ∀ a : Fin K.length, i ∈ Pnew rate rewards C_star C_h control0 (u - 1 + a.val) z →
      a.val < h ∧ ∀ r ∈ K.take a.val, ¬ physicalFailureAt r := by
    intro a hi
    obtain ⟨hraw, hflag, pay, onset, hp, hmask⟩ :=
      (mem_Pnew_iff rate rewards C_star C_h control0 _ z i).mp hi
    have he := Option.some.inj (hp.symm.trans (hcoord a).2.1)
    cases he
    have hn : ∀ b : Fin K.length, b.val < a.val →
        ¬ safetyStopAt z rewards C_star C_h control0 i (K.get b) := by
      intro b hba hb
      have ht : (K.get b).input.time.val < u - 1 + a.val := by rw [(hcoord b).1]; omega
      have hu : u ≤ (K.get b).input.time.val + 1 := by rw [(hcoord b).1]; omega
      rcases hb with ha | hf | hd | hup
      · exact hno a b i hba hraw ha
      · exact hmask ⟨_, ht, hu, _, (hcoord b).2.2.1, Or.inl hf⟩
      · exact (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h z _).mp hflag _ ht hd
      · exact hmask ⟨_, ht, hu, _, (hcoord b).2.2.1, Or.inr hup⟩
    have hle : a.val ≤ safetyStopIndex K z rewards C_star C_h control0 i := by
      by_contra hc
      let b : Fin K.length := ⟨safetyStopIndex K z rewards C_star C_h control0 i, by omega⟩
      exact hn b (by dsimp [b]; omega) (of_decide_eq_true (List.findIdx_getElem (w := b.isLt)))
    refine ⟨by dsimp only [h, safetyPrefixLength]; omega, ?_⟩
    intro r hr hf
    obtain ⟨b, hb, he⟩ := List.mem_take_iff_getElem.mp hr
    have hbL : b < K.length := (Nat.lt_min.mp hb).2
    exact hn ⟨b, hbL⟩ (Nat.lt_min.mp hb).1 (Or.inr (Or.inl (by simpa only [List.get_eq_getElem, he] using hf)))
  have hdate : ∀ n, x rate rewards C_star C_h control0 i n z = true →
      ∃ a : Fin K.length, n = u - 1 + a.val ∧ a.val < h ∧
        serviceParts rate rewards C_star C_h control0 i n z = recordServiceParts (K.get a) payload i ∧
        ∀ r ∈ K.take a.val, ¬ physicalFailureAt r := by
    intro n hx
    have hi := mem_Pnew_of_x rate rewards C_star C_h control0 i n z hx
    obtain ⟨a, ha⟩ := hloc n ⟨i, hi⟩
    have hs := hsafe a (ha ▸ hi)
    refine ⟨a, ha, hs.1, ?_, hs.2⟩
    have ht : n = (K.get a).input.time.val := ha.trans (hcoord a).1.symm
    rw [ht]
    exact serviceParts_at_record rate rewards C_star C_h control0 i _ z payload u _ (ht ▸ hi)
      (by rw [(hcoord a).1]; exact (hcoord a).2.1) (hcoord a).2.2.1
  have ho : (oldPositiveDates rate rewards C_star C_h control0 i z).card ≤
      oldDownCount K h i (payload.downRecord i) := by
    rw [oldCount_eq_card]
    apply card_le_coordinates _ (u - 1) (oldDownServiceFinset K h i (payload.downRecord i))
    intro n hn
    have hp := (Finset.mem_filter.mp hn).2
    have hx : x rate rewards C_star C_h control0 i n z = true := by
      rw [x, decide_eq_true_eq]; unfold service; omega
    obtain ⟨a, ha, hs, he, hf⟩ := hdate n hx
    rw [he] at hp
    simp only [recordServiceParts] at hp
    split_ifs at hp with hold <;> try omega
    refine ⟨a, ?_, ha⟩
    change a ∈ (Finset.univ.filter fun b : Fin K.length => b.val < h ∧ oldDownServiceAt K i (payload.downRecord i) b)
    have hpos : ReferenceSelectedAffinePairLaw.selectedChannel p ((K.get a).input.row.2 (K.get a).input.time).1 = some (0, i) ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val := by
      unfold ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive at hp
      split_ifs at hp with hpos
      · exact hpos
      · omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hold, hpos.1, hpos.2, hf⟩
  have hf : (formedPositiveDates rate rewards C_star C_h control0 i z).card ≤
      (formedPositiveEntries (K.take h) i (payload.downRecord i)).length := by
    apply le_trans (card_le_coordinates _ (u - 1) _ ?_) (formed_card_le_entries K h i (payload.downRecord i))
    intro n hn
    have hp := (Finset.mem_filter.mp hn).2
    have hx : x rate rewards C_star C_h control0 i n z = true := by
      rw [x, decide_eq_true_eq]; unfold service; omega
    obtain ⟨a, ha, hs, he, _⟩ := hdate n hx
    rw [he] at hp
    simp only [recordServiceParts] at hp
    split_ifs at hp with hformed <;> try omega
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hformed, hp⟩, ha⟩
  rw [servicePositiveDates_eq_union, Finset.card_union_of_disjoint
    (disjoint_positiveDates rate rewards C_star C_h control0 i z)]
  exact (Nat.add_le_add ho hf).trans (hquota i K.length le_rfl)

/-- Every calendar-prefix PhaseServiceWaiting count has quota four decoder batches. -/
theorem N_le_quota (i : Fin (p.m - 1)) (H : ℕ) (z : Source (p := p)) :
    PhaseServiceWaiting.N (Pnew rate rewards C_star C_h control0)
      (x rate rewards C_star C_h control0) i H z ≤ 4 * AffineBatchDecoder.quota p :=
  (N_le_terminal_card rate rewards C_star C_h control0 i H z).trans
    (card_servicePositiveDates_le rate rewards C_star C_h control0 i z)

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedTaskSupport
