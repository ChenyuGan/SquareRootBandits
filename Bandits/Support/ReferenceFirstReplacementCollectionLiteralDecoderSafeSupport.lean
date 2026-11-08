/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalUpAwaitedDateReadout
public import Bandits.Support.ReferenceFirstReplacementCollectionRawPendingTotal
public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedTaskSupport

/-!
# Literal decoder-safe collection support on the original first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-240`,
`06_interruptions.tex:37-79,246-296,425-437,459-487`, and
`appendix_a_local_protocol.tex:8-85,141-157`.

The analytical restriction scans literal source failures globally from date zero.
It retains the detecting update. It neither stops the physical execution nor
identifies local operational failure with the later analytical overflow gate.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep ReferenceCollectionSegmentExtraction
open ReferenceFirstReplacementCollectionPendingFoundation
open ReferenceFirstReplacementCollectionStoppedPureUpQuota
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstReplacementCollectionAwaitedTaskSupport
open ReferenceFirstCollectionUpConditionalService (positiveRewardCount)
open ReferenceFirstCollectionRoundEndObservation (g)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The two literal source decoder failures, on the unchanged whole source. -/
def E (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) : Prop :=
  ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
    ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t

/-- Global strict-past safety; a failure at the current date is retained. -/
def Safe (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) : Prop :=
  ∀ t : Fin p.T, t.val < n → ¬ E rate rewards C_star C_h z t

variable (rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal raw-list prefix, with no pending-set or diagnostic-union test. -/
def decoderSafePrefix (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate))) : List (Record (rate := rate)) :=
  K.takeWhile fun r => decide (Safe rate rewards C_star C_h z r.input.time.val)

/-- Literal capped collection charge, counted on the original reward table. -/
def cappedCharge (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate))) : ℝ :=
  ((decoderSafePrefix rate rewards C_star C_h z K).map fun r =>
    (min p.m (positiveRewardCount rewards r.input.time) : ℝ)).sum

/-- The same literal charge at one calendar date. -/
def calendarCharge (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate))) (n : ℕ) : ℝ :=
  ((decoderSafePrefix rate rewards C_star C_h z K).map fun r =>
    if r.input.time.val = n then
      (min p.m (positiveRewardCount rewards r.input.time) : ℝ) else 0).sum

/-- Increasing the date only adds strict-past obligations. -/
theorem safe_antitone (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Antitone (Safe rate rewards C_star C_h z) := by
  intro a b hab hb t ht
  exact hb t (lt_of_lt_of_le ht hab)

/-- At a first literal failure, safety holds exactly through its detecting date. -/
theorem safe_iff_le_first_failure (z : BootstrapPrivateRoundStreams.SourceInput p)
    (f : Fin p.T) (hf : E rate rewards C_star C_h z f)
    (hpast : Safe rate rewards C_star C_h z f.val) (n : ℕ) :
    Safe rate rewards C_star C_h z n ↔ n ≤ f.val := by
  constructor
  · intro hn
    by_contra h
    exact hn f (by omega) hf
  · intro hn
    exact safe_antitone rate rewards C_star C_h z hn hpast

/-- With no literal failure, the whole raw collection is retained. -/
theorem decoderSafePrefix_of_no_failure (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : ∀ t, ¬ E rate rewards C_star C_h z t) (K : List (Record (rate := rate))) :
    decoderSafePrefix rate rewards C_star C_h z K = K := by
  apply List.takeWhile_eq_self_iff.mpr
  intro r _
  exact decide_eq_true (fun t _ => h t)

/-- A first global failure restricts the raw collection through that update,
including when it precedes the collection or occurs at its final horizon cell. -/
theorem decoderSafePrefix_of_first_failure (z : BootstrapPrivateRoundStreams.SourceInput p)
    (f : Fin p.T) (hf : E rate rewards C_star C_h z f)
    (hpast : Safe rate rewards C_star C_h z f.val) (K : List (Record (rate := rate))) :
    decoderSafePrefix rate rewards C_star C_h z K =
      K.takeWhile (fun r => decide (r.input.time.val ≤ f.val)) := by
  unfold decoderSafePrefix
  congr 1
  funext r
  exact decide_eq_decide.mpr (safe_iff_le_first_failure rate rewards C_star C_h z f hf hpast _)

/-- On a chronological raw list, the literal prefix equals its safety filter. -/
theorem decoderSafePrefix_eq_filter (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate)))
    (horder : K.Pairwise (fun a b => a.input.time.val ≤ b.input.time.val)) :
    decoderSafePrefix rate rewards C_star C_h z K =
      K.filter (fun r => decide (Safe rate rewards C_star C_h z r.input.time.val)) := by
  induction K with
  | nil => rfl
  | cons r K ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    by_cases hr : Safe rate rewards C_star C_h z r.input.time.val
    · simp only [decoderSafePrefix, List.takeWhile_cons, decide_eq_true hr,
        ite_true, List.filter_cons_of_pos]
      congr 1
      exact ih htail
    · have hnone : ∀ s ∈ K, ¬ Safe rate rewards C_star C_h z s.input.time.val := by
        intro s hs hsafe
        exact hr (safe_antitone rate rewards C_star C_h z (hhead s hs) hsafe)
      simp only [decoderSafePrefix, List.takeWhile_cons, List.filter_cons, decide_eq_false hr,
        Bool.false_eq_true, ite_false]
      symm
      apply List.filter_eq_nil_iff.mpr
      intro s hs
      simpa only [decide_eq_true_eq] using hnone s hs

/-- Membership characterization of the literal prefix, with global strict past. -/
theorem mem_decoderSafePrefix_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate)))
    (horder : K.Pairwise (fun a b => a.input.time.val ≤ b.input.time.val))
    (r : Record (rate := rate)) :
    r ∈ decoderSafePrefix rate rewards C_star C_h z K ↔
      r ∈ K ∧ Safe rate rewards C_star C_h z r.input.time.val := by
  rw [decoderSafePrefix_eq_filter rate rewards C_star C_h z K horder]
  simp only [List.mem_filter, decide_eq_true_eq]


/-- The global finite scan has either no literal failure, or an actual earliest
failure. In the latter case the prefix includes that update and excludes all
later dates, even when the first failure precedes the collection onset. -/
theorem decoderSafePrefix_cases (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate))) :
    ((∀ t, ¬ E rate rewards C_star C_h z t) ∧
      decoderSafePrefix rate rewards C_star C_h z K = K) ∨
    ∃ f : Fin p.T, E rate rewards C_star C_h z f ∧
      Safe rate rewards C_star C_h z f.val ∧
      decoderSafePrefix rate rewards C_star C_h z K =
        K.takeWhile (fun r => decide (r.input.time.val ≤ f.val)) := by
  by_cases hex : ∃ t, E rate rewards C_star C_h z t
  · let bad : Finset (Fin p.T) := Finset.univ.filter (E rate rewards C_star C_h z)
    have hbad : bad.Nonempty := by
      obtain ⟨t, ht⟩ := hex
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩⟩
    let f := bad.min' hbad
    have hf : E rate rewards C_star C_h z f :=
      (Finset.mem_filter.mp (Finset.min'_mem bad hbad)).2
    have hpast : Safe rate rewards C_star C_h z f.val := by
      intro t ht he
      have hle : f ≤ t := Finset.min'_le bad t
        (Finset.mem_filter.mpr ⟨Finset.mem_univ t, he⟩)
      exact (not_le_of_gt ht) hle
    exact Or.inr ⟨f, hf, hpast,
      decoderSafePrefix_of_first_failure rate rewards C_star C_h z f hf hpast K⟩
  · have hnone : ∀ t, ¬ E rate rewards C_star C_h z t := by
      intro t ht
      exact hex ⟨t, ht⟩
    exact Or.inl ⟨hnone, decoderSafePrefix_of_no_failure rate rewards C_star C_h z hnone K⟩

/-- A failure strictly before the cutoff makes the analytical prefix empty;
a safe cutoff head is retained even if there are no tail records. -/
theorem decoderSafePrefix_cons_eq_nil_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (head : Record (rate := rate)) (tail : List (Record (rate := rate))) :
    decoderSafePrefix rate rewards C_star C_h z (head :: tail) = [] ↔
      ¬ Safe rate rewards C_star C_h z head.input.time.val := by
  by_cases hs : Safe rate rewards C_star C_h z head.input.time.val <;>
    simp [decoderSafePrefix, hs]

private theorem pending_eq_of_safe
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate))) (payload : ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate)) (u : ℕ)
    (hdates : ∀ a : Fin K.length, (K.get a).input.time.val + 1 = u + a.val)
    (hlookup : ∀ a : Fin K.length,
      actualRecord rate rewards C_star C_h (K.get a).input.time z = some (K.get a))
    (hfailure : ∀ a : Fin K.length, ¬ physicalFailureAt (K.get a))
    (a : Fin K.length)
    (honset : payloadOnset rate rewards C_star C_h (K.get a).input.time.val z =
      some (payload, u))
    (hsafe : Safe rate rewards C_star C_h z (K.get a).input.time.val) :
    Pnew rate rewards C_star C_h control0 (K.get a).input.time.val z =
      Praw rate rewards C_star C_h (K.get a).input.time.val z := by
  apply Finset.Subset.antisymm
  · exact Pnew_subset_Praw rate rewards C_star C_h control0 _ z
  · intro i hi
    apply (mem_Pnew_iff rate rewards C_star C_h control0 _ z i).mpr
    refine ⟨hi, ?_, payload, u, honset, ?_⟩
    · exact ReferenceLiteralSourceDecoderCoverage.pastFailureFlag_false_of_no_earlier_literal_failure
        rate rewards C_star C_h z _ hsafe
    · rintro ⟨t, ht, hu, r, hr, hf | hamb⟩
      · have ha := hdates a
        have hb : t.val + 1 - u < K.length := by omega
        let b : Fin K.length := ⟨t.val + 1 - u, hb⟩
        have hbt : (K.get b).input.time = t := by
          apply Fin.ext
          have hd := hdates b
          change (K.get b).input.time.val + 1 = u + (t.val + 1 - u) at hd
          change (K.get b).input.time.val = t.val
          omega
        have he : r = K.get b := by
          have hl := hlookup b
          rw [hbt, hr] at hl
          exact Option.some.inj hl
        exact hfailure b (he ▸ hf)
      · exact hsafe t ht (Or.inr (Or.inr
          (ReferenceOriginalUpAwaitedDateReadout.literalUpAmbiguityAt_of_originalUpAwaitedAmbiguityAtDate
            rate rewards C_star C_h control0 z i t hamb)))

private theorem sum_map_le_calendar
    (K : List (Record (rate := rate)))
    (horder : K.Pairwise (fun a b => a.input.time.val < b.input.time.val))
    (f : Record (rate := rate) → ℝ) (F : ℕ → ℝ)
    (hbound : ∀ r ∈ K, f r ≤ F r.input.time.val)
    (hnonneg : ∀ n, 0 ≤ F n) :
    (K.map f).sum ≤ ∑ n ∈ Finset.range p.T, F n := by
  have he : K.map f = List.ofFn (fun a : Fin K.length => f (K.get a)) := by
    calc
      K.map f = (List.ofFn (fun a : Fin K.length => K.get a)).map f := by
        simp only [List.get_eq_getElem, List.ofFn_getElem]
      _ = _ := List.map_ofFn
  rw [he, List.sum_ofFn]
  apply Finset.sum_le_sum_of_injOn (fun a : Fin K.length => (K.get a).input.time.val)
  · intro a _ b _ hab
    change (K.get a).input.time.val = (K.get b).input.time.val at hab
    by_contra hne
    have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · have h := horder.rel_get_of_lt hlt
      omega
    · have h := horder.rel_get_of_lt hgt
      omega
  · intro n hn
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (K.get a).input.time.isLt
  · intro a _
    exact hbound _ (List.get_mem K a)
  · intro n _ _
    exact hnonneg n

private theorem charges_le_supported
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (Record (rate := rate)))
    (horder : K.Pairwise (fun a b => a.input.time.val < b.input.time.val))
    (hsupport : ∀ r ∈ decoderSafePrefix rate rewards C_star C_h z K,
      (Pnew rate rewards C_star C_h control0 r.input.time.val z).Nonempty) :
    (∀ n, calendarCharge rate rewards C_star C_h z K n ≤
      if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0) ∧
    cappedCharge rate rewards C_star C_h z K ≤
      ∑ n ∈ Finset.range p.T,
        if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0 := by
  let F : ℕ → ℝ := fun n =>
    if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0
  have hF (n : ℕ) : 0 ≤ F n := by
    dsimp only [F]
    split
    · exact (ReferenceFirstCollectionRoundEndObservation.g_mem_Icc rewards n z).1
    · exact le_refl _
  have hD : (decoderSafePrefix rate rewards C_star C_h z K).Pairwise
      (fun a b => a.input.time.val < b.input.time.val) :=
    horder.sublist (List.takeWhile_sublist _)
  have hcap (r : Record (rate := rate))
      (hr : r ∈ decoderSafePrefix rate rewards C_star C_h z K) :
      (min p.m (positiveRewardCount rewards r.input.time) : ℝ) ≤ F r.input.time.val := by
    dsimp only [F]
    rw [ite_eq_left (hsupport r hr)]
    have hg : g rewards r.input.time.val z = (positiveRewardCount rewards r.input.time : ℝ) := by
      simp only [g, dite_eq_left r.input.time.isLt, Fin.eta]
    rw [hg]
    exact min_le_right _ _
  constructor
  · intro n
    have h := sum_map_le_calendar rate
      (decoderSafePrefix rate rewards C_star C_h z K) hD
      (fun r => if r.input.time.val = n then
        (min p.m (positiveRewardCount rewards r.input.time) : ℝ) else 0)
      (fun k => if k = n then F k else 0)
      (by
        intro r hr
        by_cases he : r.input.time.val = n
        · simp only [he, ite_true]
          simpa only [he] using hcap r hr
        · simp only [he, ite_false, le_refl])
      (by intro k; split <;> simp only [hF, le_refl])
    change calendarCharge rate rewards C_star C_h z K n ≤ F n
    change calendarCharge rate rewards C_star C_h z K n ≤
      ∑ k ∈ Finset.range p.T, (if k = n then F k else 0) at h
    calc
      calendarCharge rate rewards C_star C_h z K n ≤
          ∑ k ∈ Finset.range p.T, (if k = n then F k else 0) := h
      _ = if n ∈ Finset.range p.T then F n else 0 := by simp only [Finset.sum_ite_eq']
      _ ≤ F n := by split <;> simp only [le_refl, hF]
  · exact sum_map_le_calendar rate
      (decoderSafePrefix rate rewards C_star C_h z K) hD _ F hcap hF

/-- On the same literal first-replacement raw collection, all local outputs are
operationally safe. The global literal decoder prefix has exactly the incoming
raw pending support, and its original capped charge is dominated by the finite
new-support charge. All absent and nonmatching selectors remain alternatives.
The full initialized checked stream and its next-start/horizon endpoint are
retained from the raw construction. -/
theorem complete_first_replacement_literal_decoder_safe_support_and_charge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
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
                    ledger.pending = ∅) ∧
            (∀ a : Fin K.length, ¬ physicalFailureAt (K.get a)) ∧
            (∀ a : Fin K.length,
              let n := u - 1 + a.val
              (K.get a).input.time.val = n ∧
              (Safe rate rewards C_star C_h z n →
                Pnew rate rewards C_star C_h control0 n z = Praw rate rewards C_star C_h n z ∧
                Praw rate rewards C_star C_h n z =
                  ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                    payload.sigma.val (K.get a).input.time z ∧
                (Pnew rate rewards C_star C_h control0 n z).Nonempty)) ∧
            decoderSafePrefix rate rewards C_star C_h z K =
              K.filter (fun r => decide (Safe rate rewards C_star C_h z r.input.time.val)) ∧
            (∀ n, calendarCharge rate rewards C_star C_h z K n ≤
              if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0) ∧
            cappedCharge rate rewards C_star C_h z K ≤
              ∑ n ∈ Finset.range p.T,
                if (Pnew rate rewards C_star C_h control0 n z).Nonempty then g rewards n z else 0
          | _ => True
      | _ => True := by
  have hR := ReferenceFirstReplacementCollectionRawPendingTotal.complete_first_replacement_raw_calendar_pending_nonempty
    rate rewards C_star C_h z
  have hF := ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
    rate z rewards C_star C_h
  have hP := complete_first_replacement_pending_coordinates rate rewards C_star C_h control0 z
  dsimp only at hR hF hP ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hR hF hP ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hR hF hP
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hR hF hP ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hR hF hP ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hR hF hP
          cases outcome <;> try trivial
          dsimp only at hR hF hP ⊢
          let payload := installed.registers.payload
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          obtain ⟨stream, initializer, hdata⟩ := hR
          rcases hdata with ⟨_hsegment, _hrecords, _hremaining, _hpayload, _hinitializer,
            _hchecked, _hsigma, _hcutoff, _hfreeze, _hcursor, _hpending, _hincrement,
            _hgamma, _hraw, _hphase, _hrun, _hcompleted, hAll, _hendpoint, _hterminal⟩
          rcases hF with ⟨_hwindow, _hEzero, _hendpoints, _hu, _huT, _hfirst, hfollowers⟩
          have hdates (a : Fin K.length) :
              (K.get a).input.time.val + 1 = u + a.val := (hAll a).2.2.2.1
          have hlookup (a : Fin K.length) :
              actualRecord rate rewards C_star C_h (K.get a).input.time z = some (K.get a) :=
            (hAll a).2.2.1
          have hcoord (a : Fin K.length) : (K.get a).output.coordinator.failure = none :=
            (hAll a).2.2.2.2.2.2.2.1
          have hfollowersNone (a : Fin K.length) (i : Fin (p.m - 1)) :
              ((K.get a).output.followers i).failure = none := by
            rcases hfollowers i with ⟨_hsigma, _hcredit, old, initial, memory,
              _hinput, _hconfiguration, hcutFailure, _hinitial, _hstatus, _hdomain,
              _hmass, _hdelta, _hzero, _horigin, _hinitFailure, _hpair, _hbuffer,
              _hinvariant, hsteps, _hboundary⟩
            change (((cut :: W).get a).output.followers i).failure = none
            refine Fin.cases ?_ (fun b => ?_) a
            · exact hcutFailure
            · have hstep := (hsteps b.val b.isLt).2
              obtain ⟨state, logged, post, hstep⟩ := hstep
              have hout := hstep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              change (((W.get b).output.followers i).failure) = none
              rw [hout]
          have hfailure (a : Fin K.length) : ¬ physicalFailureAt (K.get a) := by
            rintro (⟨reason, hf⟩ | ⟨i, reason, hf⟩)
            · rw [hcoord a] at hf
              cases hf
            · rw [hfollowersNone a i] at hf
              cases hf
          have htime (a : Fin K.length) : (K.get a).input.time.val = u - 1 + a.val := by
            have hd := hdates a
            dsimp only [u] at hd ⊢
            omega
          have horder : K.Pairwise (fun a b => a.input.time.val < b.input.time.val) := by
            apply List.pairwise_iff_get.mpr
            intro a b hab
            have ha := hdates a
            have hb' := hdates b
            change a.val < b.val at hab
            omega
          have hle : K.Pairwise (fun a b => a.input.time.val ≤ b.input.time.val) :=
            horder.imp (fun h => Nat.le_of_lt h)
          have hpending (a : Fin K.length)
              (hsafe : Safe rate rewards C_star C_h z (u - 1 + a.val)) :
              Pnew rate rewards C_star C_h control0 (u - 1 + a.val) z =
                  Praw rate rewards C_star C_h (u - 1 + a.val) z ∧
              Praw rate rewards C_star C_h (u - 1 + a.val) z =
                ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  payload.sigma.val (K.get a).input.time z ∧
              (Pnew rate rewards C_star C_h control0 (u - 1 + a.val) z).Nonempty := by
            have hpa := hP a
            have honset : payloadOnset rate rewards C_star C_h (K.get a).input.time.val z =
                some (payload, u) := by
              rw [htime a]
              exact hpa.1
            have he := pending_eq_of_safe rate rewards C_star C_h control0 z K payload u
              hdates hlookup hfailure a honset (by rw [htime a]; exact hsafe)
            rw [htime a] at he
            refine ⟨he, hpa.2.2.1, ?_⟩
            rw [he, hpa.2.2.1]
            exact (hAll a).1
          have hsupport (r : Record (rate := rate))
              (hr : r ∈ decoderSafePrefix rate rewards C_star C_h z K) :
              (Pnew rate rewards C_star C_h control0 r.input.time.val z).Nonempty := by
            obtain ⟨hrK, hsafe⟩ :=
              (mem_decoderSafePrefix_iff rate rewards C_star C_h z K hle r).mp hr
            obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hrK
            rw [htime a] at hsafe ⊢
            exact (hpending a hsafe).2.2
          have hcharges := charges_le_supported rate rewards C_star C_h control0 z K horder hsupport
          refine ⟨?_, hfailure, ?_,
            decoderSafePrefix_eq_filter rate rewards C_star C_h z K hle, hcharges⟩
          · exact ⟨stream, initializer, _hsegment, _hrecords, _hremaining, _hpayload,
              _hinitializer, _hchecked, _hsigma, _hcutoff, _hfreeze, _hcursor, _hpending,
              _hincrement, _hgamma, _hraw, _hphase, _hrun, _hcompleted, hAll,
              _hendpoint, _hterminal⟩
          · intro a
            exact ⟨htime a, hpending a⟩

end Bandits.Support.ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport
