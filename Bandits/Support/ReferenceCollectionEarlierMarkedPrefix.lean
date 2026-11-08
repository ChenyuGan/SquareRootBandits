/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionSamplerChronology

/-!
# Earlier actual collection calls and their original marks

The lists in this module observe the existing actual invocation list. Each
mark retains the original source prefix, optional checked sampler outcome,
and complete assignment vector at the invocation's own date.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceCollectionEarlierMarkedPrefix

open Bandits.Support

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- Actual invocations strictly before calendar offset `n`, retaining calls
whose later checked sampler may fail. -/
def earlierCalls (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    List (ReferenceFirstCollectionSamplerCall.Call p) :=
  (ReferenceCollectionSamplerChronology.collectionCalls rate rewards C_star C_h z).filter
    (fun call => decide (call.2.1.val < n))

/-- Read the original marked payload at each retained call's calendar date. -/
def earlierMarkedCalls (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    List (Fin p.T × (Fin p.T ×
      ReferenceFirstCollectionPastSamplerFibreLaw.MarkedPayload p)) :=
  (earlierCalls rate rewards C_star C_h n z).map
    (fun call => (call.1, (call.2.1,
      ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 call.2.1 z)))

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) :=
  ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableListCons {X α : Type*} [MeasurableSpace X] [MeasurableSpace α]
    (head : X → α) (hhead : Measurable head) (tail : X → List α)
    (htail : Measurable tail) : Measurable (fun x => head x :: tail x) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    ReferenceActiveHorizonMeasurability.listObservationCoordinates (head x :: tail x))
  simp only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    List.length_cons]
  have hcoords :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp htail
  have hlength : Measurable (fun x => (tail x).length + 1) :=
    (measurable_of_countable (fun n : ℕ => n + 1)).comp
      (measurable_fst.comp hcoords)
  have hstream : Measurable (fun x => fun n =>
      ReferenceActiveHorizonMeasurability.listObservationAt (head x :: tail x) n) := by
    apply measurable_pi_iff.mpr
    intro n
    cases n with
    | zero =>
        change Measurable (fun x => Sum.inr (head x))
        exact measurable_inr.comp hhead
    | succ n =>
        have heq : (fun x =>
            ReferenceActiveHorizonMeasurability.listObservationAt (head x :: tail x) (n + 1)) =
            fun x => ReferenceActiveHorizonMeasurability.listObservationAt (tail x) n := by
          funext x
          rfl
        rw [heq]
        exact (measurable_pi_apply n).comp (measurable_snd.comp hcoords)
  exact hlength.prodMk hstream

private theorem measurableOptionCons {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α]
    (head : X → Option α) (hhead : Measurable head)
    (tail : X → List α) (htail : Measurable tail) :
    Measurable (fun x => (head x).elim (tail x) (fun a => a :: tail x)) := by
  let e := Equiv.optionEquivSumPUnit α
  let distrib := MeasurableEquiv.sumProdDistrib α PUnit X
  have hsome : Measurable (fun q : α × X => q.1 :: tail q.2) :=
    measurableListCons (fun q : α × X => q.1) measurable_fst
      (fun q : α × X => tail q.2) (htail.comp measurable_snd)
  have hnone : Measurable (fun q : PUnit × X => tail q.2) :=
    htail.comp measurable_snd
  have hsum : Measurable (Sum.elim
      (fun q : α × X => q.1 :: tail q.2)
      (fun q : PUnit × X => tail q.2) ∘ distrib) :=
    (hsome.sumElim hnone).comp distrib.measurable_toFun
  have hsource : Measurable (fun x => (e (head x), x)) :=
    ((comap_measurable e).comp hhead).prodMk measurable_id
  have hresult : Measurable (fun x =>
      Sum.elim (fun q : α × X => q.1 :: tail q.2)
        (fun q : PUnit × X => tail q.2) (distrib (e (head x), x))) :=
    hsum.comp hsource
  convert hresult using 1
  funext x
  cases head x <;> rfl

private theorem measurableFilterMapFinRange {X α : Type*}
    [MeasurableSpace X] [MeasurableSpace α] (n : ℕ)
    (f : Fin n → X → Option α) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => (List.finRange n).filterMap (fun i => f i x)) := by
  induction n with
  | zero =>
      exact measurable_const
  | succ n ih =>
      let tailFn : Fin n → X → Option α := fun i x => f i.succ x
      have htail : Measurable (fun x =>
          (List.finRange n).filterMap (fun i => tailFn i x)) :=
        ih tailFn (fun i => hf i.succ)
      have hrepr : (fun x =>
          (List.finRange (n + 1)).filterMap (fun i => f i x)) =
          fun x => (f 0 x).elim
            ((List.finRange n).filterMap (fun i => f i.succ x))
            (fun a => a :: (List.finRange n).filterMap (fun i => f i.succ x)) := by
        funext x
        simp only [List.finRange_succ, List.filterMap_cons,
          List.filterMap_map, Function.comp_def]
        cases f 0 x <;> rfl
      rw [hrepr]
      exact measurableOptionCons (fun x => f 0 x) (hf 0) _ htail

private theorem filterMap_filter {A B : Type*} (l : List A)
    (f : A → Option B) (P : B → Bool) :
    (l.filterMap f).filter P =
      l.filterMap (fun a => (f a).bind fun b => if P b then some b else none) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hf : f a with
      | none => simp [hf, ih]
      | some b =>
          cases hp : P b <;> simp [hf, hp, ih]

private theorem map_filterMap {A B C : Type*} (l : List A)
    (f : A → Option B) (g : B → C) :
    (l.filterMap f).map g = l.filterMap (fun a => (f a).map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hf : f a <;> simp [hf, ih]

/-- Filtering actual calls by their own calendar date is exactly a finite
calendar filterMap. -/
theorem earlierCalls_eq_finRange (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierCalls rate rewards C_star C_h n z =
      (List.finRange p.T).filterMap (fun s =>
        if s.val < n then
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h s z).map (fun c => (c.1, (s, c.2)))
        else none) := by
  rw [earlierCalls, ReferenceCollectionSamplerChronology.collectionCalls_eq_finRange]
  let f : Fin p.T → Option (ReferenceFirstCollectionSamplerCall.Call p) := fun s =>
    (ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h s z).map (fun c => (c.1, (s, c.2)))
  change ((List.finRange p.T).filterMap f).filter
      (fun call => decide (call.2.1.val < n)) = _
  rw [filterMap_filter]
  congr 1
  funext s
  by_cases hs : s.val < n <;>
    cases hc : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h s z <;> simp [f, hs, hc]

/-- The earlier-call marks use the same finite calendar cells and the
existing first-collection past-fibre payload. -/
theorem earlierMarkedCalls_eq_finRange
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierMarkedCalls rate rewards C_star C_h control0 n z =
      (List.finRange p.T).filterMap (fun s =>
        if s.val < n then
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h s z).map (fun c =>
              (c.1, (s, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
                rate rewards C_star C_h control0 s z)))
        else none) := by
  rw [earlierMarkedCalls, earlierCalls_eq_finRange, map_filterMap]
  congr 1
  funext s
  by_cases hs : s.val < n <;>
    cases hc : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h s z <;> simp [hs]

/-- The exact number of calls before a calendar offset is the chronology
module's finite actual-call count. -/
theorem earlierCalls_length (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (earlierCalls rate rewards C_star C_h s.val z).length =
      ReferenceCollectionSamplerChronology.priorCallCount
        rate rewards C_star C_h s z := by
  rw [earlierCalls_eq_finRange]
  have hcount :
      ((List.finRange p.T).filterMap (fun v =>
        if v.val < s.val then
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h v z).map (fun c => (c.1, (v, c.2)))
        else none)).length =
        (List.finRange p.T).countP (fun v =>
          decide (v.val < s.val) &&
            (ReferenceCalendarCollectionCallControlLaw.callAt
              rate rewards C_star C_h v z).isSome) := by
    simp only [List.length_filterMap_eq_countP]
    congr 1
    funext v
    by_cases hv : v.val < s.val <;>
      cases hc : ReferenceCalendarCollectionCallControlLaw.callAt
        rate rewards C_star C_h v z <;> simp [hv]
  rw [hcount]
  unfold ReferenceCollectionSamplerChronology.priorCallCount
  calc
    (List.finRange p.T).countP (fun v =>
        decide (v.val < s.val) &&
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h v z).isSome) =
      ((List.finRange p.T).filter (fun v =>
        decide (v.val < s.val) &&
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h v z).isSome)).length := by
          rw [List.countP_eq_length_filter]
    _ = ((List.finRange p.T).filter (fun v =>
        decide (v.val < s.val) &&
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h v z).isSome)).toFinset.card := by
          symm
          exact List.toFinset_card_of_nodup
            ((List.nodup_finRange p.T).filter _)
    _ = (Finset.univ.filter (fun v : Fin p.T =>
        v.val < s.val ∧
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h v z).isSome)).card := by
          congr 1
          ext v
          simp

/-- Mapping does not change the finite number of retained invocation marks. -/
theorem earlierMarkedCalls_length
    (control0 : ContinuousLearningRows.TimeControl p) (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (earlierMarkedCalls rate rewards C_star C_h control0 s.val z).length =
      ReferenceCollectionSamplerChronology.priorCallCount
        rate rewards C_star C_h s z := by
  simp only [earlierMarkedCalls, List.length_map]
  exact earlierCalls_length rate rewards C_star C_h s z

/-- No date is strictly before the initial calendar offset. -/
theorem earlierCalls_zero (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierCalls rate rewards C_star C_h 0 z = [] := by
  rw [earlierCalls_eq_finRange]
  simp

/-- The initial marked list is empty. -/
theorem earlierMarkedCalls_zero (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierMarkedCalls rate rewards C_star C_h control0 0 z = [] := by
  rw [earlierMarkedCalls_eq_finRange]
  simp

private theorem pastFibrePair_successor_factor
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
      rate rewards C_star C_h control0 t z =
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
      rate rewards C_star C_h control0 t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  have hprefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val (t.val + 1) (Nat.le_succ _) z
  have hout : ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
      rate rewards C_star C_h t z =
    ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
    simp only [ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt]
    rw [ReferenceCalendarLaterSamplerOutputSections.outputAt_successor_factor
      rate rewards C_star C_h control0 t z]
  have hvector : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z =
      ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
    simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
      ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
  unfold ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
  rw [hprefix, hout, hvector]

private theorem pastFibrePair_factor_through_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (ht : t.val < n) :
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
      rate rewards C_star C_h control0 t z =
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
      rate rewards C_star C_h control0 t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have htn : t.val + 1 ≤ n := by omega
  calc
    _ = ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) :=
      pastFibrePair_successor_factor rate rewards C_star C_h control0 t z
    _ = ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1)
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 (t.val + 1) n htn z]
    _ = _ := (pastFibrePair_successor_factor rate rewards C_star C_h control0 t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).symm

private theorem callAt_factor_through_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (ht : t.val < n) :
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  calc
    _ = ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
      ReferenceCalendarCollectionCallControlLaw.callAt_factor
        rate rewards C_star C_h control0 t z
    _ = ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val n ht.le z]
    _ = _ := (ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).symm

/-- Every retained actual call is determined by the original source prefix
ending at `n`. -/
theorem earlierCalls_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (_hn : n ≤ p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierCalls rate rewards C_star C_h n z =
      earlierCalls rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  rw [earlierCalls_eq_finRange, earlierCalls_eq_finRange]
  congr 1
  funext t
  by_cases ht : t.val < n
  · simp [ht]
    rw [callAt_factor_through_prefix rate rewards C_star C_h control0 n t z ht]
  · simp [ht]

/-- Every earlier marked call retains its exact original-date mark under the
same source-prefix factorization. -/
theorem earlierMarkedCalls_factor
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (_hn : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    earlierMarkedCalls rate rewards C_star C_h control0 n z =
      earlierMarkedCalls rate rewards C_star C_h control0 n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  rw [earlierMarkedCalls_eq_finRange, earlierMarkedCalls_eq_finRange]
  congr 1
  funext t
  by_cases ht : t.val < n
  · simp [ht]
    rw [callAt_factor_through_prefix rate rewards C_star C_h control0 n t z ht,
      pastFibrePair_factor_through_prefix rate rewards C_star C_h control0 n t z ht]
  · simp [ht]

private theorem callAt_ambient_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h t) :=
  (ReferenceCalendarCollectionCallControlLaw.callAt_measurable
    rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1)) le_rfl

/-- The finite list of earlier calls is Borel in the original continuous
source space. -/
theorem earlierCalls_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable (earlierCalls rate rewards C_star C_h n) := by
  have heq : (fun z => earlierCalls rate rewards C_star C_h n z) = fun z =>
      (List.finRange p.T).filterMap (fun t =>
        if t.val < n then
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h t z).map (fun c => (c.1, (t, c.2)))
        else none) := by
    funext z
    exact earlierCalls_eq_finRange rate rewards C_star C_h n z
  change Measurable (fun z => earlierCalls rate rewards C_star C_h n z)
  rw [heq]
  apply measurableFilterMapFinRange
  intro t
  by_cases ht : t.val < n
  · simp [ht]
    let pack : Fin p.T × ReferenceCalendarCollectionCallControlLaw.Theta p →
        ReferenceFirstCollectionSamplerCall.Call p :=
      fun c => (c.1, (t, c.2))
    have hpack : Measurable pack := by
      apply measurable_fst.prodMk
      exact measurable_const.prodMk measurable_snd
    exact LaterAssignmentFullOutputMeasurability.measurable_optionMap
      pack hpack _ (callAt_ambient_measurable rate rewards C_star C_h control0 t)
  · simp [ht]

/-- The finite list of actual calls with their original marked payloads is
Borel on the original product source. -/
theorem earlierMarkedCalls_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable (earlierMarkedCalls rate rewards C_star C_h control0 n) := by
  have heq : (fun z => earlierMarkedCalls rate rewards C_star C_h control0 n z) =
      fun z => (List.finRange p.T).filterMap (fun t =>
        if t.val < n then
          (ReferenceCalendarCollectionCallControlLaw.callAt
            rate rewards C_star C_h t z).map (fun c =>
              (c.1, (t, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
                rate rewards C_star C_h control0 t z)))
        else none) := by
    funext z
    exact earlierMarkedCalls_eq_finRange rate rewards C_star C_h control0 n z
  change Measurable (fun z => earlierMarkedCalls rate rewards C_star C_h control0 n z)
  rw [heq]
  apply measurableFilterMapFinRange
  intro t
  by_cases ht : t.val < n
  · simp [ht]
    have hpair := ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair_measurable
      rate rewards C_star C_h control0 t
    have hmap : Measurable (fun w :
        (Fin p.T × ReferenceCalendarCollectionCallControlLaw.Theta p) ×
          BootstrapPrivateRoundStreams.SourceInput p =>
        (w.1.1, (t, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
          rate rewards C_star C_h control0 t w.2))) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_const.prodMk (hpair.comp measurable_snd))
    exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun w => (w.1.1, (t,
        ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
          rate rewards C_star C_h control0 t w.2))) hmap
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t)
      (callAt_ambient_measurable rate rewards C_star C_h control0 t)
  · simp [ht]

/-- Earlier calls are measurable in the exact source-prefix field
`sourcePrefixFiltration control0 (n + 1)`. -/
theorem earlierCalls_sourcePrefix_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)] (earlierCalls rate rewards C_star C_h n) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  apply Measurable.of_comap_le
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (earlierCalls rate rewards C_star C_h n)
    (earlierCalls_measurable rate rewards C_star C_h control0 n)
  funext z
  exact earlierCalls_factor rate rewards C_star C_h control0 n hn z

/-- Earlier original marks are measurable in the exact successor-prefix
field, retaining the continuous vector and outcome carriers. -/
theorem earlierMarkedCalls_sourcePrefix_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)]
      (earlierMarkedCalls rate rewards C_star C_h control0 n) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  apply Measurable.of_comap_le
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (earlierMarkedCalls rate rewards C_star C_h control0 n)
    (earlierMarkedCalls_measurable rate rewards C_star C_h control0 n)
  funext z
  exact earlierMarkedCalls_factor rate rewards C_star C_h control0 n hn z

/-- Replacing the entire current control leaves every earlier actual call
unchanged. -/
theorem earlierCalls_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    earlierCalls rate rewards C_star C_h s.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
    earlierCalls rate rewards C_star C_h s.val z := by
  calc
    _ = earlierCalls rate rewards C_star C_h s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c)) :=
      earlierCalls_factor rate rewards C_star C_h control0 s.val
        (Nat.le_of_lt s.isLt)
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c)
    _ = earlierCalls rate rewards C_star C_h s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
      rw [ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl]
    _ = earlierCalls rate rewards C_star C_h s.val z :=
      (earlierCalls_factor rate rewards C_star C_h control0 s.val
        (Nat.le_of_lt s.isLt) z).symm

/-- Replacing every label of the current control leaves all earlier original
marks, including complete assignment vectors, unchanged. -/
theorem earlierMarkedCalls_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    earlierMarkedCalls rate rewards C_star C_h control0 s.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
    earlierMarkedCalls rate rewards C_star C_h control0 s.val z := by
  calc
    _ = earlierMarkedCalls rate rewards C_star C_h control0 s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c)) :=
      earlierMarkedCalls_factor rate rewards C_star C_h control0 s.val
        (Nat.le_of_lt s.isLt)
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c)
    _ = earlierMarkedCalls rate rewards C_star C_h control0 s.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
      rw [ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl]
    _ = earlierMarkedCalls rate rewards C_star C_h control0 s.val z :=
      (earlierMarkedCalls_factor rate rewards C_star C_h control0 s.val
        (Nat.le_of_lt s.isLt) z).symm

private theorem earlierCalls_eq_take_of_present_rank_aux (k : ℕ)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    earlierCalls rate rewards C_star C_h s.val z =
      (ReferenceCollectionSamplerChronology.collectionCalls
        rate rewards C_star C_h z).take k := by
  let calls := ReferenceCollectionSamplerChronology.collectionCalls
    rate rewards C_star C_h z
  let present := (u, (s, theta))
  have hget : calls[k]? = some present := hcall
  have hhead : (calls.drop k).head? = some present := by
    rw [List.head?_eq_getElem?, List.getElem?_drop]
    simpa using hget
  have hdrop : calls.drop k = present :: calls.drop (k + 1) := by
    cases hd : calls.drop k with
    | nil => simp [hd] at hhead
    | cons a tail =>
        simp only [hd, List.head?_cons] at hhead
        have ha : a = present := Option.some.inj hhead
        subst a
        have htail : tail = calls.drop (k + 1) := by
          calc
            tail = (present :: tail).drop 1 := by simp
            _ = (calls.drop k).drop 1 := by rw [hd]
            _ = calls.drop (k + 1) := by rw [List.drop_drop]
        exact congrArg (List.cons present) htail
  have hsplit : calls = calls.take k ++ (present :: calls.drop (k + 1)) := by
    calc
      calls = calls.take k ++ calls.drop k := (List.take_append_drop k calls).symm
      _ = calls.take k ++ (present :: calls.drop (k + 1)) := by rw [hdrop]
  have hpair : calls.Pairwise (fun a b => a.2.1.val < b.2.1.val) :=
    ReferenceCollectionSamplerChronology.collectionCalls_dates_strict
      rate rewards C_star C_h z
  rw [hsplit] at hpair
  obtain ⟨_, hright, hcross⟩ := List.pairwise_append.mp hpair
  have hprefix : (calls.take k).filter
      (fun call => decide (call.2.1.val < s.val)) = calls.take k := by
    apply List.filter_eq_self.mpr
    intro a ha
    have hab : a.2.1.val < present.2.1.val := hcross a ha present (by simp)
    exact of_decide_eq_true (by simpa [present] using hab)
  have htailPair : (present :: calls.drop (k + 1)).Pairwise
      (fun a b => a.2.1.val < b.2.1.val) := hright
  have htail : (present :: calls.drop (k + 1)).filter
      (fun call => decide (call.2.1.val < s.val)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    rcases List.mem_cons.mp ha with hhead' | htail'
    · subst a
      simp [present]
    · have hab := htailPair.rel_head_tail htail'
      have hnot : ¬ a.2.1.val < s.val := by
        have hdate : s.val < a.2.1.val := by simpa [present] using hab
        omega
      simp [hnot]
  change calls.filter (fun call => decide (call.2.1.val < s.val)) = calls.take k
  calc
    _ = (calls.take k ++ (present :: calls.drop (k + 1))).filter
        (fun call => decide (call.2.1.val < s.val)) :=
          congrArg (fun xs => xs.filter (fun call => decide (call.2.1.val < s.val))) hsplit
    _ = calls.take k := by
      rw [List.filter_append, hprefix, htail]
      simp

/-- At a real present rank, the earlier-date observer is exactly the genuine
rank prefix of the actual invocation list. -/
theorem earlierCalls_eq_take_of_present_rank (k : ℕ)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    earlierCalls rate rewards C_star C_h s.val z =
      (ReferenceCollectionSamplerChronology.collectionCalls
        rate rewards C_star C_h z).take k :=
  earlierCalls_eq_take_of_present_rank_aux rate rewards C_star C_h k u s theta z hcall

/-- The same actual rank prefix with its literal, unchanged original marks. -/
theorem earlierMarkedCalls_eq_mapped_take_of_present_rank
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    earlierMarkedCalls rate rewards C_star C_h control0 s.val z =
      ((ReferenceCollectionSamplerChronology.collectionCalls
        rate rewards C_star C_h z).take k).map (fun call =>
          (call.1, (call.2.1,
            ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
              rate rewards C_star C_h control0 call.2.1 z))) := by
  rw [earlierMarkedCalls, earlierCalls_eq_take_of_present_rank
    rate rewards C_star C_h k u s theta z hcall]

/-- The actual rank/date/parameter selector survives replacing the complete
current control; no equality of the current sampler outcome is asserted. -/
theorem nthCollectionCall_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
        some (u, (s, theta)) := by
  have hAt : ReferenceCollectionSamplerChronology.nthAt
      rate rewards C_star C_h k s z = some (u, theta) := by
    simp [ReferenceCollectionSamplerChronology.nthAt, hcall]
  have hAt' : ReferenceCollectionSamplerChronology.nthAt
      rate rewards C_star C_h k s
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
      some (u, theta) :=
    (ReferenceCollectionSamplerChronology.nthAt_replaceSourceControl
      rate rewards C_star C_h control0 k s z c).trans hAt
  cases hrank : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) with
  | none => simp [ReferenceCollectionSamplerChronology.nthAt, hrank] at hAt'
  | some call =>
      rcases call with ⟨u', s', theta'⟩
      simp only [ReferenceCollectionSamplerChronology.nthAt, hrank,
        Option.bind_some] at hAt'
      split_ifs at hAt' with hs'
      · have hpair : (u', theta') = (u, theta) := Option.some.inj hAt'
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        have hs' : s' = s := hs'
        subst s'
        rfl

/-- The earlier calls, all their original marks, and the present actual rank
survive replacing every coordinate of the current control. -/
theorem presentRank_prefix_and_marks_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p)
    (hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z = some (u, (s, theta))) :
    ReferenceCollectionSamplerChronology.nthCollectionCall rate rewards C_star C_h k
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
        some (u, (s, theta)) ∧
    earlierCalls rate rewards C_star C_h s.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
      (ReferenceCollectionSamplerChronology.collectionCalls
        rate rewards C_star C_h z).take k ∧
    earlierMarkedCalls rate rewards C_star C_h control0 s.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
      ((ReferenceCollectionSamplerChronology.collectionCalls
        rate rewards C_star C_h z).take k).map (fun call =>
          (call.1, (call.2.1,
            ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
              rate rewards C_star C_h control0 call.2.1 z))) := by
  refine ⟨nthCollectionCall_replaceSourceControl rate rewards C_star C_h
      control0 k u s theta z c hcall, ?_, ?_⟩
  · rw [earlierCalls_replaceSourceControl rate rewards C_star C_h control0 s z c]
    exact earlierCalls_eq_take_of_present_rank rate rewards C_star C_h k u s theta z hcall
  · rw [earlierMarkedCalls_replaceSourceControl
      rate rewards C_star C_h control0 s z c]
    exact earlierMarkedCalls_eq_mapped_take_of_present_rank
      rate rewards C_star C_h control0 k u s theta z hcall

end Bandits.Support.ReferenceCollectionEarlierMarkedPrefix

end
