/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPhysicalContinuationFibreLaw

/-!
# Ranks of actual collection sampler invocations

These observers filter the complete actual physical suffix. They retain calls
whose subsequent inclusion or orientation draw fails. The date projection of
each rank is determined by the original source strictly before its own draw.
No stochastic transport or logical learner identification is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceCollectionSamplerChronology

open Bandits.Support

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- All actual invocations, in physical order, with absent cells removed. -/
def collectionCalls (z : BootstrapPrivateRoundStreams.SourceInput p) :
    List (ReferenceFirstCollectionSamplerCall.Call p) :=
  (ReferenceFirstCollectionSamplerCall.collectionCallCalendar rate rewards C_star C_h z).filterMap
    ReferenceFirstCollectionSamplerCall.callInCell

/-- Zero-based rank in the literal invocation list. -/
def nthCollectionCall (k : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (ReferenceFirstCollectionSamplerCall.Call p) :=
  (collectionCalls rate rewards C_star C_h z)[k]?

/-- Observe rank `k` only at its own physical date. -/
def nthAt (k : ℕ) (s : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCalendarCollectionCallControlLaw.CallAt p :=
  (nthCollectionCall rate rewards C_star C_h k z).bind
    (fun c => if c.2.1 = s then some (c.1, c.2.2) else none)

/-- Number of present actual calendar calls strictly before `s`. -/
def priorCallCount (s : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  (Finset.univ.filter (fun v : Fin p.T =>
    v.val < s.val ∧
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z).isSome)).card

/-- Filtering the original actual records directly gives the same list. -/
theorem collectionCalls_eq_records (z : BootstrapPrivateRoundStreams.SourceInput p) :
    collectionCalls rate rewards C_star C_h z =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).filterMap (fun r =>
          ReferenceFirstCollectionSamplerCall.callInCell
            (r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r)) := by
  simp only [collectionCalls, ReferenceFirstCollectionSamplerCall.collectionCallCalendar,
    List.filterMap_map, Function.comp_def]

/-- The invocation readout starts with the empty actual prefix. -/
theorem actualCallPrefix_zero (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take 0).filterMap (fun r =>
        ReferenceFirstCollectionSamplerCall.callInCell
          (r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r)) = [] := by
  simp only [List.take_zero, List.filterMap_nil]

/-- Appending an actual record appends its literal optional call. There is
no test of whether the subsequent assignment sampler succeeds. -/
theorem actualCallPrefix_succ (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n]? = some r) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take (n + 1)).filterMap (fun record =>
        ReferenceFirstCollectionSamplerCall.callInCell
          (record.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt record)) =
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take n).filterMap (fun record =>
          ReferenceFirstCollectionSamplerCall.callInCell
            (record.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt record)) ++
        (ReferenceFirstCollectionSamplerCall.callInCell
          (r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r)).toList := by
  rw [List.take_add_one, hr]
  simp only [Option.toList_some, List.filterMap_append]
  cases hc : ReferenceFirstCollectionSamplerCall.callInCell
      (r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r) <;> simp [hc]

theorem collectionCalls_head (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (collectionCalls rate rewards C_star C_h z).head? =
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z := by
  exact List.head?_filterMap

theorem nthCollectionCall_zero (z : BootstrapPrivateRoundStreams.SourceInput p) :
    nthCollectionCall rate rewards C_star C_h 0 z =
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z := by
  simpa only [nthCollectionCall, ← List.head?_eq_getElem?] using
    collectionCalls_head rate rewards C_star C_h z

theorem collectionCalls_length (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (collectionCalls rate rewards C_star C_h z).length ≤
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
  exact (List.length_filterMap_le ReferenceFirstCollectionSamplerCall.callInCell _).trans_eq
    (ReferenceFirstCollectionSamplerCall.collectionCallCalendar_length (rate := rate) rewards C_star C_h z)

theorem nthCollectionCall_eq_none_iff (k : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    nthCollectionCall rate rewards C_star C_h k z = none ↔
      (collectionCalls rate rewards C_star C_h z).length ≤ k := by
  exact List.getElem?_eq_none_iff

theorem collectionCalls_dates_strict (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (collectionCalls rate rewards C_star C_h z).Pairwise
      (fun a b => a.2.1.val < b.2.1.val) := by
  have hcalendar : (ReferenceFirstCollectionSamplerCall.collectionCallCalendar rate rewards C_star C_h z).Pairwise
      (fun a b => a.1.val < b.1.val) := by
    apply List.pairwise_map.mp
    rw [ReferenceFirstCollectionSamplerCall.collectionCallCalendar_times]
    exact List.pairwise_lt_range'
  apply hcalendar.filterMap ReferenceFirstCollectionSamplerCall.callInCell
  intro a b hab x hx y hy
  obtain ⟨ax, hax, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨by', hby, rfl⟩ := Option.map_eq_some_iff.mp hy
  exact hab

private theorem nth_filterMap_spec {A B : Type*} (f : A → Option B)
    (l : List A) (k : ℕ) (b : B) :
    (l.filterMap f)[k]? = some b ↔
      ∃ n a, l[n]? = some a ∧ f a = some b ∧
        ((l.take n).filterMap f).length = k := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
      cases hf : f a with
      | none =>
          simp only [List.filterMap_cons_none hf]
          rw [ih]
          constructor
          · rintro ⟨n, x, hn, hx, hk⟩
            exact ⟨n + 1, x, hn, hx, by simpa [hf] using hk⟩
          · rintro ⟨n, x, hn, hx, hk⟩
            cases n with
            | zero => simp_all
            | succ n => exact ⟨n, x, hn, hx, by simpa [hf] using hk⟩
      | some c =>
          rw [List.filterMap_cons_some hf]
          cases k with
          | zero =>
              constructor
              · intro h
                have hcb : c = b := Option.some.inj h
                exact ⟨0, a, rfl, hcb ▸ hf, rfl⟩
              · rintro ⟨n, x, hn, hx, hk⟩
                cases n with
                | zero => simp_all
                | succ n => simp [hf] at hk
          | succ k =>
              simp only [List.getElem?_cons_succ]
              rw [ih]
              constructor
              · rintro ⟨n, x, hn, hx, hk⟩
                exact ⟨n + 1, x, hn, hx, by simp [hf, hk]⟩
              · rintro ⟨n, x, hn, hx, hk⟩
                cases n with
                | zero => simp at hk
                | succ n => exact ⟨n, x, hn, hx, by simpa [hf] using hk⟩

/-- Present ranks are exactly indexed actual records with exactly `k` earlier
present selectors. The count is over actual records, including failed draws. -/
theorem nthCollectionCall_spec (k : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p) :
    nthCollectionCall rate rewards C_star C_h k z = some (u, (s, theta)) ↔
      ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate),
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r ∧
        r.input.time = s ∧ ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take n).countP
          (fun earlier => (ReferenceFirstCollectionSamplerCall.collectionCallAt earlier).isSome) = k := by
  let f : ReferenceFirstCollectionSamplerCall.RoundRecord p rate →
      Option (ReferenceFirstCollectionSamplerCall.Call p) := fun r =>
    ReferenceFirstCollectionSamplerCall.callInCell
      (r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r)
  have hlist : collectionCalls rate rewards C_star C_h z =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).filterMap f := by
    exact collectionCalls_eq_records rate rewards C_star C_h z
  have hcount (l : List (ReferenceFirstCollectionSamplerCall.RoundRecord p rate)) :
      (l.filterMap f).length =
        l.countP (fun r => (ReferenceFirstCollectionSamplerCall.collectionCallAt r).isSome) := by
    simp only [List.length_filterMap_eq_countP, f,
      ReferenceFirstCollectionSamplerCall.callInCell, Option.isSome_map]
  unfold nthCollectionCall
  rw [hlist, nth_filterMap_spec]
  constructor
  · rintro ⟨n, r, hr, hf, hk⟩
    obtain ⟨⟨u', theta'⟩, hc, heq⟩ := Option.map_eq_some_iff.mp hf
    cases heq
    exact ⟨n, r, hr, rfl, hc, by rwa [hcount] at hk⟩
  · rintro ⟨n, r, hr, ht, hc, hk⟩
    refine ⟨n, r, hr, ?_, ?_⟩
    · simp only [f, ReferenceFirstCollectionSamplerCall.callInCell, hc, Option.map_some, ht]
    · rwa [hcount]

private theorem record_time_of_get (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r) :
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
  have hn := (List.getElem?_eq_some_iff.mp hr).1
  have hn' : n < p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
  have ht := congrArg (fun xs : List ℕ => xs[n]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h)
  simp only [List.getElem?_map, hr, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hn', Nat.one_mul] at ht
  exact Option.some.inj ht

/-- The record witness of a ranked call is the genuine calendar lookup and
supplies its actual continuous parameters. Neither is a premise. -/
theorem nthCollectionCall_actualRecord (k : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u s : Fin p.T)
    (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (h : nthCollectionCall rate rewards C_star C_h k z = some (u, (s, theta))) :
    ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h s z = some r ∧
      r.input.time = s ∧ ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h s z = some theta ∧
      (ReferenceActiveHorizonMeasurability.roundRecordCode r).1 = s.val ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1 = r.input.state := by
  obtain ⟨n, r, hr, ht, hc, _⟩ :=
    (nthCollectionCall_spec rate rewards C_star C_h k z u s theta).mp h
  have htime := record_time_of_get rate rewards C_star C_h z n r hr
  rw [ht] at htime
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ s.val := by omega
  have hoffset : s.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = n := by omega
  have ha : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h s z = some r := by
    simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart, hoffset, hr]
  obtain ⟨_, _, _, _, hp⟩ := (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hc
  obtain ⟨hlabel, hstate, _⟩ :=
    ReferenceFirstCollectionPhysicalContinuationFibreLaw.actualRecord_code_reconstructs rate r
  refine ⟨n, r, hr, ha, ht, hc, ?_, ?_, hstate⟩
  · simp only [ReferenceCalendarLaterSamplerPredictability.calendarParameters, ha, Option.bind_some, hp]
  · exact hlabel.trans (congrArg Fin.val ht)

private theorem time_of_actualRecord (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h s z = some r) : r.input.time = s := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  · have ht := record_time_of_get rate rewards C_star C_h z _ r hr
    apply Fin.ext
    omega

/-- Present calendar calls and members of the ranked list are the same actual
invocations, with both cutoff and continuous parameter retained. -/
theorem mem_collectionCalls_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u s : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p) :
    (u, (s, theta)) ∈ collectionCalls rate rewards C_star C_h z ↔
      ReferenceCalendarCollectionCallControlLaw.callAt
        rate rewards C_star C_h s z = some (u, theta) := by
  constructor
  · intro hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨_, r, _, ha, _, hc, _⟩ :=
      nthCollectionCall_actualRecord rate rewards C_star C_h k z u s theta hk
    simp only [ReferenceCalendarCollectionCallControlLaw.callAt, ha, Option.bind_some, hc]
  · intro hc
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h s z with
    | none => simp [ReferenceCalendarCollectionCallControlLaw.callAt, hr] at hc
    | some r =>
        have ht := time_of_actualRecord rate rewards C_star C_h s z r hr
        have hc' : ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) := by
          simpa only [ReferenceCalendarCollectionCallControlLaw.callAt, hr,
            Option.bind_some] using hc
        have hm : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h := by
          unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
          split_ifs at hr
          · exact List.mem_of_getElem? hr
        apply List.mem_filterMap.mpr
        refine ⟨(r.input.time, ReferenceFirstCollectionSamplerCall.collectionCallAt r), ?_, ?_⟩
        · exact List.mem_map.mpr ⟨r, hm, rfl⟩
        · simp only [ReferenceFirstCollectionSamplerCall.callInCell, hc', ht, Option.map_some]

/-- The complete invocation list is also the filter of the finite original
calendar. Before-start dates contribute `none`, and later dates use their
genuine physical suffix offsets. This equality introduces no replacement run. -/
theorem collectionCalls_eq_finRange (z : BootstrapPrivateRoundStreams.SourceInput p) :
    collectionCalls rate rewards C_star C_h z =
      (List.finRange p.T).filterMap (fun s =>
        (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z).map
          (fun c => (c.1, (s, c.2)))) := by
  let f : Fin p.T → Option (ReferenceFirstCollectionSamplerCall.Call p) := fun s =>
    (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z).map
      (fun c => (c.1, (s, c.2)))
  have hfin : (List.finRange p.T).Pairwise (fun a b => a.val < b.val) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem_finRange, Fin.val_cast] using hij
  have hfull : ((List.finRange p.T).filterMap f).Pairwise
      (fun a b => a.2.1.val < b.2.1.val) := by
    apply hfin.filterMap f
    intro a b hab x hx y hy
    obtain ⟨ax, _, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨by', _, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact hab
  have hmem (c : ReferenceFirstCollectionSamplerCall.Call p) :
      c ∈ collectionCalls rate rewards C_star C_h z ↔
        c ∈ (List.finRange p.T).filterMap f := by
    rcases c with ⟨u, s, theta⟩
    rw [mem_collectionCalls_iff]
    constructor
    · intro hc
      exact List.mem_filterMap.mpr ⟨s, List.mem_finRange s, by simp only [f, hc, Option.map_some]⟩
    · intro hm
      obtain ⟨t, _, ht⟩ := List.mem_filterMap.mp hm
      obtain ⟨⟨u', theta'⟩, hc, heq⟩ := Option.map_eq_some_iff.mp ht
      cases heq
      exact hc
  have hleft := collectionCalls_dates_strict rate rewards C_star C_h z
  have hnleft : (collectionCalls rate rewards C_star C_h z).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hleft.imp fun hab heq => by
      cases heq
      exact Nat.lt_irrefl _ hab
  have hnright : ((List.finRange p.T).filterMap f).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hfull.imp fun hab heq => by
      cases heq
      exact Nat.lt_irrefl _ hab
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by omega)
    hleft hfull ((List.perm_ext_iff_of_nodup hnleft hnright).mpr hmem)

private theorem count_before_nth {A : Type*} (date : A → ℕ)
    (l : List A) (h : l.Pairwise (fun a b => date a < date b))
    (k : ℕ) (a : A) (ha : l[k]? = some a) :
    l.countP (fun b => decide (date b < date a)) = k := by
  induction l generalizing k with
  | nil => simp at ha
  | cons b l ih =>
      obtain ⟨hbl, hl⟩ := List.pairwise_cons.mp h
      cases k with
      | zero =>
          have hba : b = a := Option.some.inj ha
          subst a
          rw [List.countP_cons_of_neg (by simp)]
          exact List.countP_eq_zero.mpr fun c hc => by
            simp only [Bool.not_eq_true, decide_eq_false_iff_not]
            exact Nat.not_lt_of_ge (Nat.le_of_lt (hbl c hc))
      | succ k =>
          have ha' : l[k]? = some a := ha
          have hba := hbl a (List.mem_of_getElem? ha')
          rw [List.countP_cons_of_pos (by simpa only [decide_eq_true_eq] using hba)]
          rw [ih hl k ha']

/-- The finite strict-past cardinal is the number of earlier entries in the
actual invocation list, including all present selectors. -/
theorem priorCallCount_eq_countP (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    priorCallCount rate rewards C_star C_h s z =
      (collectionCalls rate rewards C_star C_h z).countP
        (fun c => decide (c.2.1.val < s.val)) := by
  rw [collectionCalls_eq_finRange, List.countP_filterMap]
  have hc := (List.nodup_finRange p.T).card_eq_countP
    (P := fun v : Fin p.T => v.val < s.val ∧
      (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z).isSome)
  rw [List.toFinset_finRange] at hc
  rw [show priorCallCount rate rewards C_star C_h s z =
    (List.finRange p.T).countP (fun v => decide (v.val < s.val ∧
      (ReferenceCalendarCollectionCallControlLaw.callAt
        rate rewards C_star C_h v z).isSome)) from hc]
  apply List.countP_congr
  intro v _
  cases hv : ReferenceCalendarCollectionCallControlLaw.callAt
      rate rewards C_star C_h v z <;> simp

/-- A present invocation has exactly its list rank many prior calendar calls. -/
theorem nthCollectionCall_priorCallCount (k : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u s : Fin p.T)
    (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (h : nthCollectionCall rate rewards C_star C_h k z = some (u, (s, theta))) :
    priorCallCount rate rewards C_star C_h s z = k := by
  rw [priorCallCount_eq_countP]
  exact count_before_nth (fun c : ReferenceFirstCollectionSamplerCall.Call p => c.2.1.val)
    _ (collectionCalls_dates_strict rate rewards C_star C_h z) k (u, (s, theta)) h

/-- The cutoff/date projection of rank `k` is present precisely when the
actual call at `s` has exactly `k` actual predecessors. -/
theorem nthAt_eq_some_iff (k : ℕ) (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u : Fin p.T)
    (theta : ReferenceFirstCollectionSamplerCall.Theta p) :
    nthAt rate rewards C_star C_h k s z = some (u, theta) ↔
      priorCallCount rate rewards C_star C_h s z = k ∧
        ReferenceCalendarCollectionCallControlLaw.callAt
          rate rewards C_star C_h s z = some (u, theta) := by
  constructor
  · intro h
    obtain ⟨⟨u', t, theta'⟩, hn, ht⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at ht with hts
    change t = s at hts
    subst t
    change some (u', theta') = some (u, theta) at ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht)
    exact ⟨nthCollectionCall_priorCallCount rate rewards C_star C_h k z u' s theta' hn,
      (mem_collectionCalls_iff rate rewards C_star C_h z u' s theta').mp
        (List.mem_of_getElem? hn)⟩
  · rintro ⟨hk, hc⟩
    have hm := (mem_collectionCalls_iff rate rewards C_star C_h z u s theta).mpr hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
    have hjcount := nthCollectionCall_priorCallCount rate rewards C_star C_h j z u s theta hj
    have hjk : j = k := hjcount.symm.trans hk
    rw [hjk] at hj
    simp only [nthAt, nthCollectionCall, hj, Option.bind_some, ↓reduceIte]

/-- Exact rank identity on every original source, including absent cells and
all no-launch, terminal, reconstruction-failure, and later-draw-failure paths. -/
theorem nthAt_eq (k : ℕ) (s : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    nthAt rate rewards C_star C_h k s z =
      if priorCallCount rate rewards C_star C_h s z = k then
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z
      else none := by
  apply Option.ext
  rintro ⟨u, theta⟩
  rw [nthAt_eq_some_iff]
  by_cases hk : priorCallCount rate rewards C_star C_h s z = k <;> simp [hk]

private theorem callAt_factor_later (control0 : ContinuousLearningRows.TimeControl p)
    (v s : Fin p.T) (hvs : v.val ≤ s.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z =
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
  calc
    _ = ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val z) :=
      ReferenceCalendarCollectionCallControlLaw.callAt_factor
        rate rewards C_star C_h control0 v z
    _ = ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z)) := by
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
        v.val s.val hvs z]
    _ = _ := (ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 v _).symm

/-- The exact strict-past count factors through the same original source
prefix as the current pre-choice call. -/
theorem priorCallCount_factor (control0 : ContinuousLearningRows.TimeControl p)
    (s : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    priorCallCount rate rewards C_star C_h s z =
      priorCallCount rate rewards C_star C_h s
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
  unfold priorCallCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro v _
  by_cases hv : v.val < s.val
  · rw [callAt_factor_later rate rewards C_star C_h control0 v s (Nat.le_of_lt hv) z]
  · simp only [hv, false_and]

/-- Each rank/date observer is determined before its own assignment draw. -/
theorem nthAt_factor (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (s : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    nthAt rate rewards C_star C_h k s z =
      nthAt rate rewards C_star C_h k s
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
  rw [nthAt_eq, nthAt_eq,
    priorCallCount_factor rate rewards C_star C_h control0 s z,
    ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 s z]

private theorem measurableSet_optionNone {A : Type*} [MeasurableSpace A] :
    MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext value
  cases value <;> simp

private theorem measurableSet_optionSome {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) :
    MeasurableSet (some '' s : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

/-- The exact finite count is measurable in the pre-choice field at `s`. -/
theorem priorCallCount_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (s : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (s.val + 1)] (priorCallCount rate rewards C_star C_h s) := by
  have heq : priorCallCount rate rewards C_star C_h s = fun z =>
      ∑ v : Fin p.T, if v.val < s.val ∧
        (ReferenceCalendarCollectionCallControlLaw.callAt
          rate rewards C_star C_h v z).isSome then (1 : ℕ) else 0 := by
    funext z
    exact Finset.card_filter _ _
  rw [heq]
  apply Finset.measurable_sum
  intro v _
  by_cases hv : v.val < s.val
  · have hcall : Measurable[
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (s.val + 1)]
        (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v) :=
      (ReferenceCalendarCollectionCallControlLaw.callAt_measurable
        rate rewards C_star C_h control0 v).mono
          ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono'
            (by omega)) le_rfl
    have hnone := hcall measurableSet_optionNone
    have hpresent : MeasurableSet[
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (s.val + 1)]
        {z | (ReferenceCalendarCollectionCallControlLaw.callAt
          rate rewards C_star C_h v z).isSome} := by
      convert hnone.compl using 1
      ext z
      simp [Option.isSome_iff_ne_none]
    simpa only [hv, true_and] using
      (measurable_const.ite hpresent measurable_const :
        Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (s.val + 1)] (fun z => if
            (ReferenceCalendarCollectionCallControlLaw.callAt
              rate rewards C_star C_h v z).isSome then (1 : ℕ) else 0))
  · simpa only [hv, false_and, ite_false] using
      (measurable_const : Measurable[
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (s.val + 1)]
          (fun _ : BootstrapPrivateRoundStreams.SourceInput p => (0 : ℕ)))

/-- Continuous parameters retain their original Borel space, and the field
is `s.val + 1`, which exposes only source controls strictly before `s`. -/
theorem nthAt_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (s : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (s.val + 1)] (nthAt rate rewards C_star C_h k s) := by
  have hgate : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (s.val + 1)]
      {z | priorCallCount rate rewards C_star C_h s z = k} :=
    (priorCallCount_measurable rate rewards C_star C_h control0 s) (measurableSet_singleton k)
  have heq : nthAt rate rewards C_star C_h k s = fun z =>
      if priorCallCount rate rewards C_star C_h s z = k then
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z
      else none := by
    funext z
    exact nthAt_eq rate rewards C_star C_h k s z
  rw [heq]
  exact (ReferenceCalendarCollectionCallControlLaw.callAt_measurable
    rate rewards C_star C_h control0 s).ite hgate measurable_const

/-- The rank/cutoff/date event belongs to the same own-date pre-choice field. -/
theorem nthAt_cutoff_event_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (u s : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (s.val + 1)]
      {z | (nthAt rate rewards C_star C_h k s z).map Prod.fst = some u} := by
  have hm := nthAt_measurable rate rewards C_star C_h control0 k s
  have hs : MeasurableSet (some ''
      (({u} : Set (Fin p.T)) ×ˢ (Set.univ : Set (ReferenceFirstCollectionSamplerCall.Theta p)))) :=
    measurableSet_optionSome _ ((measurableSet_singleton u).prod MeasurableSet.univ)
  convert hm hs using 1
  ext z
  cases hn : nthAt rate rewards C_star C_h k s z with
  | none => simp [hn]
  | some c =>
      rcases c with ⟨v, a, b⟩
      simp [hn, eq_comm]

/-- Replacing the control at the call's own date leaves the rank/date
observer unchanged. Later calls need not be unchanged. -/
theorem nthAt_replaceSourceControl (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (s : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    nthAt rate rewards C_star C_h k s
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c) =
      nthAt rate rewards C_star C_h k s z := by
  calc
    _ = nthAt rate rewards C_star C_h k s
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p s z c)) :=
      nthAt_factor rate rewards C_star C_h control0 k s _
    _ = nthAt rate rewards C_star C_h k s
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) := by
      rw [ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl]
    _ = _ := (nthAt_factor rate rewards C_star C_h control0 k s z).symm

end Bandits.Support.ReferenceCollectionSamplerChronology

end
