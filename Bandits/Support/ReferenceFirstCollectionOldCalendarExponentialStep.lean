/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldSelectorRecordingLaw
public import Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Original OLD calendar exponential queue step

This module localizes one original-source OLD update strictly before the first
collection sampler invocation. Its optional prefix and cell are the accepted
calendar objects, and every queue identity below is proved from that same
recorded run. The incoming retained event includes the first update that
detects overflow.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionOldCalendarExponentialStep

open ConstructorDimensions (Parameters D D_pos)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration
  (actualRecord actualLaunchBy sourcePrefixFiltration)
open ReferenceFirstCollectionOldRecorderFoundation

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (t : Fin p.T) (a : Fin p.K)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (t.val + 1)
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private instance measurableSingleton_sum {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a =>
        simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b =>
        simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance measurableSingleton_recordList :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let _ : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a =>
          simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a =>
          simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hm := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

/-- The original OLD selector at the actual date, before its first call. -/
@[expose] public def E : Set S :=
  ReferenceFirstCollectionOldRecorderFoundation.oldSelector
    rate rewards C_star C_h t

/-- Retain an OLD update only while its actual strict-past prefix has not
overflowed and the incoming original OLD cell is enabled. -/
@[expose] public def G : Set S :=
  E rate rewards C_star C_h t ∩
    ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ∩
    {z | ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
      rate rewards C_star C_h t z = some true}

/-- The literal localized incoming exponential from the original pre-call
calendar list. -/
@[expose] public def Xminus : S → ℝ :=
  (E rate rewards C_star C_h t).indicator (fun z =>
    Real.exp (beta * ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h t.val a z))

/-- The literal localized exponential after appending the actual OLD cell to
the same original calendar list. -/
@[expose] public def Xplus : S → ℝ :=
  (E rate rewards C_star C_h t).indicator (fun z =>
    Real.exp (beta * ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h (t.val + 1) a z))

/-- The original raw arrival minus four units of service, only on the actual
retained OLD update. -/
@[expose] public def retainedIncrement : S → ℝ :=
  (G rate rewards C_star C_h t).indicator (fun z =>
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw
      rate rewards C_star C_h t a z - 4)

/-- The exponential of the literal retained OLD increment. -/
@[expose] public def expRetainedIncrement : S → ℝ :=
  fun z => Real.exp (beta * retainedIncrement rate rewards C_star C_h t a z)

/-- The old selector is exactly the strict first-call cutoff together with the
actual optional OLD cell being present. -/
theorem mem_E_iff_beforeBoundary_and_oldCell (z : S) :
    z ∈ E rate rewards C_star C_h t ↔
      t.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h z ∧
      (ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h t z).isSome = true := by
  have hbefore : z ∈ ReferenceFirstCollectionOldRecorderFoundation.beforeCall
        rate rewards C_star C_h t ↔
      t.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h z := by
    change (∀ v : Fin p.T, v.val ≤ t.val →
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z = none) ↔ _
    exact (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h t z).symm
  simp only [E, ReferenceFirstCollectionOldRecorderFoundation.oldSelector,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_congr hbefore Iff.rfl

/-- The old event is measurable in the actual pre-choice field. -/
theorem measurableSet_E :
    MeasurableSet[F] (E rate rewards C_star C_h t) :=
  ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_measurable
    rate rewards C_star C_h control0 t

/-- The three factors in the retained OLD event are all predictable in the
same source-prefix filtration. -/
theorem measurableSet_G :
    MeasurableSet[F] (G rate rewards C_star C_h t) := by
  have hE := measurableSet_E rate rewards C_star C_h control0 t
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  have hEnabled := ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled_measurable
    rate rewards C_star C_h control0 t
  have hSingleton : MeasurableSet ({some true} : Set (Option Bool)) := by
    let e := Equiv.optionEquivSumPUnit Bool
    have he : Measurable e := comap_measurable _
    have hset : ({some true} : Set (Option Bool)) = e ⁻¹' {e (some true)} := by
      ext x
      exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
    rw [hset]
    exact (measurableSet_singleton _).preimage he
  have hEnabledSet : MeasurableSet[F]
      {z : S | ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h t z = some true} :=
    hSingleton.preimage hEnabled
  exact hE.inter hH |>.inter hEnabledSet

private theorem mem_G_imp_mem_E (z : S) (hz : z ∈ G rate rewards C_star C_h t) :
    z ∈ E rate rewards C_star C_h t := hz.1.1

private theorem launch_of_mem_E (z : S)
    (hz : z ∈ E rate rewards C_star C_h t) :
    actualLaunchBy rate rewards C_star C_h t.val z := by
  obtain ⟨_, hcell⟩ := (mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcell
  obtain ⟨r, hr, _⟩ := Option.bind_eq_some_iff.mp (by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?] using hc)
  by_contra hnot
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
    rate rewards C_star C_h t z hnot] at hr
  cases hr

/-- At an OLD-selector date, P's actual optional prefix appends the exact
same record and actual OLD cell, with no replacement run or queue reset. -/
theorem actual_old_calendar_append (z : S)
    (hz : z ∈ E rate rewards C_star C_h t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h t.val z = some L ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      RecordedQueueRun.run q (L ++ [c]) =
        RecordedQueueRun.step q (RecordedQueueRun.run q L) c := by
  have hbefore := (mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz |>.1
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    ((mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hz).2
  obtain ⟨r, hr, hcollection⟩ := Option.bind_eq_some_iff.mp (by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?] using hc)
  obtain ⟨L, r', c', hL, hactual, _, hcell0, hread, hnext, hrun⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_append
      rate rewards C_star C_h t z (launch_of_mem_E rate rewards C_star C_h t z hz)
      hbefore
  have hrEq : r' = r := Option.some.inj (hactual.symm.trans hr)
  subst r'
  have hcEq : c' = c := by
    rcases hread with ⟨_, hnone⟩ | ⟨hread, _⟩
    · rw [hnone] at hcollection
      cases hcollection
    · exact Option.some.inj (hread.symm.trans hcollection)
  subst c'
  exact ⟨L, c, hL, hc, hnext, hrun⟩

/-- On E, the original incoming optional readout equals the existing
strict-past queue readout at the same date. -/
theorem precallReadout_eq_prefixReadout_on_E (z : S)
    (hz : z ∈ E rate rewards C_star C_h t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
        rate rewards C_star C_h t.val z =
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t z := by
  have hbefore := (mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz |>.1
  have hcut : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z = t.val :=
    Nat.min_eq_left (Nat.le_of_lt hbefore)
  have hlt : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z < p.T := by
    rw [hcut]
    exact t.isLt
  simp only [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?,
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?]
  rw [ReferenceFirstCollectionPrecallCalendarSupport.precallCells_eq_pastCells
    rate rewards C_star C_h t.val z hlt]
  have hfin : (⟨ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z, hlt⟩ : Fin p.T) = t := Fin.ext hcut
  rw [hfin]

/-- The old-calendar scalar incoming backlog is the exact normalized value of
that same already-predictable prefix readout. -/
theorem precallBacklog_eq_prefixReadout_on_E (z : S)
    (hz : z ∈ E rate rewards C_star C_h t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h t.val a z =
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
        (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
          rate rewards C_star C_h t z) a := by
  obtain ⟨L, _, hcells, _, _, _⟩ := actual_old_calendar_append
    rate rewards C_star C_h t z hz
  have hbefore := (mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz |>.1
  have hcut : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z = t.val :=
    Nat.min_eq_left (Nat.le_of_lt hbefore)
  have hlt : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z < p.T := by
    rw [hcut]
    exact t.isLt
  have hfin : (⟨ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z, hlt⟩ : Fin p.T) = t := Fin.ext hcut
  have hPast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some L := by
    rw [← hfin]
    rw [← ReferenceFirstCollectionPrecallCalendarSupport.precallCells_eq_pastCells
      rate rewards C_star C_h t.val z hlt]
    exact hcells
  have hprefix : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run q L)) := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hPast]
  rw [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hcells, hprefix]
  rfl

private theorem beta_lower_bound :
    32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have heta : 0 ≤ 32 * rate.eta.val :=
    mul_nonneg (by norm_num) rate.eta.property.le
  unfold CanonicalRecordingRates.beta
  calc
    32 * rate.eta.val = (32 * rate.eta.val) * 1 := by ring
    _ ≤ (32 * rate.eta.val) * (CanonicalRecordingRates.L_stab p : ℝ) :=
      mul_le_mul_of_nonneg_left hL heta
    _ = 32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ) := by ring

private theorem originalCell_rate_floor
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some cell) :
    ∀ i, 32 * rate.eta.val ≤ cell.rate i := by
  unfold ReferenceFirstCollectionCurrentRetainedGate.cell0 at hcell
  cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
  | none =>
      have hcollection :
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
        simpa only [hlive, Option.none_or] using hcell
      obtain ⟨payload, _, _, _, _, _, _, _, _, _, hrate, _, _, _, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
          0 record cell hcollection
      intro i
      calc
        32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val :=
          beta_lower_bound rate
        _ ≤ payload.rate i := AssignmentStartPayload.Input.beta_le_rate payload i
        _ = cell.rate i := by rw [hrate]
  | some live =>
      have hcell' : some live = some cell := by
        simpa only [hlive, Option.some_or] using hcell
      have hEq : live = cell := Option.some.inj hcell'
      subst cell
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
          0 record live hlive
      intro i
      rw [hrate]
      exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p
        rate.eta.property selected.view.payload.anchor i

private theorem precallPrefix_rate_floor (n : ℕ) (hn : n ≤ p.T) (z : S)
    (hlaunch : actualLaunchBy rate rewards C_star C_h
      (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
        rate rewards C_star C_h n z) z) :
    ∃ L, ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h n z = some L ∧
      ∀ cell ∈ L, ∀ i, 32 * rate.eta.val ≤ cell.rate i := by
  obtain ⟨L, hL, _, _, hcoverage⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_present
      rate rewards C_star C_h n hn z hlaunch
  refine ⟨L, hL, ?_⟩
  intro cell hmem i
  obtain ⟨k, hk, hcell⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨record, _, _, hcell0⟩ := hcoverage ⟨k, hk⟩
  have hEq : L[k] = cell := hcell
  subst cell
  exact originalCell_rate_floor rate record _ hcell0 i

/-- Both the pre-update and appended original prefix obey the existing
stopped-run backlog envelope, including the retained overflow-detecting step.
-/
theorem precallBacklog_bounds (n : ℕ) (hn : n ≤ p.T) (z : S) :
    0 ≤ ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h n a z ∧
      ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h n a z ≤ 2 * (1 / (32 * rate.eta.val)) := by
  classical
  cases hc : ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h n z with
  | none =>
      rw [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hc]
      have heta : 0 < 32 * rate.eta.val :=
        mul_pos (by norm_num) rate.eta.property
      exact ⟨by norm_num,
        mul_nonneg (by norm_num) (one_div_nonneg.mpr heta.le)⟩
  | some L =>
      have hlaunch : actualLaunchBy rate rewards C_star C_h
          (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
            rate rewards C_star C_h n z) z := by
        unfold ReferenceFirstCollectionPrecallCalendarSupport.precallCells? at hc
        split_ifs at hc with hlaunch
        · exact hlaunch
      obtain ⟨L', hL', hrate⟩ := precallPrefix_rate_floor
        rate rewards C_star C_h n hn z hlaunch
      have hEq : L' = L := Option.some.inj (hL'.symm.trans hc)
      subst L'
      have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
        q L hrate L.length a
      have hnonneg : 0 ≤ StoppedQueueBound.normalizedBacklog q
          (RecordedQueueRun.run q L) a := by
        unfold StoppedQueueBound.normalizedBacklog
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      constructor
      · simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hc,
          StoppedQueueBound.normalizedBacklog] using hnonneg
      · simpa [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hc,
          StoppedQueueBound.normalizedBacklog,
          ReferenceFirstLaunchNumericalCell.queueParameters] using hbound

private def incomingBacklog : S → ℝ :=
  (E rate rewards C_star C_h t).indicator (fun z =>
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h t.val a z)

private def postBacklogCandidate : S → ℝ := fun z =>
  if z ∈ G rate rewards C_star C_h t then
    max (incomingBacklog rate rewards C_star C_h t a z +
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t a z - 4) 0
  else incomingBacklog rate rewards C_star C_h t a z

/-- The pre-call scalar is exactly the predictable prefix observation on E. -/
theorem Xminus_eq_predictable_readout (z : S) :
    Xminus rate rewards C_star C_h t a z =
      (E rate rewards C_star C_h t).indicator (fun y =>
        Real.exp (beta * ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
            rate rewards C_star C_h t y) a)) z := by
  by_cases hz : z ∈ E rate rewards C_star C_h t
  · rw [Xminus, Set.indicator_of_mem hz,
      Set.indicator_of_mem hz,
      precallBacklog_eq_prefixReadout_on_E rate rewards C_star C_h t a z hz]
  · simp [Xminus, hz]

/-- The actual OLD run transition is reflected on G and preserved on E\G.
The proof uses the same appended original cell and the run's enabled/overflow
semantics, so the first detecting update remains included. -/
theorem precallBacklog_step_on_G (z : S)
    (hz : z ∈ G rate rewards C_star C_h t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h (t.val + 1) a z =
      max (ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
          rate rewards C_star C_h t.val a z +
        ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t a z - 4) 0 := by
  have hzE := hz.1.1
  obtain ⟨L, c, hL, hc, hnext, hrun⟩ :=
    actual_old_calendar_append rate rewards C_star C_h t z hzE
  have hprefix : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run q L)) := by
    have hread := precallReadout_eq_prefixReadout_on_E
      rate rewards C_star C_h t z hzE
    have hread' : ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
        rate rewards C_star C_h t.val z =
          some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)) := by
      simp [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL]
    exact hread.symm.trans hread'
  obtain ⟨readout, hreadout, hoverflow⟩ := hz.1.2
  have hreadoutEq : readout =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run q L) := Option.some.inj (hreadout.symm.trans hprefix)
  have hstate' :
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run q L)).2.1 = false := by
    rw [← hreadoutEq]
    exact hoverflow
  have hstate : (RecordedQueueRun.run q L).overflow = false := by
    simpa [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout] using hstate'
  have henabled : c.enabled = true := by
    have hinc := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
      rate rewards C_star C_h t z c hc
    exact Option.some.inj (hinc.symm.trans hz.2)
  have hraw : RecordedRoundMoments.rawEstimate q (RecordedQueueRun.run q L) c a =
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t a z := by
    simp [RecordedRoundMoments.rawEstimate,
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hc,
      RecordedQueueRun.acceptedRecord, hstate, henabled,
      RecordedQueueRun.acceptedArrival,
      RecordedRoundMoments.normalizedQuantizedArrival]
  have hstep := CanonicalQueueProcess.normalizedBacklog_step_of_retained
    q (RecordedQueueRun.run q L) c a hstate henabled
  have hafter : ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h (t.val + 1) a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q (L ++ [c])) a := by
    simp [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hnext]
  have hbefore : ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h t.val a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a := by
    simp [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hL]
  rw [hafter, hbefore, hrun]
  simpa [hraw] using hstep

theorem precallBacklog_preserve_on_E_outside_G (z : S)
    (hzE : z ∈ E rate rewards C_star C_h t)
    (hzG : z ∉ G rate rewards C_star C_h t) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h (t.val + 1) a z =
      ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h t.val a z := by
  obtain ⟨L, c, hL, hc, hnext, hrun⟩ :=
    actual_old_calendar_append rate rewards C_star C_h t z hzE
  have hprefix : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run q L)) := by
    have hread := precallReadout_eq_prefixReadout_on_E
      rate rewards C_star C_h t z hzE
    have hread' : ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
        rate rewards C_star C_h t.val z =
          some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)) := by
      simp [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL]
    exact hread.symm.trans hread'
  have hdisable_or_overflow : c.enabled = false ∨
      (RecordedQueueRun.run q L).overflow = true := by
    by_cases hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
        rate rewards C_star C_h t
    · have hnotEnabled : ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
          rate rewards C_star C_h t z ≠ some true := by
        intro he
        exact hzG ⟨⟨hzE, hH⟩, he⟩
      have hinc := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
        rate rewards C_star C_h t z c hc
      have hnot : c.enabled ≠ true := by
        intro he
        apply hnotEnabled
        simpa [he] using hinc
      cases he : c.enabled with
      | false => exact Or.inl rfl
      | true => exact False.elim (hnot he)
    · have hnotFalse :
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)).2.1 ≠ false := by
        intro hfalse
        apply hH
        exact ⟨_, hprefix, hfalse⟩
      have hoverflow : (RecordedQueueRun.run q L).overflow = true := by
        cases he : (RecordedQueueRun.run q L).overflow with
        | false => exact False.elim (hnotFalse (by simp [he,
            ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]))
        | true => exact rfl
      exact Or.inr hoverflow
  have hpreserve := CanonicalQueueProcess.normalizedBacklog_step_of_inactive
    q (RecordedQueueRun.run q L) c a hdisable_or_overflow
  have hafter : ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h (t.val + 1) a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q (L ++ [c])) a := by
    simp [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hnext]
  have hbefore : ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
      rate rewards C_star C_h t.val a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a := by
    simp [ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog, hL]
  rw [hafter, hbefore, hrun]
  simpa using hpreserve

/-- The retained increment is exactly the original OLD raw arrival minus
service, localized to the produced predictable gate. -/
theorem retainedIncrement_eq_G_indicator :
    retainedIncrement rate rewards C_star C_h t a =
      (G rate rewards C_star C_h t).indicator (fun z =>
        ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t a z - 4) := rfl

theorem retainedIncrement_bounds (z : S) :
    -4 ≤ retainedIncrement rate rewards C_star C_h t a z ∧
      retainedIncrement rate rewards C_star C_h t a z ≤ 1 / beta := by
  have hraw := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
    rate rewards C_star C_h t a z
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hg : z ∈ G rate rewards C_star C_h t
  · rw [retainedIncrement, Set.indicator_of_mem hg]
    constructor <;> linarith
  · rw [retainedIncrement, Set.indicator_of_notMem hg]
    exact ⟨by norm_num, one_div_nonneg.mpr hb.le⟩

private theorem beta_mul_retainedIncrement_bounds (z : S) :
    -4 * beta ≤ beta * retainedIncrement rate rewards C_star C_h t a z ∧
      beta * retainedIncrement rate rewards C_star C_h t a z ≤ 1 := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hx := retainedIncrement_bounds rate rewards C_star C_h t a z
  constructor
  · calc
      -4 * beta = beta * (-4) := by ring
      _ ≤ beta * retainedIncrement rate rewards C_star C_h t a z :=
        mul_le_mul_of_nonneg_left hx.1 hb.le
  · calc
      beta * retainedIncrement rate rewards C_star C_h t a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hx.2 hb.le
      _ = 1 := by field_simp [ne_of_gt hb]

theorem retainedIncrement_measurable (control0 : TimeControl p) :
    Measurable (retainedIncrement rate rewards C_star C_h t a) := by
  have hraw := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_measurable
    rate rewards C_star C_h t a
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact (hraw.sub_const 4).indicator
    (hle _ (measurableSet_G rate rewards C_star C_h control0 t))

theorem retainedIncrement_integrable (control0 : TimeControl p) :
    Integrable (retainedIncrement rate rewards C_star C_h t a) mu := by
  have hraw := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
    rate rewards C_star C_h t a
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hsub : Integrable (fun z : S =>
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t a z - 4) mu := by
    simpa [Pi.add_apply, sub_eq_add_neg] using hraw.add (integrable_const (-4 : ℝ))
  simpa [retainedIncrement] using hsub.indicator
    (hle _ (measurableSet_G rate rewards C_star C_h control0 t))

theorem expRetainedIncrement_bounds (z : S) :
    Real.exp (-4 * beta) ≤ expRetainedIncrement rate rewards C_star C_h t a z ∧
      expRetainedIncrement rate rewards C_star C_h t a z ≤ Real.exp 1 := by
  have hx := beta_mul_retainedIncrement_bounds rate rewards C_star C_h t a z
  exact ⟨Real.exp_le_exp_of_le hx.1, Real.exp_le_exp_of_le hx.2⟩

theorem expRetainedIncrement_measurable (control0 : TimeControl p) :
    Measurable (expRetainedIncrement rate rewards C_star C_h t a) := by
  have hscaled : Measurable (fun z : S => beta *
      retainedIncrement rate rewards C_star C_h t a z) :=
    (measurable_const : Measurable (fun _ : S => beta)).mul
      (retainedIncrement_measurable rate rewards C_star C_h t a control0)
  exact hscaled.exp

private theorem integrable_of_bounded_measurable
    {f : S → ℝ} (hf : Measurable f) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : S => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  exact hbound z

theorem expRetainedIncrement_integrable (control0 : TimeControl p) :
    Integrable (expRetainedIncrement rate rewards C_star C_h t a) mu := by
  apply integrable_of_bounded_measurable
    (expRetainedIncrement_measurable rate rewards C_star C_h t a control0)
    (Real.exp 1)
  intro z
  have h := expRetainedIncrement_bounds rate rewards C_star C_h t a z
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (Real.exp_nonneg _) h.1)]
  exact h.2

private theorem condExp_real_const_mul (c : ℝ) (f : S → ℝ) :
    mu[(fun z : S => c * f z) | F] =ᵐ[mu]
      (fun z : S => c * mu[f | F] z) := by
  have hscaled := condExp_smul (μ := mu) c f F
  have hfun : (fun z : S => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    mu[(fun z : S => c * f z) | F] =ᵐ[mu] mu[c • f | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[mu] (fun z : S => c * mu[f | F] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

private def selectorRaw : S → ℝ :=
  (E rate rewards C_star C_h t).indicator
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t a)

private def gateRaw : S → ℝ :=
  (G rate rewards C_star C_h t).indicator
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t a)

private theorem readoutOption_measurableSingleton
    (y : Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :
    @MeasurableSet (Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K))
      ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace {y} := by
  let e := Equiv.optionEquivSumPUnit
    (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)
  have he : @Measurable (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K))
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K ⊕ PUnit)
      ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({y} : Set (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K))) =
      e ⁻¹' {e y} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  exact (measurableSet_singleton _).preimage he

/-- The original OLD floor and incoming rate give the predictable localized
first moment needed by the exponential chord. -/
theorem condExp_gateRaw_le_indicator :
    mu[((G rate rewards C_star C_h t).indicator
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t a)) | F] ≤ᵐ[mu]
      (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) := by
  change mu[(gateRaw rate rewards C_star C_h t a) | F] ≤ᵐ[mu]
    (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))
  let rhs : S → ℝ := fun z =>
    (E rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z *
      (if ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h t z = some true then (1 : ℝ) else 0) *
      (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h t z).getD (fun _ => 0) a *
      (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
        rate rewards C_star C_h t a z).getD 0
  let f := selectorRaw rate rewards C_star C_h t a
  let g : S → ℝ := (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))
  have hGfield := measurableSet_G rate rewards C_star C_h control0 t
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hEambient : MeasurableSet (E rate rewards C_star C_h t) :=
    hle _ (measurableSet_E rate rewards C_star C_h control0 t)
  have hGambient : MeasurableSet (G rate rewards C_star C_h t) := hle _ hGfield
  have hselectorInt : Integrable f mu := by
    simpa [f, selectorRaw] using
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
        rate rewards C_star C_h t a).indicator hEambient
  have hgateInt : Integrable (gateRaw rate rewards C_star C_h t a) mu := by
    have hEq : gateRaw rate rewards C_star C_h t a =
        (G rate rewards C_star C_h t).indicator f := by
      funext z
      by_cases hz : z ∈ G rate rewards C_star C_h t
      · simp [gateRaw, f, selectorRaw, hz, hz.1.1]
      · simp [gateRaw, f, selectorRaw, hz]
    rw [hEq]
    exact hselectorInt.indicator hGambient
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hselectorCE := ReferenceFirstCollectionOldSelectorRecordingLaw.oldRaw_condExp
    rate rewards C_star C_h control0 t a
  have hselectorCE' : mu[f | F] =ᵐ[mu] rhs := by
    simpa [f, selectorRaw, rhs, E] using hselectorCE
  have hgateEq : gateRaw rate rewards C_star C_h t a =
      (G rate rewards C_star C_h t).indicator f := by
    funext z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · simp [gateRaw, f, selectorRaw, hz, hz.1.1]
    · simp [gateRaw, f, selectorRaw, hz]
  have hceGate : mu[gateRaw rate rewards C_star C_h t a | F] =ᵐ[mu]
      (G rate rewards C_star C_h t).indicator (mu[f | F]) := by
    rw [hgateEq]
    exact condExp_indicator hselectorInt hGfield
  have hfloor : ∀ z ∈ G rate rewards C_star C_h t, rhs z ≤ 1 := by
    intro z hz
    rcases hz with ⟨⟨hE, _⟩, henabled⟩
    change ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
      rate rewards C_star C_h t z = some true at henabled
    obtain ⟨payload, hp, hamp, _, hfirst, hreward⟩ :=
      ReferenceFirstCollectionOldSelectorRecordingLaw.oldRaw_floor_firstMean_bounds
        rate rewards C_star C_h t a z hE
    have hrate : (ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h t z).getD (fun _ => 0) a = payload.rate a := by
      simp [ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp]
    have hE' : z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector
        rate rewards C_star C_h t := by simpa [E] using hE
    calc
      rhs z = payload.rate a *
          ((Nat.floor (((D p : ℝ) * rate.eta.val *
            ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t a) /
              payload.rate a) : ℝ) / (rate.n : ℝ)) := by
        simp [rhs, E, hE', henabled, hrate, hamp]
      _ ≤ 1 := hfirst.trans hreward
  filter_upwards [hceGate, hselectorCE'] with z hceGateZ hselectorCEZ
  by_cases hz : z ∈ G rate rewards C_star C_h t
  · have hval : mu[gateRaw rate rewards C_star C_h t a | F] z = rhs z := by
      calc
        mu[gateRaw rate rewards C_star C_h t a | F] z =
            (G rate rewards C_star C_h t).indicator (mu[f | F]) z := hceGateZ
        _ = mu[f | F] z := by simp [hz]
        _ = rhs z := hselectorCEZ
    rw [hval]
    have hindicator : (G rate rewards C_star C_h t).indicator
        (fun _ => (1 : ℝ)) z = 1 := by simp [hz]
    rw [hindicator]
    exact hfloor z hz
  · have hzero : mu[gateRaw rate rewards C_star C_h t a | F] z = 0 := by
      simpa [hz] using hceGateZ
    rw [hzero]
    simp [hz]

private theorem exp_neg_four_beta_chord_le_one :
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤ 1 := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hc : 0 ≤ (Real.exp 1 - 1) * beta := by
    exact mul_nonneg (by linarith [Real.exp_one_gt_two]) hb.le
  have hlinear := Real.add_one_le_exp ((Real.exp 1 - 1) * beta)
  have harg : (Real.exp 1 - 1) * beta - 4 * beta ≤ 0 := by
    have hcoef : Real.exp 1 - 5 ≤ 0 := by linarith [Real.exp_one_lt_three]
    calc
      (Real.exp 1 - 1) * beta - 4 * beta = (Real.exp 1 - 5) * beta := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef hb.le
  calc
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤
        Real.exp (-4 * beta) * Real.exp ((Real.exp 1 - 1) * beta) :=
      mul_le_mul_of_nonneg_left (by linarith [hlinear]) (Real.exp_nonneg _)
    _ = Real.exp ((Real.exp 1 - 1) * beta - 4 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp_of_le harg
    _ = 1 := Real.exp_zero

/-- The original-source retained exponential has conditional expectation at
most one. Its only moment input is the locally proved OLD floor first mean. -/
theorem condExp_expRetainedIncrement_le_one :
    mu[(expRetainedIncrement rate rewards C_star C_h t a) | F] ≤ᵐ[mu]
      (fun _ : S => 1) := by
  let raw : S → ℝ :=
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t a
  let rawExp : S → ℝ := fun z => Real.exp (beta * raw z)
  let gateExp : S → ℝ := (G rate rewards C_star C_h t).indicator rawExp
  let g : S → ℝ := (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))
  let gComp : S → ℝ := (G rate rewards C_star C_h t)ᶜ.indicator
    (fun _ => (1 : ℝ))
  let penalty : ℝ := Real.exp (-4 * beta)
  let chord : ℝ := (Real.exp 1 - 1) * beta
  have hGfield := measurableSet_G rate rewards C_star C_h control0 t
  have hle : F ≤ (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGambient : MeasurableSet (G rate rewards C_star C_h t) := hle _ hGfield
  have hrawMeas : Measurable raw := by
    simpa [raw] using
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw_measurable
        rate rewards C_star C_h t a
  have hrawInt : Integrable raw mu := by
    simpa [raw] using
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
        rate rewards C_star C_h t a
  have hrawExpMeas : Measurable rawExp := by
    have hscaled : Measurable (fun z : S => beta * raw z) :=
      (measurable_const : Measurable (fun _ : S => beta)).mul hrawMeas
    simpa [rawExp] using hscaled.exp
  have hrawExpInt : Integrable rawExp mu := by
    apply integrable_of_bounded_measurable hrawExpMeas (Real.exp 1)
    intro z
    have hbounds := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
      rate rewards C_star C_h t a z
    have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hscaled : 0 ≤ beta * raw z ∧ beta * raw z ≤ 1 := by
      constructor
      · exact mul_nonneg hb.le hbounds.1
      · calc
          beta * raw z ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left hbounds.2 hb.le
          _ = 1 := by field_simp [ne_of_gt hb]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp_of_le hscaled.2
  have hgateExpInt : Integrable gateExp mu := by
    simpa [gateExp] using hrawExpInt.indicator hGambient
  have hselectorInt : Integrable (selectorRaw rate rewards C_star C_h t a) mu := by
    have hEfield := measurableSet_E rate rewards C_star C_h control0 t
    simpa [selectorRaw] using
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
        rate rewards C_star C_h t a).indicator (hle _ hEfield)
  have hgateRawInt : Integrable (gateRaw rate rewards C_star C_h t a) mu := by
    have hEq : gateRaw rate rewards C_star C_h t a =
        (G rate rewards C_star C_h t).indicator
          (selectorRaw rate rewards C_star C_h t a) := by
      funext z
      by_cases hz : z ∈ G rate rewards C_star C_h t
      · simp [gateRaw, selectorRaw, hz, hz.1.1]
      · simp [gateRaw, selectorRaw, hz]
    rw [hEq]
    exact hselectorInt.indicator hGambient
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hgInt : Integrable g mu := by simpa [g] using hone.indicator hGambient
  have hgCompInt : Integrable gComp mu := by
    simpa [gComp] using hone.indicator hGambient.compl
  have hscaledRawInt : Integrable
      (fun z : S => chord * gateRaw rate rewards C_star C_h t a z) mu :=
    hgateRawInt.const_mul chord
  have hsumInt : Integrable
      (fun z : S => g z + chord * gateRaw rate rewards C_star C_h t a z) mu :=
    hgInt.add hscaledRawInt
  have hchordPoint : ∀ z, gateExp z ≤
      g z + chord * gateRaw rate rewards C_star C_h t a z := by
    intro z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · have hbounds := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
        rate rewards C_star C_h t a z
      have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
      have hscaled : 0 ≤ beta * raw z ∧ beta * raw z ≤ 1 := by
        constructor
        · exact mul_nonneg hb.le hbounds.1
        · calc
            beta * raw z ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left hbounds.2 hb.le
            _ = 1 := by field_simp [ne_of_gt hb]
      have hchord := RecordedRoundMoments.exp_le_unit_chord hscaled.1 hscaled.2
      simp only [gateExp, g, gateRaw, Set.indicator_of_mem hz]
      change Real.exp (beta * raw z) ≤ 1 + chord * raw z
      simpa [chord, mul_assoc] using hchord
    · simp [gateExp, g, gateRaw, hz]
  have hmono := condExp_mono (μ := mu) (m := F) hgateExpInt hsumInt
    (Filter.Eventually.of_forall hchordPoint)
  have hsumCE0 := condExp_add hgInt hscaledRawInt F
  have hsumFun : (fun z : S => g z + chord *
      gateRaw rate rewards C_star C_h t a z) =
      g + (fun z : S => chord * gateRaw rate rewards C_star C_h t a z) := by
    funext z
    rfl
  have hsumCE : mu[(fun z : S => g z + chord *
      gateRaw rate rewards C_star C_h t a z) | F] =ᵐ[mu]
      mu[g | F] + mu[(fun z : S => chord *
        gateRaw rate rewards C_star C_h t a z) | F] := by
    calc
      mu[(fun z : S => g z + chord * gateRaw rate rewards C_star C_h t a z) | F] =ᵐ[mu]
          mu[g + (fun z : S => chord * gateRaw rate rewards C_star C_h t a z) | F] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hsumFun z)
      _ =ᵐ[mu] mu[g | F] +
          mu[(fun z : S => chord * gateRaw rate rewards C_star C_h t a z) | F] := hsumCE0
  have hscaleCE := condExp_real_const_mul (control0 := control0) (t := t) chord
    (gateRaw rate rewards C_star C_h t a)
  have hmask := condExp_indicator (μ := mu) (m := F) hone hGfield
  have hconst := condExp_const (μ := mu) (m := F)
    (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
  have hgCE : mu[g | F] =ᵐ[mu] g := by
    filter_upwards [hmask] with z hz
    rw [hconst] at hz
    simpa [g] using hz
  have hgateRawCE := condExp_gateRaw_le_indicator
    rate rewards C_star C_h control0 t a
  have hpenaltyInt : Integrable (fun z : S => penalty * gateExp z) mu :=
    hgateExpInt.const_mul penalty
  have hdecomp : expRetainedIncrement rate rewards C_star C_h t a =
      fun z => penalty * gateExp z + gComp z := by
    funext z
    by_cases hz : z ∈ G rate rewards C_star C_h t
    · have hsplit : Real.exp (beta *
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t a z - 4)) =
            Real.exp (-4 * beta) * Real.exp (beta * raw z) := by
        rw [show beta * (raw z - 4) = (-4 * beta) + beta * raw z by ring,
          Real.exp_add]
      simp [expRetainedIncrement, retainedIncrement, gateExp, rawExp, raw, penalty,
        gComp, hz, hsplit]
    · simp [expRetainedIncrement, retainedIncrement, gateExp, rawExp, gComp, hz, penalty]
  have hsumExp := condExp_add hpenaltyInt hgCompInt F
  have hpenaltyCE := condExp_real_const_mul (control0 := control0) (t := t) penalty gateExp
  have hmaskComp := condExp_indicator (μ := mu) (m := F) hone hGfield.compl
  have hCEdecomp :
      mu[(expRetainedIncrement rate rewards C_star C_h t a) | F] =ᵐ[mu]
        (fun z => penalty * mu[gateExp | F] z +
          (G rate rewards C_star C_h t)ᶜ.indicator (fun _ => (1 : ℝ)) z) := by
    calc
      mu[(expRetainedIncrement rate rewards C_star C_h t a) | F] =ᵐ[mu]
          mu[(fun z : S => penalty * gateExp z + gComp z) | F] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hdecomp z)
      _ =ᵐ[mu] mu[(fun z : S => penalty * gateExp z) | F] + mu[gComp | F] := hsumExp
      _ =ᵐ[mu] (fun z : S => penalty * mu[gateExp | F] z + mu[gComp | F] z) := by
        filter_upwards [hpenaltyCE] with z hz
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x + mu[gComp | F] z) hz
      _ =ᵐ[mu] (fun z : S => penalty * mu[gateExp | F] z +
          (G rate rewards C_star C_h t)ᶜ.indicator (fun _ => (1 : ℝ)) z) := by
        filter_upwards [hmaskComp] with z hz
        rw [hz, hconst]
  have hchordNonneg : 0 ≤ chord := by
    dsimp [chord]
    exact mul_nonneg (by linarith [Real.exp_one_gt_two])
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  have hgateExpCE : mu[gateExp | F] ≤ᵐ[mu]
      (fun z => g z + chord * (G rate rewards C_star C_h t).indicator
        (fun _ => (1 : ℝ)) z) := by
    filter_upwards [hmono, hsumCE, hscaleCE, hgCE, hgateRawCE]
      with z hmonoZ hsumZ hscaleZ hgZ hrawGateZ
    have hsumZ' : mu[(fun z : S => g z + chord *
        gateRaw rate rewards C_star C_h t a z) | F] z =
        mu[g | F] z + mu[(fun z : S => chord *
          gateRaw rate rewards C_star C_h t a z) | F] z := by
      simpa only [Pi.add_apply] using hsumZ
    rw [hsumZ', hgZ, hscaleZ] at hmonoZ
    have hrawZ : mu[gateRaw rate rewards C_star C_h t a | F] z ≤ g z := by
      simpa [g, gateRaw] using hrawGateZ
    have hmul := mul_le_mul_of_nonneg_left hrawZ hchordNonneg
    have hstep := hmonoZ.trans (add_le_add_right hmul (g z))
    simpa [g] using hstep
  have hscalar := exp_neg_four_beta_chord_le_one rate
  have hcoef : penalty * (1 + chord) - 1 ≤ 0 := by
    dsimp [penalty, chord]
    linarith [hscalar]
  filter_upwards [hCEdecomp, hgateExpCE, hgCE] with z hCE hgateExp hg
  rw [hCE]
  have hgval : 0 ≤ g z := by by_cases hz : z ∈ G rate rewards C_star C_h t <;> simp [g, hz]
  have hgateExp' : mu[gateExp | F] z ≤ g z + chord * g z := by
    simpa [g] using hgateExp
  have hcomp : (G rate rewards C_star C_h t)ᶜ.indicator
      (fun _ => (1 : ℝ)) z = 1 - g z := by
    by_cases hz : z ∈ G rate rewards C_star C_h t <;> simp [g, hz]
  rw [hcomp]
  have hmul := mul_le_mul_of_nonneg_left hgateExp' (Real.exp_nonneg (-4 * beta))
  have hbound : penalty * mu[gateExp | F] z + 1 - g z ≤ 1 := by
    have hle : penalty * mu[gateExp | F] z ≤ penalty * (g z + chord * g z) := by
      simpa [penalty] using hmul
    have hfactor : g z + chord * g z = (1 + chord) * g z := by ring
    rw [hfactor] at hle
    have hle' : penalty * ((1 + chord) * g z) ≤ g z := by
      calc
        penalty * ((1 + chord) * g z) =
            (penalty * (1 + chord)) * g z := by ring
        _ ≤ 1 * g z := mul_le_mul_of_nonneg_right
          (by linarith [hcoef]) hgval
        _ = g z := by ring
    linarith
  linarith [hbound]

private theorem incomingBacklog_measurable :
    Measurable[F] (incomingBacklog rate rewards C_star C_h t a) := by
  let _ : MeasurableSpace (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
    ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace
  let _ : MeasurableSingletonClass (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
    ⟨fun y => readoutOption_measurableSingleton y⟩
  have hproject : Measurable (fun r : Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) =>
        ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate r a) := by
    classical
    exact measurable_of_countable _
  have hread := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 t
  have hbase : Measurable[F] (fun z =>
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
        rate (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
          rate rewards C_star C_h t z) a) := hproject.comp hread
  have hfun : incomingBacklog rate rewards C_star C_h t a =
      (E rate rewards C_star C_h t).indicator (fun z =>
        ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog rate
          (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
            rate rewards C_star C_h t z) a) := by
    funext z
    by_cases hz : z ∈ E rate rewards C_star C_h t
    · simp only [incomingBacklog, Set.indicator_of_mem hz]
      rw [precallBacklog_eq_prefixReadout_on_E rate rewards C_star C_h t a z hz]
    · simp [incomingBacklog, hz]
  rw [hfun]
  exact hbase.indicator (measurableSet_E rate rewards C_star C_h control0 t)

/-- The incoming exponential is measurable in the original pre-choice field.
Its only queue readout is CurrentRetainedGate's existing predictable prefix. -/
theorem Xminus_measurable : Measurable[F] (Xminus rate rewards C_star C_h t a) := by
  let _ : MeasurableSpace (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
    ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace
  let _ : MeasurableSingletonClass (Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
    ⟨fun y => readoutOption_measurableSingleton y⟩
  have hproject : Measurable (fun r : Option
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) =>
        ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate r a) := by
    classical
    exact measurable_of_countable _
  have hbase : Measurable[F] (fun z =>
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
        rate (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
          rate rewards C_star C_h t z) a) :=
    hproject.comp (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
      rate rewards C_star C_h control0 t)
  have hscaled : Measurable[F] (fun z : S => beta *
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
        rate (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
          rate rewards C_star C_h t z) a) :=
    (measurable_const : Measurable[F] (fun _ : S => beta)).mul hbase
  have hfun : Xminus rate rewards C_star C_h t a =
      (E rate rewards C_star C_h t).indicator (fun z =>
        Real.exp (beta * ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
            rate rewards C_star C_h t z) a)) := by
    funext z
    exact Xminus_eq_predictable_readout rate rewards C_star C_h t a z
  rw [hfun]
  exact hscaled.exp.indicator
    (measurableSet_E rate rewards C_star C_h control0 t)

theorem Xminus_bounds (z : S) :
    0 ≤ Xminus rate rewards C_star C_h t a z ∧
      Xminus rate rewards C_star C_h t a z ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
  by_cases hz : z ∈ E rate rewards C_star C_h t
  · rw [Xminus, Set.indicator_of_mem hz]
    have hback := precallBacklog_bounds rate rewards C_star C_h a t.val
      (Nat.le_of_lt t.isLt) z
    have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
    constructor
    · exact Real.exp_nonneg _
    · exact Real.exp_le_exp_of_le
        (mul_le_mul_of_nonneg_left hback.2 hb.le)
  · rw [Xminus, Set.indicator_of_notMem hz]
    constructor
    · norm_num
    · exact Real.exp_nonneg _

theorem Xminus_measurable_ambient (control0 : TimeControl p) :
    Measurable (Xminus rate rewards C_star C_h t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono (Xminus_measurable rate rewards C_star C_h control0 t a) hle le_rfl

theorem Xminus_integrable (control0 : TimeControl p) :
    Integrable (Xminus rate rewards C_star C_h t a) mu := by
  apply integrable_of_bounded_measurable
    (Xminus_measurable_ambient rate rewards C_star C_h t a control0)
    (Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))))
  intro z
  have h := Xminus_bounds rate rewards C_star C_h t a z
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

private theorem Xplus_eq_candidate (z : S) :
    Xplus rate rewards C_star C_h t a z =
      (E rate rewards C_star C_h t).indicator (fun y =>
        Real.exp (beta * postBacklogCandidate rate rewards C_star C_h t a y)) z := by
  by_cases hE : z ∈ E rate rewards C_star C_h t
  · have hback : incomingBacklog rate rewards C_star C_h t a z =
        ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
          rate rewards C_star C_h t.val a z := by
      simp [incomingBacklog, hE]
    by_cases hG : z ∈ G rate rewards C_star C_h t
    · have hstep := precallBacklog_step_on_G rate rewards C_star C_h t a z hG
      rw [Xplus, Set.indicator_of_mem hE,
        Set.indicator_of_mem hE, postBacklogCandidate, ite_eq_left hG]
      rw [hstep, hback]
    · have hpreserve := precallBacklog_preserve_on_E_outside_G
        rate rewards C_star C_h t a z hE hG
      rw [Xplus, Set.indicator_of_mem hE,
        Set.indicator_of_mem hE, postBacklogCandidate, ite_eq_right hG]
      rw [hpreserve, hback]
  · have hG : z ∉ G rate rewards C_star C_h t := by
      intro hz
      exact hE hz.1.1
    simp [Xplus, hE]

theorem Xplus_bounds (z : S) :
    0 ≤ Xplus rate rewards C_star C_h t a z ∧
      Xplus rate rewards C_star C_h t a z ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
  by_cases hz : z ∈ E rate rewards C_star C_h t
  · rw [Xplus, Set.indicator_of_mem hz]
    have hback := precallBacklog_bounds rate rewards C_star C_h a (t.val + 1)
      (Nat.succ_le_of_lt t.isLt) z
    have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
    exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le
      (mul_le_mul_of_nonneg_left hback.2 hb.le)⟩
  · rw [Xplus, Set.indicator_of_notMem hz]
    exact ⟨by norm_num, Real.exp_nonneg _⟩

theorem Xplus_measurable (control0 : TimeControl p) :
    Measurable (Xplus rate rewards C_star C_h t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hE : MeasurableSet (E rate rewards C_star C_h t) :=
    hle _ (measurableSet_E rate rewards C_star C_h control0 t)
  have hG : MeasurableSet (G rate rewards C_star C_h t) :=
    hle _ (measurableSet_G rate rewards C_star C_h control0 t)
  have hback : Measurable (incomingBacklog rate rewards C_star C_h t a) :=
    Measurable.mono (incomingBacklog_measurable rate rewards C_star C_h control0 t a)
      hle le_rfl
  have hraw : Measurable (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
      rate rewards C_star C_h t a) :=
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw_measurable
      rate rewards C_star C_h t a
  have hpost : Measurable (postBacklogCandidate rate rewards C_star C_h t a) := by
    apply Measurable.ite hG
    · exact (hback.add hraw).sub_const 4 |>.max measurable_const
    · exact hback
  have hscaled : Measurable (fun z : S => beta *
      postBacklogCandidate rate rewards C_star C_h t a z) :=
    (measurable_const : Measurable (fun _ : S => beta)).mul hpost
  have hfun : Xplus rate rewards C_star C_h t a =
      (E rate rewards C_star C_h t).indicator (fun y =>
        Real.exp (beta * postBacklogCandidate rate rewards C_star C_h t a y)) := by
    funext z
    exact Xplus_eq_candidate rate rewards C_star C_h t a z
  rw [hfun]
  exact hscaled.exp.indicator hE

theorem Xplus_integrable (control0 : TimeControl p) :
    Integrable (Xplus rate rewards C_star C_h t a) mu := by
  apply integrable_of_bounded_measurable
    (Xplus_measurable rate rewards C_star C_h t a control0)
    (Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))))
  intro z
  have h := Xplus_bounds rate rewards C_star C_h t a z
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- Pointwise reflected OLD transition. The gate cost appears only on the
actual retained event; outside the original selector both observations vanish. -/
theorem Xplus_le_gate_add_oldIncrementProduct (z : S) :
    Xplus rate rewards C_star C_h t a z ≤
      (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z +
        Xminus rate rewards C_star C_h t a z *
          expRetainedIncrement rate rewards C_star C_h t a z := by
  by_cases hE : z ∈ E rate rewards C_star C_h t
  · by_cases hG : z ∈ G rate rewards C_star C_h t
    · have hstep := precallBacklog_step_on_G rate rewards C_star C_h t a z hG
      have hraw : retainedIncrement rate rewards C_star C_h t a z =
          ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t a z - 4 := by
        simp [retainedIncrement, hG]
      let b := ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
        rate rewards C_star C_h t.val a z
      let x := ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t a z - 4
      have hsum : b + ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t a z - 4 = b + x := by
        dsimp [x]
        ring
      rw [Xplus, Set.indicator_of_mem hE, Xminus, Set.indicator_of_mem hE,
        Set.indicator_of_mem hG]
      rw [hstep, expRetainedIncrement, hraw, hsum]
      change Real.exp (beta * max (b + x) 0) ≤
        1 + Real.exp (beta * b) * Real.exp (beta * x)
      by_cases hnonneg : 0 ≤ b + x
      · rw [max_eq_left hnonneg]
        have hexp : Real.exp (beta * (b + x)) =
            Real.exp (beta * b) * Real.exp (beta * x) := by
          rw [show beta * (b + x) = beta * b + beta * x by ring,
            Real.exp_add]
        rw [hexp]
        linarith
      · have hneg : b + x < 0 := lt_of_not_ge hnonneg
        rw [max_eq_right (le_of_lt hneg)]
        simp only [mul_zero, Real.exp_zero]
        exact le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _)
          (Real.exp_nonneg _))
    · have hpreserve := precallBacklog_preserve_on_E_outside_G
        rate rewards C_star C_h t a z hE hG
      have hzero : retainedIncrement rate rewards C_star C_h t a z = 0 := by
        simp [retainedIncrement, hG]
      rw [Xplus, Set.indicator_of_mem hE, Xminus, Set.indicator_of_mem hE,
        Set.indicator_of_notMem hG, hpreserve]
      simp [expRetainedIncrement, hzero]
  · have hG : z ∉ G rate rewards C_star C_h t := by
      intro hz
      exact hE hz.1.1
    have hzero : retainedIncrement rate rewards C_star C_h t a z = 0 := by
      simp [retainedIncrement, hG]
    simp [Xplus, Xminus, hE, hG, expRetainedIncrement, hzero]

/-- The product of the predictable incoming exponential and the OLD exponential
increment is integrable under the original source law. -/
theorem Xminus_mul_expRetainedIncrement_integrable (control0 : TimeControl p) :
    Integrable (Xminus rate rewards C_star C_h t a *
      expRetainedIncrement rate rewards C_star C_h t a) mu := by
  have hmeas : Measurable (Xminus rate rewards C_star C_h t a *
      expRetainedIncrement rate rewards C_star C_h t a) :=
    (Xminus_measurable_ambient rate rewards C_star C_h t a control0).mul
      (expRetainedIncrement_measurable rate rewards C_star C_h t a control0)
  apply integrable_of_bounded_measurable hmeas
    (Real.exp (beta * (2 * (1 / (32 * rate.eta.val))) ) * Real.exp 1)
  intro z
  have hx := Xminus_bounds rate rewards C_star C_h t a z
  have hy := expRetainedIncrement_bounds rate rewards C_star C_h t a z
  have hyNonneg : 0 ≤ expRetainedIncrement rate rewards C_star C_h t a z :=
    le_trans (Real.exp_nonneg _) hy.1
  change ‖Xminus rate rewards C_star C_h t a z *
    expRetainedIncrement rate rewards C_star C_h t a z‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg hyNonneg]
  calc
    Xminus rate rewards C_star C_h t a z *
        expRetainedIncrement rate rewards C_star C_h t a z ≤
      Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) *
        expRetainedIncrement rate rewards C_star C_h t a z :=
      mul_le_mul_of_nonneg_right hx.2 hyNonneg
    _ ≤ Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hy.2 (by positivity)

/-- Conditional expectation of the actual OLD post-update exponential. The
incoming exponential is predictable, and the only extra conditional cost is
the indicator of the retained OLD event. -/
theorem condExp_Xplus_le_Xminus_add_G_indicator :
    mu[(Xplus rate rewards C_star C_h t a) | F] ≤ᵐ[mu]
      (fun z => Xminus rate rewards C_star C_h t a z +
        (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ)) z) := by
  let gate : S → ℝ := (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))
  have hplusInt := Xplus_integrable rate rewards C_star C_h t a control0
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hGambient : MeasurableSet (G rate rewards C_star C_h t) :=
    hle _ (measurableSet_G rate rewards C_star C_h control0 t)
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hgateInt : Integrable gate mu := by
    simpa [gate] using hone.indicator hGambient
  have hsumInt : Integrable
      (fun z : S => gate z + Xminus rate rewards C_star C_h t a z *
        expRetainedIncrement rate rewards C_star C_h t a z) mu := by
    exact hgateInt.add (Xminus_mul_expRetainedIncrement_integrable
      rate rewards C_star C_h t a control0)
  have hmono := condExp_mono (μ := mu) (m := F) hplusInt hsumInt
    (Filter.Eventually.of_forall fun z => by
      simpa [gate, add_comm] using Xplus_le_gate_add_oldIncrementProduct
        rate rewards C_star C_h t a z)
  let prod : S → ℝ := fun z => Xminus rate rewards C_star C_h t a z *
    expRetainedIncrement rate rewards C_star C_h t a z
  have hprodInt : Integrable prod mu := by
    change Integrable (Xminus rate rewards C_star C_h t a *
      expRetainedIncrement rate rewards C_star C_h t a) mu
    exact Xminus_mul_expRetainedIncrement_integrable
      rate rewards C_star C_h t a control0
  have hsumCE := condExp_add hgateInt hprodInt F
  have hgateCE' : mu[gate | F] =ᵐ[mu] gate := by
    have hmask := condExp_indicator (μ := mu) hone
      (measurableSet_G rate rewards C_star C_h control0 t)
    have hconst := condExp_const (μ := mu) (m := F)
      (m₀ := (inferInstance : MeasurableSpace S)) hle (1 : ℝ)
    filter_upwards [hmask] with z hz
    rw [hconst] at hz
    simpa [gate] using hz
  have hXminusAES : AEStronglyMeasurable[F]
      (Xminus rate rewards C_star C_h t a) mu :=
    (Xminus_measurable rate rewards C_star C_h control0 t a).aestronglyMeasurable
  have hExpInt := expRetainedIncrement_integrable rate rewards C_star C_h t a control0
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    hXminusAES hprodInt hExpInt
  have hpullProd : mu[prod | F] =ᵐ[mu] (fun z : S =>
      Xminus rate rewards C_star C_h t a z *
        mu[expRetainedIncrement rate rewards C_star C_h t a | F] z) := by
    filter_upwards [hpull] with z hz
    change mu[prod | F] z = _ at hz
    exact hz
  have hExpBound := condExp_expRetainedIncrement_le_one
    rate rewards C_star C_h control0 t a
  filter_upwards [hmono, hsumCE, hgateCE', hpullProd, hExpBound]
    with z hmonoZ hsumZ hgateZ hpullZ hExpZ
  have hsumZ' : mu[(fun z : S => gate z + prod z) | F] z =
      mu[gate | F] z + mu[prod | F] z := by
    change mu[(gate + prod) | F] z = _
    exact hsumZ
  have hXnonneg := (Xminus_bounds rate rewards C_star C_h t a z).1
  calc
    mu[(Xplus rate rewards C_star C_h t a) | F] z ≤
        mu[(fun y : S => gate y + prod y) | F] z := hmonoZ
    _ = gate z + Xminus rate rewards C_star C_h t a z *
          mu[expRetainedIncrement rate rewards C_star C_h t a | F] z := by
      rw [hsumZ', hgateZ, hpullZ]
    _ ≤ gate z + Xminus rate rewards C_star C_h t a z := by
      have hm := mul_le_mul_of_nonneg_left hExpZ hXnonneg
      have hm' : Xminus rate rewards C_star C_h t a z *
          mu[expRetainedIncrement rate rewards C_star C_h t a | F] z ≤
            Xminus rate rewards C_star C_h t a z := by
        simpa using hm
      exact add_le_add_right hm' (gate z)
    _ = Xminus rate rewards C_star C_h t a z + gate z := by ring

/-- Sharp localized increment mass for every predictable set. No mass is
normalized, and zero-mass events remain included. -/
theorem setIntegral_Xplus_sub_Xminus_le_G_mass (Bset : Set S)
    (hB : MeasurableSet[F] Bset) :
    ∫ z in Bset, Xplus rate rewards C_star C_h t a z -
        Xminus rate rewards C_star C_h t a z ∂mu ≤
      (mu).real (Bset ∩ G rate rewards C_star C_h t) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hBambient : MeasurableSet Bset := hle _ hB
  have hGambient : MeasurableSet (G rate rewards C_star C_h t) :=
    hle _ (measurableSet_G rate rewards C_star C_h control0 t)
  have hplusInt := Xplus_integrable rate rewards C_star C_h t a control0
  have hminusInt := Xminus_integrable rate rewards C_star C_h t a control0
  have hdiffInt : Integrable
      (fun z : S => Xplus rate rewards C_star C_h t a z -
        Xminus rate rewards C_star C_h t a z) mu := hplusInt.sub hminusInt
  have hone : Integrable (fun _ : S => (1 : ℝ)) mu := integrable_const 1
  have hgateInt : Integrable
      ((G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))) mu :=
    hone.indicator hGambient
  let gate : S → ℝ := (G rate rewards C_star C_h t).indicator (fun _ => (1 : ℝ))
  have hsumInt : Integrable (fun z : S => Xminus rate rewards C_star C_h t a z +
      gate z) mu := hminusInt.add (by simpa [gate] using hgateInt)
  have hceInt : Integrable (mu[Xplus rate rewards C_star C_h t a | F]) mu :=
    integrable_condExp
  have hconditional := condExp_Xplus_le_Xminus_add_G_indicator
    rate rewards C_star C_h control0 t a
  have hconditional' : mu[(Xplus rate rewards C_star C_h t a) | F] ≤ᵐ[mu]
      (fun z => Xminus rate rewards C_star C_h t a z + gate z) := by
    simpa [gate] using hconditional
  have hceOn : IntegrableOn (mu[Xplus rate rewards C_star C_h t a | F]) Bset mu :=
    hceInt.integrableOn
  have hsumOn : IntegrableOn
      (fun z : S => Xminus rate rewards C_star C_h t a z + gate z) Bset mu :=
    hsumInt.integrableOn
  have hmono := setIntegral_mono_ae hceOn hsumOn hconditional'
  have hceSet := setIntegral_condExp hle hplusInt hB
  have hsubSet :
      (∫ z in Bset, Xplus rate rewards C_star C_h t a z -
        Xminus rate rewards C_star C_h t a z ∂mu) =
      (∫ z in Bset, Xplus rate rewards C_star C_h t a z ∂mu) -
        (∫ z in Bset, Xminus rate rewards C_star C_h t a z ∂mu) := by
    rw [integral_sub hplusInt.integrableOn.integrable
      hminusInt.integrableOn.integrable]
  have hsumSet :
      (∫ z in Bset, Xminus rate rewards C_star C_h t a z + gate z ∂mu) =
      (∫ z in Bset, Xminus rate rewards C_star C_h t a z ∂mu) +
        (∫ z in Bset, gate z ∂mu) := by
    rw [integral_add hminusInt.integrableOn.integrable
      (by simpa [gate] using hgateInt.integrableOn.integrable)]
  calc
    ∫ z in Bset, Xplus rate rewards C_star C_h t a z -
        Xminus rate rewards C_star C_h t a z ∂mu =
      (∫ z in Bset, mu[Xplus rate rewards C_star C_h t a | F] z ∂mu) -
        (∫ z in Bset, Xminus rate rewards C_star C_h t a z ∂mu) := by
      rw [hsubSet, ← hceSet]
    _ ≤ ∫ z in Bset, Xminus rate rewards C_star C_h t a z + gate z ∂mu -
        (∫ z in Bset, Xminus rate rewards C_star C_h t a z ∂mu) :=
      sub_le_sub_right hmono _
    _ = ∫ z in Bset, gate z ∂mu := by rw [hsumSet]; ring
    _ = (mu).real (Bset ∩ G rate rewards C_star C_h t) := by
      dsimp [gate]
      rw [setIntegral_indicator hGambient, setIntegral_one_eq_measureReal]

/-- Whole-space specialization of the sharp localized estimate. -/
theorem integral_Xplus_sub_Xminus_le_G_mass (control0 : TimeControl p) :
    ∫ z, Xplus rate rewards C_star C_h t a z -
        Xminus rate rewards C_star C_h t a z ∂mu ≤
      (mu).real (G rate rewards C_star C_h t) := by
  have h := setIntegral_Xplus_sub_Xminus_le_G_mass
    rate rewards C_star C_h control0 t a Set.univ MeasurableSet.univ
  simpa using h

end Bandits.Support.ReferenceFirstCollectionOldCalendarExponentialStep

end
