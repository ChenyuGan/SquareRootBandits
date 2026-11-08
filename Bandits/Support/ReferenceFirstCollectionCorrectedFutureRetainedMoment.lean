/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingLaw

import Mathlib.Tactic

/-!
# Original-source strict-future retained moments

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:354-431`, and `06_interruptions.tex:355-426`.
The actual accepted arrival uses the initialized stopped prefix on the same
corrected first-call event E(u,t). Only the incoming overflow flag is tested.
These are internal ingredients for CorrectedOriginalSourceOverflow.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionCorrectedFutureRecordingView
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCollectionCorrectedFutureRecordingLaw
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedFutureRetainedMoment

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

/-- The whole reward table evaluated at the queried calendar date. -/
def rewardAt (q : Fin p.T) (a : Fin p.K) : ℝ :=
  ((rewards q a).val : ℝ) / (D p : ℝ)

/-- Actual accepted normalized arrival; missing observations contribute zero. -/
def futureArrival (u t q : Fin p.T) (a : Fin p.K) (x : X) : ℝ :=
  match prefixInputs rate rewards C_star C_h q.val x,
      futureCell rate rewards C_star C_h u t q x with
  | some L, some c => RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a
  | _, _ => 0

/-- Incoming clearance and actual enabled parameters on the literal slice.
There is deliberately no outgoing-overflow test. -/
def retainedGate (u t q : Fin p.T) : Set X :=
  (futureGate rate rewards C_star C_h u t q ∩
    {x | ∃ v, prefixReadout rate rewards C_star C_h q.val x = some v ∧ v.2.1 = false}) ∩
    {x | ∃ xi, futureParameters rate rewards C_star C_h u t q x = some (true, xi)}

/-- Enabled zero arrivals receive service; all other branches contribute zero. -/
def retainedIncrement (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (retainedGate rate rewards C_star C_h u t q).indicator
    (fun x => futureArrival rate rewards C_star C_h u t q a x - 4)

/-- Predictable quantized size from the actual optional recording parameters. -/
def amplitudeOfParameters (q : Fin p.T) (a : Fin p.K)
    (parameters : Option (Bool × (Fin p.K → ℝ))) : ℝ :=
  parameters.elim 0 (fun v => QuantizedRecordingMoments.quantizedValue
    (Q).D (Q).eta (v.2 a) (rewardAt rewards q a))

/-- The actual amplitude includes incoming retention and enablement. -/
def futureAmplitude (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (retainedGate rate rewards C_star C_h u t q).indicator (fun x =>
    amplitudeOfParameters rate rewards q a
      (futureParameters rate rewards C_star C_h u t q x))

/-- Literal original-source first moment. -/
def futureMomentOne (u t q : Fin p.T) (a : Fin p.K) (x : X) : ℝ :=
  futureAmplitude rate rewards C_star C_h u t q a x *
    futureCoefficient rate rewards C_star C_h u t q (some (some a)) x

/-- Literal original-source second moment. -/
def futureMomentTwo (u t q : Fin p.T) (a : Fin p.K) (x : X) : ℝ :=
  (futureAmplitude rate rewards C_star C_h u t q a x) ^ 2 *
    futureCoefficient rate rewards C_star C_h u t q (some (some a)) x

private theorem range_slots_eq_take {A B : Type*} (R : List A)
    (f : A → Option B) (n : ℕ) (hn : n ≤ R.length) :
    (List.range n).map (fun k => (R[k]?).bind f) = (R.take n).map f := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hir : i < R.length := lt_of_lt_of_le hin hn
    simp [List.getElem?_eq_getElem hir]

/-- Every dated slot agrees with the existing current-prefix observation,
including absence and no-launch branches. -/
theorem prefixInputs_eq_pastCells (q : Fin p.T) (x : X) :
    prefixInputs rate rewards C_star C_h q.val x =
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h q x := by
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  have hslots := range_slots_eq_take
    (sourceRecords rate rewards C_star C_h x)
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
    (q.val - sourceStart rate rewards C_star C_h x) (by
      simpa only [sourceRecords, sourceStart, hlen] using
        Nat.sub_le_sub_right (Nat.le_of_lt q.isLt)
          (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h))
  unfold prefixInputs ReferenceFirstCollectionCurrentRetainedGate.pastCells?
    ReferenceFirstCollectionCurrentRetainedGate.pastSlots
  simpa only [sourceRecords, sourceStart, hslots] using
    congrArg (fun slots => if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h q.val x then slots.mapM id else none) hslots.symm

/-- The full incoming stopped readout agrees, rather than only its queue. -/
theorem prefixReadout_eq_current (q : Fin p.T) (x : X) :
    prefixReadout rate rewards C_star C_h q.val x =
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h q x := by
  simp only [prefixReadout, prefixInputs_eq_pastCells,
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?]

/-- Actual incoming-clear event, expressed in the established prior field. -/
theorem incoming_clear_eq (q : Fin p.T) :
    {x : X | ∃ v, prefixReadout rate rewards C_star C_h q.val x = some v ∧ v.2.1 = false} =
      ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q := by
  ext x
  simp only [prefixReadout_eq_current, ReferenceFirstCollectionCurrentRetainedGate.H,
    Set.mem_ofPred_eq]

/-- A present cell has its actual reward and a positive canonical rate vector.
The optional marker and parameters are the projections of that very cell. -/
theorem futureCell_identities (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (c : RecordedQueueRun.RoundInput p.K)
    (hc : futureCell rate rewards C_star C_h u t q x = some c) :
    ∃ anchor : Fin p.K → ℝ,
      c.rate = CanonicalRecordingRates.xi p rate.eta.val anchor ∧
      c.reward = rewardAt rewards q ∧
      futureParameters rate rewards C_star C_h u t q x = some (c.enabled, c.rate) ∧
      futureMarker rate rewards C_star C_h u t q x = some c.recordedArm := by
  have hk := corrected_future_physical_kernel rate rewards C_star C_h u t q hfuture x
  cases hv : futureRecordingView rate rewards C_star C_h u t q x with
  | none => rw [hv] at hk; rw [hk.1] at hc; cases hc
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hk
    obtain ⟨r, c', selected, states, memories, snapshot, valid, _har, _ht,
      _hr, _hj, _hw, _hc, _hsel, _hv, _ho, _hf, _ht', hcell,
      _hparameters, hrate, hreward, _hcode, _hmarker⟩ := hk
    have he : c' = c := Option.some.inj (hcell.symm.trans hc)
    subst c'
    refine ⟨view.payload.anchor, hrate.trans (funext view.payload.rate_eq_canonical),
      hreward, ?_, ?_⟩
    · simp only [futureParameters, hc, Option.map_some]
    · simp only [futureMarker, hc, Option.map_some]

/-- Present actual parameters have the canonical positive beta lower bound. -/
theorem futureParameters_beta_le (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (enabled : Bool) (xi : Fin p.K → ℝ)
    (hp : futureParameters rate rewards C_star C_h u t q x = some (enabled, xi)) :
    ∀ a, beta ≤ xi a := by
  obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨anchor, hr, _⟩ := futureCell_identities rate rewards C_star C_h u t q hfuture x c hc
  have hxi : c.rate = xi := congrArg Prod.snd he
  rw [← hxi, hr]
  exact CanonicalRecordingRates.beta_le_xi p rate.eta.property anchor

/-- Existence comes from the actual slice, including its chosen cutoff endpoint. -/
theorem future_prefix_exists (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (hg : x ∈ futureGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val x = some L ∧
      futureCell rate rewards C_star C_h u t q x = some c ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) x = some (L ++ [c]) := by
  have hpres := (corrected_future_recordingView_presence rate rewards C_star C_h u t q hfuture x).2.1
  have hs := (corrected_future_sliceBranch_eq_literalGate rate rewards C_star C_h u t q hfuture x).1.mp hg
  rw [hs] at hpres
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hpres
  have hstep := corrected_future_step_inputs rate rewards C_star C_h u t q hfuture x
  rw [hc] at hstep
  obtain ⟨L, hL, hnext, _hread⟩ := hstep
  exact ⟨L, c, hL, hc, hnext⟩

/-- The actual accepted arrival has the nominal quantized value on retention. -/
theorem futureArrival_on_gate (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) (hg : x ∈ retainedGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val x = some L ∧
      futureCell rate rewards C_star C_h u t q x = some c ∧
      c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false ∧
      futureArrival rate rewards C_star C_h u t q a x =
        RecordedRoundMoments.normalizedQuantizedArrival Q c a := by
  obtain ⟨L, c, hL, hc, _⟩ := future_prefix_exists rate rewards C_star C_h u t q hfuture x hg.1.1
  obtain ⟨v, hv, hflag⟩ := hg.1.2
  have hread : prefixReadout rate rewards C_star C_h q.val x = some
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q L)) := by simp only [prefixReadout, hL, Option.map_some]
  have hf : (RecordedQueueRun.run Q L).overflow = false := by
    have he := Option.some.inj (hread.symm.trans hv)
    exact (congrArg (fun z => z.2.1) he).trans hflag
  obtain ⟨xi, hp⟩ := hg.2
  have he : c.enabled = true := by
    simpa only [futureParameters, hc, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] using (congrArg (Option.map Prod.fst) hp)
  refine ⟨L, c, hL, hc, he, hf, ?_⟩
  simp only [futureArrival, hL, hc]
  exact RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled Q _ c a he hf

/-- Absent, disabled and previously overflowed dates have no accepted arrival. -/
theorem futureArrival_off_gate (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (hg : x ∉ retainedGate rate rewards C_star C_h u t q) :
    futureArrival rate rewards C_star C_h u t q a x = 0 := by
  cases hL : prefixInputs rate rewards C_star C_h q.val x with
  | none => simp only [futureArrival, hL]
  | some L =>
    cases hc : futureCell rate rewards C_star C_h u t q x with
    | none => simp only [futureArrival, hL, hc]
    | some c =>
      simp only [futureArrival, hL, hc]
      by_cases he : c.enabled = true
      · by_cases hf : (RecordedQueueRun.run Q L).overflow = false
        · exfalso
          apply hg
          have hgate : x ∈ futureGate rate rewards C_star C_h u t q := by
            by_contra hn
            simp only [futureCell, ite_eq_right hn] at hc
            cases hc
          refine ⟨⟨hgate, ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run Q L), ?_, hf⟩⟩, ⟨c.rate, ?_⟩⟩
          · simp only [prefixReadout, hL, Option.map_some]
          · simp only [futureParameters, hc, Option.map_some, he]
        · exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q _ c a
            (Bool.eq_true_of_not_eq_false hf)
      · exact RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q _ c a
          (Bool.eq_false_iff.mpr he)

/-- Incoming clearance is predictable without an end-date invariance premise. -/
theorem incoming_clear_measurable (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {x : X | ∃ v, prefixReadout rate rewards C_star C_h q.val x = some v ∧ v.2.1 = false} := by
  rw [incoming_clear_eq]
  exact ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 q

private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hs : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  convert (hf.sumElim measurable_const).comp hs using 1
  funext o
  cases o <;> rfl

/-- Actual enabled parameters are predictable, including absent parameters. -/
theorem enabled_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {x : X | ∃ xi, futureParameters rate rewards C_star C_h u t q x = some (true, xi)} := by
  have hf : Measurable (fun o : Option (Bool × (Fin p.K → ℝ)) =>
      o.elim false Prod.fst) :=
    measurable_option_elim Prod.fst measurable_fst false
  have hm := hf.comp (futureParameters_prior_measurable
    rate rewards C_star C_h control0 u t q hfuture)
  have he : {x : X | ∃ xi, futureParameters rate rewards C_star C_h u t q x = some (true, xi)} =
      (fun x => (futureParameters rate rewards C_star C_h u t q x).elim false Prod.fst) ⁻¹' {true} := by
    ext x
    cases hp : futureParameters rate rewards C_star C_h u t q x with
    | none => simp [hp]
    | some v => rcases v with ⟨enabled, xi⟩; cases enabled <;> simp [hp]
  rw [he]
  exact (measurableSet_singleton true).preimage hm

/-- The full retention/enablement gate is in the original strict-prior field. -/
theorem retainedGate_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (retainedGate rate rewards C_star C_h u t q) :=
  ((futureGate_measurable rate rewards C_star C_h control0 u t q hfuture).inter
    (incoming_clear_measurable rate rewards C_star C_h control0 q)).inter
      (enabled_measurable rate rewards C_star C_h control0 u t q hfuture)

theorem rewardAt_bounds (q : Fin p.T) (a : Fin p.K) :
    rewardAt rewards q a ∈ Set.Icc (0 : ℝ) 1 := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hv : ((rewards q a).val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (rewards q a).isLt
  exact ⟨div_nonneg (Nat.cast_nonneg _) hD.le,
    (div_le_iff₀ hD).2 (by simpa only [one_mul] using hv)⟩

private theorem amplitudeOfParameters_measurable (q : Fin p.T) (a : Fin p.K) :
    Measurable (amplitudeOfParameters rate rewards q a) := by
  apply measurable_option_elim
  have hr : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (((Q).D : ℝ) * (Q).eta * rewardAt rewards q a) / v.2 a) :=
    measurable_const.div ((measurable_pi_apply a).comp measurable_snd)
  have hf := Nat.measurable_floor.comp hr
  have hc : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (Nat.floor ((((Q).D : ℝ) * (Q).eta * rewardAt rewards q a) / v.2 a) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hf
  exact hc.div_const _

theorem futureAmplitude_prior_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureAmplitude rate rewards C_star C_h u t q a) :=
  ((amplitudeOfParameters_measurable rate rewards q a).comp
    (futureParameters_prior_measurable rate rewards C_star C_h control0 u t q hfuture)).indicator
      (retainedGate_measurable rate rewards C_star C_h control0 u t q hfuture)

/-- The true amplitude is bounded using only actual present canonical xi. -/
theorem futureAmplitude_bounds (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) :
    0 ≤ futureAmplitude rate rewards C_star C_h u t q a x ∧
      futureAmplitude rate rewards C_star C_h u t q a x ≤ 1 / beta := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · obtain ⟨xi, hp⟩ := hg.2
    have hxi := futureParameters_beta_le rate rewards C_star C_h u t q hfuture x true xi hp a
    simp only [futureAmplitude, Set.indicator_of_mem hg, amplitudeOfParameters, hp,
      Option.elim_some]
    exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ (Q).eta_pos,
      QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
        (Q).D (Q).eta (xi a) _ beta (Q).D_pos (Q).eta_pos (hb.trans_le hxi)
        (rewardAt_bounds rewards q a) hb hxi⟩
  · simp only [futureAmplitude, Set.indicator_of_notMem hg]
    exact ⟨le_rfl, (one_div_pos.mpr hb).le⟩

/-- Exact scalar identity using L's actual optional arm indicator. -/
theorem futureArrival_eq_amplitude_mul_test (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (x : X) :
    futureArrival rate rewards C_star C_h u t q a x =
      futureAmplitude rate rewards C_star C_h u t q a x *
        futureTest rate rewards C_star C_h u t q (some (some a)) x := by
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · obtain ⟨L, c, _hL, hc, _he, _hf, ha⟩ :=
      futureArrival_on_gate rate rewards C_star C_h u t q hfuture a x hg
    obtain ⟨anchor, _hr, hreward, hp, hm⟩ :=
      futureCell_identities rate rewards C_star C_h u t q hfuture x c hc
    rw [ha]
    simp only [futureAmplitude, Set.indicator_of_mem hg, amplitudeOfParameters,
      hp, Option.elim_some, futureTest, hm, Option.some.injEq]
    by_cases hrecord : c.recordedArm = some a
    · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
        Q c a hrecord, hreward]
      simp only [hrecord, ite_true, mul_one]
    · simp only [RecordedRoundMoments.normalizedQuantizedArrival,
        RecordedQueueRun.quantizedArrival_eq_zero Q c a hrecord, Nat.cast_zero,
        zero_div, hrecord, ite_false, mul_zero]
  · rw [futureArrival_off_gate rate rewards C_star C_h u t q a x hg]
    simp only [futureAmplitude, Set.indicator_of_notMem hg, zero_mul]

/-- Squaring uses the same single arm atom, not an independent second draw. -/
theorem futureArrival_sq_eq (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) :
    (futureArrival rate rewards C_star C_h u t q a x) ^ 2 =
      (futureAmplitude rate rewards C_star C_h u t q a x) ^ 2 *
        futureTest rate rewards C_star C_h u t q (some (some a)) x := by
  rw [futureArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q hfuture a x]
  unfold futureTest
  split <;> ring

theorem futureArrival_bounds (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) :
    0 ≤ futureArrival rate rewards C_star C_h u t q a x ∧
      futureArrival rate rewards C_star C_h u t q a x ≤ 1 / beta := by
  rw [futureArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q hfuture a x]
  have hb := futureAmplitude_bounds rate rewards C_star C_h u t q hfuture a x
  unfold futureTest
  split
  · simpa only [mul_one] using hb
  · simp only [mul_zero]
    exact ⟨le_rfl, (one_div_pos.mpr (CanonicalRecordingRates.beta_pos p rate.eta.property)).le⟩

theorem beta_mul_futureArrival_bounds (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (x : X) :
    0 ≤ beta * futureArrival rate rewards C_star C_h u t q a x ∧
      beta * futureArrival rate rewards C_star C_h u t q a x ≤ 1 := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have ha := futureArrival_bounds rate rewards C_star C_h u t q hfuture a x
  refine ⟨mul_nonneg hb.le ha.1, ?_⟩
  calc
    _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left ha.2 hb.le
    _ = 1 := by field_simp [ne_of_gt hb]

theorem futureArrival_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable (futureArrival rate rewards C_star C_h u t q a) := by
  have ha := (futureAmplitude_prior_measurable
    rate rewards C_star C_h control0 u t q hfuture a).mono
      ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl
  have he : futureArrival rate rewards C_star C_h u t q a =
      (futureAmplitude rate rewards C_star C_h u t q a) *
        (futureTest rate rewards C_star C_h u t q (some (some a))) := by
    funext x
    exact futureArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q hfuture a x
  rw [he]
  exact ha.mul (futureTest_measurable rate rewards C_star C_h control0 u t q hfuture _)

theorem futureArrival_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (futureArrival rate rewards C_star C_h u t q a) mu := by
  apply (integrable_const (1 / beta)).mono'
    (futureArrival_measurable rate rewards C_star C_h control0 u t q hfuture a).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (futureArrival_bounds rate rewards C_star C_h u t q hfuture a x).1]
  exact (futureArrival_bounds rate rewards C_star C_h u t q hfuture a x).2

theorem futureArrival_sq_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable (fun x => (futureArrival rate rewards C_star C_h u t q a x) ^ 2) :=
  (futureArrival_measurable rate rewards C_star C_h control0 u t q hfuture a).pow_const 2

theorem futureArrival_sq_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (fun x => (futureArrival rate rewards C_star C_h u t q a x) ^ 2) mu := by
  apply (integrable_const ((1 / beta) ^ 2)).mono'
    (futureArrival_sq_measurable rate rewards C_star C_h control0 u t q hfuture a).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have ha := futureArrival_bounds rate rewards C_star C_h u t q hfuture a x
  exact pow_le_pow_left₀ ha.1 ha.2 2

/-- The real rate coefficient on a retained enabled date is the actual xi. -/
theorem futureCoefficient_on_gate (u t q : Fin p.T) (a : Fin p.K) (x : X)
    (xi : Fin p.K → ℝ)
    (hp : futureParameters rate rewards C_star C_h u t q x = some (true, xi)) :
    futureCoefficient rate rewards C_star C_h u t q (some (some a)) x = xi a := by
  simp only [futureCoefficient, hp,
    ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]

/-- Present canonical xi is used only on its real positive branch. -/
theorem futureMoments_on_gate (u t q : Fin p.T) (a : Fin p.K) (x : X)
    (hg : x ∈ retainedGate rate rewards C_star C_h u t q)
    (xi : Fin p.K → ℝ)
    (hp : futureParameters rate rewards C_star C_h u t q x = some (true, xi)) :
    futureMomentOne rate rewards C_star C_h u t q a x =
      QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (xi a) (rewardAt rewards q a) * xi a ∧
    futureMomentTwo rate rewards C_star C_h u t q a x =
      (QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (xi a) (rewardAt rewards q a)) ^ 2 * xi a := by
  simp only [futureMomentOne, futureMomentTwo, futureAmplitude, Set.indicator_of_mem hg,
    amplitudeOfParameters, hp, Option.elim_some, futureCoefficient_on_gate rate rewards C_star C_h u t q a x xi hp,
    and_self]

/-- Scalar rounding and second-moment estimates on the real present branch. -/
theorem futureMoments_retained_bounds (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (x : X)
    (hg : x ∈ retainedGate rate rewards C_star C_h u t q)
    (xi : Fin p.K → ℝ)
    (hp : futureParameters rate rewards C_star C_h u t q x = some (true, xi)) :
    0 < xi a ∧
    rewardAt rewards q a - xi a / ((Q).eta * ((Q).D : ℝ)) ≤
      futureMomentOne rate rewards C_star C_h u t q a x ∧
    futureMomentOne rate rewards C_star C_h u t q a x ≤ rewardAt rewards q a ∧
    0 ≤ futureMomentTwo rate rewards C_star C_h u t q a x ∧
    futureMomentTwo rate rewards C_star C_h u t q a x ≤ (rewardAt rewards q a) ^ 2 / xi a ∧
    (rewardAt rewards q a) ^ 2 / xi a ≤ 1 / xi a := by
  have hxi := (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
    (futureParameters_beta_le rate rewards C_star C_h u t q hfuture x true xi hp a)
  have hr := rewardAt_bounds rewards q a
  obtain ⟨h1, h2⟩ := futureMoments_on_gate rate rewards C_star C_h u t q a x hg xi hp
  rw [h1, h2]
  have hl := QuantizedRecordingMoments.quantizedValue_roundingError
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  have hu := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  have hs := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos hxi hr
  refine ⟨hxi, by simpa only [mul_comm] using hl, by simpa only [mul_comm] using hu,
    mul_nonneg (sq_nonneg _) hxi.le, by simpa only [mul_comm] using hs, ?_⟩
  exact div_le_div_of_nonneg_right (by nlinarith [hr.1, hr.2]) hxi.le

/-- Both moments vanish outside the true incoming-retained enabled gate. -/
theorem futureMoments_off_gate (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (hg : x ∉ retainedGate rate rewards C_star C_h u t q) :
    futureMomentOne rate rewards C_star C_h u t q a x = 0 ∧
      futureMomentTwo rate rewards C_star C_h u t q a x = 0 := by
  simp only [futureMomentOne, futureMomentTwo, futureAmplitude,
    Set.indicator_of_notMem hg, zero_pow (by decide : 2 ≠ 0), zero_mul, and_self]

/-- Gated first-moment rounding bounds, on the entire original source. -/
theorem futureMomentOne_bounds (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) :
    0 ≤ futureMomentOne rate rewards C_star C_h u t q a x ∧
    (retainedGate rate rewards C_star C_h u t q).indicator
        (fun _ => rewardAt rewards q a) x -
      (retainedGate rate rewards C_star C_h u t q).indicator
        (fun x => futureCoefficient rate rewards C_star C_h u t q (some (some a)) x /
          ((Q).eta * ((Q).D : ℝ))) x ≤ futureMomentOne rate rewards C_star C_h u t q a x ∧
    futureMomentOne rate rewards C_star C_h u t q a x ≤
      (retainedGate rate rewards C_star C_h u t q).indicator (fun _ => rewardAt rewards q a) x ∧
    futureMomentOne rate rewards C_star C_h u t q a x ≤ 1 := by
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · obtain ⟨xi, hp⟩ := hg.2
    have hb := futureMoments_retained_bounds rate rewards C_star C_h u t q hfuture a x hg xi hp
    have hn : 0 ≤ futureMomentOne rate rewards C_star C_h u t q a x := by
      unfold futureMomentOne
      rw [futureCoefficient_on_gate rate rewards C_star C_h u t q a x xi hp]
      exact mul_nonneg (futureAmplitude_bounds rate rewards C_star C_h u t q hfuture a x).1 hb.1.le
    simp only [Set.indicator_of_mem hg, futureCoefficient_on_gate rate rewards C_star C_h u t q a x xi hp]
    exact ⟨hn, hb.2.1, hb.2.2.1, hb.2.2.1.trans (rewardAt_bounds rewards q a).2⟩
  · rw [(futureMoments_off_gate rate rewards C_star C_h u t q a x hg).1]
    simp only [Set.indicator_of_notMem hg, sub_self, le_refl, zero_le_one, and_self]

/-- The second-moment bound uses a literal option case; absent xi is never invented. -/
theorem futureMomentTwo_bounds (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) :
    0 ≤ futureMomentTwo rate rewards C_star C_h u t q a x ∧
    futureMomentTwo rate rewards C_star C_h u t q a x ≤
      (retainedGate rate rewards C_star C_h u t q).indicator (fun x =>
        match futureParameters rate rewards C_star C_h u t q x with
        | some (true, xi) => (rewardAt rewards q a) ^ 2 / xi a
        | _ => 0) x := by
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · obtain ⟨xi, hp⟩ := hg.2
    have hb := futureMoments_retained_bounds rate rewards C_star C_h u t q hfuture a x hg xi hp
    simp only [Set.indicator_of_mem hg, hp]
    exact ⟨hb.2.2.2.1, hb.2.2.2.2.1⟩
  · rw [(futureMoments_off_gate rate rewards C_star C_h u t q a x hg).2]
    simp only [Set.indicator_of_notMem hg, le_refl, and_self]

/-- Exact original-mu first conditional moment, with no supplied law or inclusion. -/
theorem futureArrival_condExp (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    mu[futureArrival rate rewards C_star C_h u t q a |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        futureMomentOne rate rewards C_star C_h u t q a := by
  have he : futureArrival rate rewards C_star C_h u t q a =
      (futureAmplitude rate rewards C_star C_h u t q a) *
        (futureTest rate rewards C_star C_h u t q (some (some a))) := by
    funext x
    exact futureArrival_eq_amplitude_mul_test rate rewards C_star C_h u t q hfuture a x
  have hi := futureArrival_integrable rate rewards C_star C_h control0 u t q hfuture a
  rw [he] at hi ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (futureAmplitude_prior_measurable rate rewards C_star C_h control0 u t q hfuture a).stronglyMeasurable
    hi (futureTest_integrable rate rewards C_star C_h control0 u t q hfuture _)
  have hlaw := futureMarker_condExp rate rewards C_star C_h control0 u t q hfuture (some (some a))
  filter_upwards [hpull, hlaw] with x hp hl
  exact hp.trans (congrArg (fun v => futureAmplitude rate rewards C_star C_h u t q a x * v) hl)

/-- Exact second conditional moment of the same accepted arrival. -/
theorem futureArrival_sq_condExp (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    mu[(fun x => (futureArrival rate rewards C_star C_h u t q a x) ^ 2) |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        futureMomentTwo rate rewards C_star C_h u t q a := by
  have he : (fun x => (futureArrival rate rewards C_star C_h u t q a x) ^ 2) =
      (fun x => (futureAmplitude rate rewards C_star C_h u t q a x) ^ 2) *
        (futureTest rate rewards C_star C_h u t q (some (some a))) := by
    funext x
    exact futureArrival_sq_eq rate rewards C_star C_h u t q hfuture a x
  have hi := futureArrival_sq_integrable rate rewards C_star C_h control0 u t q hfuture a
  rw [he] at hi ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    ((futureAmplitude_prior_measurable rate rewards C_star C_h control0 u t q hfuture a).pow_const 2).stronglyMeasurable
    hi (futureTest_integrable rate rewards C_star C_h control0 u t q hfuture _)
  have hlaw := futureMarker_condExp rate rewards C_star C_h control0 u t q hfuture (some (some a))
  filter_upwards [hpull, hlaw] with x hp hl
  exact hp.trans (congrArg (fun v => (futureAmplitude rate rewards C_star C_h u t q a x) ^ 2 * v) hl)

/-- The increment vanishes on every excluded branch. -/
theorem retainedIncrement_off_gate (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (hg : x ∉ retainedGate rate rewards C_star C_h u t q) :
    retainedIncrement rate rewards C_star C_h u t q a x = 0 := by
  exact Set.indicator_of_notMem hg _

/-- A retained enabled zero arrival still subtracts four. -/
theorem retainedIncrement_zero_arrival (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (hg : x ∈ retainedGate rate rewards C_star C_h u t q)
    (hz : futureArrival rate rewards C_star C_h u t q a x = 0) :
    retainedIncrement rate rewards C_star C_h u t q a x = -4 := by
  simp only [retainedIncrement, Set.indicator_of_mem hg, hz, zero_sub]

/-- Disabled parameters preserve the increment even when the slice is present. -/
theorem retainedIncrement_disabled (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (xi : Fin p.K → ℝ)
    (hp : futureParameters rate rewards C_star C_h u t q x = some (false, xi)) :
    retainedIncrement rate rewards C_star C_h u t q a x = 0 := by
  apply retainedIncrement_off_gate
  rintro ⟨_hg, xi', hp'⟩
  rw [hp] at hp'
  cases hp'

/-- Prior overflow, rather than the outgoing flag, excludes a later update. -/
theorem retainedIncrement_prior_overflow (u t q : Fin p.T) (a : Fin p.K)
    (x : X) (v : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)
    (hv : prefixReadout rate rewards C_star C_h q.val x = some v)
    (hf : v.2.1 = true) :
    retainedIncrement rate rewards C_star C_h u t q a x = 0 := by
  apply retainedIncrement_off_gate
  rintro ⟨⟨_hg, w, hw, hclear⟩, _⟩
  have he : w = v := Option.some.inj (hw.symm.trans hv)
  rw [he, hf] at hclear
  cases hclear

theorem retainedIncrement_bounds (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (x : X) :
    -4 ≤ retainedIncrement rate rewards C_star C_h u t q a x ∧
      retainedIncrement rate rewards C_star C_h u t q a x ≤ 1 / beta := by
  by_cases hg : x ∈ retainedGate rate rewards C_star C_h u t q
  · rw [retainedIncrement, Set.indicator_of_mem hg]
    have ha := futureArrival_bounds rate rewards C_star C_h u t q hfuture a x
    constructor <;> linarith only [ha.1, ha.2]
  · rw [retainedIncrement_off_gate rate rewards C_star C_h u t q a x hg]
    exact ⟨by norm_num, (one_div_pos.mpr
      (CanonicalRecordingRates.beta_pos p rate.eta.property)).le⟩

theorem retainedIncrement_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable (retainedIncrement rate rewards C_star C_h u t q a) :=
  ((futureArrival_measurable rate rewards C_star C_h control0 u t q hfuture a).sub
    measurable_const).indicator (((sourcePrefixFiltration control0).le' (q.val + 1)) _
      (retainedGate_measurable rate rewards C_star C_h control0 u t q hfuture))

theorem retainedIncrement_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (retainedIncrement rate rewards C_star C_h u t q a) mu := by
  apply (integrable_const (4 + 1 / beta)).mono'
    (retainedIncrement_measurable rate rewards C_star C_h control0 u t q hfuture a).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  have hx := retainedIncrement_bounds rate rewards C_star C_h u t q hfuture a x
  have hb : 0 ≤ 1 / beta := (one_div_pos.mpr
    (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
  constructor <;> linarith only [hx.1, hx.2, hb]

theorem exp_retainedIncrement_measurable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Measurable (fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t q a x)) :=
  ((measurable_const : Measurable (fun _ : X => beta)).mul
    (retainedIncrement_measurable rate rewards C_star C_h control0 u t q hfuture a)).exp

theorem exp_retainedIncrement_integrable (control0 : TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    Integrable (fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t q a x)) mu := by
  apply (integrable_const (Real.exp 1)).mono'
    (exp_retainedIncrement_measurable rate rewards C_star C_h control0 u t q hfuture a).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp_of_le
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  calc
    _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left
      (retainedIncrement_bounds rate rewards C_star C_h u t q hfuture a x).2 hb.le
    _ = 1 := by field_simp [ne_of_gt hb]

/-- The existing chord applies to the actual accepted arrival. -/
theorem exp_retainedIncrement_le_chord (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (a : Fin p.K) (x : X)
    (hg : x ∈ retainedGate rate rewards C_star C_h u t q) :
    Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x) ≤
      Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) *
        (beta * futureArrival rate rewards C_star C_h u t q a x)) := by
  have ha := beta_mul_futureArrival_bounds rate rewards C_star C_h u t q hfuture a x
  have hc := RecordedRoundMoments.exp_le_unit_chord ha.1 ha.2
  rw [retainedIncrement, Set.indicator_of_mem hg]
  have he : beta * (futureArrival rate rewards C_star C_h u t q a x - 4) =
      -4 * beta + beta * futureArrival rate rewards C_star C_h u t q a x := by ring
  rw [he, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)

/-- Original-mu conditional exponential increment bound at every strict-future
finite date. All retention, measurability and integrability inputs are produced. -/
theorem condExp_exp_retainedIncrement_le_one (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    mu[(fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t q a x)) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] (fun _ => (1 : ℝ)) := by
  let Fq := sourcePrefixFiltration control0 (q.val + 1)
  let G := retainedGate rate rewards C_star C_h u t q
  let A := futureArrival rate rewards C_star C_h u t q a
  let c := Real.exp (-4 * beta)
  let d := c * ((Real.exp 1 - 1) * beta)
  let b : X → ℝ := fun x => if x ∈ G then c else 1
  let B : X → ℝ := fun x => b x + d * A x
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hG : MeasurableSet[Fq] G :=
    retainedGate_measurable rate rewards C_star C_h control0 u t q hfuture
  have hb : Measurable[Fq] b := Measurable.ite hG measurable_const measurable_const
  have hbi : Integrable b mu := by
    apply (integrable_const (|c| + 1)).mono'
      (hb.mono hle le_rfl).aestronglyMeasurable
    filter_upwards [] with x
    dsimp only [b]
    split <;> simp only [Real.norm_eq_abs]
    · linarith only [abs_nonneg c]
    · norm_num
  have hAi : Integrable A mu :=
    futureArrival_integrable rate rewards C_star C_h control0 u t q hfuture a
  have hBi : Integrable B mu := hbi.add (hAi.const_mul d)
  have hpoint : (fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t q a x)) ≤ B := by
    intro x
    change Real.exp (beta * retainedIncrement rate rewards C_star C_h u t q a x) ≤ B x
    by_cases hg : x ∈ G
    · have hc := exp_retainedIncrement_le_chord rate rewards C_star C_h u t q hfuture a x hg
      simp only [B, b, ite_eq_left hg]
      convert hc using 1
      dsimp only [c, d, A]
      ring
    · rw [retainedIncrement_off_gate rate rewards C_star C_h u t q a x hg,
        mul_zero, Real.exp_zero]
      simp only [B, b, ite_eq_right hg, A,
        futureArrival_off_gate rate rewards C_star C_h u t q a x hg, mul_zero, add_zero, le_refl]
  have hmono := condExp_mono (m := Fq)
    (exp_retainedIncrement_integrable rate rewards C_star C_h control0 u t q hfuture a)
    hBi (Filter.Eventually.of_forall hpoint)
  have hadd := condExp_add hbi (hAi.const_mul d) Fq
  have hscale := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_const : StronglyMeasurable[Fq] (fun _ : X => d))
    (hAi.const_mul d) hAi
  have hbase : mu[b | Fq] = b := condExp_of_stronglyMeasurable hle hb.stronglyMeasurable hbi
  have hmean := futureArrival_condExp rate rewards C_star C_h control0 u t q hfuture a
  have hd : 0 ≤ d := mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (by linarith [Real.exp_one_gt_two])
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)
  have hscalar : c + d ≤ 1 := by
    have h := ReferenceFirstCollectionRenewalExponentialIncrement.exp_neg_four_beta_chord_le_one rate
    dsimp only [c, d]
    nlinarith only [h]
  filter_upwards [hmono, hadd, hscale, hmean] with x hm ha hs hmean'
  apply hm.trans
  have he : mu[B | Fq] x = b x + d *
      futureMomentOne rate rewards C_star C_h u t q a x := by
    calc
      _ = mu[b | Fq] x + mu[(fun x => d * A x) | Fq] x := ha
      _ = b x + d * mu[A | Fq] x := by
        rw [hbase]
        exact congrArg (fun z => b x + z) hs
      _ = _ := by rw [hmean']
  rw [he]
  by_cases hg : x ∈ G
  · simp only [b, ite_eq_left hg]
    calc
      _ ≤ c + d * 1 := add_le_add (le_refl c) (mul_le_mul_of_nonneg_left
        (futureMomentOne_bounds rate rewards C_star C_h u t q hfuture a x).2.2.2 hd)
      _ = c + d := by ring
      _ ≤ 1 := hscalar
  · simp only [b, ite_eq_right hg,
      (futureMoments_off_gate rate rewards C_star C_h u t q a x hg).1,
      mul_zero, add_zero, le_refl]

/-- The queue witness retains its first outgoing crossing update. Its inputs
are the actual prefix, actual cell and incoming-clear flag; it never resets. -/
theorem retained_queue_step (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (a : Fin p.K) (x : X) (hg : x ∈ retainedGate rate rewards C_star C_h u t q) :
    ∃ L c, prefixInputs rate rewards C_star C_h q.val x = some L ∧
      futureCell rate rewards C_star C_h u t q x = some c ∧
      c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false ∧
      prefixInputs rate rewards C_star C_h (q.val + 1) x = some (L ++ [c]) ∧
      prefixReadout rate rewards C_star C_h (q.val + 1) x = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) ∧
      retainedIncrement rate rewards C_star C_h u t q a x =
        RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a - 4 := by
  obtain ⟨L, c, hL, hc, he, hf, _ha⟩ :=
    futureArrival_on_gate rate rewards C_star C_h u t q hfuture a x hg
  have hstep := corrected_future_step_inputs rate rewards C_star C_h u t q hfuture x
  rw [hc] at hstep
  obtain ⟨L', hL', hnext, hread⟩ := hstep
  have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
  subst L'
  refine ⟨L, c, hL, hc, he, hf, hnext, hread, ?_⟩
  simp only [retainedIncrement, Set.indicator_of_mem hg, futureArrival, hL, hc]

/-- The selected cutoff endpoint is part of the actual finite update gate. -/
theorem cutoff_endpoint_in_gate (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (hcut : sliceBranch rate rewards C_star C_h u t q x = some true) :
    x ∈ futureGate rate rewards C_star C_h u t q ∧
      ∃ L c, prefixInputs rate rewards C_star C_h q.val x = some L ∧
        futureCell rate rewards C_star C_h u t q x = some c ∧
        prefixInputs rate rewards C_star C_h (q.val + 1) x = some (L ++ [c]) := by
  have hg := (corrected_future_sliceBranch_eq_literalGate
    rate rewards C_star C_h u t q hfuture x).1.mpr (by simp only [hcut, Option.isSome_some])
  exact ⟨hg, future_prefix_exists rate rewards C_star C_h u t q hfuture x hg⟩

/-- Joint consumer interface on the original law and the same E(u,t).
No recording law, retention, prefix, measurability or integrability is supplied. -/
theorem strict_future_retained_moments (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    (mu[futureArrival rate rewards C_star C_h u t q a |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        futureMomentOne rate rewards C_star C_h u t q a) ∧
    (mu[(fun x => (futureArrival rate rewards C_star C_h u t q a x) ^ 2) |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu]
        futureMomentTwo rate rewards C_star C_h u t q a) ∧
    (mu[(fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t q a x)) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] (fun _ => (1 : ℝ))) :=
  ⟨futureArrival_condExp rate rewards C_star C_h control0 u t q hfuture a,
    futureArrival_sq_condExp rate rewards C_star C_h control0 u t q hfuture a,
    condExp_exp_retainedIncrement_le_one rate rewards C_star C_h control0 u t q hfuture a⟩

/-- The first conditional moment is at most the gated calendar reward. -/
theorem futureArrival_condExp_bounds (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val) (a : Fin p.K) :
    ∀ᵐ x ∂mu, 0 ≤ mu[futureArrival rate rewards C_star C_h u t q a |
        sourcePrefixFiltration control0 (q.val + 1)] x ∧
      mu[futureArrival rate rewards C_star C_h u t q a |
        sourcePrefixFiltration control0 (q.val + 1)] x ≤
        (retainedGate rate rewards C_star C_h u t q).indicator
          (fun _ => rewardAt rewards q a) x ∧
      mu[futureArrival rate rewards C_star C_h u t q a |
        sourcePrefixFiltration control0 (q.val + 1)] x ≤ 1 := by
  filter_upwards [futureArrival_condExp rate rewards C_star C_h control0 u t q hfuture a] with x hx
  rw [hx]
  have hb := futureMomentOne_bounds rate rewards C_star C_h u t q hfuture a x
  exact ⟨hb.1, hb.2.2.1, hb.2.2.2⟩

end Bandits.Support.ReferenceFirstCollectionCorrectedFutureRetainedMoment
