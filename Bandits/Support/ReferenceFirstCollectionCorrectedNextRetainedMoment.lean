/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedNextRecordingLaw
public import Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedGate

/-!
# Actual corrected successor retained moment

The normalized arrival comes from the actual optional successor cell and the
whole reward table. Retention uses the inherited AFTER flag, strictly before
this successor update. Enabled zero arrivals still subtract four; terminal
successors contribute zero. These are internal ingredients for the original
source corrected overflow tail, not manuscript or regret closure.

Sources: `04_slow_fast_learner.tex:140-188,245-278`,
`05_binary_transport.tex:354-431`, `06_interruptions.tex:31-100,355-426`
under `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedMoment

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p

variable (u t : Fin p.T)

local notation "C" => Set.ofPred (fun x : X =>
  x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t ∧
    ∃ g, ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g ∧ t.val + 1 < g)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "G" hq => Set.ofPred (fun x : X => x ∈ C ∧
  (∃ y, ReferenceFirstCollectionCurrentQueueReadout.after?
    rate rewards C_star C_h t x = some y ∧ Prod.fst (Prod.snd y) = false) ∧
  ∃ xi, ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
    rate rewards C_star C_h t hq x = some (true, xi))

/-- The actual normalized successor arrival. Only the absent optional cell
contributes the scalar zero by convention. -/
def nextArrival (hq : t.val + 1 < p.T) (a : Fin p.K) (x : X) : ℝ :=
  match ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
      rate rewards C_star C_h t hq x with
  | none => 0
  | some c => RecordedRoundMoments.normalizedQuantizedArrival Q c a

/-- Retain the enabled successor exactly when the inherited queue after the
first-call cell has not overflowed. There is no outgoing-overflow test. -/
def retainedIncrement (hq : t.val + 1 < p.T) (a : Fin p.K) : X → ℝ :=
  (G hq).indicator (fun x => nextArrival rate rewards C_star C_h t hq a x - 4)

/-- Natural optional-successor extension: the terminal date adds zero and
never constructs a nonexistent finite successor. -/
def successorIncrement (a : Fin p.K) (x : X) : ℝ :=
  if hq : t.val + 1 < p.T then
    retainedIncrement rate rewards C_star C_h u t hq a x else 0

private theorem run_append_one (L : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.run Q (L ++ [c]) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
  have he (state : RecordedQueueRun.RunState p.K) :
      RecordedQueueRun.execute Q (L ++ [c]) state =
        RecordedQueueRun.step Q (RecordedQueueRun.execute Q L state) c := by
    induction L generalizing state with
    | nil => rfl
    | cons head rest ih => exact ih _
  exact he _

/-- The original after-readout in the retained test comes from the inherited
actual list followed by the actual first-call cell, with no queue reset. -/
theorem retainedIncrement_queue_witness (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (hx : x ∈ G hq) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t x = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t x = some c ∧
      c.enabled = true ∧
      ReferenceFirstCollectionCurrentQueueReadout.after? rate rewards C_star C_h t x =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q (L ++ [c]))) ∧
      (RecordedQueueRun.run Q (L ++ [c])).overflow = false := by
  obtain ⟨L, c, hL, hc, he, _hb, ha, _⟩ :=
    ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts
      rate rewards C_star C_h u t a x hx.1.1
  obtain ⟨y, hy, hflag⟩ := hx.2.1
  have ha' : ReferenceFirstCollectionCurrentQueueReadout.after?
      rate rewards C_star C_h t x =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q (L ++ [c]))) := by
    rw [run_append_one]
    exact ha
  have hread := Option.some.inj (ha'.symm.trans hy)
  have hf := congrArg (fun z => z.2.1) hread
  exact ⟨L, c, hL, hc, he, ha', hf.trans hflag⟩

/-- Every present corrected successor cell reads the original whole reward
table at its actual date, in both continuing LIVE and immediate COLLECTION. -/
theorem nextCell_reward (hq : t.val + 1 < p.T) (x : X) (hx : x ∈ C)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
      rate rewards C_star C_h t hq x = some c) :
    c.reward = fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ) := by
  obtain ⟨_r0, r, _h0, _h1, _ha0, hr, _ht0, ht, _hstate,
      _hrows, _hj, hreward, _hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_successor_records
      rate rewards C_star C_h u t hq x hx.1
  have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simpa only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell,
      hr, Option.bind_some] using hc
  have hread := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_next_readouts
    rate rewards C_star C_h u t hq x hx.1 r hr
  have hcut := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_next_cutoff_physical
    rate rewards C_star C_h u t hq x hx.1 r hr
  cases hd : r.output.preparation.coordinator <;> simp only [hd] at hread hcut
  all_goals try (rw [hread] at hcell; cases hcell)
  rename_i registers owned base outcome
  cases outcome
  case continuingChosen =>
    obtain ⟨cell, hlive, hcollection⟩ := hread
    have he : cell.input = c := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
        hlive, hcollection, Option.some_or, Option.some.injEq] using hcell
    rw [← he, cell.input_eq]
    change (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) = _
    rw [hreward, ht]
  case cutoffChosen =>
    obtain ⟨c', hcollection, hlive⟩ := hread
    have he : c' = c := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
        hlive, hcollection, Option.none_or, Option.some.injEq] using hcell
    obtain ⟨c'', _payload, _ledger, _started, _weights, _out,
      hc'', _hcall, _hrate, hrew, _⟩ := hcut
    have he' : c'' = c' := Option.some.inj (hc''.symm.trans hcollection)
    rw [← he, ← he', hrew, ht]
  all_goals rw [hread] at hcell; cases hcell

/-- Present physical cells use their own canonical payload and original whole
reward table. Absence remains an absent marker and absent parameters. -/
theorem nextCell_identities (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ C) :
    match ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
        rate rewards C_star C_h t hq x with
    | none =>
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = none ∧
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x = none ∧
        nextArrival rate rewards C_star C_h t hq a x = 0
    | some c => ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextDownView
          rate rewards C_star C_h t hq x = some view ∧
        c.rate = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor ∧
        c.reward = (fun j => ((rewards ⟨t.val + 1, hq⟩ j).val : ℝ) / (D p : ℝ)) ∧
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = some c.recordedArm ∧
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x = some (c.enabled, c.rate) ∧
        nextArrival rate rewards C_star C_h t hq a x =
          if c.recordedArm = some a then
            QuantizedRecordingMoments.quantizedValue (Q).D (Q).eta (c.rate a)
              (((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) else 0 := by
  cases hc : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
      rate rewards C_star C_h t hq x with
  | none => simp [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker,
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters, nextArrival, hc]
  | some c =>
      have hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x = some (c.enabled, c.rate) := by
        simp [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters, hc]
      obtain ⟨view, hv, hr, _hb, _hs⟩ :=
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_nextParameters_bounds
          rate rewards C_star C_h u t hq x hx.1 c.enabled c.rate hp
      have hw := nextCell_reward rate rewards C_star C_h u t hq x hx c hc
      refine ⟨view, hv, hr.trans (funext view.payload.rate_eq_canonical), hw, ?_, hp, ?_⟩
      · simp [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker, hc]
      · simp only [nextArrival, hc]
        by_cases hm : c.recordedArm = some a
        · rw [ite_eq_left hm,
            RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
              Q c a hm, hw]
        · rw [ite_eq_right hm, RecordedRoundMoments.normalizedQuantizedArrival,
            RecordedQueueRun.quantizedArrival_eq_zero Q c a hm, Nat.cast_zero, zero_div]

/-- The inherited AFTER flag is the run of the actual successor prefix.
No outgoing overflow of the successor appears in this conclusion. -/
theorem retained_successor_queue_witness (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ G hq) :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = some L ∧
      ReferenceFirstCollectionCurrentQueueReadout.after? rate rewards C_star C_h t x =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q L)) ∧
      (RecordedQueueRun.run Q L).overflow = false := by
  obtain ⟨y, hy, hf⟩ := hx.2.1
  have he := ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_after_eq_successor_prefix
    rate rewards C_star C_h u t hq x hx.1.1
  rw [he, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?] at hy
  cases hL : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h ⟨t.val + 1, hq⟩ x with
  | none => simp only [hL, Option.map_none] at hy; cases hy
  | some L =>
      simp only [hL, Option.map_some, Option.some.injEq] at hy
      refine ⟨L, rfl, ?_, ?_⟩
      · rw [he, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
        rfl
      · exact (congrArg (fun z => z.2.1) hy).trans hf

/-- Canonical actual rates bound the nominal successor arrival even before
restricting by the inherited-overflow gate. -/
theorem nextArrival_bounds (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ C) :
    0 ≤ nextArrival rate rewards C_star C_h t hq a x ∧
      nextArrival rate rewards C_star C_h t hq a x ≤ 1 / beta := by
  have hb : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hc : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
      rate rewards C_star C_h t hq x with
  | none => simp only [nextArrival, hc]; exact ⟨le_rfl, (one_div_pos.mpr hb).le⟩
  | some c =>
      have hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x = some (c.enabled, c.rate) := by
        rw [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters, hc]
        rfl
      obtain ⟨_view, _hv, _hr, hrate, _hs⟩ :=
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_nextParameters_bounds
          rate rewards C_star C_h u t hq x hx.1 c.enabled c.rate hp
      simp only [nextArrival, hc]
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · by_cases hm : c.recordedArm = some a
        · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
            Q c a hm]
          exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
            (Q).D (Q).eta (c.rate a) (c.reward a) beta (Q).D_pos (Q).eta_pos
            (c.rate_pos a) ⟨c.reward_nonneg a, c.reward_le_one a⟩ hb (hrate a).1
        · rw [RecordedRoundMoments.normalizedQuantizedArrival,
            RecordedQueueRun.quantizedArrival_eq_zero Q c a hm]
          simpa only [Nat.cast_zero, zero_div] using (one_div_pos.mpr hb).le

private def amplitudeOfParameters (hq : t.val + 1 < p.T) (a : Fin p.K)
    (parameters : Option (Bool × (Fin p.K → ℝ))) : ℝ :=
  parameters.elim 0 (fun v => QuantizedRecordingMoments.quantizedValue
    (Q).D (Q).eta (v.2 a)
    (((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)))

private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hs : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  convert (hf.sumElim measurable_const).comp hs using 1
  funext o
  cases o <;> rfl

private theorem amplitudeOfParameters_measurable (hq : t.val + 1 < p.T)
    (a : Fin p.K) : Measurable (amplitudeOfParameters rate rewards t hq a) := by
  apply measurable_option_elim
  have hr : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (((Q).D : ℝ) * (Q).eta *
        (((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ))) / v.2 a) :=
    measurable_const.div ((measurable_pi_apply a).comp measurable_snd)
  have hf := Nat.measurable_floor.comp hr
  have hc : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      (Nat.floor ((((Q).D : ℝ) * (Q).eta *
        (((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ))) / v.2 a) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hf
  exact hc.div_const _

private theorem nextArrival_amplitude_identity (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (hx : x ∈ C) :
    nextArrival rate rewards C_star C_h t hq a x =
      amplitudeOfParameters rate rewards t hq a
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x) *
      (if ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = some (some a) then (1 : ℝ) else 0) := by
  cases hc : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
      rate rewards C_star C_h t hq x with
  | none => simp [nextArrival, amplitudeOfParameters,
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters,
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker, hc]
  | some c =>
      have hreward := nextCell_reward rate rewards C_star C_h u t hq x hx c hc
      simp only [nextArrival, ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker, hc,
        Option.map_some, amplitudeOfParameters, Option.elim_some]
      by_cases hm : c.recordedArm = some a
      · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded Q c a hm,
          hreward]
        simp only [hm, ite_true, mul_one]
      · rw [RecordedRoundMoments.normalizedQuantizedArrival,
          RecordedQueueRun.quantizedArrival_eq_zero Q c a hm]
        simp only [Nat.cast_zero, zero_div, Option.some.injEq, hm, ite_false, mul_zero]

/-- An absent outer marker supplies zero actual arrival, with no cell invented. -/
theorem nextArrival_of_absent_marker (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ C)
    (hm : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
      rate rewards C_star C_h t hq x = none) :
    nextArrival rate rewards C_star C_h t hq a x = 0 := by
  rw [nextArrival_amplitude_identity rate rewards C_star C_h u t hq a x hx, hm]
  simp only [reduceCtorEq, ite_false, mul_zero]

/-- A present cell with inner-none marker also supplies zero arrival. -/
theorem nextArrival_of_inner_none (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ C)
    (hm : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
      rate rewards C_star C_h t hq x = some none) :
    nextArrival rate rewards C_star C_h t hq a x = 0 := by
  rw [nextArrival_amplitude_identity rate rewards C_star C_h u t hq a x hx, hm]
  simp only [Option.some.injEq, reduceCtorEq, ite_false, mul_zero]

/-- The actual raw observation localized to the corrected event is Borel;
its amplitude uses the original whole reward table and actual prior rates. -/
theorem corrected_nextArrival_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable ((C).indicator (nextArrival rate rewards C_star C_h t hq a)) := by
  have hC : MeasurableSet C := ((sourcePrefixFiltration control0).le' (t.val + 2)) _
    (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable rate rewards C_star C_h control0 u t)
  have hp := (ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCellParameters_measurable
    rate rewards C_star C_h control0 u t hq).mono
      ((sourcePrefixFiltration control0).le' (t.val + 2)) le_rfl
  have ha := (amplitudeOfParameters_measurable rate rewards t hq a).comp hp
  have ht : Measurable (fun x : X => if
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = some (some a) then (1 : ℝ) else 0) :=
    measurable_const.ite ((measurableSet_singleton (some (some a))).preimage
      (ReferenceFirstCollectionCorrectedNextRecordingLaw.corrected_nextMarker_measurable rate rewards C_star C_h t hq)) measurable_const
  have hm := ha.mul (ht.indicator hC)
  convert hm using 1
  funext x
  by_cases hx : x ∈ C
  · simp only [Pi.mul_apply, Function.comp_def, Set.indicator_of_mem hx, hx.1, ite_true]
    exact nextArrival_amplitude_identity rate rewards C_star C_h u t hq a x hx
  · simp only [Pi.mul_apply, Set.indicator_of_notMem hx, mul_zero]

private theorem roundedReward_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) :
    (((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hv : ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (rewards ⟨t.val + 1, hq⟩ a).isLt
  exact ⟨div_nonneg (Nat.cast_nonneg _) hD.le,
    (div_le_iff₀ hD).2 (by simpa only [one_mul] using hv)⟩

private def localizedAmplitude (hq : t.val + 1 < p.T) (a : Fin p.K) : X → ℝ :=
  (C).indicator (fun x => amplitudeOfParameters rate rewards t hq a
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
      rate rewards C_star C_h t hq x))

private theorem localizedAmplitude_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (localizedAmplitude rate rewards C_star C_h u t hq a) := by
  have hp := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCellParameters_measurable
    rate rewards C_star C_h control0 u t hq
  have ha := ((amplitudeOfParameters_measurable rate rewards t hq a).comp hp).indicator
    (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable
      rate rewards C_star C_h control0 u t)
  convert ha using 1
  funext x
  by_cases hx : x ∈ C
  · simp only [localizedAmplitude, Set.indicator_of_mem hx, Function.comp_def,
      hx.1, ite_true]
  · simp only [localizedAmplitude, Set.indicator_of_notMem hx]

private theorem localizedAmplitude_bounds (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) :
    0 ≤ localizedAmplitude rate rewards C_star C_h u t hq a x ∧
      localizedAmplitude rate rewards C_star C_h u t hq a x ≤ 1 / beta := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  by_cases hx : x ∈ C
  · rw [localizedAmplitude, Set.indicator_of_mem hx]
    cases hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
        rate rewards C_star C_h t hq x with
    | none => simp only [amplitudeOfParameters, Option.elim_none]
                  ; exact ⟨le_rfl, (one_div_pos.mpr hb).le⟩
    | some v =>
        rcases v with ⟨enabled, xi⟩
        obtain ⟨_view, _hv, _hr, hxi, _hs⟩ :=
          ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_nextParameters_bounds
            rate rewards C_star C_h u t hq x hx.1 enabled xi hp
        exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ (Q).eta_pos,
          QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
            (Q).D (Q).eta (xi a) _ beta (Q).D_pos (Q).eta_pos (hb.trans_le (hxi a).1)
            (roundedReward_bounds rewards t hq a) hb (hxi a).1⟩
  · rw [localizedAmplitude, Set.indicator_of_notMem hx]
    exact ⟨le_rfl, (one_div_pos.mpr hb).le⟩

private theorem localizedAmplitude_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (localizedAmplitude rate rewards C_star C_h u t hq a) mu := by
  have hm := (localizedAmplitude_measurable
    rate rewards C_star C_h u t control0 hq a).mono
      ((sourcePrefixFiltration control0).le' (t.val + 2)) le_rfl
  apply (integrable_const (1 / beta)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (localizedAmplitude_bounds rate rewards C_star C_h u t hq a x).1]
  exact (localizedAmplitude_bounds rate rewards C_star C_h u t hq a x).2

/-- Internal arrival integrability on the original, unnormalized source law. -/
theorem corrected_nextArrival_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable ((C).indicator (nextArrival rate rewards C_star C_h t hq a)) mu := by
  apply (integrable_const (1 / beta)).mono'
    (corrected_nextArrival_measurable
      rate rewards C_star C_h u t control0 hq a).aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_nonneg (nextArrival_bounds rate rewards C_star C_h u t hq a x hx).1]
    exact (nextArrival_bounds rate rewards C_star C_h u t hq a x hx).2
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact (one_div_pos.mpr (CanonicalRecordingRates.beta_pos p rate.eta.property)).le

private theorem weighted_marker_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) (o : Option (Option (Fin p.K))) :
    Integrable ((localizedAmplitude rate rewards C_star C_h u t hq a) *
      ((C).indicator (fun x => if
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0))) mu := by
  have htest := ReferenceFirstCollectionCorrectedNextRecordingLaw.corrected_markerTest_integrable
    rate rewards C_star C_h u t control0 hq o
  exact (localizedAmplitude_integrable
    rate rewards C_star C_h u t control0 hq a).mul_bdd htest.aestronglyMeasurable
      (c := 1) (Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ C
        · rw [Set.indicator_of_mem hx]
          split_ifs <;> norm_num
        · rw [Set.indicator_of_notMem hx, norm_zero]
          norm_num))

private theorem weighted_marker_condExp (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) (o : Option (Option (Fin p.K))) :
    mu[(localizedAmplitude rate rewards C_star C_h u t hq a) *
      ((C).indicator (fun x => if
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0)) |
      sourcePrefixFiltration control0 (t.val + 2)] =ᵐ[mu]
      (localizedAmplitude rate rewards C_star C_h u t hq a) *
        ((C).indicator (fun x =>
          ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
            (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
              rate rewards C_star C_h t hq x))) := by
  have htest := ReferenceFirstCollectionCorrectedNextRecordingLaw.corrected_markerTest_integrable
    rate rewards C_star C_h u t control0 hq o
  have hproduct := weighted_marker_integrable rate rewards C_star C_h u t control0 hq a o
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (localizedAmplitude_measurable
      rate rewards C_star C_h u t control0 hq a).stronglyMeasurable hproduct htest
  have hlaw := ReferenceFirstCollectionCorrectedNextRecordingLaw.corrected_nextMarker_condExp
    rate rewards C_star C_h control0 u t hq o
  filter_upwards [hpull, hlaw] with x hp hl
  exact hp.trans (congrArg
    (fun z => localizedAmplitude rate rewards C_star C_h u t hq a x * z) hl)

private theorem all_tags_arrival_condExp (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    mu[(C).indicator (nextArrival rate rewards C_star C_h t hq a) |
      sourcePrefixFiltration control0 (t.val + 2)] =ᵐ[mu]
      (localizedAmplitude rate rewards C_star C_h u t hq a) *
        ((C).indicator (fun x =>
          ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters (some (some a))
            (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
              rate rewards C_star C_h t hq x))) := by
  let Fq := sourcePrefixFiltration control0 (t.val + 2)
  let W : Option (Option (Fin p.K)) → X → ℝ := fun o =>
    (localizedAmplitude rate rewards C_star C_h u t hq a) *
      ((C).indicator (fun x => if
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0))
  let V : Option (Option (Fin p.K)) → X → ℝ := fun o =>
    (localizedAmplitude rate rewards C_star C_h u t hq a) *
      ((C).indicator (fun x =>
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
          (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
            rate rewards C_star C_h t hq x)))
  let b : Option (Option (Fin p.K)) → ℝ := fun o => if o = some (some a) then 1 else 0
  have hW : ∀ o, Integrable (W o) mu := fun o =>
    weighted_marker_integrable rate rewards C_star C_h u t control0 hq a o
  have hleft : (C).indicator (nextArrival rate rewards C_star C_h t hq a) =
      ∑ o, b o • W o := by
    have he : (∑ o, b o • W o) = W (some (some a)) := by simp [b, ite_smul]
    rw [he]
    funext x
    by_cases hx : x ∈ C
    · simp only [W, Pi.mul_apply, localizedAmplitude, Set.indicator_of_mem hx]
      exact nextArrival_amplitude_identity rate rewards C_star C_h u t hq a x hx
    · simp only [W, Pi.mul_apply, localizedAmplitude, Set.indicator_of_notMem hx, zero_mul]
  have hright : (∑ o, b o • V o) = V (some (some a)) := by simp [b, ite_smul]
  have hsum := condExp_finsetSum (μ := mu) (s := Finset.univ)
    (f := fun o => b o • W o) (fun o _ => (hW o).smul (b o)) Fq
  have hterms : ∀ o, mu[b o • W o | Fq] =ᵐ[mu] b o • V o := by
    intro o
    have hmarker := weighted_marker_condExp rate rewards C_star C_h u t control0 hq a o
    have hscale := condExp_smul (μ := mu) (b o) (W o) Fq
    filter_upwards [hmarker, hscale] with x hm hs
    exact hs.trans (congrArg (fun z => b o • z) hm)
  rw [hleft]
  filter_upwards [hsum, Filter.eventually_all.mpr hterms] with x hs ht
  calc
    _ = (∑ o, mu[b o • W o | Fq]) x := hs
    _ = (∑ o, b o • V o) x := by
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun o _ => ht o)
    _ = V (some (some a)) x := congrFun hright x

/-- The original-source conditional arrival bound. Quantization uses the
actual predictable rate, not a fixed or independently chosen coefficient. -/
theorem corrected_nextArrival_condExp_le_reward (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    mu[(C).indicator (nextArrival rate rewards C_star C_h t hq a) |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu]
      (C).indicator (fun _ => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) := by
  have hlaw := all_tags_arrival_condExp rate rewards C_star C_h u t control0 hq a
  filter_upwards [hlaw] with x hl
  rw [hl]
  by_cases hx : x ∈ C
  · simp only [Pi.mul_apply, localizedAmplitude, Set.indicator_of_mem hx]
    cases hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
        rate rewards C_star C_h t hq x with
    | none =>
        simp only [amplitudeOfParameters, Option.elim_none, zero_mul]
        exact (roundedReward_bounds rewards t hq a).1
    | some v =>
        rcases v with ⟨enabled, xi⟩
        cases enabled with
        | false =>
            simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
              mul_zero]
            exact (roundedReward_bounds rewards t hq a).1
        | true =>
            obtain ⟨_view, _hv, _hr, hxi, _hs⟩ :=
              ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_nextParameters_bounds
                rate rewards C_star C_h u t hq x hx.1 true xi hp
            have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
            simpa only [amplitudeOfParameters, Option.elim_some,
              ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters, mul_comm]
              using QuantizedRecordingMoments.quantizedValue_firstMoment_le
                (Q).D (Q).eta (xi a) _ (Q).D_pos (Q).eta_pos (hb.trans_le (hxi a).1)
                (roundedReward_bounds rewards t hq a)
  · simp only [Pi.mul_apply, localizedAmplitude, Set.indicator_of_notMem hx, zero_mul, le_refl]

/-- Rounding keeps the conditional arrival below the localized unit bound. -/
theorem corrected_nextArrival_condExp_le_one (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    mu[(C).indicator (nextArrival rate rewards C_star C_h t hq a) |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu] (C).indicator (fun _ => (1 : ℝ)) := by
  refine (corrected_nextArrival_condExp_le_reward
    rate rewards C_star C_h u t control0 hq a).trans ?_
  filter_upwards [] with x
  by_cases hx : x ∈ C
  · simp only [Set.indicator_of_mem hx]
    exact (roundedReward_bounds rewards t hq a).2
  · simp only [Set.indicator_of_notMem hx, le_refl]

/-- The retained increment is zero off its literal prior gate. -/
theorem retainedIncrement_of_not_mem (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (hx : x ∉ G hq) :
    retainedIncrement rate rewards C_star C_h u t hq a x = 0 :=
  Set.indicator_of_notMem hx _

/-- Enabled zero arrivals still retain the four-unit service subtraction. -/
theorem retainedIncrement_of_zero_arrival (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (hx : x ∈ G hq)
    (ha : nextArrival rate rewards C_star C_h t hq a x = 0) :
    retainedIncrement rate rewards C_star C_h u t hq a x = -4 := by
  rw [retainedIncrement, Set.indicator_of_mem hx, ha, zero_sub]

/-- A disabled present successor contributes zero to the retained increment. -/
theorem retainedIncrement_of_disabled (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
      rate rewards C_star C_h t hq x = some (false, xi)) :
    retainedIncrement rate rewards C_star C_h u t hq a x = 0 := by
  apply retainedIncrement_of_not_mem
  rintro ⟨_hC, _hy, zeta, hz⟩
  rw [hp] at hz
  cases hz

/-- The retained increment has a uniform finite envelope from the actual
canonical successor rates; this includes the first outgoing overflow. -/
theorem retainedIncrement_bounds (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) :
    -4 ≤ retainedIncrement rate rewards C_star C_h u t hq a x ∧
      retainedIncrement rate rewards C_star C_h u t hq a x ≤ 1 / beta := by
  by_cases hx : x ∈ G hq
  · rw [retainedIncrement, Set.indicator_of_mem hx]
    have ha := nextArrival_bounds rate rewards C_star C_h u t hq a x hx.1
    constructor <;> linarith only [ha.1, ha.2]
  · rw [retainedIncrement_of_not_mem rate rewards C_star C_h u t hq a x hx]
    exact ⟨by norm_num, (one_div_pos.mpr
      (CanonicalRecordingRates.beta_pos p rate.eta.property)).le⟩

/-- The retained increment is Borel on the original source. -/
theorem retainedIncrement_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (retainedIncrement rate rewards C_star C_h u t hq a) := by
  have hm := ((corrected_nextArrival_measurable
    rate rewards C_star C_h u t control0 hq a).sub
      (measurable_const : Measurable (fun _ : X => (4 : ℝ)))).indicator
      (((sourcePrefixFiltration control0).le' (t.val + 2)) _
        (ReferenceFirstCollectionCorrectedNextRetainedGate.retainedGate_measurable
          rate rewards C_star C_h control0 u t hq))
  convert hm using 1
  funext x
  by_cases hx : x ∈ G hq
  · simp only [retainedIncrement, Set.indicator_of_mem hx, Pi.sub_apply,
      Set.indicator_of_mem hx.1]
  · rw [retainedIncrement, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- Integrability follows internally from the actual rate envelope. -/
theorem retainedIncrement_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (retainedIncrement rate rewards C_star C_h u t hq a) (sourceInputLaw p) := by
  have hm := retainedIncrement_measurable rate rewards C_star C_h u t control0 hq a
  apply (integrable_const (4 + 1 / beta)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  have hx := retainedIncrement_bounds rate rewards C_star C_h u t hq a x
  have hb : 0 ≤ 1 / beta := (one_div_pos.mpr
    (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
  constructor <;> linarith only [hx.1, hx.2, hb]

/-- The exponential is integrable before taking any conditional expectation;
no source/event mass or integrability premise is needed. -/
theorem exp_retainedIncrement_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t hq a x)) (sourceInputLaw p) := by
  have hm := ((measurable_const : Measurable (fun _ : X => beta)).mul (retainedIncrement_measurable
    rate rewards C_star C_h u t control0 hq a)).exp
  apply (integrable_const (Real.exp 1)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp_of_le
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  calc
    beta * retainedIncrement rate rewards C_star C_h u t hq a x ≤ beta * (1 / beta) :=
      mul_le_mul_of_nonneg_left
        (retainedIncrement_bounds rate rewards C_star C_h u t hq a x).2 hb.le
    _ = 1 := by field_simp [ne_of_gt hb]

/-- The actual arrival satisfies the unit-interval hypothesis of the
exponential chord on every corrected source point. -/
theorem beta_mul_nextArrival_bounds (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ C) :
    0 ≤ beta * nextArrival rate rewards C_star C_h t hq a x ∧
      beta * nextArrival rate rewards C_star C_h t hq a x ≤ 1 := by
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have ha := nextArrival_bounds rate rewards C_star C_h u t hq a x hx
  refine ⟨mul_nonneg hb.le ha.1, ?_⟩
  calc
    _ ≤ beta * (1 / beta) := mul_le_mul_of_nonneg_left ha.2 hb.le
    _ = 1 := by field_simp [ne_of_gt hb]

/-- The deterministic chord uses the actual retained arrival, including an
enabled zero arrival and the first update which detects an overflow. -/
theorem exp_retainedIncrement_le_chord (hq : t.val + 1 < p.T)
    (a : Fin p.K) (x : X) (hx : x ∈ G hq) :
    Real.exp (beta * retainedIncrement rate rewards C_star C_h u t hq a x) ≤
      Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) *
        (beta * nextArrival rate rewards C_star C_h t hq a x)) := by
  have ha := beta_mul_nextArrival_bounds rate rewards C_star C_h u t hq a x hx.1
  have hc := RecordedRoundMoments.exp_le_unit_chord ha.1 ha.2
  rw [retainedIncrement, Set.indicator_of_mem hx]
  have he : beta * (nextArrival rate rewards C_star C_h t hq a x - 4) =
      -4 * beta + beta * nextArrival rate rewards C_star C_h t hq a x := by ring
  rw [he, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)

private theorem condExp_affine {Ω : Type*} {m0 : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} {ν : @Measure Ω m0} [IsFiniteMeasure ν]
    (hm : m ≤ m0) {f : Ω → ℝ} (hf : Integrable f ν) (c d : ℝ) :
    ν[(fun x => c + d * f x) | m] =ᵐ[ν]
      (fun x => c + d * ν[f | m] x) := by
  have hadd := condExp_add (integrable_const c) (hf.const_mul d) m
  have hscale : ν[(fun x => d * f x) | m] =ᵐ[ν]
      (fun x => d * ν[f | m] x) := by
    have he : (fun x => d * f x) = d • f := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    have hs := condExp_smul (μ := ν) d f m
    rw [he]
    filter_upwards [hs] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul] using hx
  have hconst := condExp_const (μ := ν) (m := m) hm c
  filter_upwards [hadd, hscale] with x ha hs
  calc
    _ = ν[(fun _ => c) | m] x + ν[(fun x => d * f x) | m] x := ha
    _ = c + d * ν[f | m] x := by rw [hconst, hs]

/-- The retained exponential moment on the original source. The strict-prior
AFTER gate retains the first detecting successor update. -/
theorem condExp_exp_retainedIncrement_le_one (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    mu[(fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t hq a x)) |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu] (fun _ => (1 : ℝ)) := by
  let Fq := sourcePrefixFiltration control0 (t.val + 2)
  let A := (C).indicator (nextArrival rate rewards C_star C_h t hq a)
  let c := Real.exp (-4 * beta)
  let d := c * ((Real.exp 1 - 1) * beta)
  let f : X → ℝ := fun x => c + d * A x
  let B : X → ℝ := (G hq).indicator f + (G hq)ᶜ.indicator (fun _ => (1 : ℝ))
  have hle := (sourcePrefixFiltration control0).le' (t.val + 2)
  have hG : MeasurableSet[Fq] (G hq) :=
    ReferenceFirstCollectionCorrectedNextRetainedGate.retainedGate_measurable
      rate rewards C_star C_h control0 u t hq
  have hGa := hle _ hG
  have hA : Integrable A mu :=
    corrected_nextArrival_integrable rate rewards C_star C_h u t control0 hq a
  have hf : Integrable f mu := (integrable_const c).add (hA.const_mul d)
  have hB : Integrable B mu :=
    (hf.indicator hGa).add ((integrable_const (1 : ℝ)).indicator hGa.compl)
  have hpoint : (fun x => Real.exp (beta *
      retainedIncrement rate rewards C_star C_h u t hq a x)) ≤ B := by
    intro x
    by_cases hx : x ∈ G hq
    · have hc := exp_retainedIncrement_le_chord rate rewards C_star C_h u t hq a x hx
      have hnot : x ∉ (G hq)ᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
      simp only [B, Pi.add_apply, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hnot, add_zero, f, A, Set.indicator_of_mem hx.1]
      convert hc using 1
      dsimp only [c, d]
      ring
    · simp only [B, Pi.add_apply, Set.indicator_of_notMem hx,
        Set.indicator_of_mem (show x ∈ (G hq)ᶜ from hx), zero_add]
      rw [retainedIncrement_of_not_mem rate rewards C_star C_h u t hq a x hx,
        mul_zero, Real.exp_zero]
  have hmono := condExp_mono (m := Fq)
    (exp_retainedIncrement_integrable rate rewards C_star C_h u t control0 hq a)
    hB (Filter.Eventually.of_forall hpoint)
  have hadd := condExp_add (hf.indicator hGa)
    ((integrable_const (1 : ℝ)).indicator hGa.compl) Fq
  have hmask := condExp_indicator (μ := mu) hf hG
  have hcomp := condExp_indicator (μ := mu) (integrable_const (1 : ℝ)) hG.compl
  have haff := condExp_affine hle hA c d
  have hone := condExp_const (μ := mu) hle (1 : ℝ)
  have hmean := corrected_nextArrival_condExp_le_one
    rate rewards C_star C_h u t control0 hq a
  have hd : 0 ≤ d := mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (by linarith [Real.exp_one_gt_two])
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)
  have hscalar : c + d ≤ 1 := by
    have h := ReferenceFirstCollectionRenewalExponentialIncrement.exp_neg_four_beta_chord_le_one
      rate
    dsimp only [c, d]
    nlinarith only [h]
  filter_upwards [hmono, hadd, hmask, hcomp, haff, hmean] with x hm ha hg hc hf' hmean'
  change mu[(fun x => Real.exp (beta *
    retainedIncrement rate rewards C_star C_h u t hq a x)) | Fq] x ≤ 1
  apply hm.trans
  calc
    mu[B | Fq] x = mu[(G hq).indicator f | Fq] x +
        mu[(G hq)ᶜ.indicator (fun _ => (1 : ℝ)) | Fq] x := ha
    _ = (G hq).indicator (mu[f | Fq]) x +
        (G hq)ᶜ.indicator (fun _ => (1 : ℝ)) x := by
      have hg' : mu[(G hq).indicator f | Fq] x = (G hq).indicator (mu[f | Fq]) x := hg
      have hc' : mu[(G hq)ᶜ.indicator (fun _ => (1 : ℝ)) | Fq] x =
          (G hq)ᶜ.indicator (mu[(fun _ => (1 : ℝ)) | Fq]) x := hc
      rw [hg', hc', hone]
    _ ≤ 1 := by
      by_cases hx : x ∈ G hq
      · have hnot : x ∉ (G hq)ᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hnot, add_zero]
        change mu[(fun x => c + d * A x) | Fq] x ≤ 1
        rw [hf']
        have hm1 : mu[A | Fq] x ≤ 1 := by
          simpa only [Set.indicator_of_mem hx.1] using hmean'
        calc
          c + d * mu[A | Fq] x ≤ c + d * 1 :=
            add_le_add (le_refl c) (mul_le_mul_of_nonneg_left hm1 hd)
          _ = c + d := by ring
          _ ≤ 1 := hscalar
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hx, zero_add]

/-- Retained enabled service has conditional drift at most minus three.
The test uses only the inherited AFTER queue, including a first overflow update. -/
theorem retainedIncrement_condExp_le_neg_three (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    mu[retainedIncrement rate rewards C_star C_h u t hq a |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu]
      (G hq).indicator (fun _ => (-3 : ℝ)) := by
  let Fq := sourcePrefixFiltration control0 (t.val + 2)
  let A := (C).indicator (nextArrival rate rewards C_star C_h t hq a)
  have hG : MeasurableSet[Fq] (G hq) :=
    ReferenceFirstCollectionCorrectedNextRetainedGate.retainedGate_measurable
      rate rewards C_star C_h control0 u t hq
  have hA := corrected_nextArrival_integrable rate rewards C_star C_h u t control0 hq a
  have he : retainedIncrement rate rewards C_star C_h u t hq a =
      (G hq).indicator (fun x => A x - 4) := by
    funext x
    by_cases hx : x ∈ G hq
    · simp only [retainedIncrement, Set.indicator_of_mem hx, A, Set.indicator_of_mem hx.1]
    · simp only [retainedIncrement, Set.indicator_of_notMem hx]
  have hsame := condExp_congr_ae (μ := mu) (m := Fq)
    (Filter.Eventually.of_forall (fun x => congrFun he x))
  have hmask := condExp_indicator (μ := mu) (hA.sub (integrable_const (4 : ℝ))) hG
  have hsub := condExp_sub (μ := mu) hA (integrable_const (4 : ℝ)) Fq
  have hconst := condExp_const (μ := mu) ((sourcePrefixFiltration control0).le' (t.val + 2)) (4 : ℝ)
  have hmean := corrected_nextArrival_condExp_le_one
    rate rewards C_star C_h u t control0 hq a
  filter_upwards [hsame, hmask, hsub, hmean] with x hs hm hd hmean'
  calc
    _ = mu[(G hq).indicator (fun x => A x - 4) | Fq] x := hs
    _ = (G hq).indicator (mu[(fun x => A x - 4) | Fq]) x := hm
    _ ≤ (G hq).indicator (fun _ => (-3 : ℝ)) x := by
      by_cases hx : x ∈ G hq
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have hd' : mu[(fun x => A x - 4) | Fq] x =
            mu[A | Fq] x - mu[(fun _ => (4 : ℝ)) | Fq] x := hd
        rw [hd', hconst]
        have hm1 : mu[A | Fq] x ≤ 1 := by
          simpa only [Set.indicator_of_mem hx.1] using hmean'
        linarith only [hm1]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- On its literal gate the successor subtracts four, irrespective of its
outgoing overflow. In particular the first detecting update is retained. -/
theorem retainedIncrement_eq_on_gate (hq : t.val + 1 < p.T) (a : Fin p.K)
    (x : X) (hx : x ∈ G hq) :
    retainedIncrement rate rewards C_star C_h u t hq a x =
      nextArrival rate rewards C_star C_h t hq a x - 4 :=
  Set.indicator_of_mem hx _

/-- At the terminal date the optional successor increment is literally zero. -/
theorem terminal_successorIncrement_zero (a : Fin p.K) (x : X)
    (ht : t.val + 1 = p.T) :
    successorIncrement rate rewards C_star C_h u t a x = 0 := by
  simp only [successorIncrement, ht, lt_self_iff_false, dite_false]

/-- The optional physical successor retains the terminal date without
inventing a recording cell or marker there. -/
theorem terminal_successorCell_absent (x : X)
    (ht : t.val + 1 = p.T) :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.successorCell?
      rate rewards C_star C_h t x = none :=
  (ReferenceFirstCollectionCorrectedNextPhysicalReadout.terminal_successor_absent
    rate rewards C_star C_h t x ht).2

/-- The natural successor extension is integrable, including the terminal date. -/
theorem successorIncrement_integrable (control0 : TimeControl p) (a : Fin p.K) :
    Integrable (successorIncrement rate rewards C_star C_h u t a) mu := by
  change Integrable (fun x => successorIncrement rate rewards C_star C_h u t a x) mu
  by_cases hq : t.val + 1 < p.T
  · simpa only [successorIncrement, dite_eq_left hq] using
      retainedIncrement_integrable rate rewards C_star C_h u t control0 hq a
  · simp only [successorIncrement, dite_eq_right hq]
    exact integrable_zero _ _ _

/-- The terminal mean is literally zero; no `Fin T` successor is constructed. -/
theorem terminal_successorIncrement_condExp (control0 : TimeControl p) (a : Fin p.K)
    (ht : t.val + 1 = p.T) :
    mu[successorIncrement rate rewards C_star C_h u t a |
      sourcePrefixFiltration control0 (t.val + 2)] = (fun _ => (0 : ℝ)) := by
  have he : successorIncrement rate rewards C_star C_h u t a = (fun _ => (0 : ℝ)) :=
    funext (fun x => terminal_successorIncrement_zero rate rewards C_star C_h u t a x ht)
  rw [he]
  exact condExp_zero

/-- The conditional mean extension is nonpositive, with exact terminal zero. -/
theorem successorIncrement_condExp_le_zero (control0 : TimeControl p) (a : Fin p.K) :
    mu[successorIncrement rate rewards C_star C_h u t a |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu] (fun _ => (0 : ℝ)) := by
  by_cases hq : t.val + 1 < p.T
  · have he : successorIncrement rate rewards C_star C_h u t a =
        retainedIncrement rate rewards C_star C_h u t hq a := by
      funext x
      simp only [successorIncrement, dite_eq_left hq]
    rw [he]
    refine (retainedIncrement_condExp_le_neg_three
      rate rewards C_star C_h u t control0 hq a).trans ?_
    filter_upwards [] with x
    change (G hq).indicator (fun _ => (-3 : ℝ)) x ≤ 0
    by_cases hx : x ∈ G hq
    · rw [Set.indicator_of_mem hx]
      norm_num
    · rw [Set.indicator_of_notMem hx]
  · have he : successorIncrement rate rewards C_star C_h u t a = (fun _ => (0 : ℝ)) := by
      funext x
      simp only [successorIncrement, dite_eq_right hq]
    rw [he, condExp_const (μ := mu)
      ((sourcePrefixFiltration control0).le' (t.val + 2)) (0 : ℝ)]

/-- At the terminal date the exponential extension is literally one. -/
theorem terminal_exp_successorIncrement (a : Fin p.K) (x : X)
    (ht : t.val + 1 = p.T) :
    Real.exp (beta * successorIncrement rate rewards C_star C_h u t a x) = 1 := by
  rw [terminal_successorIncrement_zero rate rewards C_star C_h u t a x ht,
    mul_zero, Real.exp_zero]

/-- The natural terminal extension has the same exponential moment bound. -/
theorem condExp_exp_successorIncrement_le_one (control0 : TimeControl p) (a : Fin p.K) :
    mu[(fun x => Real.exp (beta * successorIncrement rate rewards C_star C_h u t a x)) |
      sourcePrefixFiltration control0 (t.val + 2)] ≤ᵐ[mu] (fun _ => (1 : ℝ)) := by
  by_cases hq : t.val + 1 < p.T
  · simpa only [successorIncrement, dite_eq_left hq] using
      condExp_exp_retainedIncrement_le_one rate rewards C_star C_h u t control0 hq a
  · simp only [successorIncrement, dite_eq_right hq, mul_zero, Real.exp_zero]
    rw [condExp_const (μ := mu) ((sourcePrefixFiltration control0).le' (t.val + 2)) (1 : ℝ)]

/-- Exponential integrability also extends literally by one at a terminal date. -/
theorem exp_successorIncrement_integrable (control0 : TimeControl p) (a : Fin p.K) :
    Integrable (fun x => Real.exp (beta *
      successorIncrement rate rewards C_star C_h u t a x)) mu := by
  by_cases hq : t.val + 1 < p.T
  · simpa only [successorIncrement, dite_eq_left hq] using
      exp_retainedIncrement_integrable rate rewards C_star C_h u t control0 hq a
  · simp only [successorIncrement, dite_eq_right hq, mul_zero, Real.exp_zero]
    exact integrable_const _

end Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedMoment

end
