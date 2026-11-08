/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSuffixInputMeasurability
public import Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability

/-!
# Numerical values on the actual later-live readout locus

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The subtype below has the induced space of the original natural-index/product
source. No measurability of its ambient domain is assumed or asserted here.
All selections and ordinary states are extracted from this same computed
readout. Continuous weights, buffers and controls keep their existing spaces.
These are internal value producers, without a physical law or regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.ContinuousControlSlice

namespace Bandits.Support.ReferenceLaterLiveReadoutValuesMeasurability

variable {p : ConstructorDimensions.Parameters}

private theorem measurable_of_code_fibers {Ω β γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    [Countable β] [MeasurableSingletonClass β]
    (code : Ω → β) (hc : Measurable code) (f : Ω → γ)
    (hf : ∀ b, Measurable (fun x : {x // code x = b} => f x.val)) :
    Measurable f := by
  intro s hs
  have heq : f ⁻¹' s = ⋃ b, Subtype.val ''
      ((fun x : {x // code x = b} => f x.val) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨code x, ⟨x, rfl⟩, hx, rfl⟩
    · rintro ⟨_, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun b =>
    MeasurableSet.subtype_image ((measurableSet_singleton b).preimage hc) (hf b hs)

private theorem measurable_of_some {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (f : Ω → α)
    (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hsum := (comap_measurable (Equiv.optionEquivSumPUnit α)).comp hf
  have hinl : MeasurableEmbedding (@Sum.inl α PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp hsum

private theorem measurable_option_fibers {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (f : Ω → Option α)
    (hf : ∀ a, MeasurableSet {x | f x = some a}) : Measurable f := by
  apply measurable_to_countable'
  intro target
  cases target with
  | some a => exact hf a
  | none =>
      have heq : {x | f x = none} = (⋃ a, {x | f x = some a})ᶜ := by
        ext x
        cases h : f x <;> simp [h]
      change MeasurableSet {x | f x = none}
      rw [heq]
      exact (MeasurableSet.iUnion hf).compl

/- The arithmetic helpers below are conditional only on explicitly displayed
measurable coordinates and the actual sampler's pointwise validity proofs.
The final source theorem supplies every such input internally. -/
private theorem measurable_qGamma_varying {Ω : Type*} [MeasurableSpace Ω]
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (v w : Ω → Fin p.K → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hpos : ∀ x j, 0 < v x j) (hwpos : ∀ x j, 0 < w x j)
    (hlow : ∀ x j, v x j ≤ w x j) (hhigh : ∀ x j, w x j ≤ 2 * v x j)
    (j : FastArm U) : Measurable (fun x =>
      qGamma p rate.eta.val rate.eta.property rate.sourceCap (v x) (w x)
        (hpos x) (hwpos x) (hlow x) (hhigh x) U j) := by
  classical
  have hc (a : Fin p.K) : Measurable (fun x =>
      FiniteOrientationDisintegration.candidateWeight (w x) (v x) U.val a) := by
    unfold FiniteOrientationDisintegration.candidateWeight
      FiniteOrientationDisintegration.inverseAnchorSum
    exact ((measurable_pi_apply a).comp hw).div (measurable_const.add
      ((Finset.measurable_fun_sum U.val fun i _ =>
        measurable_const.div ((measurable_pi_apply i).comp hv)).mul
          ((measurable_pi_apply a).comp hv)))
  have hn : Measurable (fun x =>
      FiniteOrientationDisintegration.candidateNormalizer Finset.univ (w x) (v x) U.val) :=
    Finset.measurable_fun_sum _ fun a _ => hc a.val
  exact (measurable_const.mul ((hc j.val).div hn)).add measurable_const

private theorem measurable_sampleFast_varying {Ω : Type*} [MeasurableSpace Ω]
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (v w : Ω → Fin p.K → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hpos : ∀ x j, 0 < v x j) (hwpos : ∀ x j, 0 < w x j)
    (hlow : ∀ x j, v x j ≤ w x j) (hhigh : ∀ x j, w x j ≤ 2 * v x j)
    (u : Ω → ContinuousCategorical.Scalar) (hu : Measurable u) :
    Measurable (fun x => sampleFast p rate.eta.val rate.eta.property rate.sourceCap
      (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) U (u x)) := by
  classical
  let masses (x : Ω) (k : Fin (p.K - p.m + 1)) :=
    qGamma p rate.eta.val rate.eta.property rate.sourceCap (v x) (w x)
      (hpos x) (hwpos x) (hlow x) (hhigh x) U (fastArmOrderIso U k)
  have hm (k : Fin (p.K - p.m + 1)) : Measurable (fun x => masses x k) :=
    measurable_qGamma_varying rate U v w hv hw hpos hwpos hlow hhigh _
  have hsum (x : Ω) : ∑ k, masses x k = 1 := by
    change (∑ k, qGamma p rate.eta.val rate.eta.property rate.sourceCap
      (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) U (fastArmOrderIso U k)) = 1
    calc
      _ = ∑ j : FastArm U, qGamma p rate.eta.val rate.eta.property rate.sourceCap
          (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) U j :=
        Equiv.sum_comp (fastArmOrderIso U).toEquiv _
      _ = 1 := qGamma_sum_eq_one p rate.eta.property rate.sourceCap _ _ _ _ _ _ U
  have hnonneg (x : Ω) (k : Fin (p.K - p.m + 1)) : 0 ≤ masses x k :=
    (qGamma_pos p rate.eta.property rate.sourceCap _ _ _ _ _ _ U _).le
  apply measurable_to_countable'
  intro j
  have heq : {x | sampleFast p rate.eta.val rate.eta.property rate.sourceCap
      (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) U (u x) = j} =
      {x | ContinuousCategorical.lower (masses x) ((fastArmOrderIso U).symm j) ≤ (u x).val ∧
        (u x).val < ContinuousCategorical.upper (masses x) ((fastArmOrderIso U).symm j)} := by
    ext x
    change fastArmOrderIso U (ContinuousCategorical.sample _ (masses x) (hsum x) (u x)) = j ↔ _
    rw [← OrderIso.eq_symm_apply]
    exact ContinuousCategorical.sample_eq_iff _ (hnonneg x) (hsum x) _ _
  change MeasurableSet {x | sampleFast p rate.eta.val rate.eta.property rate.sourceCap
    (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) U (u x) = j}
  rw [heq]
  exact (measurableSet_le (Finset.measurable_fun_sum _ fun k _ => hm k)
    (measurable_subtype_coe.comp hu)).inter
      (measurableSet_lt (measurable_subtype_coe.comp hu)
        (Finset.measurable_fun_sum _ fun k _ => hm k))

private theorem measurable_recordingMap_varying_weights {Ω : Type*} [MeasurableSpace Ω]
    (rate : ReferenceActivePhysicalStep.RateInput p) (regime : Regime p)
    (v w : Ω → Fin p.K → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hpos : ∀ x j, 0 < v x j) (hwpos : ∀ x j, 0 < w x j)
    (hlow : ∀ x j, v x j ≤ w x j) (hhigh : ∀ x j, w x j ≤ 2 * v x j)
    (hxi : ∀ j, Measurable (fun x => CanonicalRecordingRates.xi p rate.eta.val (v x) j))
    (slice : Ω → CanonicalRecordingSlice.Slice p.m p.K) (hslice : Measurable slice) :
    Measurable (fun x => recordingMap p regime true rate.eta.val rate.eta.property
      rate.sourceCap (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (slice x)) := by
  classical
  have haction (i : Fin p.m) : Measurable (fun x =>
      dataAction p regime rate.eta.val rate.eta.property rate.sourceCap
        (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (slice x) i) := by
    cases regime with
    | collection => exact (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) i).comp hslice
    | live a snapshot =>
        by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
        · by_cases hm : snapshot.missing = ∅
          · simp only [dataAction, dite_eq_left hi, dite_eq_left hm]
            exact measurable_subtype_coe.comp (measurable_sampleFast_varying rate
              (assignmentSlowSet p a) v w hv hw hpos hwpos hlow hhigh
              (fun x => coordinate Label.fast (slice x))
              ((measurable_coordinate Label.fast).comp hslice))
          · simpa only [Function.comp_def, dataAction, dite_eq_left hi, dite_eq_right hm] using
              (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) i).comp hslice
        · by_cases hstatus : snapshot.status (ActiveRoundActions.followerIndex p.two_le_m i hi) =
              .unoccupied
          · simpa only [Function.comp_def, dataAction, dite_eq_right hi, dite_eq_left hstatus] using
              (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) i).comp hslice
          · simp only [dataAction, dite_eq_right hi, dite_eq_right hstatus]
            exact measurable_const
  have hprob (i : Fin p.m) (j : Fin p.K) : Measurable (fun x =>
      actionProbability p regime rate.eta.val rate.eta.property rate.sourceCap
        (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) i j) := by
    cases regime with
    | collection => exact measurable_const
    | live a snapshot =>
        by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
        · by_cases hm : snapshot.missing ≠ ∅
          · simp only [actionProbability, dite_eq_left hi, dite_eq_left hm]
            exact measurable_const
          · by_cases hj : j ∈ fastArmFinset (assignmentSlowSet p a)
            · simp only [actionProbability, dite_eq_left hi, dite_eq_right hm, dite_eq_left hj]
              exact measurable_qGamma_varying rate _ v w hv hw hpos hwpos hlow hhigh _
            · simp only [actionProbability, dite_eq_left hi, dite_eq_right hm, dite_eq_right hj]
              exact measurable_const
        · by_cases hstatus : snapshot.status (ActiveRoundActions.followerIndex p.two_le_m i hi) =
              .unoccupied
          · simp only [actionProbability, dite_eq_right hi, dite_eq_left hstatus]
            exact measurable_const
          · by_cases hj : j = a.assigned (ActiveRoundActions.followerIndex p.two_le_m i hi)
            · simp only [actionProbability, dite_eq_right hi, dite_eq_right hstatus, dite_eq_left hj]
              exact measurable_const
            · simp only [actionProbability, dite_eq_right hi, dite_eq_right hstatus, dite_eq_right hj]
              exact measurable_const
  apply measurable_option_fibers
  intro j
  let i := ownerSource p regime j
  have heq : {x | recordingMap p regime true rate.eta.val rate.eta.property rate.sourceCap
      (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (slice x) = some j} =
      {x | PublicDiscreteDraws.slotDraw (slice x) = PublicDiscreteDraws.dataSlot ∧
        PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (slice x) = i ∧
        dataAction p regime rate.eta.val rate.eta.property rate.sourceCap
          (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (slice x) i = j ∧
        CanonicalRecordingSlice.recordingMask (K_pos p) i j (slice x) ∧
        (coordinate Label.thin (slice x)).val ≤
          thinningThreshold p regime rate.eta.val rate.eta.property rate.sourceCap
            (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) i j} := by
    ext x
    exact Set.ext_iff.mp (recordingMap_owner_event_eq p regime rate.eta.val
      rate.eta.property rate.sourceCap (v x) (w x) (hpos x) (hwpos x)
        (hlow x) (hhigh x) i j (owns_ownerSource p regime j)) (slice x)
  rw [heq]
  have hthin : Measurable (fun x => thinningThreshold p regime rate.eta.val rate.eta.property
      rate.sourceCap (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) i j) :=
    (hxi j).div (((measurable_const.mul measurable_const).mul (hprob i j)).mul measurable_const)
  exact (measurableSet_eq_fun (PublicDiscreteDraws.measurable_slotDraw.comp hslice)
    measurable_const).inter ((measurableSet_eq_fun
      ((PublicDiscreteDraws.measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp hslice)
      measurable_const).inter ((measurableSet_eq_fun (haction i) measurable_const).inter
        (((CanonicalRecordingSlice.measurableSet_recordingMask p.two_le_m (K_pos p) i j).preimage
          hslice).inter (measurableSet_le
            (measurable_subtype_coe.comp ((measurable_coordinate Label.thin).comp hslice)) hthin))))

-- This code contains only the finite assignment and snapshot fields.
-- Anchor/current weights and the slice remain varying real product coordinates.

private def regimeCode (r : Regime p) :
    Option ((Fin (p.m - 1) → Fin p.K) ×
      (Fin p.K × (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Fin 3)))) :=
  match r with
  | .collection => none
  | .live a snapshot => some (a.assigned, (a.auxiliary,
      (snapshot.missing, fun i => FollowerDownMeasurability.followerStatusCode (snapshot.status i))))

private theorem regimeCode_injective : Function.Injective (regimeCode (p := p)) := by
  intro r t h
  cases r with
  | collection => cases t <;> simp_all [regimeCode]
  | live a snapshot =>
      cases t with
      | collection => simp [regimeCode] at h
      | live b other =>
          rcases a with ⟨assigned, injective, auxiliary, outside⟩
          rcases b with ⟨assigned', injective', auxiliary', outside'⟩
          rcases snapshot with ⟨missing, status⟩
          rcases other with ⟨missing', status'⟩
          have hh := Option.some.inj h
          have ha := congrArg (fun c => c.1) hh
          have haux := congrArg (fun c => c.2.1) hh
          have hmissing := congrArg (fun c => c.2.2.1) hh
          have hs := congrArg (fun c => c.2.2.2) hh
          have heq : status = status' := by
            funext i
            have hc := congrArg FollowerDownMeasurability.followerStatusOfCode (congrFun hs i)
            simpa only [FollowerDownMeasurability.followerStatusOfCode_code] using hc
          cases ha
          cases haux
          cases hmissing
          cases heq
          rfl

private theorem measurable_recordingMap_varying {Ω : Type*} [MeasurableSpace Ω]
    (rate : ReferenceActivePhysicalStep.RateInput p) (regime : Ω → Regime p)
    (hr : Measurable (fun x => regimeCode (regime x)))
    (v w : Ω → Fin p.K → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hpos : ∀ x j, 0 < v x j) (hwpos : ∀ x j, 0 < w x j)
    (hlow : ∀ x j, v x j ≤ w x j) (hhigh : ∀ x j, w x j ≤ 2 * v x j)
    (hxi : ∀ j, Measurable (fun x => CanonicalRecordingRates.xi p rate.eta.val (v x) j))
    (slice : Ω → CanonicalRecordingSlice.Slice p.m p.K) (hslice : Measurable slice) :
    Measurable (fun x => recordingMap p (regime x) true rate.eta.val rate.eta.property
      rate.sourceCap (v x) (w x) (hpos x) (hwpos x) (hlow x) (hhigh x) (slice x)) := by
  classical
  apply measurable_of_code_fibers (fun x => regimeCode (regime x)) hr
  intro b
  by_cases hn : Nonempty {x : Ω // regimeCode (regime x) = b}
  · obtain ⟨x0⟩ := hn
    -- The representative fixes only this countable code. Injectivity identifies
    -- the entire regime; all continuous inputs still vary throughout the fiber.
    have heq (x : {x : Ω // regimeCode (regime x) = b}) : regime x.val = regime x0.val :=
      regimeCode_injective (x.property.trans x0.property.symm)
    have hm := measurable_recordingMap_varying_weights rate (regime x0.val)
      (fun x : {x : Ω // regimeCode (regime x) = b} => v x.val)
      (fun x => w x.val) (hv.comp measurable_subtype_coe) (hw.comp measurable_subtype_coe)
      (fun x => hpos x.val) (fun x => hwpos x.val) (fun x => hlow x.val) (fun x => hhigh x.val)
      (fun j => (hxi j).comp measurable_subtype_coe)
      (fun x => slice x.val) (hslice.comp measurable_subtype_coe)
    convert hm using 1
    funext x
    rw [heq x]
  · let : IsEmpty {x : Ω // regimeCode (regime x) = b} := not_nonempty_iff.mp hn
    exact measurable_of_empty _

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The actual existing complete-suffix record, without a padded index. -/
def actualRecord (k : ℕ) (x : ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate x.val rewards C_star C_h).get ⟨k, x.property⟩

/-- The genuine locus of the literal readout, with the induced product space.
The first natural coordinate is the older-start comparison argument. -/
abbrev ReadoutSource (k : ℕ) :=
  {z : ℕ × ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k //
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout z.1
      (actualRecord rate rewards C_star C_h k z.2)).isSome = true}

/-- Extract the value of this same readout at this same source. -/
def actualCell (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout z.val.1
    (actualRecord rate rewards C_star C_h k z.val.2)).get z.property

/-- Literal numerical coordinates, erasing only propositional certificates. -/
def numericalCoordinates (c : RecordedQueueRun.RoundInput p.K) :=
  (c.enabled, (c.recordedArm, (c.reward, c.rate)))

/-- Integer arrivals from exactly the same numerical cell and queue scale. -/
def arrivalCoordinates (c : RecordedQueueRun.RoundInput p.K) :=
  (c.enabled, fun a => RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)

variable {rate rewards C_star C_h}

theorem actual_selection_exists (k : ℕ)
    (z : ReadoutSource rate rewards C_star C_h k) :
    ((actualRecord rate rewards C_star C_h k z.val.2).output.preparation.coordinator.selection).isSome = true := by
  obtain ⟨selected, hs, _, _, _⟩ := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain _ _).mp z.property
  rw [hs]
  rfl

/-- The computed selection, extracted by `Option.get`, never chosen externally. -/
def actualSelection (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :=
  ((actualRecord rate rewards C_star C_h k z.val.2).output.preparation.coordinator.selection).get
    (actual_selection_exists k z)

theorem actualSelection_spec (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualRecord rate rewards C_star C_h k z.val.2).output.preparation.coordinator.selection =
      some (actualSelection k z) := (Option.some_get _).symm

/-- Ordinariness is produced by the literal readout's constructor test. -/
theorem actual_preparedOrdinary (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    ReferenceLaterLiveNumericalReadout.preparedOrdinary (actualRecord rate rewards C_star C_h k z.val.2) := by
  obtain ⟨_, _, _, _, ho⟩ := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain _ _).mp z.property
  exact ho

/-- Exact reconstruction using the same computed selection and actual prepared
states, retaining its payload, pending set, time, cutoff and complement weights. -/
theorem actualCell_eq_sourceCell (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    actualCell rate rewards C_star C_h k z =
      ReferenceFirstWindowNumericalStream.sourceCell
        (actualRecord rate rewards C_star C_h k z.val.2)
        (actualSelection k z).view.payload (actualSelection k z).view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates _ (actual_preparedOrdinary k z))
        (actualSelection k z).view.complementWeights (actualSelection k z).view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid (actualSelection k z)) := by
  obtain ⟨selected, ho, hs, _, _, hc⟩ := ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ _
    (actualCell rate rewards C_star C_h k z) (Option.some_get z.property).symm
  have heq : selected = actualSelection k z :=
    Option.some.inj (hs.symm.trans (actualSelection_spec k z))
  subst selected
  exact hc

/-- This exact readout is enabled, including when its arrival is zero. -/
theorem actualCell_enabled (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualCell rate rewards C_star C_h k z).enabled = true := by
  rw [actualCell_eq_sourceCell]
  rfl

private theorem measurable_input (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt rate rewards C_star C_h k z.val.2) :=
  (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt rate rewards C_star C_h k).comp
    (measurable_snd.comp measurable_subtype_coe)

private theorem measurable_selection (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      ReferenceLiveDispatchOutputMeasurability.encodeSelection (actualSelection k z)) := by
  apply measurable_of_some
  have hc : Measurable (fun z : ReadoutSource rate rewards C_star C_h k =>
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
        rate rewards C_star C_h k z.val.2) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
      rate rewards C_star C_h k).comp
        (measurable_snd.comp measurable_subtype_coe)
  have hm := measurable_fst.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hc)))
  convert hm using 1
  funext z
  have hfront := (ReferenceActiveHorizonMeasurability.roundRecordCode_front
    (actualRecord rate rewards C_star C_h k z.val.2)).1
  have hp : (actualRecord rate rewards C_star C_h k z.val.2).output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch (actualRecord rate rewards C_star C_h k z.val.2).input := by
    rw [(actualRecord rate rewards C_star C_h k z.val.2).output_eq]
    rfl
  rw [← hp, actualSelection_spec] at hfront
  exact hfront.symm

private theorem measurable_payload (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k => (actualSelection k z).view.payload) := by
  have hv : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
    (p := p) (rate := rate)) := comap_measurable _
  exact measurable_fst.comp (hv.comp (measurable_fst.comp (measurable_selection (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)))

/-- The marker is the literal whole-row source arm of this computed selection. -/
theorem actualCell_recordedArm (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualCell rate rewards C_star C_h k z).recordedArm =
      ReferenceFirstWindowNumericalStream.sourceArm
        (actualRecord rate rewards C_star C_h k z.val.2)
        (actualSelection k z).view.payload (actualSelection k z).view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates _ (actual_preparedOrdinary k z))
        (actualSelection k z).view.complementWeights (actualSelection k z).view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid (actualSelection k z)) := by
  rw [actualCell_eq_sourceCell]
  rfl

/-- The exact numerical reward vector of this actual input. -/
theorem actualCell_reward (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualCell rate rewards C_star C_h k z).reward = fun a =>
      (((ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
        rate rewards C_star C_h k z.val.2).rewards
          (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
            rate rewards C_star C_h k z.val.2).time a).val : ℝ) / (D p : ℝ) := by
  rw [actualCell_eq_sourceCell]
  rfl

/-- The actual input reads the whole original reward table at its actual time. -/
theorem actualCell_reward_eq_whole (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualCell rate rewards C_star C_h k z).reward = fun a =>
      ((rewards (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
        rate rewards C_star C_h k z.val.2).time a).val : ℝ) / (D p : ℝ) := by
  rw [actualCell_reward,
    (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
      rate rewards C_star C_h k z.val.2).2.2.1]

/-- The full rate vector belongs to this same computed selected payload. -/
theorem actualCell_rate (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :
    (actualCell rate rewards C_star C_h k z).rate = (actualSelection k z).view.payload.rate := by
  rw [actualCell_eq_sourceCell]
  rfl

/-- Current slice of the actual input, including all continuous coordinates. -/
def actualSlice (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :=
  let input := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
    rate rewards C_star C_h k z.val.2
  ContinuousLearningRows.sliceAt input.time input.row.2

theorem measurable_actualSlice (k : ℕ) :
    Measurable (actualSlice (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k) := by
  have heval : Measurable (fun q : Fin p.T × ContinuousLearningRows.LearningRow p =>
      ContinuousLearningRows.sliceAt q.1 q.2) :=
    measurable_from_prod_countable_right fun t => ContinuousLearningRows.measurable_sliceAt t
  exact heval.comp
    (((ReferenceActivePhysicalStepMeasurability.measurable_time).comp (measurable_input (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)).prodMk
      (measurable_snd.comp ((ReferenceActivePhysicalStepMeasurability.measurable_row).comp
        (measurable_input (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k))))

private theorem measurable_view (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      ReferenceDownReceptionMeasurability.choiceTimeViewObservation (actualSelection k z).view) :=
  (comap_measurable _).comp (measurable_fst.comp (measurable_selection (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k))

private theorem measurable_slowSet (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualSelection k z).view.payload.slowSet) := by
  have hp := (comap_measurable (LaterAssignmentStartMeasurability.payloadObservation
    (p := p) (eta := rate.eta))).comp (measurable_payload (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hp))).subtype_mk

/-- The current whole-arm weights extend the actual complement by the actual
selected anchor, exactly as in `sourceArm`. -/
def actualWeights (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) :=
  ReferenceFirstWindowNumericalStream.sourceWeights (actualSelection k z).view.payload
    (actualSelection k z).view.complementWeights

theorem measurable_actualWeights (k : ℕ) :
    Measurable (actualWeights (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k) := by
  classical
  have ha := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_payload (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have hw := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_view (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)))
  have hs := measurable_subtype_coe.comp (measurable_slowSet (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  apply measurable_pi_iff.mpr
  intro arm
  have heq : (fun z : ReadoutSource rate rewards C_star C_h k => actualWeights k z arm) =
      fun z => if arm ∈ (actualSelection k z).view.payload.slowSet.val then
        (actualSelection k z).view.payload.anchor arm else
        ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
          (actualSelection k z).view arm := by
    funext z
    dsimp only [actualWeights, ReferenceFirstWindowNumericalStream.sourceWeights]
    by_cases h : arm ∈ (actualSelection k z).view.payload.slowSet.val
    · simp only [h, dite_eq_left, ite_true]
    · have hf : arm ∈ fastArmFinset (actualSelection k z).view.payload.slowSet :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
      simp only [h, dite_false, ite_false,
        ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector, hf, dite_eq_left]
  rw [heq]
  exact ((measurable_pi_apply arm).comp ha).ite
    ((measurableSet_mem_finset arm).preimage hs) ((measurable_pi_apply arm).comp hw)

/-- Code of each actual prepared status. Continuous PREPARE buffers are
retained by the generic incoming helper and erased only by this projection. -/
def actualPreparedStatusCode (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k)
    (i : Fin (p.m - 1)) : Fin 3 :=
  FollowerDownMeasurability.followerStatusCode
    ((ReferenceLaterLiveNumericalReadout.preparedStates
      (actualRecord rate rewards C_star C_h k z.val.2) (actual_preparedOrdinary k z) i).status)

private theorem preparedIncoming_eq (k : ℕ)
    (z : ReadoutSource rate rewards C_star C_h k) (i : Fin (p.m - 1)) :
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput i
        (fun z : ReadoutSource rate rewards C_star C_h k =>
          ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
            rate rewards C_star C_h k z.val.2) z) =
      ((actualRecord rate rewards C_star C_h k z.val.2).output.preparation.followers.followers i).configuration := by
  have h := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct
      (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
        rate rewards C_star C_h k z.val.2) i)
  have hp : (actualRecord rate rewards C_star C_h k z.val.2).output.preparation =
      ReferenceActivePhysicalStep.prepare (actualRecord rate rewards C_star C_h k z.val.2).input := by
    rw [(actualRecord rate rewards C_star C_h k z.val.2).output_eq]
    rfl
  rw [hp]
  exact h

theorem measurable_actualPreparedStatusCode (k : ℕ) :
    Measurable (actualPreparedStatusCode (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  let input := fun z : ReadoutSource rate rewards C_star C_h k =>
    ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt rate rewards C_star C_h k z.val.2
  let incoming := ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput i input
  let tag : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate → Option (Fin 3)
    | .dagger => none
    | .ordinary index => some (FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode index.1.status))
  have hm : Measurable (fun z => tag
      (ReferenceUpReceptionMeasurability.incomingOfferIndex (incoming z))) :=
    (measurable_of_countable tag).comp
      ((ReferenceUpReceptionMeasurability.measurable_incomingOfferIndex rate).comp
        (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_preparedIncomingForInput
          i input (measurable_input (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k)))
  have heq (z : ReadoutSource rate rewards C_star C_h k) :
      tag (ReferenceUpReceptionMeasurability.incomingOfferIndex (incoming z)) =
        some (actualPreparedStatusCode k z i) := by
    have hc := (preparedIncoming_eq k z i).trans
      (ReferenceLaterLiveNumericalReadout.prepared_configuration
        (actualRecord rate rewards C_star C_h k z.val.2) (actual_preparedOrdinary k z) i)
    have htag (a : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
        tag (ReferenceUpReceptionMeasurability.incomingOfferIndex a) =
          match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate a with
          | .dagger => none
          | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status) := by
      cases a <;> rfl
    rw [htag]
    change (match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
        (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput i input z) with
      | .dagger => none
      | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status)) = _
    rw [hc]
    rfl
  apply measurable_to_countable'
  intro c
  have hf : {z : ReadoutSource rate rewards C_star C_h k | actualPreparedStatusCode k z i = c} =
      {z | tag (ReferenceUpReceptionMeasurability.incomingOfferIndex (incoming z)) = some c} := by
    ext z
    change actualPreparedStatusCode k z i = c ↔
      tag (ReferenceUpReceptionMeasurability.incomingOfferIndex (incoming z)) = some c
    rw [heq]
    simp only [Option.some.injEq]
  change MeasurableSet {z | actualPreparedStatusCode k z i = c}
  rw [hf]
  exact (measurableSet_singleton (some c)).preimage hm

private def actualRegime (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k) : Regime p :=
  .live (actualSelection k z).view.payload.assignment
    { missing := (actualSelection k z).view.pendingAtChoice
      status := fun i => (ReferenceLaterLiveNumericalReadout.preparedStates
        (actualRecord rate rewards C_star C_h k z.val.2) (actual_preparedOrdinary k z) i).status }

private theorem measurable_actualRegimeCode (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k => regimeCode (actualRegime k z)) := by
  have hassigned := (measurable_of_countable (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
    fun i => CanonicalAssignmentVector.followerArm p.two_le_m U i)).comp (measurable_slowSet (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  have haux := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    (measurable_payload (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have hpending := measurable_fst.comp (measurable_snd.comp (measurable_view (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k))
  have hc := hassigned.prodMk (haux.prodMk (hpending.prodMk (measurable_actualPreparedStatusCode (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)))
  have hsome : Measurable (some :
      ((Fin (p.m - 1) → Fin p.K) ×
        (Fin p.K × (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Fin 3)))) → Option _) :=
    measurable_of_countable _
  exact hsome.comp hc

/-- Joint Borelness of the actual later-live arm marker, with all continuous
parameters and all countable prepared statuses varying on the original source. -/
theorem measurable_actualCell_recordedArm (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualCell rate rewards C_star C_h k z).recordedArm) := by
  let payload := fun z : ReadoutSource rate rewards C_star C_h k => (actualSelection k z).view.payload
  let weights := actualWeights (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k
  have ha : Measurable (fun z => (payload z).anchor) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp (measurable_payload (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  have hr : Measurable (fun z => (payload z).rate) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp (measurable_payload (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  have hvalid (z : ReadoutSource rate rewards C_star C_h k) :=
    ReferenceLaterLiveNumericalReadout.selection_choiceValid (actualSelection k z)
  have hxi (arm : Fin p.K) : Measurable (fun z =>
      CanonicalRecordingRates.xi p rate.eta.val (payload z).anchor arm) := by
    have heq : (fun z => CanonicalRecordingRates.xi p rate.eta.val (payload z).anchor arm) =
        fun z => (payload z).rate arm := funext fun z => ((payload z).rate_eq_canonical arm).symm
    rw [heq]
    exact (measurable_pi_apply arm).comp hr
  have hm := measurable_recordingMap_varying rate (actualRegime k) (measurable_actualRegimeCode (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
    (fun z => (payload z).anchor) weights ha (measurable_actualWeights (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
    (fun z => (payload z).anchor_pos)
    (fun z => ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ (hvalid z))
    (fun z => ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ (hvalid z))
    (fun z => ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ (hvalid z))
    hxi (fun z => actualSlice k z) (measurable_actualSlice (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  convert hm using 1
  funext z
  rw [actualCell_eq_sourceCell]
  rfl

/-- The whole numerical reward vector is jointly Borel. -/
theorem measurable_actualCell_reward (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualCell rate rewards C_star C_h k z).reward) := by
  have ht := ReferenceActivePhysicalStepMeasurability.measurable_time.comp
    (measurable_input (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have hr := ReferenceActivePhysicalStepMeasurability.measurable_rewards.comp
    (measurable_input (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have heval : Measurable (fun q : ActualInitializationPhysicalStep.GridRewardTable p × Fin p.T =>
      fun a => ((q.1 q.2 a).val : ℝ) / (D p : ℝ)) := measurable_of_countable _
  have hm := heval.comp (hr.prodMk ht)
  convert hm using 1
  funext z
  exact actualCell_reward k z

/-- The whole rate vector of the same selected payload is jointly Borel. -/
theorem measurable_actualCell_rate (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualCell rate rewards C_star C_h k z).rate) := by
  have hm := AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp
    (measurable_payload (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  convert hm using 1
  funext z
  exact actualCell_rate k z

/-- Enabled is a literal constant on the readout locus, with no positivity
condition on any coordinate of its reward or arrival vector. -/
theorem measurable_actualCell_enabled (k : ℕ) : Measurable
    (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualCell rate rewards C_star C_h k z).enabled) := by
  have heq : (fun z : ReadoutSource rate rewards C_star C_h k =>
      (actualCell rate rewards C_star C_h k z).enabled) = fun _ => true :=
    funext (actualCell_enabled k)
  rw [heq]
  exact measurable_const

/-- Numerical values on the genuine locus, jointly in the older-start argument
and the whole original public/private source. No ambient Option claim. -/
theorem measurable_numericalCoordinates_actualCell (k : ℕ) : Measurable
    (numericalCoordinates ∘ actualCell rate rewards C_star C_h k) :=
  (measurable_actualCell_enabled (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k).prodMk ((measurable_actualCell_recordedArm (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k).prodMk
    ((measurable_actualCell_reward (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k).prodMk (measurable_actualCell_rate (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)))

/-- The integer arrival uses the same integer `rate.n`, reward, rate and marker. -/
theorem actualCell_quantizedArrival (k : ℕ) (z : ReadoutSource rate rewards C_star C_h k)
    (arm : Fin p.K) :
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (actualCell rate rewards C_star C_h k z) arm =
      if (actualCell rate rewards C_star C_h k z).recordedArm = some arm then
        Nat.floor ((rate.n : ℝ) * (actualCell rate rewards C_star C_h k z).reward arm /
          (actualCell rate rewards C_star C_h k z).rate arm) else 0 := by
  rfl

/-- Integer-arrival values on exactly the same readout locus, including enabled
zero arrivals and every nonmarker arm. -/
theorem measurable_arrivalCoordinates_actualCell (k : ℕ) : Measurable
    (arrivalCoordinates rate ∘ actualCell rate rewards C_star C_h k) := by
  classical
  apply (measurable_actualCell_enabled (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k).prodMk
  apply measurable_pi_iff.mpr
  intro arm
  have hbranch : MeasurableSet {z : ReadoutSource rate rewards C_star C_h k |
      (actualCell rate rewards C_star C_h k z).recordedArm = some arm} :=
    (measurableSet_singleton (some arm)).preimage (measurable_actualCell_recordedArm (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) k)
  have hr := (measurable_pi_apply arm).comp (measurable_actualCell_reward (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have hrate := (measurable_pi_apply arm).comp (measurable_actualCell_rate (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) k)
  have hfloor : Measurable (fun z : ReadoutSource rate rewards C_star C_h k =>
      Nat.floor ((rate.n : ℝ) * (actualCell rate rewards C_star C_h k z).reward arm /
        (actualCell rate rewards C_star C_h k z).rate arm)) :=
    Nat.measurable_floor.comp (((measurable_const (a := (rate.n : ℝ))).mul hr).div hrate)
  have hm : Measurable (fun z : ReadoutSource rate rewards C_star C_h k =>
      if (actualCell rate rewards C_star C_h k z).recordedArm = some arm then
        Nat.floor ((rate.n : ℝ) * (actualCell rate rewards C_star C_h k z).reward arm /
          (actualCell rate rewards C_star C_h k z).rate arm) else 0) :=
    Measurable.ite hbranch hfloor measurable_const
  convert hm using 1
  funext z
  exact actualCell_quantizedArrival k z arm

end Bandits.Support.ReferenceLaterLiveReadoutValuesMeasurability
