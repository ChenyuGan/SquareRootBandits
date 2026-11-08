/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveRetainedConditionalMoments
public import Bandits.Support.ReferenceFirstLiveSourceCellReadout

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Common-source all-arm strict-past adaptation

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module restricts the original-source prefix, all-arm rate coefficients,
and strict-past numerical readouts to the already existing continuing-source
subtype. Its measures, payload, rows, selected index, and private coordinates
are inherited unchanged. The overflow test uses the first `t.val - s` cells of
the actual `t.val - s + 1` cell list, so it retains the current update even
when that update is the first overflow. No manuscript-history identification,
future-coordinate adaptation, recording law, or regret conclusion is asserted.
-/

public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
  (rate : RateInput p)
  (rewards : RewardTable p)
  (C_star C_h : ℝ)
  (q : Fin (ConstructorDimensions.M p))
  (t : Fin p.T)
  (s : ℕ)
  (hs : s ≤ t.val)
  (control0 : TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t s hs control0
local notation "Xplus" => ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs control0
local notation "μplus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t s hs control0
local notation "νplus" => ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s

/-! ## The literal restricted field and its prefix -/

/-- The current-control-erased source prefix, restricted to the existing
continuing original-source subtype. -/
@[instance_reducible, expose] def sourcePlusPrefixField : MeasurableSpace Zplus :=
  (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)).comap
    (fun z : Zplus => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)

/-- The restricted field is included in the inherited Borel space. -/
theorem sourcePlusPrefixField_le :
    sourcePlusPrefixField rate rewards C_star C_h q t s hs control0 ≤ (inferInstance : MeasurableSpace Zplus) := by
  exact ((ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comp
    (measurable_subtype_coe.comp measurable_subtype_coe)).comap_le

/-- The inherited continuing-source measure is finite, including when it is
the zero measure. -/
theorem isFiniteMeasure_branchSourceMeasure : IsFiniteMeasure μplus := by
  infer_instance

/-- Finite trimming by the literal restricted prefix field uses the original
inherited branch measure. -/
theorem sourcePlusPrefixField_trim_finite :
    IsFiniteMeasure ((μplus).trim (sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0)) := by
  infer_instance

local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0
local notation "pre" => ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ rate rewards C_star C_h q t s hs control0

/-- Prefix the original source through B's source-prefix map and transport its
actual continuing-branch proof by B's constructor-derived equivalence. -/
@[expose] def prefixPlus (z : Zplus) : Zplus :=
  ⟨pre z.val, (ReferenceFirstLiveSourcePrefixBranchInvariance.continuingRecordingBranch_prefix_iff rate rewards C_star C_h q t s hs control0 z.val).mpr z.property⟩

@[simp] theorem prefixPlus_val (z : Zplus) :
    (prefixPlus rate rewards C_star C_h q t s hs control0 z).val = pre z.val := rfl

/-- The underlying original source is exactly B's literal source prefix. -/
theorem prefixPlus_source (z : Zplus) :
    (prefixPlus rate rewards C_star C_h q t s hs control0 z).val.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val := by
  exact ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val rate rewards C_star C_h q t s hs control0 z.val

/-- The actual source-prefix map is idempotent on the continuing subtype. -/
theorem prefixPlus_idempotent (z : Zplus) :
    prefixPlus rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z) = prefixPlus rate rewards C_star C_h q t s hs control0 z := by
  apply Subtype.ext
  exact ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_idempotent rate rewards C_star C_h q t s hs control0 z.val

local notation "Fplus" => sourcePlusPrefixField rate rewards C_star C_h q t s hs control0

/-- The source-subtype projection is measurable into A's same original
current-control comap. -/
theorem measurable_sourcePlus_val :
    Measurable[Fplus,
      (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)).comap
        (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)]
      (fun z : Zplus => z.val) := by
  rw [measurable_comap_iff]
  change Measurable[Fplus] (fun z : Zplus => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
  exact comap_measurable _

/-- Prefixing factors through precisely the field just defined. -/
theorem measurable_prefixPlus : Measurable[Fplus] (prefixPlus rate rewards C_star C_h q t s hs control0) := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  change Measurable[Fplus]
    (fun z : Zplus => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val)
  have heq :
      (fun z : Zplus => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val) =
        fun z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val := by
    funext z
    exact (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix
      control0 t z.val.val).symm
  rw [heq]
  exact comap_measurable _

/-- On the first-round branch, the existing continuing schema has no points.
This uses the real Bplus event and does not assume branch positivity. -/
theorem sourcePlus_empty_of_s_eq_t (hfirst : s = t.val) : IsEmpty Zplus := by
  have hempty := ReferenceFirstLiveRecordingBranchMeasurability.continuingRecordingBranch_eq_empty_of_offset_eq_zero
    rate rewards C_star C_h q t s hs control0 (by omega)
  let : IsEmpty Xplus := ⟨fun x => by
    have hx : x.val ∈ {y : ReferenceFirstLiveRecordingReadoutMeasurability.SourceX rate rewards C_star C_h q t s hs control0 |
        ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t s hs control0 y} := x.property
    rw [hempty] at hx
    exact hx⟩
  exact ⟨fun z => isEmptyElim (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1⟩

/-- Both inherited branch measures vanish on that genuinely empty first-round
domain. -/
theorem branch_measures_zero_of_s_eq_t (hfirst : s = t.val) :
    μplus = 0 ∧ νplus = 0 := by
  have h := ReferenceFirstLiveRecordingSourceCylinder.branch_measures_eq_zero_of_s_eq_t
    rate rewards C_star C_h q t s hs control0 hfirst
  exact ⟨h.2, h.1⟩

/-! ## The actual selected payload code and all-arm coefficients -/

/-- The exact existing remainder projection of the original branch split. -/
@[expose] def sourcePlusRemainder (z : Zplus) : Xplus :=
  (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1

theorem measurable_sourcePlusRemainder : Measurable (sourcePlusRemainder rate rewards C_star C_h q t s hs control0) :=
  measurable_fst.comp (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)

/-- The unchanged payload selected by the actual current PREPARE code. -/
@[expose] def sourcePlusPayload (z : Zplus) : ReferenceActivePhysicalStep.Payload rate :=
  ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z)

/-- The faithful option-valued payload projection from the existing canonical
whole-step selection code. -/
@[expose] def sourcePlusPayloadCode (z : Zplus) :
    Option (ReferenceActivePhysicalStep.Payload rate) :=
  ReferenceFirstLiveRecordingReadoutMeasurability.sourceSelectionPayloadOption (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).val

/-- On the actual continuing constructor, the canonical code contains exactly
the selected baseline payload. -/
theorem sourcePlusPayloadCode_eq_some (z : Zplus) :
    sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 z = some (sourcePlusPayload rate rewards C_star C_h q t s hs control0 z) := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hcode⟩ :=
    ReferenceFirstLiveRecordingReadoutMeasurability.sourceSelectionPayloadOption_eq_some_actual
      (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).val (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).property
  have hpayload := ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_of_continuing
    (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z) r owned base d hsStart c arm hcoord
  change ReferenceFirstLiveRecordingReadoutMeasurability.sourceSelectionPayloadOption (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).val =
    some (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z))
  rw [hcode, hpayload]

/-- Prefixing preserves the complete selected payload. B's continuing-branch
equivalence uses its actual prepared-start identity; the full payload equality
then follows from the actual continuing constructor and incoming registers. -/
theorem sourcePlusPayload_prefix (z : Zplus) :
    sourcePlusPayload rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z) = sourcePlusPayload rate rewards C_star C_h q t s hs control0 z := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpayload⟩ :=
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_actual (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z))
  obtain ⟨r', owned', base', d', hsStart', c', arm', hcoord', hpayload'⟩ :=
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_actual (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z)
  have hleft := ReferenceFirstLiveSourcePrefixBranchInvariance.incoming_payload_of_continuing rate
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z)).val)
    r owned base d hsStart c arm hcoord
  have hright := ReferenceFirstLiveSourcePrefixBranchInvariance.incoming_payload_of_continuing rate
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).val)
    r' owned' base' d' hsStart' c' arm' hcoord'
  change (match (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput rate rewards C_star C_h q t s hs control0
      (ret (pre z.val))).state.coordinator with
    | .live registers _ _ => some registers.payload
    | _ => none) = some r.payload at hleft
  change (match (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput rate rewards C_star C_h q t s hs control0
      (ret z.val)).state.coordinator with
    | .live registers _ _ => some registers.payload
    | _ => none) = some r'.payload at hright
  rw [ReferenceFirstLiveSourcePrefixBranchInvariance.source_prefix_incoming rate rewards C_star C_h q t s hs control0 z.val] at hright
  have hpayloadEq : r.payload = r'.payload := Option.some.inj (hleft.symm.trans hright)
  change ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z)) =
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z)
  exact hpayload.trans (hpayloadEq.trans hpayload'.symm)

/-- The canonical payload code is invariant under the produced prefix. -/
theorem sourcePlusPayloadCode_prefix (z : Zplus) :
    sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z) = sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 z := by
  rw [sourcePlusPayloadCode_eq_some, sourcePlusPayloadCode_eq_some,
    sourcePlusPayload_prefix]

/-- The existing faithful payload code is measurable on Fplus. -/
theorem measurable_sourcePlusPayloadCode : Measurable[Fplus] (sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0) := by
  have hsource : Measurable (fun z : Zplus => (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z).val) :=
    measurable_subtype_coe.comp (measurable_sourcePlusRemainder rate rewards C_star C_h q t s hs control0)
  have hcode : Measurable (sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0) :=
    (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_sourceSelectionPayloadOption
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)).comp hsource
  have hprefix : Measurable[Fplus]
      (fun z : Zplus => sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z)) :=
    hcode.comp (measurable_prefixPlus rate rewards C_star C_h q t s hs control0)
  have hinv : (fun z : Zplus => sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z)) =
      sourcePlusPayloadCode rate rewards C_star C_h q t s hs control0 := funext (sourcePlusPayloadCode_prefix rate rewards C_star C_h q t s hs control0)
  rw [hinv] at hprefix
  exact hprefix

/-- The literal canonical marker rate for arm `j`, evaluated on the same
selected payload and the inherited branch remainder. -/
@[expose] def markerRatePlus (j : Fin p.K) (z : Zplus) : ℝ :=
  ReferenceFirstLiveRecordingSourceCylinder.markerRate rate rewards C_star C_h q t s hs control0 (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z) j

/-- The unchanged rounded reward ratio for arm `j`. -/
@[expose] def roundedRewardPlus (j : Fin p.K) : ℝ :=
  ((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ)

/-- The source's literal Nat.floor coefficient, using the actual integer
scale `rate.n` and the same marker rate and reward. -/
@[expose] noncomputable def quantizedValuePlus (j : Fin p.K) (z : Zplus) : ℝ :=
  (Nat.floor ((rate.n : ℝ) * roundedRewardPlus rewards t j /
    markerRatePlus rate rewards C_star C_h q t s hs control0 j z) : ℝ) /
      (rate.eta.val * (ConstructorDimensions.D p : ℝ))

@[expose] def firstCoefficientPlus (j : Fin p.K) (z : Zplus) : ℝ :=
  markerRatePlus rate rewards C_star C_h q t s hs control0 j z * quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z

@[expose] def secondCoefficientPlus (j : Fin p.K) (z : Zplus) : ℝ :=
  markerRatePlus rate rewards C_star C_h q t s hs control0 j z * (quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z) ^ 2

@[expose] def rhoSquaredDivRatePlus (j : Fin p.K) (z : Zplus) : ℝ :=
  (roundedRewardPlus rewards t j) ^ 2 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z

local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate

/-- Every actual arm rate has the canonical positive lower bound and its
source-derived finite upper bound. -/
theorem markerRatePlus_bounds (j : Fin p.K) (z : Zplus) :
    0 < beta ∧ beta ≤ markerRatePlus rate rewards C_star C_h q t s hs control0 j z ∧ markerRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 := by
  let payload := sourcePlusPayload rate rewards C_star C_h q t s hs control0 z
  have heta := rate.eta.property
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p heta
  have hbetaxi : CanonicalRecordingRates.beta p rate.eta.val ≤
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor j :=
    CanonicalRecordingRates.beta_le_xi p heta payload.anchor j
  have hxiUpper := CanonicalRecordingRates.xi_le_one_div_16mK p heta rate.sourceCap
    payload.anchor payload.anchor_pos j
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hKnat : 1 ≤ p.K :=
    Nat.le_trans (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
      (Nat.le_of_lt p.m_lt_K)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
  have hmk : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (p.m : ℝ) * (p.K : ℝ) :=
        mul_le_mul hm hK (by norm_num) (by positivity)
  have hden : (1 : ℝ) ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith [hmk]
  have hdenPos : 0 < 16 * (p.m : ℝ) * (p.K : ℝ) := by positivity
  have hsmall : 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 :=
    (div_le_one hdenPos).2 hden
  have hxiOne : CanonicalRecordingRates.xi p rate.eta.val payload.anchor j ≤ 1 :=
    hxiUpper.trans hsmall
  change 0 < CanonicalRecordingRates.beta p rate.eta.val ∧
    CanonicalRecordingRates.beta p rate.eta.val ≤
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor j ∧
    CanonicalRecordingRates.xi p rate.eta.val payload.anchor j ≤ 1
  exact ⟨hbeta, hbetaxi, hxiOne⟩

/-- The rounded reward ratio lies in the source interval, including at zero. -/
theorem roundedRewardPlus_bounds (j : Fin p.K) :
    0 ≤ roundedRewardPlus rewards t j ∧
      roundedRewardPlus rewards t j ≤ 1 := by
  have hD : 0 < (ConstructorDimensions.D p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hrewardNat : (rewards t j).val ≤ ConstructorDimensions.D p :=
    Nat.le_of_lt_succ (rewards t j).isLt
  have hreward : ((rewards t j).val : ℝ) ≤ (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast hrewardNat
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hD.le
  · calc
      roundedRewardPlus rewards t j =
          ((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ) := rfl
      _ ≤ (ConstructorDimensions.D p : ℝ) / (ConstructorDimensions.D p : ℝ) :=
        div_le_div_of_nonneg_right hreward hD.le
      _ = 1 := by field_simp [ne_of_gt hD]

/-- The literal coefficient is the existing quantized-value formula after
using the exact `n = eta * D` source witness. -/
theorem quantizedValuePlus_eq_quantizedValue (j : Fin p.K) (z : Zplus) :
    quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z =
      QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
        rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
        (roundedRewardPlus rewards t j) := by
  have harg :
      (rate.n : ℝ) * roundedRewardPlus rewards t j /
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z =
      ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        roundedRewardPlus rewards t j) /
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z := by
    rw [rate.n_scale]
    ring
  unfold quantizedValuePlus QuantizedRecordingMoments.quantizedValue
    QuantizedRecordingMoments.quantizedIndex
  rw [harg]

/-- The literal coefficient and its first-moment envelope. -/
theorem quantizedValuePlus_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z ∧
      quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / beta := by
  have hrate := markerRatePlus_bounds rate rewards C_star C_h q t s hs control0 j z
  have hrho := roundedRewardPlus_bounds rewards t j
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hvalue := quantizedValuePlus_eq_quantizedValue rate rewards C_star C_h q t s hs control0 j z
  constructor
  · rw [hvalue]
    exact QuantizedRecordingMoments.quantizedValue_nonneg
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) rate.eta.property
  · rw [hvalue]
    exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) beta
      (ConstructorDimensions.D_pos p) rate.eta.property (hrate.1.trans_le hrate.2.1)
      ⟨hrho.1, hrho.2⟩ hbeta hrate.2.1

/-- The first coefficient obeys the exact quantization error and reward
ceiling on every original-source branch point. -/
theorem firstCoefficientPlus_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j z ∧
      roundedRewardPlus rewards t j -
          markerRatePlus rate rewards C_star C_h q t s hs control0 j z /
            (rate.eta.val * (ConstructorDimensions.D p : ℝ)) ≤
        firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j z ∧
      firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j z ≤ roundedRewardPlus rewards t j ∧
      roundedRewardPlus rewards t j ≤ 1 := by
  have hrate := markerRatePlus_bounds rate rewards C_star C_h q t s hs control0 j z
  have hrho := roundedRewardPlus_bounds rewards t j
  have hvalue := quantizedValuePlus_eq_quantizedValue rate rewards C_star C_h q t s hs control0 j z
  have hD := ConstructorDimensions.D_pos p
  have heta := rate.eta.property
  have hxi := hrate.2.1
  have hxiPos := hrate.1.trans_le hxi
  have hq0 : 0 ≤ QuantizedRecordingMoments.quantizedValue
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) :=
    QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ heta
  refine ⟨?_, ?_, ?_, hrho.2⟩
  · change 0 ≤ markerRatePlus rate rewards C_star C_h q t s hs control0 j z * quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z
    exact mul_nonneg hxiPos.le (by rw [hvalue]; exact hq0)
  · change roundedRewardPlus rewards t j -
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) ≤
      markerRatePlus rate rewards C_star C_h q t s hs control0 j z * quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z
    rw [hvalue]
    exact QuantizedRecordingMoments.quantizedValue_roundingError
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) hD heta hxiPos
      ⟨hrho.1, hrho.2⟩
  · change markerRatePlus rate rewards C_star C_h q t s hs control0 j z * quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z ≤
      roundedRewardPlus rewards t j
    rw [hvalue]
    exact QuantizedRecordingMoments.quantizedValue_firstMoment_le
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) hD heta hxiPos
      ⟨hrho.1, hrho.2⟩

/-- The square coefficient and the requested `rho^2 / xi` pointwise envelope. -/
theorem secondCoefficientPlus_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ secondCoefficientPlus rate rewards C_star C_h q t s hs control0 j z ∧
      secondCoefficientPlus rate rewards C_star C_h q t s hs control0 j z ≤ rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j z ∧
      rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z ∧
      1 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / beta := by
  have hrate := markerRatePlus_bounds rate rewards C_star C_h q t s hs control0 j z
  have hrho := roundedRewardPlus_bounds rewards t j
  have hvalue := quantizedValuePlus_eq_quantizedValue rate rewards C_star C_h q t s hs control0 j z
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hD := ConstructorDimensions.D_pos p
  have heta := rate.eta.property
  have hxiPos := hrate.1.trans_le hrate.2.1
  have hrhoSq : (roundedRewardPlus rewards t j) ^ 2 ≤ 1 := by
    nlinarith [hrho.1, hrho.2]
  refine ⟨?_, ?_, ?_, one_div_le_one_div_of_le hbeta hrate.2.1⟩
  · change 0 ≤ markerRatePlus rate rewards C_star C_h q t s hs control0 j z * (quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z) ^ 2
    exact mul_nonneg hxiPos.le (sq_nonneg _)
  · change markerRatePlus rate rewards C_star C_h q t s hs control0 j z * (quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z) ^ 2 ≤
      (roundedRewardPlus rewards t j) ^ 2 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z
    rw [hvalue]
    exact QuantizedRecordingMoments.quantizedValue_secondMoment_le
      (ConstructorDimensions.D p) rate.eta.val (markerRatePlus rate rewards C_star C_h q t s hs control0 j z)
      (roundedRewardPlus rewards t j) hD heta hxiPos
      ⟨hrho.1, hrho.2⟩
  · change (roundedRewardPlus rewards t j) ^ 2 /
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z
    exact div_le_div_of_nonneg_right hrhoSq hxiPos.le

/-- The squared-reward envelope itself is nonnegative and has a finite
canonical upper bound. -/
theorem rhoSquaredDivRatePlus_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j z ∧
      rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / beta := by
  have hrate := markerRatePlus_bounds rate rewards C_star C_h q t s hs control0 j z
  have hrho := roundedRewardPlus_bounds rewards t j
  have hxiPos := hrate.1.trans_le hrate.2.1
  have hrhoSq : (roundedRewardPlus rewards t j) ^ 2 ≤ 1 := by
    nlinarith [hrho.1, hrho.2]
  constructor
  · exact div_nonneg (sq_nonneg _) hxiPos.le
  · change (roundedRewardPlus rewards t j) ^ 2 /
      markerRatePlus rate rewards C_star C_h q t s hs control0 j z ≤ 1 / beta
    calc
      (roundedRewardPlus rewards t j) ^ 2 /
          markerRatePlus rate rewards C_star C_h q t s hs control0 j z ≤
        1 / markerRatePlus rate rewards C_star C_h q t s hs control0 j z :=
          div_le_div_of_nonneg_right hrhoSq hxiPos.le
      _ ≤ 1 / beta := one_div_le_one_div_of_le hrate.1 hrate.2.1

/-! ## Prefix invariance and measurability of the coefficients -/

theorem markerRatePlus_prefix (j : Fin p.K) (z : Zplus) :
    markerRatePlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z) = markerRatePlus rate rewards C_star C_h q t s hs control0 j z := by
  change CanonicalRecordingRates.xi p rate.eta.val
      (sourcePlusPayload rate rewards C_star C_h q t s hs control0 (prefixPlus rate rewards C_star C_h q t s hs control0 z)).anchor j =
    CanonicalRecordingRates.xi p rate.eta.val (sourcePlusPayload rate rewards C_star C_h q t s hs control0 z).anchor j
  rw [sourcePlusPayload_prefix]

theorem quantizedValuePlus_prefix (j : Fin p.K) (z : Zplus) :
    quantizedValuePlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z) = quantizedValuePlus rate rewards C_star C_h q t s hs control0 j z := by
  unfold quantizedValuePlus
  rw [markerRatePlus_prefix]

theorem firstCoefficientPlus_prefix (j : Fin p.K) (z : Zplus) :
    firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z) = firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j z := by
  simp only [firstCoefficientPlus, markerRatePlus_prefix, quantizedValuePlus_prefix]

theorem secondCoefficientPlus_prefix (j : Fin p.K) (z : Zplus) :
    secondCoefficientPlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z) = secondCoefficientPlus rate rewards C_star C_h q t s hs control0 j z := by
  simp only [secondCoefficientPlus, markerRatePlus_prefix, quantizedValuePlus_prefix]

theorem rhoSquaredDivRatePlus_prefix (j : Fin p.K) (z : Zplus) :
    rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z) = rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j z := by
  simp only [rhoSquaredDivRatePlus, markerRatePlus_prefix]

theorem measurable_markerRatePlus (j : Fin p.K) :
    Measurable[Fplus] (markerRatePlus rate rewards C_star C_h q t s hs control0 j) := by
  have hx : Measurable (fun z : Zplus =>
      ReferenceFirstLiveRecordingSourceCylinder.markerRate rate rewards C_star C_h q t s hs control0 (sourcePlusRemainder rate rewards C_star C_h q t s hs control0 z) j) :=
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_markerRate rate rewards C_star C_h q t s hs control0 j).comp (measurable_sourcePlusRemainder rate rewards C_star C_h q t s hs control0)
  have hpre : Measurable[Fplus]
      (fun z : Zplus => markerRatePlus rate rewards C_star C_h q t s hs control0 j (prefixPlus rate rewards C_star C_h q t s hs control0 z)) :=
    hx.comp (measurable_prefixPlus rate rewards C_star C_h q t s hs control0)
  rw [funext (markerRatePlus_prefix rate rewards C_star C_h q t s hs control0 j)] at hpre
  exact hpre

theorem measurable_quantizedValuePlus (j : Fin p.K) :
    Measurable[Fplus] (quantizedValuePlus rate rewards C_star C_h q t s hs control0 j) := by
  have harg : Measurable[Fplus] (fun z : Zplus =>
      (rate.n : ℝ) * roundedRewardPlus rewards t j /
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z) :=
    measurable_const.div (measurable_markerRatePlus rate rewards C_star C_h q t s hs control0 j)
  have hfloor : Measurable[Fplus] (fun z : Zplus =>
      (Nat.floor ((rate.n : ℝ) * roundedRewardPlus rewards t j /
        markerRatePlus rate rewards C_star C_h q t s hs control0 j z) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (Nat.measurable_floor.comp harg)
  change Measurable[Fplus] (fun z : Zplus =>
    (Nat.floor ((rate.n : ℝ) * roundedRewardPlus rewards t j /
      markerRatePlus rate rewards C_star C_h q t s hs control0 j z) : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)))
  exact hfloor.div measurable_const

theorem measurable_firstCoefficientPlus (j : Fin p.K) :
    Measurable[Fplus] (firstCoefficientPlus rate rewards C_star C_h q t s hs control0 j) := by
  exact (measurable_markerRatePlus rate rewards C_star C_h q t s hs control0 j).mul
    (measurable_quantizedValuePlus rate rewards C_star C_h q t s hs control0 j)

theorem measurable_secondCoefficientPlus (j : Fin p.K) :
    Measurable[Fplus] (secondCoefficientPlus rate rewards C_star C_h q t s hs control0 j) := by
  exact (measurable_markerRatePlus rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_quantizedValuePlus rate rewards C_star C_h q t s hs control0 j).pow_const 2)

theorem measurable_rhoSquaredDivRatePlus (j : Fin p.K) :
    Measurable[Fplus] (rhoSquaredDivRatePlus rate rewards C_star C_h q t s hs control0 j) := by
  exact measurable_const.div (measurable_markerRatePlus rate rewards C_star C_h q t s hs control0 j)

/-! ## The literal strict-past numerical readouts -/

/-- The actual numerical tuple on the first `n` cells, restricted from A's
original source-stratum readout. -/
@[expose] def numericalCountPastReadoutPlus (z : Zplus) :=
  ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0 z.val

/-- The actual strict-past queue registers, overflow bit, and chronological
per-arm records, restricted from A's source-stratum run readout. -/
@[expose] def numericalCountRunReadoutPlus (z : Zplus) :=
  ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z.val

theorem measurable_numericalCountPastReadoutPlus :
    Measurable[Fplus] (numericalCountPastReadoutPlus rate rewards C_star C_h q t s hs control0) := by
  exact (ReferenceFirstLiveNumericalPrefixAdaptation.measurable_numericalCountPastReadout rate rewards C_star C_h q t s hs control0).comp
    (measurable_sourcePlus_val rate rewards C_star C_h q t s hs control0)

theorem measurable_numericalCountRunReadoutPlus :
    Measurable[Fplus] (numericalCountRunReadoutPlus rate rewards C_star C_h q t s hs control0) := by
  exact (ReferenceFirstLiveNumericalPrefixAdaptation.measurable_numericalCountRunReadout rate rewards C_star C_h q t s hs control0).comp
    (measurable_sourcePlus_val rate rewards C_star C_h q t s hs control0)

local notation "cells" => ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The retained event tests exactly the first `n` actual cells. -/
@[expose] def strictPastOverflowFalseSet : Set Zplus :=
  {z : Zplus |
    (RecordedQueueRun.run queue ((cells z).take n)).overflow = false}

private def originalStrictPastOverflowFalseSet : Set Z :=
  {z : Z |
    (RecordedQueueRun.run queue
      ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
        (n + 1)
        (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
          rw [hz.2.2]
          omega)).take n)).overflow = false}

/-- C's complete `n + 1` source-cell list is A's literal full window list;
only proof witnesses for the same launch/elapsed facts differ. -/
private theorem cells_eq_actualLiveSourceCells (z : Zplus) :
    cells z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val).2.1
        (n + 1)
        (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val
          rw [hz.2.2]
          omega) := by
  dsimp [ReferenceFirstLiveSourceCellReadout.cells, ReferenceFirstLiveSourceCellReadout.sourceCurrentCount]

/-- The actual event of no overflow in A's first `n` cells is measurable on
the same Fplus comap. It does not test the current `n`th update. -/
theorem measurableSet_strictPastOverflowFalseSet :
    MeasurableSet[Fplus] (strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0) := by
  let originalField : MeasurableSpace Z :=
    (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)).comap
      (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
  have hset : MeasurableSet[originalField] (originalStrictPastOverflowFalseSet rate rewards C_star C_h q t s hs) := by
    exact ReferenceFirstLiveNumericalPrefixAdaptation.measurableSet_numericalCountRunOverflowFalse rate rewards C_star C_h q t s hs control0
  have hpre : MeasurableSet[Fplus]
      ((fun z : Zplus => z.val) ⁻¹' originalStrictPastOverflowFalseSet rate rewards C_star C_h q t s hs) :=
    hset.preimage (measurable_sourcePlus_val rate rewards C_star C_h q t s hs control0)
  have heq : strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0 =
      (fun z : Zplus => z.val) ⁻¹' originalStrictPastOverflowFalseSet rate rewards C_star C_h q t s hs := by
    ext z
    change (RecordedQueueRun.run queue ((cells z).take n)).overflow = false ↔
      (RecordedQueueRun.run queue
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val).2.1
          (n + 1)
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val
            rw [hz.2.2]
            omega)).take n)).overflow = false
    rw [cells_eq_actualLiveSourceCells rate rewards C_star C_h q t s hs control0 z]
  rw [heq]
  exact hpre

/-- The same literal strict-past event is ambient Borel on the inherited
continuing-source subtype. -/
theorem measurableSet_strictPastOverflowFalseSet_ambient :
    MeasurableSet (strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0) :=
  sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0 _
    (measurableSet_strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0)

end Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation

end
