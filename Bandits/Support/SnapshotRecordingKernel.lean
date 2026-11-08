/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalRecordingSlice
public import Bandits.Support.CanonicalFastSampling
public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.ActiveObservationBridge
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.RecordedRoundMoments

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-round arm-or-bottom recording kernel

This module builds the DATA recorder from one fixed continuous control slice,
the canonical recording rates, and the existing active-assignment actions.
The source inputs are the fixed anchor/current weights and one existing
assignment snapshot. It states no conditional-freshness result for protocol
histories and no multiround execution law.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-429`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-155`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.SnapshotRecordingKernel

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActiveObservationBridge
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ProductSetLaw

/-- A fixed single-round source regime: initial collection, or one live
assignment with its supplied pre-round snapshot. The snapshot contains no
history reconstruction or distributional premise. -/
inductive Regime (p : Parameters) where
  | collection
  | live (assignment : ActiveRoundActions.Assignment p.m p.K)
      (snapshot : ActiveRoundActions.Snapshot assignment)

/-- The slow-set carrier induced by the true assignment vector. In particular,
an unoccupied follower's assigned arm is retained before it is decoded. -/
def assignmentSlowSet (p : Parameters)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    CanonicalOrientedSetLaw.SlowSet p.K p.m := by
  classical
  have hcard : (Finset.univ.image a.assigned).card = p.m - 1 := by
    rw [Finset.card_image_of_injective _ a.injective, Finset.card_univ]
    change Fintype.card (Fin (p.m - 1)) = p.m - 1
    exact Fintype.card_fin _
  refine ⟨Finset.univ.image a.assigned, ?_⟩
  rw [ProductSetLaw.support, Finset.mem_powersetCard]
  constructor
  · exact Finset.subset_univ _
  · exact hcard

/-- The literal DATA action at a selected source, using all existing arm
branches. Collection uses the coordinator's reserved pilot. In a live snapshot
the coordinator pilots precisely while confirmations are missing; otherwise
its arm is the canonical fast sampler on the actual reserved fast scalar. An
unoccupied follower uses its pilot, including when the true assignment has not
been decoded; an occupied follower uses its assigned arm. -/
def dataAction (p : Parameters) (regime : Regime p) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (x : CanonicalRecordingSlice.Slice p.m p.K) (source : Fin p.m) : Fin p.K := by
  classical
  cases regime with
  | collection =>
      exact PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
        source x
  | live a s =>
      by_cases hs : source = ActiveRoundActions.coordinator p.two_le_m
      · by_cases hm : s.missing = ∅
        · exact (CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw
            hvw hwv (assignmentSlowSet p a)
            (coordinate Label.fast x)).val
        · exact PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
            source x
      · let follower := ActiveRoundActions.followerIndex p.two_le_m source hs
        if hstatus : s.status follower = .unoccupied then
          exact PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
            source x
        else
          exact a.assigned follower

/-- Source ownership test. In collection the coordinator owns all arms. In a
live assignment each follower owns its true assigned arm and the coordinator
owns the complement of that assignment image. -/
def owns (p : Parameters) (regime : Regime p) (source : Fin p.m)
    (j : Fin p.K) : Prop := by
  classical
  cases regime with
  | collection => exact source = ActiveRoundActions.coordinator p.two_le_m
  | live a _ =>
      by_cases hs : source = ActiveRoundActions.coordinator p.two_le_m
      · exact j ∉ Finset.univ.image a.assigned
      · exact j = a.assigned (ActiveRoundActions.followerIndex p.two_le_m source hs)

/-- Every arm has an owner among the source players. -/
theorem exists_ownerSource (p : Parameters) (regime : Regime p)
    (j : Fin p.K) : ∃ i, owns p regime i j := by
  classical
  cases regime with
  | collection => exact ⟨ActiveRoundActions.coordinator p.two_le_m, rfl⟩
  | live a _ =>
      by_cases hj : j ∈ Finset.univ.image a.assigned
      · rcases Finset.mem_image.mp hj with ⟨r, _, hr⟩
        refine ⟨PublicDiscreteDraws.followerPlayer p.two_le_m r, ?_⟩
        have hnot := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m r
        simpa [owns, hnot,
          ActiveRoundActions.followerIndex_followerPlayer p.two_le_m r hnot] using hr.symm
      · refine ⟨ActiveRoundActions.coordinator p.two_le_m, ?_⟩
        simpa [owns] using hj

/-- The unique source owner of a fixed arm in one supplied regime. -/
noncomputable def ownerSource (p : Parameters) (regime : Regime p)
    (j : Fin p.K) : Fin p.m := Classical.choose (exists_ownerSource p regime j)

/-- Every arm has its stated source owner. -/
theorem owns_ownerSource (p : Parameters) (regime : Regime p)
    (j : Fin p.K) : owns p regime (ownerSource p regime j) j := by
  simpa [ownerSource] using Classical.choose_spec (exists_ownerSource p regime j)

/-- Source ownership is unique because the follower assignment is injective
and the coordinator owns exactly its complement. -/
theorem owns_unique (p : Parameters) (regime : Regime p) (j : Fin p.K)
    (s t : Fin p.m) (hs : owns p regime s j) (ht : owns p regime t j) : s = t := by
  classical
  cases regime with
  | collection =>
      simp only [owns] at hs ht
      exact hs.trans ht.symm
  | live a snapshot =>
      by_cases hsc : s = ActiveRoundActions.coordinator p.two_le_m
      · by_cases htc : t = ActiveRoundActions.coordinator p.two_le_m
        · exact hsc.trans htc.symm
        · have hnot : j ∉ Finset.univ.image a.assigned := by
            simpa [owns, hsc] using hs
          let r := ActiveRoundActions.followerIndex p.two_le_m t htc
          have hassigned : j = a.assigned r := by
            simpa [owns, htc, r] using ht
          have hmem : j ∈ Finset.univ.image a.assigned :=
            Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hassigned.symm⟩
          exact False.elim (hnot hmem)
      · by_cases htc : t = ActiveRoundActions.coordinator p.two_le_m
        · have hnot : j ∉ Finset.univ.image a.assigned := by
            simpa [owns, htc] using ht
          let r := ActiveRoundActions.followerIndex p.two_le_m s hsc
          have hassigned : j = a.assigned r := by
            simpa [owns, hsc, r] using hs
          have hmem : j ∈ Finset.univ.image a.assigned :=
            Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hassigned.symm⟩
          exact False.elim (hnot hmem)
        · let r := ActiveRoundActions.followerIndex p.two_le_m s hsc
          let q := ActiveRoundActions.followerIndex p.two_le_m t htc
          have hrs : j = a.assigned r := by simpa [owns, hsc, r] using hs
          have hqt : j = a.assigned q := by simpa [owns, htc, q] using ht
          have hrq : r = q := a.injective (hrs.symm.trans hqt)
          calc
            s = PublicDiscreteDraws.followerPlayer p.two_le_m r :=
              (ActiveRoundActions.followerPlayer_followerIndex p.two_le_m s hsc).symm
            _ = PublicDiscreteDraws.followerPlayer p.two_le_m q := congrArg _ hrq
            _ = t := ActiveRoundActions.followerPlayer_followerIndex p.two_le_m t htc

/-- Literal DATA-conditional action probability for an arm. It is used only
after the selected source's action and ownership tests have passed. -/
def actionProbability (p : Parameters) (regime : Regime p) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (source : Fin p.m) (j : Fin p.K) : ℝ := by
  classical
  cases regime with
  | collection => exact 1 / (p.K : ℝ)
  | live a s =>
      by_cases hs : source = ActiveRoundActions.coordinator p.two_le_m
      · if hmissing : s.missing ≠ ∅ then
          exact 1 / (p.K : ℝ)
        else
          if hj : j ∈ fastArmFinset (assignmentSlowSet p a) then
            exact qGamma p eta heta heta_le v w hv hw hvw hwv
              (assignmentSlowSet p a) ⟨j, hj⟩
          else
            exact 0
      · let follower := ActiveRoundActions.followerIndex p.two_le_m source hs
        if hstatus : s.status follower = .unoccupied then
          exact 1 / (p.K : ℝ)
        else if hj : j = a.assigned follower then
          exact 1
        else
          exact 0

/-- The complete raw DATA/source/action/mask coefficient before thinning:
`(1/2) s_i π_i(j) ζ`. -/
def rawGateMass (p : Parameters) (regime : Regime p) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (source : Fin p.m) (j : Fin p.K) : ℝ :=
  (1 / 2) * PublicDiscreteDraws.recorderMass p.m source *
    actionProbability p regime eta heta heta_le v w hv hw hvw hwv source j *
    recordingZeta p.m p.K

/-- The source inclusive thinning threshold for the selected owner and arm.
Feasibility is proved below from the source rate cap and, on the fast branch,
the accepted `qGamma ≥ 16 ξ` estimate. -/
def thinningThreshold (p : Parameters) (regime : Regime p) (eta : ℝ)
    (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (source : Fin p.m) (j : Fin p.K) : ℝ :=
  xi p eta v j / rawGateMass p regime eta heta heta_le v w hv hw hvw hwv source j

/-- The single-selected-source arm-or-bottom recording map. The arm is read
from that source's actual DATA action, then tested for ownership, the complete
nonowner-pilot mask, and the inclusive thin comparison. -/
def recordingMap (p : Parameters) (regime : Regime p) (enabled : Bool)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (x : CanonicalRecordingSlice.Slice p.m p.K) : Option (Fin p.K) := by
  classical
  if henabled : enabled = true then
    if hslot : slotFromScalar (coordinate Label.slot x) = dataSlot then
      let source := CanonicalRecordingSlice.recorderSourceFromScalar
        p.two_le_m (coordinate Label.rec x)
      let j := dataAction p regime eta heta heta_le v w hv hw hvw hwv x source
      if howns : owns p regime source j then
        if hmask : recordingMask (ConstructorDimensions.K_pos p) source j x then
          if hthin : (coordinate Label.thin x).val ≤
              thinningThreshold p regime eta heta heta_le v w hv hw hvw hwv source j then
            exact some j
          else
            exact none
        else
          exact none
      else
        exact none
    else
      exact none
  else
    exact none

/-- The disabled or incoming-frozen mask wins before every recording test. -/
@[simp] theorem recordingMap_disabled (p : Parameters) (regime : Regime p)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (x : CanonicalRecordingSlice.Slice p.m p.K) :
    recordingMap p regime false eta heta heta_le v w hv hw hvw hwv x = none := by
  simp [recordingMap]

/-- On an enabled DATA slot, recording a fixed arm is equivalent to the
literal selected-source action, ownership, mask, and inclusive thinning tests.
The source remains the one scalar draw inside this same slice. -/
theorem recordingMap_some_iff
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (x : CanonicalRecordingSlice.Slice p.m p.K) (j : Fin p.K) :
    recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j ↔
      slotFromScalar (coordinate Label.slot x) = dataSlot ∧
      dataAction p regime eta heta heta_le v w hv hw hvw hwv x
        (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec x)) = j ∧
      owns p regime (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec x)) j ∧
      recordingMask (ConstructorDimensions.K_pos p)
        (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec x)) j x ∧
      (coordinate Label.thin x).val ≤ thinningThreshold p regime eta heta heta_le
        v w hv hw hvw hwv
        (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec x)) j := by
  classical
  simp [recordingMap]
  intro hslot
  constructor
  · rintro ⟨howns, hmask, hthin, haction⟩
    exact ⟨haction, by simpa [haction] using howns,
      by simpa [haction] using hmask, by simpa [haction] using hthin⟩
  · rintro ⟨haction, howns, hmask, hthin⟩
    exact ⟨by simpa [haction] using howns,
      by simpa [haction] using hmask, by simpa [haction] using hthin, haction⟩

/-- Fixing the unique true owner removes the ownership test without replacing
any random source, action, mask, or thinning input by an assumed law. -/
theorem recordingMap_owner_event_eq
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (i : Fin p.m) (j : Fin p.K) (howner : owns p regime i j) :
    {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      {x | slotDraw x = dataSlot ∧ recorderSourceDraw p.two_le_m p.m_lt_K x = i ∧
        dataAction p regime eta heta heta_le v w hv hw hvw hwv x i = j ∧
        recordingMask (ConstructorDimensions.K_pos p) i j x ∧
        (coordinate Label.thin x).val ≤
          thinningThreshold p regime eta heta heta_le v w hv hw hvw hwv i j} := by
  ext x
  rw [Set.mem_ofPred_eq, recordingMap_some_iff]
  simp only [Set.mem_ofPred_eq,
    ← recorderSourceFromScalar_coordinate p.two_le_m p.m_lt_K x]
  constructor
  · rintro ⟨hs, ha, ho, hm, ht⟩
    have hi := owns_unique p regime j _ _ ho howner
    exact ⟨hs, hi, by simpa only [hi] using ha,
      by simpa only [hi] using hm, by simpa only [hi] using ht⟩
  · rintro ⟨hs, hi, ha, hm, ht⟩
    exact ⟨hs, by simpa only [hi] using ha, by simpa only [hi] using howner,
      by simpa only [hi] using hm, by simpa only [hi] using ht⟩

/-- If one fixed owner uses its own pilot, its map atom is exactly the accepted
pilot-recording gate. The source and action assumptions are all exposed. -/
theorem recordingMap_pilot_event_eq
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (i : Fin p.m) (j : Fin p.K)
    (howner : owns p regime i j)
    (haction : ∀ x, dataAction p regime eta heta heta_le v w hv hw hvw hwv x i =
      PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) i x)
    (hprob : actionProbability p regime eta heta heta_le v w hv hw hvw hwv i j =
      1 / (p.K : ℝ)) :
    {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      {x | CanonicalRecordingSlice.pilotRecordingGate p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) i j
        (xi p eta v j /
          CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K) i) x} := by
  have hthreshold : thinningThreshold p regime eta heta heta_le v w hv hw hvw hwv i j =
      xi p eta v j / pilotRecordingGateRawProbability (K := p.K) i := by
    unfold thinningThreshold rawGateMass
    rw [hprob]
    rfl
  rw [recordingMap_owner_event_eq p regime eta heta heta_le v w hv hw hvw hwv i j howner]
  ext x
  simp only [Set.mem_ofPred_eq, pilotRecordingGate, haction x, hthreshold]

/-- If one fixed owner plays its arm deterministically, its map atom is exactly
the accepted deterministic-owned gate. -/
theorem recordingMap_fixed_event_eq
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (i : Fin p.m) (j : Fin p.K)
    (howner : owns p regime i j)
    (haction : ∀ x, dataAction p regime eta heta heta_le v w hv hw hvw hwv x i = j)
    (hprob : actionProbability p regime eta heta heta_le v w hv hw hvw hwv i j = 1) :
    {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m
        p.m_lt_K (ConstructorDimensions.K_pos p) i j
        (xi p eta v j /
          CanonicalRecordingSlice.deterministicOwnedGateRawProbability (K := p.K) i) x} := by
  have hthreshold : thinningThreshold p regime eta heta heta_le v w hv hw hvw hwv i j =
      xi p eta v j / deterministicOwnedGateRawProbability (K := p.K) i := by
    unfold thinningThreshold rawGateMass
    rw [hprob, mul_one]
    rfl
  rw [recordingMap_owner_event_eq p regime eta heta heta_le v w hv hw hvw hwv i j howner]
  ext x
  simp only [Set.mem_ofPred_eq, deterministicOwnedRecordingGate, haction x,
    hthreshold, true_and]

/-- The actual fast-arm draw on the reserved `fast` coordinate of one
continuous slice. The returned subtype is exactly the complement of the true
assignment image. -/
def fastArmDraw (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (x : CanonicalRecordingSlice.Slice p.m p.K) :
    CanonicalFastSampling.FastArm (assignmentSlowSet p a) :=
  CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv
    (assignmentSlowSet p a) (coordinate Label.fast x)

/-- Measurability of the concrete fast-arm slice map. -/
theorem measurable_fastArmDraw (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    Measurable (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a) := by
  exact (CanonicalFastSampling.measurable_sampleFast p eta heta heta_le v w
    hv hw hvw hwv (assignmentSlowSet p a)).comp
      (ContinuousControlSlice.measurable_coordinate Label.fast)

/-- Exact fast-arm pushforward from the reserved slice coordinate, derived
from the actual `sampleFast` pushforward rather than a supplied action law. -/
theorem map_fastArmDraw (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a) =
      (CanonicalFastSampling.qGammaPMF p eta heta heta_le v w hv hw hvw hwv
        (assignmentSlowSet p a)).toMeasure := by
  change (ContinuousControlSlice.sliceLaw p.m p.K).map
      (CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv
        (assignmentSlowSet p a) ∘ coordinate Label.fast) = _
  rw [← Measure.map_map
    (CanonicalFastSampling.measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv
      (assignmentSlowSet p a))
    (ContinuousControlSlice.measurable_coordinate Label.fast),
    ContinuousControlSlice.map_coordinate,
    PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  exact CanonicalFastSampling.uniform_map_sampleFast p eta heta heta_le v w hv hw
    hvw hwv (assignmentSlowSet p a)

/-- Every fast-arm singleton has the exact `qΓ` mass on the one-slice law. -/
theorem fastArmDraw_atom (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} =
      ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv
        (assignmentSlowSet p a) j) := by
  change (ContinuousControlSlice.sliceLaw p.m p.K)
      (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a ⁻¹' {j}) = _
  rw [← Measure.map_apply (measurable_fastArmDraw p eta heta heta_le v w hv hw
      hvw hwv a) (measurableSet_singleton j),
    map_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a,
    PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j),
    CanonicalFastSampling.qGammaPMF_apply]

/-- The joint scalar index for the source/mask coordinates of a fixed owner. -/
abbrev RecordingRelevantIndex (m : ℕ) := Fin (PublicDiscreteDraws.followerCount m) ⊕ Fin 4
abbrev RecordingExtendedIndex (m : ℕ) := Option (RecordingRelevantIndex m)

/-- The actual relevant source/mask coordinates, in the two disjoint blocks
used by the accepted recording-slice factorization. -/
def recordingRelevantScalars {m K : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (x : CanonicalRecordingSlice.Slice m K) :
    RecordingRelevantIndex m → CanonicalRecordingSlice.Scalar :=
  fun q => ContinuousControlSlice.coordinate
    (CanonicalRecordingSlice.recordingScalarLabel hm i q) x

/-- The owner gate labels with the independent reserved fast coordinate added. -/
def recordingFastLabel {m K : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    RecordingExtendedIndex m → ContinuousControlSlice.Label m K
  | some q => CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i q
  | none => ContinuousControlSlice.Label.fast (m := m) (K := K)

private theorem recordingScalarLabel_ne_fast {m K : ℕ} (hm : 2 ≤ m)
    (i : Fin m) (q : RecordingRelevantIndex m) :
    CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i q ≠
      ContinuousControlSlice.Label.fast (m := m) (K := K) := by
  cases q with
  | inl r => simp [CanonicalRecordingSlice.recordingScalarLabel,
      ContinuousControlSlice.Label.pilot, ContinuousControlSlice.Label.fast]
  | inr r =>
      fin_cases r <;> simp [CanonicalRecordingSlice.recordingScalarLabel,
        CanonicalRecordingSlice.gateScalarLabel, ContinuousControlSlice.Label.slot,
        ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.pilot,
        ContinuousControlSlice.Label.thin, ContinuousControlSlice.Label.fast]

private theorem recordingFastLabel_injective {m K : ℕ} (hm : 2 ≤ m)
    (i : Fin m) : Function.Injective (recordingFastLabel (K := K) hm i) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          have hlabels : CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i b =
              ContinuousControlSlice.Label.fast (m := m) (K := K) := by
            simpa [recordingFastLabel] using hab.symm
          exact False.elim (recordingScalarLabel_ne_fast (K := K) hm i b hlabels)
  | some a =>
      cases b with
      | none =>
          have hlabels : CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i a =
              ContinuousControlSlice.Label.fast (m := m) (K := K) := by
            simpa [recordingFastLabel] using hab
          exact False.elim (recordingScalarLabel_ne_fast (K := K) hm i a hlabels)
      | some b =>
          have hlabels : CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i a =
              CanonicalRecordingSlice.recordingScalarLabel (K := K) hm i b := by
            simpa [recordingFastLabel] using hab
          exact congrArg Option.some
            (CanonicalRecordingSlice.recordingScalarLabel_injective (K := K) hm i hlabels)

/-- Disjoint-label independence: all coordinates used by the mask, slot,
recorder-source and thinning tests are independent of the reserved fast input.
The proof starts from the complete accepted slice product law. -/
theorem indepFun_recordingRelevantScalars_fastCoordinate {m K : ℕ}
    (hm : 2 ≤ m) (i : Fin m) :
    IndepFun (recordingRelevantScalars hm i)
      (fun x => ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x)
      (ContinuousControlSlice.sliceLaw m K) := by
  let leftSet : Set (RecordingExtendedIndex m) := Set.range Option.some
  let rightSet : Set (RecordingExtendedIndex m) := {none}
  let leftBlockOf : ((q : leftSet) → ContinuousControlSlice.Scalar) →
      RecordingRelevantIndex m → ContinuousControlSlice.Scalar :=
    fun z q => z ⟨some q, ⟨q, rfl⟩⟩
  let rightBlockOf : ((q : rightSet) → ContinuousControlSlice.Scalar) →
      ContinuousControlSlice.Scalar :=
    fun z => z ⟨none, by simp [rightSet]⟩
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate m K).precomp
    (recordingFastLabel_injective (K := K) hm i)
  have hblocks := hcoords.indepFun_set leftSet rightSet (by
    rw [Set.disjoint_left]
    intro q hq hr
    rcases hq with ⟨r, rfl⟩
    simp only [rightSet, Set.mem_singleton_iff] at hr
    contradiction)
    (fun q => ContinuousControlSlice.measurable_coordinate
      (recordingFastLabel (K := K) hm i q))
  have hleft : Measurable leftBlockOf := by
    apply measurable_pi_iff.mpr
    intro q
    exact measurable_pi_apply
      (⟨some q, ⟨q, rfl⟩⟩ : leftSet)
  have hright : Measurable rightBlockOf := by
    exact measurable_pi_apply
      (⟨none, by simp [rightSet]⟩ : rightSet)
  have hcomp := hblocks.comp hleft hright
  have hleftEq :
      (fun x : ContinuousControlSlice.Slice m K =>
        leftBlockOf (fun q => ContinuousControlSlice.coordinate
          (recordingFastLabel (K := K) hm i q.val) x)) = recordingRelevantScalars hm i := by
    funext x q
    rfl
  have hrightEq :
      (fun x : ContinuousControlSlice.Slice m K =>
        rightBlockOf (fun q => ContinuousControlSlice.coordinate
          (recordingFastLabel (K := K) hm i q.val) x)) =
        fun x => ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x := by
    funext x
    rfl
  change IndepFun
    (fun x : ContinuousControlSlice.Slice m K =>
      leftBlockOf (fun q => ContinuousControlSlice.coordinate
        (recordingFastLabel (K := K) hm i q.val) x))
    (fun x : ContinuousControlSlice.Slice m K =>
      rightBlockOf (fun q => ContinuousControlSlice.coordinate
        (recordingFastLabel (K := K) hm i q.val) x))
    (ContinuousControlSlice.sliceLaw m K) at hcomp
  rw [hleftEq, hrightEq] at hcomp
  exact hcomp

/-- The actual fast arm remains independent of all source and mask scalars:
compose the disjoint coordinate independence with the accepted sampler. -/
theorem indepFun_recordingRelevantScalars_fastArmDraw {p : Parameters}
    (i : Fin p.m) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K) :
    IndepFun (recordingRelevantScalars p.two_le_m i)
      (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
  have h := (indepFun_recordingRelevantScalars_fastCoordinate
      (m := p.m) (K := p.K) p.two_le_m i).comp
    (measurable_id : Measurable
      (fun z : RecordingRelevantIndex p.m → ContinuousControlSlice.Scalar => z))
    (CanonicalFastSampling.measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv
      (assignmentSlowSet p a))
  change IndepFun (recordingRelevantScalars p.two_le_m i)
    (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a)
    (ContinuousControlSlice.sliceLaw p.m p.K) at h
  exact h

/-- The complete fast-owner gate as a measurable product set on the disjoint
source/mask block. The owner pilot coordinate is deliberately unrestricted. -/
def fastGateRelevantSet {m K : ℕ} (hm : 2 ≤ m) (hK : 0 < K)
    (i : Fin m) (j : Fin K) (a : ℝ) :
    Set (RecordingRelevantIndex m → CanonicalRecordingSlice.Scalar) :=
  Set.univ.pi (fun q => match q with
  | Sum.inl _ => {v | PublicDiscreteDraws.pilotFromScalar K hK v ≠ j}
    | Sum.inr r =>
        CanonicalRecordingSlice.deterministicGateScalarFactorSet hm i a r)

theorem measurableSet_fastGateRelevantSet {m K : ℕ} (hm : 2 ≤ m)
    (hK : 0 < K) (i : Fin m) (j : Fin K) (a : ℝ) :
    MeasurableSet (fastGateRelevantSet hm hK i j a) := by
  apply MeasurableSet.univ_pi
  intro q
  cases q with
  | inl r =>
      exact (measurableSet_singleton j).compl.preimage
        (CanonicalRecordingSlice.measurable_pilotFromScalar hK)
  | inr r =>
      exact CanonicalRecordingSlice.measurableSet_deterministicGateScalarFactors
        hm i a r

theorem recordingRelevant_fastGate_preimage {m K : ℕ}
    (hm : 2 ≤ m) (hmk : m < K) (hK : 0 < K)
    (i : Fin m) (j : Fin K) (a : ℝ) :
    {x | recordingRelevantScalars hm i x ∈ fastGateRelevantSet hm hK i j a} =
      {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
        hm hmk hK i j a x} := by
  rw [CanonicalRecordingSlice.deterministicOwnedRecordingGate_event_eq
    hm hmk hK i j a]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    CanonicalRecordingSlice.nonownerMaskSet, Set.mem_univ_pi]
  have hgate :
      (∀ r : Fin 4, ContinuousControlSlice.coordinate
        (CanonicalRecordingSlice.gateScalarLabel i r) x ∈
          CanonicalRecordingSlice.deterministicGateScalarFactorSet hm i a r) ↔
        CanonicalRecordingSlice.gateScalars i x ∈
          CanonicalRecordingSlice.deterministicGateScalarSet hm i a := by
    rw [CanonicalRecordingSlice.deterministicGateScalarSet_mem_iff hm hmk i a x]
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · simpa [CanonicalRecordingSlice.gateScalars,
          CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet,
          CanonicalRecordingSlice.slotFromScalar_coordinate] using h 0
      · have hs : CanonicalRecordingSlice.recorderSourceFromScalar hm
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x) = i := by
          simpa [CanonicalRecordingSlice.gateScalars,
            CanonicalRecordingSlice.gateScalarLabel,
            CanonicalRecordingSlice.deterministicGateScalarFactorSet] using h 1
        rw [← CanonicalRecordingSlice.recorderSourceFromScalar_coordinate hm hmk x]
        exact hs
      · simpa [CanonicalRecordingSlice.gateScalars,
          CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet] using h 3
    · rintro ⟨hs, hr, ht⟩ r
      fin_cases r
      · simpa [CanonicalRecordingSlice.gateScalars,
          CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet,
          CanonicalRecordingSlice.slotFromScalar_coordinate] using hs
      · rw [← CanonicalRecordingSlice.recorderSourceFromScalar_coordinate hm hmk x] at hr
        simpa [CanonicalRecordingSlice.gateScalars,
          CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet] using hr
      · simp [CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet]
      · simpa [CanonicalRecordingSlice.gateScalars,
          CanonicalRecordingSlice.gateScalarLabel,
          CanonicalRecordingSlice.deterministicGateScalarFactorSet] using ht
  constructor
  · intro h
    constructor
    · intro r
      have hr := h (Sum.inl r)
      simpa [fastGateRelevantSet, recordingRelevantScalars,
        CanonicalRecordingSlice.recordingScalarLabel,
        CanonicalRecordingSlice.nonownerPilotScalars] using hr
    · apply hgate.mp
      intro r
      have hr := h (Sum.inr r)
      simpa [fastGateRelevantSet, recordingRelevantScalars,
        CanonicalRecordingSlice.recordingScalarLabel] using hr
  · rintro ⟨hmask, hgate'⟩ q
    cases q with
    | inl r =>
        have hr := hmask r
        simpa [fastGateRelevantSet, recordingRelevantScalars,
          CanonicalRecordingSlice.recordingScalarLabel,
          CanonicalRecordingSlice.nonownerPilotScalars] using hr
    | inr r =>
        have hr := hgate.mpr hgate' r
        simpa [fastGateRelevantSet, recordingRelevantScalars,
          CanonicalRecordingSlice.recordingScalarLabel] using hr

/-- Joint probability of the deterministic source/mask/thinning gate and the
actual reserved-coordinate fast-arm draw. The factorization follows from the
disjoint-label independence proved above. -/
theorem deterministicGate_fastArm_joint_measure
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K) (i : Fin p.m)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a))
    (threshold : ℝ) (hthreshold0 : 0 ≤ threshold) (hthreshold1 : threshold ≤ 1) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
          p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p) i j.1 threshold x ∧
        fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} =
      ENNReal.ofReal ((1 / 2) * PublicDiscreteDraws.recorderMass p.m i *
        CanonicalRecordingSlice.recordingZeta p.m p.K * threshold) *
      ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv
        (assignmentSlowSet p a) j) := by
  let S := fastGateRelevantSet p.two_le_m (ConstructorDimensions.K_pos p)
    i j.1 threshold
  have hset :
      {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
          p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p) i j.1 threshold x ∧
        fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} =
      (recordingRelevantScalars p.two_le_m i ⁻¹' S) ∩
        (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a ⁻¹' {j}) := by
    ext x
    have hgate :
        CanonicalRecordingSlice.deterministicOwnedRecordingGate
            p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p) i j.1 threshold x ↔
          recordingRelevantScalars p.two_le_m i x ∈ S := by
      have heq := congrArg (fun t : Set (ContinuousControlSlice.Slice p.m p.K) => x ∈ t)
        (recordingRelevant_fastGate_preimage p.two_le_m p.m_lt_K
          (ConstructorDimensions.K_pos p) i j.1 threshold)
      exact Iff.of_eq (by
        simpa only [Set.mem_ofPred_eq, Set.mem_preimage, S] using heq.symm)
    simp [hgate]
  rw [hset]
  rw [(indepFun_recordingRelevantScalars_fastArmDraw (i := i) eta heta heta_le v w hv hw hvw hwv a).measure_inter_preimage_eq_mul S {j}
      (measurableSet_fastGateRelevantSet p.two_le_m
        (ConstructorDimensions.K_pos p) i j.1 threshold)
      (measurableSet_singleton j)]
  change (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | recordingRelevantScalars p.two_le_m i x ∈
        fastGateRelevantSet p.two_le_m (ConstructorDimensions.K_pos p)
          i j.1 threshold} *
      (ContinuousControlSlice.sliceLaw p.m p.K)
        (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a ⁻¹' {j}) = _
  rw [recordingRelevant_fastGate_preimage p.two_le_m p.m_lt_K
      (ConstructorDimensions.K_pos p) i j.1 threshold,
    CanonicalRecordingSlice.deterministicOwnedRecordingGate_probability
      p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p) i j.1 threshold
      hthreshold0 hthreshold1]
  change ENNReal.ofReal ((1 / 2) * PublicDiscreteDraws.recorderMass p.m i *
      CanonicalRecordingSlice.recordingZeta p.m p.K * threshold) *
      (ContinuousControlSlice.sliceLaw p.m p.K)
        {x | fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} = _
  rw [fastArmDraw_atom p eta heta heta_le v w hv hw hvw hwv a j]

/-- The actual fast-owner raw gate mass is at least `ξ`: its action factor is
the sampler's `qΓ` atom, and feasibility follows from `qΓ ≥ 16ξ` and
`ζ > 1/4`. -/
theorem fastCoordinator_rawGateMass_eq
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) (hmissing : s.missing = ∅)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    rawGateMass p (.live a s) eta heta heta_le v w hv hw hvw hwv
        (ActiveRoundActions.coordinator p.two_le_m) j.1 =
      CanonicalRecordingSlice.deterministicOwnedGateRawProbability
          (K := p.K) (ActiveRoundActions.coordinator p.two_le_m) *
        qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j := by
  have hj : j.1 ∈ fastArmFinset (assignmentSlowSet p a) := j.2
  have haction : actionProbability p (.live a s) eta heta heta_le
      v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j.1 =
      qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j := by
    simp [actionProbability, hj, hmissing]
  unfold rawGateMass CanonicalRecordingSlice.deterministicOwnedGateRawProbability
  rw [haction, ActiveRoundActions.coordinator,
    PublicDiscreteDraws.recorderMass_coordinator p.two_le_m]
  ring

theorem fastCoordinator_rawGateMass_ge_xi
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) (hmissing : s.missing = ∅)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    xi p eta v j.1 ≤ rawGateMass p (.live a s) eta heta heta_le
      v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j.1 := by
  have hj : j.1 ∈ fastArmFinset (assignmentSlowSet p a) := j.2
  have haction : actionProbability p (.live a s) eta heta heta_le
      v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j.1 =
      qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j := by
    simp [actionProbability, hj, hmissing]
  have hraw : rawGateMass p (.live a s) eta heta heta_le v w hv hw hvw hwv
      (ActiveRoundActions.coordinator p.two_le_m) j.1 =
      (1 / 2) * (1 / 2) *
        qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j *
          recordingZeta p.m p.K := by
    rw [fastCoordinator_rawGateMass_eq p eta heta heta_le v w hv hw hvw hwv
      a s hmissing j]
    unfold CanonicalRecordingSlice.deterministicOwnedGateRawProbability
    rw [ActiveRoundActions.coordinator,
      PublicDiscreteDraws.recorderMass_coordinator p.two_le_m]
    ring
  have hq := CanonicalFastSampling.qGamma_ge_16_xi p heta heta_le v w hv hw
    hvw hwv (assignmentSlowSet p a) j
  have hz := CanonicalRecordingSlice.recordingZeta_gt_quarter
    p.two_le_m p.m_lt_K
  have hznn : 0 ≤ CanonicalRecordingSlice.recordingZeta p.m p.K := by linarith
  have hxi := CanonicalRecordingRates.xi_pos p heta v j.1
  have hqz : 4 * xi p eta v j.1 ≤
      qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j *
        recordingZeta p.m p.K := by
    have hqmul := mul_le_mul_of_nonneg_right hq hznn
    have hfour : 4 * xi p eta v j.1 ≤ 16 * xi p eta v j.1 *
        recordingZeta p.m p.K := by
      calc
        4 * xi p eta v j.1 = 16 * xi p eta v j.1 * (1 / 4) := by ring
        _ ≤ 16 * xi p eta v j.1 * recordingZeta p.m p.K :=
          mul_le_mul_of_nonneg_left hz.le (by positivity)
    exact hfour.trans hqmul
  rw [hraw]
  nlinarith

/-- Feasibility of the actual fast owner's source thinning threshold. -/
theorem fastCoordinator_thinningThreshold_mem_Icc
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) (hmissing : s.missing = ∅)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    thinningThreshold p (.live a s) eta heta heta_le v w hv hw hvw hwv
      (ActiveRoundActions.coordinator p.two_le_m) j.1 ∈ Set.Icc 0 1 := by
  have hxi := CanonicalRecordingRates.xi_pos p heta v j.1
  have hraw := fastCoordinator_rawGateMass_ge_xi p eta heta heta_le v w hv hw
    hvw hwv a s hmissing j
  have hrawpos : 0 < rawGateMass p (.live a s) eta heta heta_le
      v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j.1 :=
    hxi.trans_le hraw
  unfold thinningThreshold
  exact ⟨div_nonneg hxi.le hrawpos.le,
    (div_le_one₀ hrawpos).2 hraw⟩

/-- The fast owner's complete source/mask/actual-arm gate records exactly the
canonical rate. The first overflowing queue update is retained because this
identity has no outgoing-state filter. -/
theorem fastCoordinator_recordingGate_mass
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) (hmissing : s.missing = ∅)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
          p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) j.1
          (thinningThreshold p (.live a s) eta heta heta_le v w hv hw hvw hwv
            (ActiveRoundActions.coordinator p.two_le_m) j.1) x ∧
        fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} =
      ENNReal.ofReal (xi p eta v j.1) := by
  let base := CanonicalRecordingSlice.deterministicOwnedGateRawProbability
    (K := p.K) (ActiveRoundActions.coordinator p.two_le_m)
  let raw := rawGateMass p (.live a s) eta heta heta_le v w hv hw hvw hwv
    (ActiveRoundActions.coordinator p.two_le_m) j.1
  have hbasepos : 0 < base := by
    dsimp [base]
    exact CanonicalRecordingSlice.deterministicOwnedGateRawProbability_pos
      p.two_le_m p.m_lt_K (ActiveRoundActions.coordinator p.two_le_m)
  have hrawEq : raw = base * qGamma p eta heta heta_le v w hv hw hvw hwv
      (assignmentSlowSet p a) j := by
    dsimp [raw, base]
    exact fastCoordinator_rawGateMass_eq p eta heta heta_le v w hv hw hvw hwv
      a s hmissing j
  have hrawpos : 0 < raw := by
    exact (CanonicalRecordingRates.xi_pos p heta v j.1).trans_le
      (fastCoordinator_rawGateMass_ge_xi p eta heta heta_le v w hv hw hvw hwv
        a s hmissing j)
  have hqpos := CanonicalFastSampling.qGamma_pos p heta heta_le v w hv hw hvw
    hwv (assignmentSlowSet p a) j
  let threshold := CanonicalRecordingRates.xi p eta v j.1 / raw
  have hthreshold_mem : threshold ∈ Set.Icc 0 1 := by
    dsimp [threshold, raw]
    exact fastCoordinator_thinningThreshold_mem_Icc p eta heta heta_le v w hv hw
      hvw hwv a s hmissing j
  have hjoint := deterministicGate_fastArm_joint_measure p eta heta heta_le
    v w hv hw hvw hwv a (ActiveRoundActions.coordinator p.two_le_m) j threshold
    hthreshold_mem.1 hthreshold_mem.2
  have hA : 0 ≤ base * threshold := mul_nonneg hbasepos.le hthreshold_mem.1
  have hjoint' :
      (ContinuousControlSlice.sliceLaw p.m p.K)
        {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
            p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
            (ActiveRoundActions.coordinator p.two_le_m) j.1 threshold x ∧
          fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} =
        ENNReal.ofReal (base * threshold) *
          ENNReal.ofReal (qGamma p eta heta heta_le v w hv hw hvw hwv
            (assignmentSlowSet p a) j) := by
    simpa [base, CanonicalRecordingSlice.deterministicOwnedGateRawProbability]
      using hjoint
  rw [← ENNReal.ofReal_mul hA] at hjoint'
  have hcancel : (base * threshold) *
      qGamma p eta heta heta_le v w hv hw hvw hwv (assignmentSlowSet p a) j =
      xi p eta v j.1 := by
    dsimp [threshold]
    rw [hrawEq]
    field_simp [ne_of_gt hbasepos, ne_of_gt hqpos]
  rw [hcancel] at hjoint'
  simpa [threshold, raw, thinningThreshold] using hjoint'

/-- On a no-missing-confirmations live round, the fast coordinator's map atom
is exactly its deterministic source/mask/thin gate intersected with the
actual reserved-coordinate fast draw. -/
theorem recordingMap_live_fast_event_eq
    (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (s : ActiveRoundActions.Snapshot a) (hmissing : s.missing = ∅)
    (j : CanonicalFastSampling.FastArm (assignmentSlowSet p a)) :
    {x | recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv x =
        some j.1} =
    {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
        p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j.1
        (thinningThreshold p (.live a s) eta heta heta_le v w hv hw hvw hwv
          (ActiveRoundActions.coordinator p.two_le_m) j.1) x ∧
      fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j} := by
  have houtside : j.1 ∉ Finset.univ.image a.assigned := by
    have hj : j.1 ∈ Finset.univ \ (Finset.univ.image a.assigned) := j.2
    exact (Finset.mem_sdiff.mp hj).2
  have howner : owns p (.live a s) (ActiveRoundActions.coordinator p.two_le_m) j.1 := by
    simpa only [owns, dite_true] using houtside
  rw [recordingMap_owner_event_eq p (.live a s) eta heta heta_le v w hv hw hvw hwv
    (ActiveRoundActions.coordinator p.two_le_m) j.1 howner]
  ext x
  have hfast : dataAction p (.live a s) eta heta heta_le v w hv hw hvw hwv x
        (ActiveRoundActions.coordinator p.two_le_m) = j.1 ↔
      fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x = j := by
    simp only [dataAction, dite_true, hmissing, fastArmDraw, Subtype.ext_iff]
  simp only [Set.mem_ofPred_eq, deterministicOwnedRecordingGate, hfast]
  tauto

/-- An owner that takes its public pilot has exactly the canonical arm atom.
The action and owner are exposed as hypotheses so callers must discharge them
from the supplied regime and snapshot. -/
theorem recordingMap_pilot_atom_mass
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (i : Fin p.m) (j : Fin p.K)
    (howner : owns p regime i j)
    (haction : ∀ x, dataAction p regime eta heta heta_le v w hv hw hvw hwv x i =
      PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) i x)
    (hprob : actionProbability p regime eta heta heta_le v w hv hw hvw hwv i j =
      1 / (p.K : ℝ)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      ENNReal.ofReal (xi p eta v j) := by
  rw [recordingMap_pilot_event_eq p regime eta heta heta_le v w hv hw hvw hwv
    i j howner haction hprob]
  exact CanonicalRecordingSlice.canonical_pilotRecordingGate_mass p heta heta_le
    v hv i j

/-- A deterministic owner has exactly the canonical arm atom when its fixed
action probability is one. -/
theorem recordingMap_fixed_atom_mass
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (i : Fin p.m) (j : Fin p.K)
    (howner : owns p regime i j)
    (haction : ∀ x, dataAction p regime eta heta heta_le v w hv hw hvw hwv x i = j)
    (hprob : actionProbability p regime eta heta heta_le v w hv hw hvw hwv i j = 1) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      ENNReal.ofReal (xi p eta v j) := by
  rw [recordingMap_fixed_event_eq p regime eta heta heta_le v w hv hw hvw hwv
    i j howner haction hprob]
  exact CanonicalRecordingSlice.canonical_deterministicOwnedRecordingGate_mass
    p heta heta_le v hv i j

/-- Under a fixed supplied source regime, every active arm fiber has exactly
its canonical rate. The exhaustive cases follow the selected owner's actual
pilot, fixed assignment, or reserved-coordinate fast sampler. -/
theorem recordingMap_atom_mass
    (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (j : Fin p.K) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      ENNReal.ofReal (xi p eta v j) := by
  classical
  let i := ownerSource p regime j
  have howner : owns p regime i j := owns_ownerSource p regime j
  cases regime with
  | collection =>
      have hi : i = ActiveRoundActions.coordinator p.two_le_m := by
        simpa [owns] using howner
      subst i
      apply recordingMap_pilot_atom_mass p .collection eta heta heta_le v w hv hw
        hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j (by simp [owns])
      · intro x
        rfl
      · simp [actionProbability]
  | live a s =>
      by_cases hcoord : i = ActiveRoundActions.coordinator p.two_le_m
      · have houtside : j ∉ Finset.univ.image a.assigned := by
          simpa [owns, hcoord] using howner
        by_cases hmissing : s.missing = ∅
        · let fj : CanonicalFastSampling.FastArm (assignmentSlowSet p a) :=
            ⟨j, by
              have hj : j ∈ fastArmFinset (assignmentSlowSet p a) := by
                simpa [CanonicalFastSampling.fastArmFinset, assignmentSlowSet] using houtside
              exact hj⟩
          change (ContinuousControlSlice.sliceLaw p.m p.K)
            {x | recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv x =
              some fj.1} = ENNReal.ofReal (xi p eta v fj.1)
          rw [recordingMap_live_fast_event_eq p eta heta heta_le v w hv hw
            hvw hwv a s hmissing fj]
          exact fastCoordinator_recordingGate_mass p eta heta heta_le
            v w hv hw hvw hwv a s hmissing fj
        · have hpilot : ∀ x, dataAction p (.live a s) eta heta heta_le
              v w hv hw hvw hwv x (ActiveRoundActions.coordinator p.two_le_m) =
                PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
                  (ActiveRoundActions.coordinator p.two_le_m) x := by
              intro x
              simp [dataAction, hmissing]
          have hprob : actionProbability p (.live a s) eta heta heta_le
              v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j =
                1 / (p.K : ℝ) := by
            simp [actionProbability, hmissing]
          exact recordingMap_pilot_atom_mass p (.live a s) eta heta heta_le
            v w hv hw hvw hwv (ActiveRoundActions.coordinator p.two_le_m) j
            (by simpa [owns, hcoord] using howner) hpilot hprob
      · have hsource : i = PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActiveRoundActions.followerIndex p.two_le_m i hcoord) :=
          (ActiveRoundActions.followerPlayer_followerIndex p.two_le_m i hcoord).symm
        let r := ActiveRoundActions.followerIndex p.two_le_m i hcoord
        have hrarm : j = a.assigned r := by
          simpa [owns, hcoord, r] using howner
        rw [hsource] at howner
        by_cases hunoccupied : s.status r = .unoccupied
        · have howner' : owns p (.live a s)
              (PublicDiscreteDraws.followerPlayer p.two_le_m r) j := by
            simpa [owns, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r] using hrarm
          have hpilot : ∀ x, dataAction p (.live a s) eta heta heta_le
              v w hv hw hvw hwv x (PublicDiscreteDraws.followerPlayer p.two_le_m r) =
                PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m r) x := by
            intro x
            simp [dataAction, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r, hunoccupied]
          have hprob : actionProbability p (.live a s) eta heta heta_le
              v w hv hw hvw hwv (PublicDiscreteDraws.followerPlayer p.two_le_m r) j =
                1 / (p.K : ℝ) := by
            simp [actionProbability, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r, hunoccupied]
          exact recordingMap_pilot_atom_mass p (.live a s) eta heta heta_le
            v w hv hw hvw hwv (PublicDiscreteDraws.followerPlayer p.two_le_m r)
            j howner' hpilot hprob
        · have howner' : owns p (.live a s)
              (PublicDiscreteDraws.followerPlayer p.two_le_m r) j := by
            simpa [owns, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r] using hrarm
          have hfixed : ∀ x, dataAction p (.live a s) eta heta heta_le
              v w hv hw hvw hwv x (PublicDiscreteDraws.followerPlayer p.two_le_m r) = j := by
            intro x
            simp [dataAction, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r, hunoccupied, hrarm]
          have hprob : actionProbability p (.live a s) eta heta heta_le
              v w hv hw hvw hwv (PublicDiscreteDraws.followerPlayer p.two_le_m r) j = 1 := by
            simp [actionProbability, ActiveRoundActions.followerPlayer_ne_coordinator,
              ActiveRoundActions.followerIndex_followerPlayer, r, hunoccupied, hrarm]
          exact recordingMap_fixed_atom_mass p (.live a s) eta heta heta_le
            v w hv hw hvw hwv (PublicDiscreteDraws.followerPlayer p.two_le_m r)
            j howner' hfixed hprob

/-- The existing logical rate carrier instantiated with the literal canonical
rates. Probability validity is derived from the source learning-rate cap. -/
def recordingRates (p : Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) :
    RecordedRoundMoments.RecordingRates p.K :=
  ⟨xi p eta v, xi_pos p heta v, sum_xi_le_one p heta heta_le v hv⟩

section OutcomeLaw

variable (p : Parameters) (regime : Regime p) (eta : ℝ) (heta : 0 < eta)
  (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
  (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
  (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)

/-- Borel measurability of each actual DATA action, with the snapshot fixed. -/
theorem measurable_dataAction (i : Fin p.m) :
    Measurable (fun x => dataAction p regime eta heta heta_le v w hv hw hvw hwv x i) := by
  classical
  cases regime with
  | collection => exact PublicDiscreteDraws.measurable_pilotDraw _ i
  | live a s =>
      by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
      · by_cases hm : s.missing = ∅
        · simpa only [dataAction, dite_eq_left hi, dite_eq_left hm, fastArmDraw] using
            (measurable_fastArmDraw p eta heta heta_le v w hv hw hvw hwv a).subtype_val
        · simpa only [dataAction, dite_eq_left hi, dite_eq_right hm] using
            (PublicDiscreteDraws.measurable_pilotDraw (K := p.K) _ i)
      · by_cases hs : s.status (ActiveRoundActions.followerIndex p.two_le_m i hi) = .unoccupied
        · simpa only [dataAction, dite_eq_right hi, dite_eq_left hs] using
            (PublicDiscreteDraws.measurable_pilotDraw (K := p.K) _ i)
        · simpa only [dataAction, dite_eq_right hi, dite_eq_right hs] using
            (measurable_const : Measurable (fun _ : CanonicalRecordingSlice.Slice p.m p.K =>
              a.assigned (ActiveRoundActions.followerIndex p.two_le_m i hi)))

/-- Each enabled arm fiber is Borel, from its unique true owner and the literal
DATA/source/action/mask/inclusive-thinning tests. -/
theorem measurableSet_recordingMap_some (j : Fin p.K) :
    MeasurableSet {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} := by
  classical
  let i := ownerSource p regime j
  let source := fun x : CanonicalRecordingSlice.Slice p.m p.K => recorderSourceFromScalar p.two_le_m
    (coordinate Label.rec x)
  have hsource : Measurable source := by
    have heq : source = recorderSourceDraw p.two_le_m p.m_lt_K := by
      funext x
      exact recorderSourceFromScalar_coordinate p.two_le_m p.m_lt_K x
    rw [heq]
    exact measurable_recorderSourceDraw p.two_le_m p.m_lt_K
  have heq : {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j} =
      {x | slotDraw x = dataSlot} ∩ {x | source x = i} ∩
      {x | dataAction p regime eta heta heta_le v w hv hw hvw hwv x i = j} ∩
      {x | recordingMask (ConstructorDimensions.K_pos p) i j x} ∩
      {x | (coordinate Label.thin x).val ≤
        thinningThreshold p regime eta heta heta_le v w hv hw hvw hwv i j} := by
    ext x
    rw [Set.mem_ofPred_eq, recordingMap_some_iff]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hslot, hact, hown, hmask, hthin⟩
      have hi : source x = i := owns_unique p regime j _ _ hown (owns_ownerSource p regime j)
      have hi' : recorderSourceFromScalar p.two_le_m (coordinate Label.rec x) = i := hi
      exact ⟨⟨⟨⟨hslot, hi⟩, by simpa only [hi'] using hact⟩,
        by simpa only [hi'] using hmask⟩, by simpa only [hi'] using hthin⟩
    · rintro ⟨⟨⟨⟨hslot, hi⟩, hact⟩, hmask⟩, hthin⟩
      change recorderSourceFromScalar p.two_le_m (coordinate Label.rec x) = i at hi
      exact ⟨hslot, by simpa only [hi] using hact,
        by simpa only [hi] using owns_ownerSource p regime j,
        by simpa only [hi] using hmask, by simpa only [hi] using hthin⟩
  rw [heq]
  exact (((((measurableSet_singleton dataSlot).preimage measurable_slotDraw).inter
    ((measurableSet_singleton i).preimage hsource)).inter
    ((measurableSet_singleton j).preimage
      (measurable_dataAction p regime eta heta heta_le v w hv hw hvw hwv i))).inter
    (measurableSet_recordingMask p.two_le_m (ConstructorDimensions.K_pos p) i j)).inter
    (measurableSet_le ((measurable_coordinate Label.thin).subtype_val) measurable_const)

/-- Bottom is precisely the complement of all arm fibers. -/
theorem recordingMap_none_event_eq :
    {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = none} =
      (⋃ j : Fin p.K, {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j})ᶜ := by
  ext x
  cases h : recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x <;> simp [h]

/-- Borel measurability of the complete arm-or-bottom recorder. -/
theorem measurable_recordingMap (enabled : Bool) :
    Measurable (recordingMap p regime enabled eta heta heta_le v w hv hw hvw hwv) := by
  cases enabled with
  | false =>
      have heq : recordingMap p regime false eta heta heta_le v w hv hw hvw hwv =
          fun _ => none := funext (recordingMap_disabled p regime eta heta heta_le v w hv hw hvw hwv)
      rw [heq]
      exact measurable_const
  | true =>
      apply measurable_to_countable'
      intro o
      cases o with
      | some j => exact measurableSet_recordingMap_some p regime eta heta heta_le v w hv hw hvw hwv j
      | none =>
          change MeasurableSet {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = none}
          rw [recordingMap_none_event_eq]
          exact (MeasurableSet.iUnion (measurableSet_recordingMap_some p regime eta heta heta_le v w hv hw hvw hwv)).compl

/-- The exact bottom mass, derived from the disjoint actual arm fibers.
Source: `04_slow_fast_learner.tex:143-148`. -/
theorem recordingMap_none_mass :
    (sliceLaw p.m p.K) {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = none} =
      ENNReal.ofReal (1 - ∑ j, xi p eta v j) := by
  rw [recordingMap_none_event_eq, prob_compl_eq_one_sub
    (MeasurableSet.iUnion (measurableSet_recordingMap_some p regime eta heta heta_le v w hv hw hvw hwv))]
  have hd : Pairwise (Function.onFun Disjoint
      (fun j : Fin p.K => {x | recordingMap p regime true eta heta heta_le v w hv hw hvw hwv x = some j})) := by
    intro j k hjk
    change Disjoint _ _
    rw [Set.disjoint_left]
    intro x hxj hxk
    exact hjk (Option.some.inj (hxj.symm.trans hxk))
  rw [measure_iUnion hd (measurableSet_recordingMap_some p regime eta heta heta_le v w hv hw hvw hwv),
    tsum_fintype]
  simp only [recordingMap_atom_mass p regime eta heta heta_le v w hv hw hvw hwv]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (xi_pos p heta v j).le),
    ENNReal.ofReal_sub 1 (Finset.sum_nonneg (fun j _ => (xi_pos p heta v j).le)), ENNReal.ofReal_one]

/-- The actual enabled recorder pushes the continuous product slice to the
accepted logical recording PMF with the literal canonical rates. -/
theorem map_recordingMap :
    (sliceLaw p.m p.K).map (recordingMap p regime true eta heta heta_le v w hv hw hvw hwv) =
      (RecordedRoundMoments.recordingOutcomePMF (recordingRates p eta heta heta_le v hv)).toMeasure := by
  apply Measure.ext_of_singleton
  intro o
  rw [Measure.map_apply (measurable_recordingMap p regime eta heta heta_le v w hv hw hvw hwv true)
      (measurableSet_singleton o), PMF.toMeasure_apply_singleton _ o (measurableSet_singleton o)]
  cases o with
  | some j => simpa only [Set.preimage, Set.mem_singleton_iff, RecordedRoundMoments.recordingOutcomePMF_some, recordingRates] using
      recordingMap_atom_mass p regime eta heta heta_le v w hv hw hvw hwv j
  | none => simpa only [Set.preimage, Set.mem_singleton_iff, RecordedRoundMoments.recordingOutcomePMF_none, recordingRates] using
      recordingMap_none_mass p regime eta heta heta_le v w hv hw hvw hwv

end OutcomeLaw

/-- Incoming control only: an already overflowed state or a frozen coordinator
cannot enable recording. The outgoing overflow flag is deliberately absent. -/
def recordingEnabled (scheduleEnabled incomingOverflow : Bool) (sigma t g : ℕ) : Bool :=
  scheduleEnabled && !incomingOverflow && !decide (0 < sigma ∧ g ≤ t)

/-- Either incoming overflow or frozen status disables the recorder. -/
theorem recordingEnabled_eq_false (scheduleEnabled incomingOverflow : Bool) (sigma t g : ℕ)
    (h : incomingOverflow = true ∨ (0 < sigma ∧ g ≤ t)) :
    recordingEnabled scheduleEnabled incomingOverflow sigma t g = false := by
  rcases h with h | h <;> simp only [recordingEnabled, h, and_self, decide_true, Bool.not_true,
    Bool.and_false, Bool.false_and]

/-- The logical increment of a recorded arm, before any outgoing overflow test.
This definition alone makes no physical-feedback assertion. -/
def recordedIncrement (p : Parameters) (eta : ℝ) (v reward : Fin p.K → ℝ) : Option (Fin p.K) → ℕ
  | none => 0
  | some j => Nat.floor ((ConstructorDimensions.D p : ℝ) * eta * reward j / xi p eta v j)

/-- A disabled snapshot emits bottom and has zero logical raw increment. -/
theorem disabled_recording_zero (p : Parameters) (regime : Regime p)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w reward : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j) (x : CanonicalRecordingSlice.Slice p.m p.K) :
    recordingMap p regime false eta heta heta_le v w hv hw hvw hwv x = none ∧
      recordedIncrement p eta v reward
        (recordingMap p regime false eta heta heta_le v w hv hw hvw hwv x) = 0 := by
  rw [recordingMap_disabled]
  exact ⟨rfl, rfl⟩

/-- Incoming overflow or the literal `sigma > 0, t ≥ g` freeze test makes
both the map and its logical increment inactive. -/
theorem incoming_disabled_recording_zero (p : Parameters) (regime : Regime p)
    (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v w reward : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (scheduleEnabled incomingOverflow : Bool) (sigma t g : ℕ)
    (h : incomingOverflow = true ∨ (0 < sigma ∧ g ≤ t)) (x : CanonicalRecordingSlice.Slice p.m p.K) :
    let enabled := recordingEnabled scheduleEnabled incomingOverflow sigma t g
    recordingMap p regime enabled eta heta heta_le v w hv hw hvw hwv x = none ∧
      recordedIncrement p eta v reward
        (recordingMap p regime enabled eta heta heta_le v w hv hw hvw hwv x) = 0 := by
  dsimp only
  rw [recordingEnabled_eq_false scheduleEnabled incomingOverflow sigma t g h]
  exact disabled_recording_zero p regime eta heta heta_le v w reward hv hw hvw hwv x

section PhysicalCollection

variable (p : Parameters) (eta : ℝ) (heta : 0 < eta)
  (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
  (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
  (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)

/-- During collection all players pilot. The recorder mask makes the recorded
owner collision free in the accepted physical environment. -/
theorem collection_recording_feedback (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) (j : Fin p.K)
    (hrecord : recordingMap p .collection true eta heta heta_le v w hv hw hvw hwv x = some j) :
    FiniteBanditModel.playerFeedback (fun i => pilotDraw (ConstructorDimensions.K_pos p) i x)
      row.val (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) = row.val j := by
  rcases (recordingMap_some_iff p .collection eta heta heta_le v w hv hw hvw hwv x j).mp
    hrecord with ⟨_, haction, _, hmask, _⟩
  have ha : pilotDraw (ConstructorDimensions.K_pos p)
      (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) x = j := haction
  have hfree : FiniteBanditModel.collisionFreeFor
      (fun i => pilotDraw (ConstructorDimensions.K_pos p) i x)
      (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) := by
    intro k hk
    change pilotDraw (ConstructorDimensions.K_pos p) k x ≠
      pilotDraw (ConstructorDimensions.K_pos p)
        (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) x
    rw [ha]
    exact hmask k hk
  simp only [FiniteBanditModel.playerFeedback, ite_eq_left hfree, ha]

/-- Collection's physical increment uses the actual environment observation. -/
def collectionPhysicalIncrement (enabled : Bool) (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : ℕ :=
  match recordingMap p .collection enabled eta heta heta_le v w hv hw hvw hwv x with
  | none => 0
  | some j => Nat.floor ((ConstructorDimensions.D p : ℝ) * eta *
      FiniteBanditModel.playerFeedback (fun i => pilotDraw (ConstructorDimensions.K_pos p) i x)
        row.val (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) / xi p eta v j)

/-- Collection's physical raw increment has the required exact floor. -/
theorem collectionPhysicalIncrement_eq_floor (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) (j : Fin p.K)
    (hrecord : recordingMap p .collection true eta heta heta_le v w hv hw hvw hwv x = some j) :
    collectionPhysicalIncrement p eta heta heta_le v w hv hw hvw hwv true x row =
      Nat.floor ((ConstructorDimensions.D p : ℝ) * eta * row.val j / xi p eta v j) := by
  rw [collectionPhysicalIncrement, hrecord,
    collection_recording_feedback p eta heta heta_le v w hv hw hvw hwv x row j hrecord]

/-- Disabled collection recording has zero physical arrival. -/
theorem collectionPhysicalIncrement_disabled (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) :
    collectionPhysicalIncrement p eta heta heta_le v w hv hw hvw hwv false x row = 0 := by
  simp only [collectionPhysicalIncrement, recordingMap_disabled]

end PhysicalCollection

section PhysicalLive

variable (p : Parameters) (eta : ℝ) (heta : 0 < eta)
  (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
  (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
  (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
  (a : ActiveRoundActions.Assignment p.m p.K) (s : ActiveRoundActions.Snapshot a)
  {B : ℕ} (down up : ActiveRoundActions.HashedWord B)

/-- An actual one-slice input for the accepted active action/feedback functions.
All DATA-relevant fields, selected follower and tuple use this same slice;
only the supplied DOWN/UP message words are external inputs. No law for those
words or chronological execution is asserted. -/
def liveRoundInput (x : CanonicalRecordingSlice.Slice p.m p.K) :
    ActiveRoundActions.RoundInput a B where
  slot := slotDraw x
  selected := selectedFollowerDraw p.two_le_m p.m_lt_K x
  tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K x
  pilots := fun i => pilotDraw (ConstructorDimensions.K_pos p) i x
  down := down
  up := up
  fast := (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x).val
  fast_outside := by
    intro i heq
    have hfast := (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x).property
    have hnot : (fastArmDraw p eta heta heta_le v w hv hw hvw hwv a x).val ∉
        Finset.univ.image a.assigned := (Finset.mem_sdiff.mp hfast).2
    exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩)

/-- On DATA, the literal action map agrees with the accepted physical actions
for the actual slice input, for every player and every supplied message word. -/
theorem live_dataAction_eq_actions (x : CanonicalRecordingSlice.Slice p.m p.K)
    (hslot : slotDraw x = dataSlot) (i : Fin p.m) :
    dataAction p (.live a s) eta heta heta_le v w hv hw hvw hwv x i =
      ActiveRoundActions.actions p.two_le_m s
        (liveRoundInput p eta heta heta_le v w hv hw hvw hwv a down up x) i := by
  classical
  by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
  · subst i
    by_cases hm : s.missing = ∅
    · simp [dataAction, ActiveRoundActions.actions, ActiveRoundActions.coordinatorAction,
        liveRoundInput, fastArmDraw, hm]
    · simp [dataAction, ActiveRoundActions.actions, ActiveRoundActions.coordinatorAction,
        liveRoundInput, hm, hslot]
  · by_cases hs : s.status (ActiveRoundActions.followerIndex p.two_le_m i hi) = .unoccupied
    · simp [dataAction, ActiveRoundActions.actions, ActiveRoundActions.followerAction,
        liveRoundInput, hi, hs, hslot, ActiveRoundActions.followerPlayer_followerIndex]
    · simp [dataAction, ActiveRoundActions.actions, ActiveRoundActions.followerAction,
        liveRoundInput, hi, hs, hslot]

/-- Recording on a live snapshot implies the actual owner receives the fixed
reward, by the accepted physical collision bridge. This includes an unoccupied
follower tested against its true assignment before decoding.
Source: `05_binary_transport.tex:402-415`. -/
theorem live_recording_feedback (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) (j : Fin p.K)
    (hrecord : recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv x = some j) :
    ActiveRoundActions.feedback p.two_le_m s
      (liveRoundInput p eta heta heta_le v w hv hw hvw hwv a down up x) row
      (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) = row.val j := by
  rcases (recordingMap_some_iff p (.live a s) eta heta heta_le v w hv hw hvw hwv x j).mp
    hrecord with ⟨hslot, haction, howner, hmask, _⟩
  let r := liveRoundInput p eta heta heta_le v w hv hw hvw hwv a down up x
  let i := recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)
  change owns p (.live a s) i j at howner
  have hmask' : ∀ ell, ell ≠ i → r.pilots ell ≠ j := hmask
  have hslot' : r.slot = dataSlot := hslot
  have haction' : ActiveRoundActions.actions p.two_le_m s r i = j :=
    (live_dataAction_eq_actions p eta heta heta_le v w hv hw hvw hwv a s down up x hslot i).symm.trans haction
  by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
  · have houtside : ∀ k, j ≠ a.assigned k := by
      intro k heq
      have hnot : j ∉ Finset.univ.image a.assigned := by simpa only [owns, dite_eq_left hi] using howner
      exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq.symm⟩)
    change ActiveRoundActions.feedback p.two_le_m s r row i = row.val j
    rw [hi] at haction' ⊢
    exact coordinator_data_recording_correct p.two_le_m a s r row j hslot' houtside
      haction' (by simpa only [hi] using hmask')
  · let k := ActiveRoundActions.followerIndex p.two_le_m i hi
    have hk : followerPlayer p.two_le_m k = i :=
      ActiveRoundActions.followerPlayer_followerIndex p.two_le_m i hi
    have hj : j = a.assigned k := by simpa only [owns, dite_eq_right hi] using howner
    change ActiveRoundActions.feedback p.two_le_m s r row i = row.val j
    rw [← hk] at haction' ⊢
    rw [hj] at haction' ⊢
    exact follower_data_recording_correct p.two_le_m a s r row k hslot' haction'
      (by simpa only [hk, ← hj] using hmask')

/-- Physical raw increment: the numerator is the accepted environment's owner
feedback, not a reward substituted by definition. No outgoing-overflow test
can remove this round's increment. -/
def livePhysicalIncrement (enabled : Bool) (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : ℕ :=
  match recordingMap p (.live a s) enabled eta heta heta_le v w hv hw hvw hwv x with
  | none => 0
  | some j => Nat.floor ((ConstructorDimensions.D p : ℝ) * eta *
      ActiveRoundActions.feedback p.two_le_m s
        (liveRoundInput p eta heta heta_le v w hv hw hvw hwv a down up x) row
        (recorderSourceFromScalar p.two_le_m (coordinate Label.rec x)) / xi p eta v j)

/-- The physical live increment has the manuscript's exact floor on a recorded
arm, with feedback equality proved through collision freedom. -/
theorem livePhysicalIncrement_eq_floor (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) (j : Fin p.K)
    (hrecord : recordingMap p (.live a s) true eta heta heta_le v w hv hw hvw hwv x = some j) :
    livePhysicalIncrement p eta heta heta_le v w hv hw hvw hwv a s down up true x row =
      Nat.floor ((ConstructorDimensions.D p : ℝ) * eta * row.val j / xi p eta v j) := by
  rw [livePhysicalIncrement, hrecord,
    live_recording_feedback p eta heta heta_le v w hv hw hvw hwv a s down up x row j hrecord]

/-- Disabled physical recording has zero arrival. -/
theorem livePhysicalIncrement_disabled (x : CanonicalRecordingSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) :
    livePhysicalIncrement p eta heta heta_le v w hv hw hvw hwv a s down up false x row = 0 := by
  simp only [livePhysicalIncrement, recordingMap_disabled]

end PhysicalLive

end Bandits.Support.SnapshotRecordingKernel

end
