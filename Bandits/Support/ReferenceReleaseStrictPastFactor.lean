/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSReferenceActivePhysicalStepMeasurability.
-/
module

public import Bandits.Support.ReferenceRetainedReleasePhaseObservation
public import Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance

/-!
# A strict-past factor of the actual finite release observation

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

Normalization is an internal readout operation on the existing actual launch
stratum. It replaces selected learning controls at and after the incoming
coordinate by one fixed baseline. All other rows, forwards, identification
coordinates and original private arrays remain present. Its comap is not an
identification of the manuscript filtration, release stopping time, freshness
or conditional service law. The later consumer is
`ReferenceSourceReleaseStoppedSupport`, after common-queue, all-decoder/awaited
and complete-history/filtration producers; generic waiting remains later.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceReleaseStrictPastFactor

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

open ReferenceActivePhysicalStepMeasurability
  (StateCode CoordinatorCode LiveDiscrete decodeState encodeState encodeCoordinator decodeCoordinator)
open ReferenceRetainedReleasePhaseObservation (Payload)
open FollowerPrepareJointMeasurability
  (IncomingConfiguration LocalMemoryCode incomingOfLocalConfiguration localConfigurationOfIncoming
    incomingConfigurationToSum measurable_incomingConfigurationToSum)
open FollowerObservationStageMeasurabilityRepair
  (CarriedState FollowerCarryIndex carriedStateOfState reconstructCarriedState)
open FollowerDownJointMeasurability
  (bufferFromSkeletonAndScalars bufferSkeletonCode bufferScalarsCode)
open FollowerDownMeasurability (SavedScalarFamily followerStateCode followerStateOfCode)

private theorem measurable_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) :
    Measurable f := by
  intro u hu
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ u}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hu

private theorem measurable_sigma_mk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ a

/-- Re-encoding the original carried-state decoder preserves the saved real
fiber. Only the countable discrete register code can be normalized. -/
private theorem measurable_recodeCarry (rate : RateInput p) :
    Measurable (fun c : CarriedState p rate =>
      carriedStateOfState rate (reconstructCarriedState c.1 c.2)) := by
  apply measurable_sigma_sections
  intro index
  let index' : FollowerCarryIndex p rate :=
    (followerStateCode rate (followerStateOfCode rate index.1 []), index.2)
  have heq : (fun values : SavedScalarFamily index.2.1 =>
      carriedStateOfState rate (reconstructCarriedState index values)) =
      fun values => (⟨index', values⟩ : CarriedState p rate) := by
    funext values
    rcases index with ⟨registers, n, skeleton⟩
    simp only [carriedStateOfState, reconstructCarriedState, followerStateCode,
      followerStateOfCode, bufferFromSkeletonAndScalars,
      index', List.length_ofFn, Sigma.mk.inj_iff, Prod.mk.injEq, true_and]
    constructor
    · apply (Fin.heq_fun_iff (by simp)).mpr
      intro i
      simp [bufferSkeletonCode]
    · apply (Fin.heq_fun_iff (by simp)).mpr
      intro i
      simp [bufferScalarsCode]
  rw [heq]
  exact measurable_sigma_mk index'

private theorem measurable_recodeIncoming (rate : RateInput p) :
    Measurable (fun incoming : IncomingConfiguration p rate =>
      incomingOfLocalConfiguration rate (localConfigurationOfIncoming rate incoming)) := by
  apply measurable_comap_iff.mpr
  let recode : Unit ⊕ (CarriedState p rate × LocalMemoryCode p) →
      Unit ⊕ (CarriedState p rate × LocalMemoryCode p) :=
    Sum.elim (fun _ => .inl ()) (fun z => .inr
      (carriedStateOfState rate (reconstructCarriedState z.1.1 z.1.2), z.2))
  have hr : Measurable recode :=
    measurable_const.sumElim (measurable_inr.comp
      (((measurable_recodeCarry rate).comp measurable_fst).prodMk measurable_snd))
  have h := hr.comp (measurable_incomingConfigurationToSum rate)
  convert h using 1
  funext incoming
  cases incoming with
  | none => rfl
  | some z =>
      simp only [Function.comp_apply, incomingConfigurationToSum, recode,
        localConfigurationOfIncoming, incomingOfLocalConfiguration,
        FollowerLifecycleMeasurability.localMemoryCodeOfCode, Sum.elim_inr]

/-- The actual decoder is measurable on the full canonical StateCode carrier,
including noncanonical padded live coordinates and all saved-real fibers. -/
theorem measurable_decodeState (rate : RateInput p) :
    Measurable (decodeState (p := p) (rate := rate)) := by
  apply measurable_comap_iff.mpr
  let pad : Finset (Fin p.K) × LiveDiscrete p → LiveDiscrete p := fun z =>
    { z.2 with
      scores := fun a => if a ∈ Finset.univ \ z.1 then z.2.scores a else 0
      queues := fun a => if a ∈ Finset.univ \ z.1 then z.2.queues a else 0
      previousServices := fun a =>
        if a ∈ Finset.univ \ z.1 then z.2.previousServices a else 0 }
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hslow : Measurable (fun payload : Payload p rate => payload.slowSet.val) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))
  have hpad : Measurable pad := measurable_of_countable _
  have hlive : Measurable (fun z : Payload p rate × LiveDiscrete p =>
      (z.1, pad (z.1.slowSet.val, z.2))) :=
    measurable_fst.prodMk (hpad.comp ((hslow.comp measurable_fst).prodMk measurable_snd))
  have hcoord : Measurable (fun code : CoordinatorCode p rate =>
      encodeCoordinator (decodeCoordinator code)) := by
    have hsum : Measurable (fun code : CoordinatorCode p rate =>
        match code with
        | .inl _ => (Sum.inl () : CoordinatorCode p rate)
        | .inr (.inl z) => Sum.inr (Sum.inl (z.1, pad (z.1.slowSet.val, z.2)))
        | .inr (.inr tail) => Sum.inr (Sum.inr tail)) :=
      measurable_const.sumElim (measurable_inr.comp
        ((measurable_inl.comp hlive).sumElim (measurable_inr.comp measurable_id)))
    convert hsum using 1
    funext code
    cases code with
    | inl u => rfl
    | inr tail => cases tail with
      | inl z => rfl
      | inr z => cases z <;> rfl
  have hfollowers : Measurable (fun code : StateCode p rate => fun i =>
      incomingOfLocalConfiguration rate
        (localConfigurationOfIncoming rate (code.2.2.2 i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_recodeIncoming rate).comp
      ((measurable_pi_apply i).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (hcoord.comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hfollowers))

/-- Actual whole-payload selection is Borel, with its original continuous
anchor and complete queue vector. No payload from another time is substituted. -/
theorem measurable_localStoredPayload (rate : RateInput p) :
    Measurable (ReferenceRetainedReleasePhaseObservation.localStoredPayload (p := p) (rate := rate)) := by
  have hsome : Measurable (some : Payload p rate → Option (Payload p rate)) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hcode : Measurable (fun code : CoordinatorCode p rate =>
      match code with
      | .inl _ => (none : Option (Payload p rate))
      | .inr (.inl z) => some z.1
      | .inr (.inr (.inl z)) => some z.1
      | .inr (.inr (.inr _)) => none) :=
    measurable_const.sumElim ((hsome.comp measurable_fst).sumElim
      ((hsome.comp measurable_fst).sumElim measurable_const))
  convert hcode.comp measurable_fst using 1
  funext code
  rcases code with ⟨coordinator, rest⟩
  cases coordinator with
  | inl u => rfl
  | inr tail => cases tail with
    | inl z => rfl
    | inr tail => cases tail <;> rfl

private theorem measurable_option_pending (rate : RateInput p) (b : ℕ)
    (time : Fin p.T) :
    Measurable (fun z : Option (Payload p rate) × StateCode p rate =>
      match z.1 with
      | none => (none : Option (Finset (Fin (p.m - 1))))
      | some payload => some (ReferenceRetainedReleasePhaseObservation.localReleasePending rate b payload time
          (decodeState z.2))) := by
  have hp := (ReferenceRetainedReleasePhaseObservation.measurable_localReleasePending rate b time).comp
    (measurable_fst.prodMk ((measurable_decodeState rate).comp measurable_snd))
  have hsome : Measurable (some : Finset (Fin (p.m - 1)) →
      Option (Finset (Fin (p.m - 1)))) := measurable_of_countable _
  have hnone : Measurable (fun _ : PUnit.{1} ×
      StateCode p rate =>
        (none : Option (Finset (Fin (p.m - 1))))) := measurable_const
  have hsum := ((hsome.comp hp).sumElim hnone).comp
    (MeasurableEquiv.sumProdDistrib (Payload p rate) PUnit.{1} (StateCode p rate)).measurable
  have htag : Measurable (fun z : Option (Payload p rate) × StateCode p rate =>
      ((Equiv.optionEquivSumPUnit (Payload p rate)) z.1, z.2)) :=
    ((comap_measurable _).comp measurable_fst).prodMk measurable_snd
  convert hsum.comp htag using 1
  funext z
  rcases z with ⟨payload, code⟩
  cases payload <;> rfl

/-- Joint Borel measurability of O's exact combined entry. The actual full
payload is selected at this same code, then paired with its actual decoder;
the pending producer retains its whole-payload diagonal test. -/
theorem measurable_localReleaseEntry (rate : RateInput p) (b : ℕ) (time : Fin p.T) :
    Measurable (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b time) := by
  have hg := ReferenceRetainedReleasePhaseObservation.measurable_localReleaseGate rate b time
  have hp := (measurable_option_pending rate b time).comp
    ((measurable_localStoredPayload rate).prodMk measurable_id)
  exact hg.prodMk (Measurable.ite (measurableSet_eq_fun hg measurable_const)
    hp measurable_const)

/-- Joint measurability also allows the timestamp and physical time to vary
on their original countable carriers, without changing the state-code space. -/
theorem measurable_localReleaseEntry_joint (rate : RateInput p) :
    Measurable (fun z : (ℕ × Fin p.T) × StateCode p rate =>
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate z.1.1 z.1.2 z.2) := by
  exact measurable_from_prod_countable_right fun bt =>
    measurable_localReleaseEntry rate bt.1 bt.2

open ReferenceGeneratedPrefixSuffixInvariance
open ReferenceGeneratedActivePrefixFactor (splitSource)
open ReferenceFixedTimeSourceControlCoupling (fixedControlSplit)
open ReferenceRetainedReleasePhaseObservation
  (generatedPhaseBefore localReleaseEntry firstLocalReleaseGateRound)

section Launch

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "X" =>
  ReferenceRetainedReleasePhaseObservation.LaunchStart rate rewards C_star C_h q t s hs control0

/-- The original complete source reconstructed from the retained remainder. -/
def launchSource (x : X) : SourceInput p := splitSource q t control0 x.val

theorem launchSource_selected (x : X) :
    ActualInitializationPhysicalStep.selectedRowIndex p
      (launchSource rate rewards C_star C_h q t s hs control0 x) = q := by
  rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t control0 x.val x.property.1

theorem measurable_launchSource :
    Measurable (launchSource rate rewards C_star C_h q t s hs control0) := by
  exact (fixedControlSplit p q t).symm.measurable.comp
    (measurable_const.prodMk measurable_subtype_coe)

/-- Literal internal normalization: replace only the selected learning-control
suffix, including the incoming coordinate, by the fixed whole control. -/
def normalizedSource (x : X) : SourceInput p :=
  replaceSelectedControlSuffix
    (launchSource rate rewards C_star C_h q t s hs control0 x) t (fun _ => control0)

theorem measurable_normalizedSource :
    Measurable (normalizedSource rate rewards C_star C_h q t s hs control0) := by
  let src := launchSource rate rewards C_star C_h q t s hs control0
  have hsrc : Measurable src := measurable_launchSource rate rewards C_star C_h q t s hs control0
  have hrows : Measurable (fun x : X => (src x).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsrc)
  have hrow : Measurable (fun x : X => (src x).1.2 q) :=
    (measurable_pi_apply q).comp hrows
  have hcontrols : Measurable (fun x : X => fun v : Fin p.T =>
      if v.val < t.val then ((src x).1.2 q).2 v else control0) := by
    apply measurable_pi_iff.mpr
    intro v
    by_cases hv : v.val < t.val
    · simpa only [hv, ite_true, Function.comp_def] using
        (measurable_pi_apply v).comp (measurable_snd.comp hrow)
    · simpa only [hv, ite_false] using (measurable_const :
        Measurable (fun _ : X => control0))
  have hnewRows : Measurable (fun x : X =>
      Function.update (src x).1.2 q
        (((src x).1.2 q).1, fun v =>
          if v.val < t.val then ((src x).1.2 q).2 v else control0)) :=
    measurable_update'.comp (hrows.prodMk
      ((measurable_fst.comp hrow).prodMk hcontrols))
  have h := ((measurable_fst.comp (measurable_fst.comp hsrc)).prodMk hnewRows).prodMk
    (measurable_snd.comp hsrc)
  convert h using 1
  funext x
  dsimp only [normalizedSource, replaceSelectedControlSuffix]
  rw [launchSource_selected]
  rfl

/-- These launch facts are produced by actual initialization locality. -/
theorem normalizedSource_launch (x : X) :
    ActualInitializationPhysicalStep.selectedRowIndex p
      (normalizedSource rate rewards C_star C_h q t s hs control0 x) = q ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        (normalizedSource rate rewards C_star C_h q t s hs control0 x)
        rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        (normalizedSource rate rewards C_star C_h q t s hs control0 x)
        rewards C_star C_h rate)).completed = s ∧
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (launchSource rate rewards C_star C_h q t s hs control0 x) rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (normalizedSource rate rewards C_star C_h q t s hs control0 x) rewards C_star C_h := by
  have hbranch := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2
  exact replaceSelectedControlSuffix_preserves_actual_launch rewards C_star C_h q t s hs
    (launchSource rate rewards C_star C_h q t s hs control0 x)
    (launchSource_selected rate rewards C_star C_h q t s hs control0 x)
    (fun _ => control0) hbranch.1 hbranch.2

/-- Reconstruct the normalized member of the SAME inherited actual launch
subtype from its exact fixed-control remainder and the produced launch facts. -/
def normalize (x : X) : X :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0
    (normalizedSource rate rewards C_star C_h q t s hs control0 x)
    (normalizedSource_launch rate rewards C_star C_h q t s hs control0 x).1
    (normalizedSource_launch rate rewards C_star C_h q t s hs control0 x).2.1
    (normalizedSource_launch rate rewards C_star C_h q t s hs control0 x).2.2.1

theorem normalize_val (x : X) :
    (normalize rate rewards C_star C_h q t s hs control0 x).val =
      (fixedControlSplit p q t
        (normalizedSource rate rewards C_star C_h q t s hs control0 x)).2 := rfl

theorem measurable_normalize :
    Measurable (normalize rate rewards C_star C_h q t s hs control0) := by
  exact (measurable_snd.comp ((fixedControlSplit p q t).measurable.comp
    (measurable_normalizedSource rate rewards C_star C_h q t s hs control0))).subtype_mk

/-- Splitting and reconstructing the normalized member recovers the entire
normalized source, not just its state/evidence projections. -/
theorem launchSource_normalize (x : X) :
    launchSource rate rewards C_star C_h q t s hs control0
        (normalize rate rewards C_star C_h q t s hs control0 x) =
      normalizedSource rate rewards C_star C_h q t s hs control0 x := by
  apply (fixedControlSplit p q t).injective
  change fixedControlSplit p q t ((fixedControlSplit p q t).symm
    (control0, (normalize rate rewards C_star C_h q t s hs control0 x).val)) = _
  rw [(fixedControlSplit p q t).apply_symm_apply, normalize_val]
  apply Prod.ext
  · rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
    have h := replaceSelectedControlSuffix_control_from
      (launchSource rate rewards C_star C_h q t s hs control0 x) t t
      (fun _ => control0) (Nat.le_refl _)
    rw [launchSource_selected] at h
    exact h.symm
  · rfl

private theorem replace_suffix_twice (z : SourceInput p) :
    replaceSelectedControlSuffix
        (replaceSelectedControlSuffix z t (fun _ => control0)) t (fun _ => control0) =
      replaceSelectedControlSuffix z t (fun _ => control0) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext row
      by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z
      · subst row
        apply Prod.ext
        · simpa only [replaceSelectedControlSuffix_selected] using
            replaceSelectedControlSuffix_forward
              (replaceSelectedControlSuffix z t (fun _ => control0)) t (fun _ => control0)
        · funext v
          by_cases hv : v.val < t.val
          · simpa only [replaceSelectedControlSuffix_selected] using
              replaceSelectedControlSuffix_control_before
                (replaceSelectedControlSuffix z t (fun _ => control0)) t v
                (fun _ => control0) hv
          · have hv' := Nat.le_of_not_gt hv
            have hleft := replaceSelectedControlSuffix_control_from
              (replaceSelectedControlSuffix z t (fun _ => control0)) t v
              (fun _ => control0) hv'
            have hright := replaceSelectedControlSuffix_control_from z t v
              (fun _ => control0) hv'
            simpa only [replaceSelectedControlSuffix_selected] using hleft.trans hright.symm
      · exact replaceSelectedControlSuffix_otherRow
          (replaceSelectedControlSuffix z t (fun _ => control0)) t (fun _ => control0) row
          (by simpa only [replaceSelectedControlSuffix_selected] using hr)
  · rfl

theorem normalize_idempotent (x : X) :
    normalize rate rewards C_star C_h q t s hs control0
        (normalize rate rewards C_star C_h q t s hs control0 x) =
      normalize rate rewards C_star C_h q t s hs control0 x := by
  apply Subtype.ext
  rw [normalize_val, normalize_val]
  apply congrArg (fun z : SourceInput p => (fixedControlSplit p q t z).2)
  change replaceSelectedControlSuffix
      (launchSource rate rewards C_star C_h q t s hs control0
        (normalize rate rewards C_star C_h q t s hs control0 x)) t (fun _ => control0) = _
  rw [launchSource_normalize]
  exact replace_suffix_twice t control0
    (launchSource rate rewards C_star C_h q t s hs control0 x)

/-- The complete original vector factors through this one normalization for
EVERY replacement of the whole removed current control. -/
theorem generatedPhaseBefore_normalize (x : X) (control : TimeControl p) :
    generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control =
      generatedPhaseBefore rate rewards C_star C_h q t s hs control0
        (normalize rate rewards C_star C_h q t s hs control0 x) control0 := by
  obtain ⟨x', hxval, _hseed, hprefix⟩ :=
    retainedGeneratedPrefix_suffix_invariant rewards C_star C_h q t s hs control0 x
      (fun _ => control0)
  have hx : x' = normalize rate rewards C_star C_h q t s hs control0 x := by
    apply Subtype.ext
    exact hxval.trans (normalize_val rate rewards C_star C_h q t s hs control0 x).symm
  rw [ReferenceRetainedReleasePhaseObservation.generatedPhaseBefore_currentControl_invariant
    rate rewards C_star C_h q t s hs control0 x control control0]
  subst x'
  funext j
  exact congrArg encodeState (hprefix j).1

/-- Every side coordinate survives literally, and precisely the selected
controls at and after `t` are replaced. The original private scalar J and
all private arrays are part of the second equality. -/
theorem normalize_source_coordinates (x : X) :
    let z := launchSource rate rewards C_star C_h q t s hs control0 x
    let z' := launchSource rate rewards C_star C_h q t s hs control0
      (normalize rate rewards C_star C_h q t s hs control0 x)
    z'.1.1 = z.1.1 ∧ z'.2 = z.2 ∧
    (z'.1.2 q).1 = (z.1.2 q).1 ∧
    (∀ row, row ≠ q → z'.1.2 row = z.1.2 row) ∧
    (∀ v : Fin p.T, v.val < t.val → (z'.1.2 q).2 v = (z.1.2 q).2 v) ∧
    (∀ v : Fin p.T, t.val ≤ v.val → (z'.1.2 q).2 v = control0) := by
  dsimp only
  rw [launchSource_normalize]
  have hq := launchSource_selected rate rewards C_star C_h q t s hs control0 x
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [normalizedSource, hq] using replaceSelectedControlSuffix_forward
      (launchSource rate rewards C_star C_h q t s hs control0 x) t (fun _ => control0)
  · intro row hr
    exact replaceSelectedControlSuffix_otherRow
      (launchSource rate rewards C_star C_h q t s hs control0 x) t (fun _ => control0)
      row (by simpa only [hq] using hr)
  · intro v hv
    simpa only [normalizedSource, hq] using replaceSelectedControlSuffix_control_before
      (launchSource rate rewards C_star C_h q t s hs control0 x) t v (fun _ => control0) hv
  · intro v hv
    simpa only [normalizedSource, hq] using replaceSelectedControlSuffix_control_from
      (launchSource rate rewards C_star C_h q t s hs control0 x) t v (fun _ => control0) hv

/-- Equality of strict-past selected controls and of every unchanged side
coordinate suffices for equality of the normalized retained members. These
are explicit comparison inputs, not an assumed invariance law. -/
theorem normalize_eq_of_strictPast (x y : X)
    (hids : (launchSource rate rewards C_star C_h q t s hs control0 x).1.1 =
      (launchSource rate rewards C_star C_h q t s hs control0 y).1.1)
    (hprivate : (launchSource rate rewards C_star C_h q t s hs control0 x).2 =
      (launchSource rate rewards C_star C_h q t s hs control0 y).2)
    (hforward : ((launchSource rate rewards C_star C_h q t s hs control0 x).1.2 q).1 =
      ((launchSource rate rewards C_star C_h q t s hs control0 y).1.2 q).1)
    (hother : ∀ row, row ≠ q →
      (launchSource rate rewards C_star C_h q t s hs control0 x).1.2 row =
        (launchSource rate rewards C_star C_h q t s hs control0 y).1.2 row)
    (hbefore : ∀ v : Fin p.T, v.val < t.val →
      ((launchSource rate rewards C_star C_h q t s hs control0 x).1.2 q).2 v =
        ((launchSource rate rewards C_star C_h q t s hs control0 y).1.2 q).2 v) :
    normalize rate rewards C_star C_h q t s hs control0 x =
      normalize rate rewards C_star C_h q t s hs control0 y := by
  have hsource : normalizedSource rate rewards C_star C_h q t s hs control0 x =
      normalizedSource rate rewards C_star C_h q t s hs control0 y := by
    dsimp only [normalizedSource, replaceSelectedControlSuffix]
    rw [launchSource_selected, launchSource_selected]
    apply Prod.ext
    · apply Prod.ext
      · exact hids
      · funext row
        change Function.update
            (launchSource rate rewards C_star C_h q t s hs control0 x).1.2 q
            (((launchSource rate rewards C_star C_h q t s hs control0 x).1.2 q).1,
              fun v => if v.val < t.val then
                ((launchSource rate rewards C_star C_h q t s hs control0 x).1.2 q).2 v
              else control0) row =
          Function.update
            (launchSource rate rewards C_star C_h q t s hs control0 y).1.2 q
            (((launchSource rate rewards C_star C_h q t s hs control0 y).1.2 q).1,
              fun v => if v.val < t.val then
                ((launchSource rate rewards C_star C_h q t s hs control0 y).1.2 q).2 v
              else control0) row
        by_cases hr : row = q
        · subst row
          rw [Function.update_self, Function.update_self]
          apply Prod.ext
          · exact hforward
          · funext v
            by_cases hv : v.val < t.val
            · simp only [hv, ite_true]
              exact hbefore v hv
            · simp only [hv, ite_false]
        · simp only [Function.update_of_ne hr]
          exact hother row hr
    · exact hprivate
  apply Subtype.ext
  rw [normalize_val, normalize_val, hsource]

/-- The sigma algebra generated by the literal normalized source remainder.
It retains all side coordinates; it is not asserted to be source F_t. -/
abbrev strictPastSpace : MeasurableSpace X :=
  (inferInstance : MeasurableSpace X).comap
    (normalize rate rewards C_star C_h q t s hs control0)

theorem strictPastSpace_le :
    strictPastSpace rate rewards C_star C_h q t s hs control0 ≤
      (inferInstance : MeasurableSpace X) :=
  (measurable_normalize rate rewards C_star C_h q t s hs control0).comap_le

/-- The explicit normalized factor has exactly O's original vector output. -/
def phaseFactor (x : X) : Fin (t.val - s + 1) →
    StateCode p rate :=
  generatedPhaseBefore rate rewards C_star C_h q t s hs control0
    (normalize rate rewards C_star C_h q t s hs control0 x) control0

theorem phaseFactor_eq (x : X) (control : TimeControl p) :
    phaseFactor rate rewards C_star C_h q t s hs control0 x =
      generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control :=
  (generatedPhaseBefore_normalize rate rewards C_star C_h q t s hs control0 x control).symm

/-- Factor measurability uses Mathlib's comap map directly, not an ambient
Borel wrapper or an additional measurable-run premise. -/
theorem measurable_phaseFactor :
    Measurable[strictPastSpace rate rewards C_star C_h q t s hs control0]
      (phaseFactor rate rewards C_star C_h q t s hs control0) := by
  exact (ReferenceRetainedReleasePhaseObservation.measurable_generatedPhaseBefore
    rate rewards C_star C_h q t s hs control0 control0).comp
      (comap_measurable (normalize rate rewards C_star C_h q t s hs control0))

theorem measurable_generatedPhaseBefore_strictPast (control : TimeControl p) :
    Measurable[strictPastSpace rate rewards C_star C_h q t s hs control0]
      (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control) := by
  have heq : (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control) =
      phaseFactor rate rewards C_star C_h q t s hs control0 := by
    funext x
    exact (phaseFactor_eq rate rewards C_star C_h q t s hs control0 x control).symm
  rw [heq]
  exact measurable_phaseFactor rate rewards C_star C_h q t s hs control0

/-- Joint gate/pending entries at ALL retained incoming coordinates. The
payload is reselected separately from each actual code, including the last
incoming coordinate. A true gate with empty pending set remains `some ∅`. -/
def releaseEntries (b : ℕ) (x : X) :
    Fin (t.val - s + 1) → Bool × Option (Finset (Fin (p.m - 1))) := fun j =>
  localReleaseEntry rate b
    (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
    (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j)

theorem releaseEntries_normalize (b : ℕ) (x : X) :
    releaseEntries rate rewards C_star C_h q t s hs control0 b x =
      releaseEntries rate rewards C_star C_h q t s hs control0 b
        (normalize rate rewards C_star C_h q t s hs control0 x) := by
  unfold releaseEntries
  rw [generatedPhaseBefore_normalize rate rewards C_star C_h q t s hs control0 x control0]

theorem measurable_releaseEntries (b : ℕ) :
    Measurable[strictPastSpace rate rewards C_star C_h q t s hs control0]
      (releaseEntries rate rewards C_star C_h q t s hs control0 b) := by
  let mX : MeasurableSpace X := strictPastSpace rate rewards C_star C_h q t s hs control0
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_localReleaseEntry rate b
    (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)).comp
      ((measurable_pi_iff.mp (measurable_generatedPhaseBefore_strictPast
        rate rewards C_star C_h q t s hs control0 control0)) j)

/-- The finite readout is also joint in the zero-based assignment timestamp.
Its first coordinate uses the SAME normalization comap. -/
theorem measurable_releaseEntries_joint :
    Measurable[(strictPastSpace rate rewards C_star C_h q t s hs control0).prod
      (inferInstance : MeasurableSpace ℕ)]
      (fun z : X × ℕ => releaseEntries rate rewards C_star C_h q t s hs control0 z.2 z.1) := by
  let mX : MeasurableSpace X := strictPastSpace rate rewards C_star C_h q t s hs control0
  exact measurable_from_prod_countable_left fun b =>
    measurable_releaseEntries rate rewards C_star C_h q t s hs control0 b

/-- The first local gate uses the original one-based `s+j+1` conversion and
`T+1` empty sentinel. Its entire finite search is unchanged by normalization. -/
theorem firstLocalReleaseGateRound_normalize (x : X) (b : ℕ) :
    firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b =
      firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0
        (normalize rate rewards C_star C_h q t s hs control0 x) b := by
  unfold firstLocalReleaseGateRound
  rw [generatedPhaseBefore_normalize rate rewards C_star C_h q t s hs control0 x control0]

/-- Every first-gate sublevel belongs to the SAME normalization comap. This
is a local finite observation claim, not a source stopping-time theorem. -/
theorem measurableSet_firstLocalReleaseGateRound_le_strictPast (b n : ℕ) :
    MeasurableSet[strictPastSpace rate rewards C_star C_h q t s hs control0]
      {x : X | firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ n} := by
  have hpre := (ReferenceRetainedReleasePhaseObservation.measurableSet_firstLocalReleaseGateRound_le
    rate rewards C_star C_h q t s hs control0 b n).preimage
      (comap_measurable (normalize rate rewards C_star C_h q t s hs control0))
  have heq : {x : X | firstLocalReleaseGateRound
      rate rewards C_star C_h q t s hs control0 x b ≤ n} =
      (normalize rate rewards C_star C_h q t s hs control0) ⁻¹'
        {x : X | firstLocalReleaseGateRound
          rate rewards C_star C_h q t s hs control0 x b ≤ n} := by
    ext x
    exact (congrArg (fun k : ℕ => k ≤ n)
      (firstLocalReleaseGateRound_normalize rate rewards C_star C_h q t s hs control0 x b)).to_iff
  rw [heq]
  exact hpre

end Launch

/-- On an original source with its actual selected/crossing/elapsed branch,
all retained witnesses come from R and G. The factor recovers each incoming
state of the original physical run, with ALL original rows and private J. -/
theorem phaseFactor_source_specialization
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let control := split.1
    let remainder := split.2
    let hrem : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t z]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control z hselected s hs).mpr ⟨hcross, helapsed⟩
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control remainder hrem s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    ∀ j : Fin (t.val - s + 1),
      phaseFactor rate rewards C_star C_h q t s hs control0 x j =
        encodeState
          ((ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val
            (by have hj := j.isLt; omega) hmode).finalState) := by
  intro split control remainder hrem hstart seed hmode x j
  rw [phaseFactor_eq rate rewards C_star C_h q t s hs control0 x control]
  exact ReferenceRetainedReleasePhaseObservation.generatedPhaseBefore_source_specialization
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed j

/-- The finite combined readout specializes to the original source run at
its original physical time. Its gate and actual reselected payload/pending
branches are exactly O's entry, including the inclusive incoming endpoint. -/
theorem releaseEntries_source_specialization
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (b : ℕ) (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let control := split.1
    let remainder := split.2
    let hrem : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t z]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control z hselected s hs).mpr ⟨hcross, helapsed⟩
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control remainder hrem s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    ∀ j : Fin (t.val - s + 1),
      releaseEntries rate rewards C_star C_h q t s hs control0 b x j =
        localReleaseEntry rate b
          (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
          (encodeState
            ((ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val
              (by have hj := j.isLt; omega) hmode).finalState)) := by
  intro split control remainder hrem hstart seed hmode x j
  unfold releaseEntries
  rw [← phaseFactor_eq rate rewards C_star C_h q t s hs control0 x control0]
  rw [phaseFactor_source_specialization
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed j]

end Bandits.Support.ReferenceReleaseStrictPastFactor
