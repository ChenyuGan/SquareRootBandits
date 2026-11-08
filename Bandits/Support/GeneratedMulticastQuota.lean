/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedClockBlockBalance
public import Bandits.Support.GeneratedClockBlockTail
public import Bandits.Support.BootstrapMulticastAcceptance
public import Bandits.Support.BootstrapStartupCostScale

/-!
# Generated-reference multicast quota assembly

On the actual generated reference run, combine the block ID-row balance, the
actual conditional-mean clock, the localized lower-tail event, and the existing
multicast boundary acceptance operation. This module proves only a guarded
one-block internal result under the original coordinate law.

Sources: sources/zip4/manuscript/appendix_b_communication.tex:398-483 and
sources/zip4/manuscript/07_public_setup.tex:63-113.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedMulticastQuota

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open BootstrapPrivateRoundStreams
open ActiveRoundActions FiniteBanditModel
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open GeneratedClockConditionalMeans GeneratedClockBlockBalance GeneratedClockBlockTail
open ReferenceInitializationRun BootstrapStartupCostScale
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters}

/-- The actual generated-reference multicast clock count on all finite source
rounds. Its equality with the clipped calendar-block sum is proved below from
the literal clock definition. -/
@[expose] def actualMulticastClockSum
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m)
    (e : Coordinates p) : ℝ :=
  ∑ t : Fin p.T,
    multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (GeneratedClockConditionalMeans.sourceClockIndex t) e

/-- Failure of the actual generated-reference multicast count to reach the
source decoding quota. -/
@[expose] def actualMulticastQuotaFailureEvent
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) : Set (Coordinates p) :=
  {e | actualMulticastClockSum ids rewards C_star C_h eta rowCompletion
      scalarCompletion s focal e < (q_dec p : ℝ)}

/-- The actual fixed-block descriptor carries exactly the boundary, original
block-profile projections, target, and physical state used by the runtime
guard. -/
@[expose] def descriptorGuardPredicate
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K) :
    Option (Descriptor p) → Prop
  | none => False
  | some (b, (profile, (target, _st))) =>
      b.crossing = none ∧
        focal ∈ ReferenceInitializationRun.uninformed b ∧
        ∀ hm : focal ∈ ReferenceInitializationRun.uninformed b,
          let j : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨focal, hm⟩
          let draw := profile (BootstrapPhysicalInput.sourceFollowerIndex p j.val)
          draw.1 = true ∧ draw.2.1 = a ∧ target = a ∧
            (∀ k : {j // j ∈ ReferenceInitializationRun.uninformed b},
              k ≠ j →
                (profile (BootstrapPhysicalInput.sourceFollowerIndex p k.val)).1 = false) ∧
            IdentificationLocalRowBalance.localBalanceRowPredicate p s
              (positiveRewardBlockSupport p s rewards a)
              (ids (draw.2.2))

private theorem intervalSum_eq_calendarBlock_sum
    (s : Fin (n_boot p)) (Y : ℕ → Coordinates p → ℝ) (e : Coordinates p) :
    BootstrapIntervalBounds.intervalSum Y (s.val * B_boot p + 1) p.T
        (min p.T ((s.val + 1) * B_boot p)) e =
      ∑ t ∈ calendarBlock p s, Y (GeneratedClockConditionalMeans.sourceClockIndex t) e := by
  classical
  rw [BootstrapIntervalBounds.intervalSum_eq_sum_Icc (Y := Y)
    (α := s.val * B_boot p + 1) (T := p.T)
    (n := min p.T ((s.val + 1) * B_boot p)) (Nat.min_le_left _ _) e]
  symm
  apply Finset.sum_bij (fun t _ => GeneratedClockConditionalMeans.sourceClockIndex t)
  · intro t ht
    rw [Finset.mem_Icc]
    have hmem := (BootstrapDimensions.mem_calendarBlock_iff_manuscriptRound p s t).mp ht
    simpa [GeneratedClockConditionalMeans.sourceClockIndex,
      BootstrapDimensions.manuscriptRound] using hmem
  · intro t ht u hu htu
    apply Fin.ext
    dsimp [GeneratedClockConditionalMeans.sourceClockIndex] at htu
    omega
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hkα, hkβ⟩
    have hbounds := GeneratedClockBlockTail.blockClock_bounds p s
    let t : Fin p.T := ⟨k - 1, by omega⟩
    have hstart : s.val * B_boot p ≤ k - 1 := by omega
    have hstop : k - 1 < min p.T ((s.val + 1) * B_boot p) := by omega
    have ht : t ∈ calendarBlock p s :=
      (BootstrapDimensions.mem_calendarBlock_iff p s t).mpr ⟨hstart, hstop⟩
    refine ⟨t, ht, ?_⟩
    dsimp [GeneratedClockConditionalMeans.sourceClockIndex, t]
    omega
  · intro t ht
    rfl

/-- The full Fin-indexed clock sum is exactly its clipped calendar sum. The
zero branch outside the selected block is unfolded from the actual
multicastClock; no reindexing identity is assumed. -/
theorem actualMulticastClockSum_eq_calendarBlock
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (e : Coordinates p) :
    actualMulticastClockSum ids rewards C_star C_h eta rowCompletion
        scalarCompletion s focal e =
      ∑ t ∈ calendarBlock p s,
        multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
          (GeneratedClockConditionalMeans.sourceClockIndex t) e := by
  classical
  have hzero (t : Fin p.T) (ht : t ∉ calendarBlock p s) :
      multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e = 0 := by
    simp [GeneratedClockConditionalMeans.multicastClock,
      GeneratedClockConditionalMeans.sourceClockIndex, t.isLt, ht]
  unfold actualMulticastClockSum
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t ht hnot
  exact hzero t hnot

private theorem actualMulticastClock_source_measurable
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (t : Fin p.T) :
    Measurable (fun e : Coordinates p =>
      multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) e) := by
  classical
  by_cases ht : t ∈ calendarBlock p s
  · have htest := testValue_adapted_integrable ids rewards C_star C_h eta s t ht
      (multicastTest ids rewards rowCompletion scalarCompletion s t focal)
      (multicastTest_measurable ids rewards rowCompletion scalarCompletion s t focal)
      1 (by norm_num) (fun z => by
        rcases multicastTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal z with
          ⟨hlo, hhi⟩
        exact abs_le.mpr ⟨by linarith, hhi⟩)
    have hfun : multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) =
      testValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal) := by
      funext e
      exact multicastClock_at_sourceIndex ids rewards C_star C_h eta rowCompletion
        scalarCompletion s t ht focal e
    rw [hfun]
    exact htest.1.mono (analysisFiltration_le p (t.val + 1)) le_rfl
  · have hfun : multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
        (GeneratedClockConditionalMeans.sourceClockIndex t) = fun _ => 0 := by
      funext e
      simp [GeneratedClockConditionalMeans.multicastClock,
        GeneratedClockConditionalMeans.sourceClockIndex, t.isLt, ht]
    rw [hfun]
    exact measurable_const

/-- The actual generated-count failure event is ambient measurable under the
original coordinate sigma algebra. -/
theorem actualMulticastQuotaFailureEvent_measurable
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) :
    MeasurableSet (actualMulticastQuotaFailureEvent ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal) := by
  have hsum : Measurable (actualMulticastClockSum ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal) := by
    unfold actualMulticastClockSum
    exact Finset.measurable_fun_sum Finset.univ (fun t _ =>
      actualMulticastClock_source_measurable ids rewards C_star C_h eta
        rowCompletion scalarCompletion s focal t)
  change MeasurableSet
    (actualMulticastClockSum ids rewards C_star C_h eta rowCompletion scalarCompletion s focal ⁻¹'
      Set.Iio (q_dec p : ℝ))
  exact measurableSet_Iio.preimage hsum

/-- The universal choice C_h ≥ 4096 dominates the literal source threshold
needed to turn the clock lower bound into the exact decoding quota. This
retains the same C_h used by the actual generated reference input. -/
theorem h_boot_dominates_multicast_clock_threshold
    (C_h : ℝ) (hC_h : (4096 : ℝ) ≤ C_h) :
    384 * ((q_dec p : ℝ) + (7 / 8 : ℝ) * (b_N p : ℝ) +
      4 * (b_N p : ℝ)) ≤ (h_boot C_h p : ℝ) := by
  have hbNat : 1 ≤ b_N p :=
    Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hb1 : (1 : ℝ) ≤ (b_N p : ℝ) := by exact_mod_cast hbNat
  have hL0Nat : 2 ≤ L0 p :=
    (Nat.mul_le_mul_left 2 hbNat).trans (BootstrapDimensions.two_mul_b_N_le_L0 p)
  have hL0 : (2 : ℝ) ≤ (L0 p : ℝ) := by exact_mod_cast hL0Nat
  have hbootLower : C_h * (L0 p : ℝ) * (b_N p : ℝ) ≤ (h_boot C_h p : ℝ) := by
    unfold h_boot
    exact_mod_cast Nat.le_ceil (C_h * (L0 p : ℝ) * (b_N p : ℝ))
  have hbnonneg : 0 ≤ (b_N p : ℝ) := by positivity
  have hcoef : (1872 : ℝ) ≤ 1024 * (L0 p : ℝ) := by nlinarith
  have hterms := mul_le_mul_of_nonneg_right hcoef hbnonneg
  have hmain : 384 * ((q_dec p : ℝ) + (7 / 8 : ℝ) * (b_N p : ℝ) +
      4 * (b_N p : ℝ)) ≤ 4096 * (L0 p : ℝ) * (b_N p : ℝ) := by
    rw [BootstrapDimensions.q_dec]
    push_cast
    nlinarith [hterms]
  have hprodNonneg : 0 ≤ (L0 p : ℝ) * (b_N p : ℝ) :=
    mul_nonneg (by positivity) hbnonneg
  have hCmul := mul_le_mul_of_nonneg_right hC_h hprodNonneg
  have hCterm : 4096 * (L0 p : ℝ) * (b_N p : ℝ) ≤
      C_h * (L0 p : ℝ) * (b_N p : ℝ) := by nlinarith
  exact hmain.trans (hCterm.trans hbootLower)

private theorem actual_multicast_calendar_lower_ae
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (hid : IdentificationRectangleExclusion.idArrayPropertyII p ids) :
    ∀ᵐ e ∂originalLaw p,
      generatedClockBlockGuard ids rewards C_star C_h eta s focal a e →
      e ∈ clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal →
      ∑ t ∈ calendarBlock p s,
        multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
          (GeneratedClockConditionalMeans.sourceClockIndex t) e ≥
        BootstrapDownCountMean.rewardSupportCount p s rewards a / 384 -
          (7 / 8 : ℝ) * (b_N p : ℝ) - 4 * (b_N p : ℝ) := by
  have hmean := generated_oneClock_conditionalMean_intervalSum_ge ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal a
  filter_upwards [hmean] with e he
  intro hguard
  have hmeanInterval := he hguard
  have hinterval := intervalSum_eq_calendarBlock_sum s
    (BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
      (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)) e
  have hmeanCalendar :
      (∑ t ∈ calendarBlock p s,
        BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
          (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
          (GeneratedClockConditionalMeans.sourceClockIndex t) e) ≥
        BootstrapDownCountMean.rewardSupportCount p s rewards a / 192 -
          (b_N p : ℝ) / 4 := by
    rw [← hinterval]
    exact hmeanInterval
  have hdiscovery := generatedDiscoveryClock_blockSum_le_of_idArrayPropertyII
    ids rewards C_star C_h eta rowCompletion scalarCompletion s e hid
  have htail := clockGood_multicast_calendar_lower ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal e
  intro hclockGood
  have htail' := htail hclockGood
  linarith

/-- On the actual runtime guard and the accepted clock-good event, the full
Fin-indexed generated multicast count obeys the source block lower bound. -/
theorem actualMulticastClockSum_lower_ae
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (hid : IdentificationRectangleExclusion.idArrayPropertyII p ids) :
    ∀ᵐ e ∂originalLaw p,
      generatedClockBlockGuard ids rewards C_star C_h eta s focal a e →
      e ∈ clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal →
      actualMulticastClockSum ids rewards C_star C_h eta rowCompletion scalarCompletion
          s focal e ≥
        BootstrapDownCountMean.rewardSupportCount p s rewards a / 384 -
          (7 / 8 : ℝ) * (b_N p : ℝ) - 4 * (b_N p : ℝ) := by
  have hlower := actual_multicast_calendar_lower_ae ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal a hid
  filter_upwards [hlower] with e he
  intro hguard hclockGood
  rw [actualMulticastClockSum_eq_calendarBlock ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal e]
  exact he hguard hclockGood

private theorem generatedClockBlockGuard_iff_descriptorGuardPredicate
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (e : Coordinates p) :
    generatedClockBlockGuard ids rewards C_star C_h eta s focal a e ↔
      descriptorGuardPredicate ids rewards s focal a
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) := by
  classical
  let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run src s.val
  by_cases hcross : boundary.crossing = none
  · have hvalid := processedBoundary_valid ids rewards C_star C_h eta s e
      (by simpa [src, boundary] using hcross)
    let phys := ReferenceInitializationRun.physical src boundary hvalid
    let profile := BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators
      boundary.weight_ge_one src.coordinates
    let st := BootstrapPhysicalBlock.run phys t.val
    have hnext : ReferenceInitializationRun.nextBlock boundary hvalid = s := by
      exact GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e
        (by simpa [src, boundary] using hcross) hvalid
    have hdesc : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
        some (boundary, (profile, (phys.target, st))) := by
      apply (GeneratedBootstrapRoundLaw.descriptor_eq_some_iff ids rewards C_star C_h eta s t e
        boundary profile phys.target st).2
      refine ⟨rfl, ?_, ?_⟩
      · simpa [boundary] using hcross
      · refine ⟨hvalid, ?_, rfl, rfl⟩
        rw [hnext]
    rw [hdesc]
    simp [descriptorGuardPredicate, generatedClockBlockGuard, src, boundary, hvalid, phys,
      profile, st, hnext, hcross, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.activityMap,
      BootstrapPhysicalInput.heldMap, BootstrapPhysicalInput.privateIDMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap, Subtype.ext_iff]
  · have hcross' : boundary.crossing ≠ none := hcross
    have hnone : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e = none :=
      (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta s t e).2
        (by simpa [src, boundary] using hcross')
    rw [hnone]
    constructor
    · intro hguard
      exact (hcross (by simpa [src, boundary] using hguard.1)).elim
    · intro hfalse
      exact hfalse.elim

/-- On the actual guard and clockGood, the generated multicast count reaches
q_dec whenever the literal productive support condition holds. The existing
candidate is pending at the block boundary, activates at the exact next
boundary, and previously activated followers remain activated. -/
theorem generated_multicast_quota_boundary_activation_ae
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (hid : IdentificationRectangleExclusion.idArrayPropertyII p ids)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hproductive : h_boot C_h p ≤ BootstrapDownCountMean.rewardSupportCount p s rewards a) :
    ∀ᵐ e ∂originalLaw p,
      ∀ hguard : generatedClockBlockGuard ids rewards C_star C_h eta s focal a e,
      e ∈ clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal →
      let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
      let b := ReferenceInitializationRun.run src s.val
      (q_dec p : ℝ) ≤ actualMulticastClockSum ids rewards C_star C_h eta
        rowCompletion scalarCompletion s focal e ∧
      ∃ hvalid : b.completed < n_boot p,
        ∃ i : {i // i ∈
          (ReferenceInitializationRun.physical src b hvalid).uninformed},
          (ReferenceInitializationRun.candidate src b hvalid i).pending = true ∧
            (ReferenceInitializationRun.finishBlock src b hvalid).activation focal =
              some (BootstrapObservedFollower.nextActivationRound p
                (ReferenceInitializationRun.nextBlock b hvalid)) ∧
            ∀ j arm, b.activation j = some arm →
              (ReferenceInitializationRun.finishBlock src b hvalid).activation j = some arm := by
  have hlower := actualMulticastClockSum_lower_ae ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal a hid
  filter_upwards [hlower] with e hlower
  intro hguard hclockGood
  have hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none :=
    hguard.1
  have hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hcross
  let src := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run src s.val
  let phys := ReferenceInitializationRun.physical src b hvalid
  have hincoming : focal ∈ ReferenceInitializationRun.uninformed b := by
    simpa [src, b, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput] using (hguard.2 hvalid).1
  let i : {i // i ∈ phys.uninformed} := ⟨focal, by
    simpa [phys, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput] using hincoming⟩
  have hactive : phys.active i = true := (hguard.2 hvalid).2 hincoming |>.1
  have hheld : phys.held i = a := (hguard.2 hvalid).2 hincoming |>.2.1
  have htarget : phys.target = a := (hguard.2 hvalid).2 hincoming |>.2.2.1
  have hthreshold := h_boot_dominates_multicast_clock_threshold (p := p) C_h hC_h
  have hprodReal : (h_boot C_h p : ℝ) ≤
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
    exact_mod_cast hproductive
  have hclockLower := hlower hguard hclockGood
  have hquota : (q_dec p : ℝ) ≤ actualMulticastClockSum ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal e := by
    nlinarith [hclockLower, hthreshold, hprodReal]
  have hquotaActivation := BootstrapMulticastAcceptance.generated_multicast_quota_boundary_activation
    ids rewards C_star C_h eta rowCompletion scalarCompletion s e focal
    (by simpa [src, b] using hcross) (by simpa [src, b] using hincoming)
  have hresult := hquotaActivation hactive (hheld.trans htarget.symm) (by
    simpa [actualMulticastClockSum] using hquota)
  refine ⟨hquota, hvalid, ?_⟩
  refine ⟨i, ?_⟩
  exact ⟨hresult.1, hresult.2.1, hresult.2.2⟩

/-- The actual block guard is measurable at the original round-analysis
filtration immediately before the block starts. It factors through the actual
first-round descriptor and its original block-profile, target, and ID
projections. -/
theorem generatedClockBlockGuard_measurable
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K) :
    MeasurableSet[analysisFiltration p (blockClockStart p s - 1)]
      {e | generatedClockBlockGuard ids rewards C_star C_h eta s focal a e} := by
  have hstartStop := calendarBlock_start_lt_stop_local p s
  have hstartT : s.val * B_boot p < p.T :=
    lt_of_lt_of_le hstartStop (Nat.min_le_left _ _)
  let t : Fin p.T := ⟨s.val * B_boot p, hstartT⟩
  have ht : t ∈ calendarBlock p s :=
    (BootstrapDimensions.mem_calendarBlock_iff p s t).mpr
      ⟨le_rfl, hstartStop⟩
  have hdesc := GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta
    s t ht
  have hpredicate : MeasurableSet
      {d : Option (Descriptor p) | descriptorGuardPredicate ids rewards s focal a d} := by
    exact MeasurableSet.of_discrete
  have hpre : MeasurableSet[analysisFiltration p t.val]
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t ⁻¹'
        {d | descriptorGuardPredicate ids rewards s focal a d}) :=
    hdesc hpredicate
  have hfactor :
      {e | generatedClockBlockGuard ids rewards C_star C_h eta s focal a e} =
        GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t ⁻¹'
          {d | descriptorGuardPredicate ids rewards s focal a d} := by
    ext e
    exact generatedClockBlockGuard_iff_descriptorGuardPredicate ids rewards C_star C_h eta
      s focal a t ht e
  rw [hfactor]
  change MeasurableSet[analysisFiltration p (s.val * B_boot p)] _
  simpa [GeneratedClockBlockTail.blockClockStart, t] using hpre

/-- Unnormalized original-law failure localization for the actual generated
quota event, on any event measurable before the block starts. The fixed ID
property (ii), productive support condition, and universal C_h bound are the
only deterministic inputs; zero-mass events require no division. -/
theorem actual_multicast_quota_failure_localized
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (hid : IdentificationRectangleExclusion.idArrayPropertyII p ids)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hproductive : h_boot C_h p ≤ BootstrapDownCountMean.rewardSupportCount p s rewards a)
    (A : Set (Coordinates p))
    (hA : MeasurableSet[analysisFiltration p (blockClockStart p s - 1)] A) :
    (originalLaw p).real
        (A ∩ {e | generatedClockBlockGuard ids rewards C_star C_h eta s focal a e} ∩
          actualMulticastQuotaFailureEvent ids rewards C_star C_h eta
            rowCompletion scalarCompletion s focal) ≤
      Real.exp (-(4 * (b_N p : ℝ))) *
        (originalLaw p).real
          (A ∩ {e | generatedClockBlockGuard ids rewards C_star C_h eta s focal a e}) ∧
      Real.exp (-(4 * (b_N p : ℝ))) ≤ (1 / (N p : ℝ)) ^ 2 ∧
      Real.exp (-(4 * (b_N p : ℝ))) < 1 / 8 := by
  let guard : Set (Coordinates p) :=
    {e | generatedClockBlockGuard ids rewards C_star C_h eta s focal a e}
  let failure := actualMulticastQuotaFailureEvent ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal
  have hguardMeas := generatedClockBlockGuard_measurable ids rewards C_star C_h eta s focal a
  have hAguard : MeasurableSet[analysisFiltration p (blockClockStart p s - 1)]
      (A ∩ guard) := hA.inter hguardMeas
  have hlocalized := clockGood_failure_localized ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal (A ∩ guard) hAguard
  have hactivationAE := generated_multicast_quota_boundary_activation_ae ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal a hid hC_h hproductive
  have hsubset : (originalLaw p) (A ∩ guard ∩ failure) ≤
      (originalLaw p) (A ∩ guard ∩
        (clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)ᶜ) := by
    apply measure_mono_ae
    filter_upwards [hactivationAE] with e hactivation
    intro hmem
    rcases hmem with ⟨⟨hA', hguard⟩, hfail⟩
    refine ⟨⟨hA', hguard⟩, ?_⟩
    intro hgood
    have hresult := hactivation hguard hgood
    change actualMulticastClockSum ids rewards C_star C_h eta rowCompletion
      scalarCompletion s focal e < (q_dec p : ℝ) at hfail
    exact (not_lt_of_ge hresult.1) hfail
  have hreal := (ENNReal.toReal_mono (measure_ne_top _ _) hsubset).trans hlocalized
  have hexp := source_clock_failure_exponent_bound p
  unfold guard failure at hreal
  exact ⟨hreal, hexp.1, hexp.2⟩

end Bandits.Support.GeneratedMulticastQuota

end
