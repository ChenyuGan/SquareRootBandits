/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteHorizonBoundedLocalRollout
public import Bandits.Support.FiniteHorizonRolePrivateLaw
public import Bandits.Support.ActualBoundedFollowerDecisionMeasurability

/-!
# Actual finite-horizon local policy and execution law

The local information and collision feedback conventions are those of
`sources/zip4/manuscript/01_introduction.tex:18-52`. The actual decisions retain
the original private coordinates and use the bounded real strict past, as in
`07_public_setup.tex:27-38,55-114`. All physical records are read from the existing
total protocol of `06_interruptions.tex:240-296` and
`appendix_a_local_protocol.tex:6-14`, with no new protocol transition.

The fixed-public expectations use the same whole original reward matrix as the
pathwise identities, following `08_main_theorem.tex:67-75,163-168`. These internal
results supply actual finite local-policy membership and its execution law to
`ActualReferenceRegretAssembly`. They do not establish an actual/reference
coupling, stopped-filtration identity, exceptional-event estimate, or regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.ActualFiniteHorizonLocalPolicyMembership

variable {p : ConstructorDimensions.Parameters}

/-- The genuine role-specific decisions on public output, own input, and the
whole bounded real strict past. The role transports use the actual player/slot
inverse; no decision is defined on a wrong-role input. -/
def actualDecision (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ) :
    FiniteHorizonBoundedLocalRollout.FiniteBoundedLocalDecision p
      (FiniteHorizonRolePrivateLaw.Role p) := fun i t =>
  if hi : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p then
    hi.symm ▸ (fun x =>
      ActualSampledBoundedCoordinatorDecision.sampledBoundedDecision rate C_star C_h t
        (x.1, ((FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm x.2.1, x.2.2)))
  else
    let slot := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p i hi
    let hslot := PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p i hi
    hslot ▸ (fun x =>
      ActualBoundedFollowerDecision.followerBoundedDecision rate C_star C_h slot t
        (x.1, ((FiniteHorizonRolePrivateLaw.followerRoleEquiv p slot).symm x.2.1, x.2.2)))

/-- Literal coordinator branch at label zero. -/
theorem actualDecision_coordinator
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (t : Fin p.T)
    (x : PublishedOutput p ×
      (FiniteHorizonRolePrivateLaw.Role p (PlayerPrivateCoordinateProduct.coordinatorPlayer p) ×
        FiniteBoundedLocalHistoryCode.BoundedHistory p t.val)) :
    actualDecision rate C_star C_h (PlayerPrivateCoordinateProduct.coordinatorPlayer p) t x =
      ActualSampledBoundedCoordinatorDecision.sampledBoundedDecision rate C_star C_h t
        (x.1, ((FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm x.2.1, x.2.2)) := by
  simp only [actualDecision, ↓reduceDIte]

/-- Literal follower branch at the actual label of a follower slot. -/
theorem actualDecision_follower
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (x : PublishedOutput p ×
      (FiniteHorizonRolePrivateLaw.Role p (PlayerPrivateCoordinateProduct.followerPlayer p i) ×
        FiniteBoundedLocalHistoryCode.BoundedHistory p t.val)) :
    actualDecision rate C_star C_h (PlayerPrivateCoordinateProduct.followerPlayer p i) t x =
      ActualBoundedFollowerDecision.followerBoundedDecision rate C_star C_h i t
        (x.1, ((FiniteHorizonRolePrivateLaw.followerRoleEquiv p i).symm x.2.1, x.2.2)) := by
  unfold actualDecision
  rw [dite_eq_right (PlayerPrivateCoordinateProduct.coordinatorPlayer_ne_followerPlayer p i).symm]
  simp only [PlayerPrivateCoordinateProduct.followerSlotOfPlayer_followerPlayer]
  rfl

/-- Joint Borel measurability is produced on each exact role domain. -/
theorem measurable_actualDecision
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (i : Fin p.m) (t : Fin p.T) :
    Measurable (actualDecision rate C_star C_h i t) := by
  classical
  by_cases hi : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · subst i
    simp only [show actualDecision rate C_star C_h (PlayerPrivateCoordinateProduct.coordinatorPlayer p) t =
      (fun x => ActualSampledBoundedCoordinatorDecision.sampledBoundedDecision rate C_star C_h t
        (x.1, ((FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm x.2.1, x.2.2))) from
          funext (actualDecision_coordinator rate C_star C_h t)]
    exact (ActualSampledBoundedCoordinatorDecision.measurable_sampledBoundedDecision rate C_star C_h t).comp
      (measurable_fst.prodMk
        (((FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm.measurable.comp
          (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)))
  · let slot := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p i hi
    have hslot : PlayerPrivateCoordinateProduct.followerPlayer p slot = i :=
      PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p i hi
    have hmeas : Measurable
        (actualDecision rate C_star C_h
          (PlayerPrivateCoordinateProduct.followerPlayer p slot) t) := by
      simp only [show actualDecision rate C_star C_h
          (PlayerPrivateCoordinateProduct.followerPlayer p slot) t =
        (fun x => ActualBoundedFollowerDecision.followerBoundedDecision rate C_star C_h slot t
          (x.1, ((FiniteHorizonRolePrivateLaw.followerRoleEquiv p slot).symm x.2.1, x.2.2))) from
            funext (actualDecision_follower rate C_star C_h slot t)]
      exact (ActualBoundedFollowerDecisionMeasurability.measurable_followerBoundedDecision
        rate C_star C_h slot t).comp
        (measurable_fst.prodMk
          (((FiniteHorizonRolePrivateLaw.followerRoleEquiv p slot).symm.measurable.comp
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)))
    exact hslot ▸ hmeas

/-- Extracting the source coordinator role recovers its original sampled
index, target arms, and complete own-round stream. -/
theorem coordinatorRoleEquiv_symm_phi (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm (FiniteHorizonRolePrivateLaw.phi p source
        (PlayerPrivateCoordinateProduct.coordinatorPlayer p)) =
      PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) := by
  apply (FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (ActualSampledBoundedCoordinatorDecision.sampledCoordinatorInput_source_eq source).symm

/-- Extracting a source follower role retains every original block triple and
the follower's entire own-round scalar stream. -/
theorem followerRoleEquiv_symm_phi (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    (FiniteHorizonRolePrivateLaw.followerRoleEquiv p i).symm (FiniteHorizonRolePrivateLaw.phi p source
        (PlayerPrivateCoordinateProduct.followerPlayer p i)) =
      ActualFollowerFiniteHistoryReplay.ownProjection p source i := by
  apply (FiniteHorizonRolePrivateLaw.followerRoleEquiv p i).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Subtype.ext
  exact BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_follower p i source

/-- Read the existing all-player physical records at the first `n` calendar
indices, with original real collision feedback at those same indices. -/
def actualPrefix (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) : RunPrefix p.m p.K n where
  action u :=
    (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
      ⟨u.val, lt_of_lt_of_le u.isLt hn⟩).actions
  feedback u i :=
    playerFeedback
      (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
        ⟨u.val, lt_of_lt_of_le u.isLt hn⟩).actions
      (r.reward ⟨u.val, lt_of_lt_of_le u.isLt hn⟩) i

/-- The literal readout has bounded original feedback on every path. -/
theorem actualPrefix_feedback_mem_Icc
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) (u : Fin n) (i : Fin p.m) :
    (actualPrefix rate C_star C_h r source n hn).feedback u i ∈ Set.Icc (0 : ℝ) 1 :=
  rewardMatrixFeedback_mem_Icc _ r _ i

/-- Every pair of the coordinator's bounded history is exactly the same
physical arm and real observation as in the prefix readout. -/
theorem actualPrefix_coordinator_history
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) :
    FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p (actualPrefix rate C_star C_h r source n hn)
      (actualPrefix_feedback_mem_Icc rate C_star C_h r source n hn)
      (PlayerPrivateCoordinateProduct.coordinatorPlayer p) =
        ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory rate C_star C_h r source n hn := by
  funext u
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change playerFeedback _ (r.reward _) _ = playerFeedback _ (r.reward _) _
    rw [ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt_time]
    rfl

/-- The whole follower history agrees pair by pair, including the original
real feedback rather than just its quantized code. -/
theorem actualPrefix_follower_history
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) (i : Fin (p.m - 1)) :
    FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p (actualPrefix rate C_star C_h r source n hn)
      (actualPrefix_feedback_mem_Icc rate C_star C_h r source n hn)
      (PlayerPrivateCoordinateProduct.followerPlayer p i) =
        ActualBoundedFollowerDecision.actualBoundedFollowerHistory rate C_star C_h r source i n hn := by
  funext u
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change playerFeedback _ (r.reward _) _ = playerFeedback _ (r.reward _) _
    rw [ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt_time]
    rfl

/-- Reindex the existing coordinator arm list by the same physical record
lookup. No arm equality is an input. -/
theorem sampledBoundedDecision_actualRecord
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ActualSampledBoundedCoordinatorDecision.sampledBoundedDecision rate C_star C_h t
      (source.1,
        ((FiniteHorizonRolePrivateLaw.coordinatorRoleEquiv p).symm
          (FiniteHorizonRolePrivateLaw.phi p source (PlayerPrivateCoordinateProduct.coordinatorPlayer p)),
          ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory rate C_star C_h r source t.val
              t.isLt.le)) =
      (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
          t).actions
        (PlayerPrivateCoordinateProduct.coordinatorPlayer p) := by
  rw [coordinatorRoleEquiv_symm_phi]
  rw [ActualSampledBoundedCoordinatorDecision.sourceInitialized_sampledBoundedDecision]
  simp only [ActualCompleteCoordinatorOwnHistory.sourceOwnArms,
    ActualCompletePhysicalHistory.playerArmHistory, ActualCompletePhysicalHistory.actionHistory,
        List.getElem_map,
    ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt,
        ActualBoundedCoordinatorDecision.actualOriginalHistory]
  rfl

/-- The existing source follower arm is the same entry of the same physical
action profile. -/
theorem followerBoundedDecision_actualRecord
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    ActualBoundedFollowerDecision.followerBoundedDecision rate C_star C_h i t
      (source.1,
        ((FiniteHorizonRolePrivateLaw.followerRoleEquiv p i).symm
          (FiniteHorizonRolePrivateLaw.phi p source (PlayerPrivateCoordinateProduct.followerPlayer p i)),
          ActualBoundedFollowerDecision.actualBoundedFollowerHistory rate C_star C_h r source i t.val
              t.isLt.le)) =
      (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
          t).actions
        (PlayerPrivateCoordinateProduct.followerPlayer p i) := by
  rw [followerRoleEquiv_symm_phi]
  rw [ActualBoundedFollowerDecision.source_initialized_follower_bounded_decision]
  simp only [ActualFollowerFiniteHistoryReplay.sourceFollowerArm,
      ActualCompletePhysicalHistory.playerArmHistory, ActualCompletePhysicalHistory.actionHistory,
    List.getElem_map, ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt,
        ActualBoundedCoordinatorDecision.actualOriginalHistory,
    ActualFollowerCalendarContinuity.actualHistory,
    ActualCompleteCoordinatorOwnHistory.actualHistory]
  rfl

/-- At the original source tuple, the actual local decision on the produced
whole real strict past returns the existing simultaneous physical arm. -/
theorem actualDecision_actualPrefix_history
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin p.m) :
    actualDecision rate C_star C_h i t
      (source.1, (FiniteHorizonRolePrivateLaw.phi p source i,
        FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p
          (actualPrefix rate C_star C_h r source t.val t.isLt.le)
          (actualPrefix_feedback_mem_Icc rate C_star C_h r source t.val t.isLt.le) i)) =
      (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
          t).actions i := by
  classical
  by_cases hi : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · subst i
    rw [actualDecision_coordinator, actualPrefix_coordinator_history]
    exact sampledBoundedDecision_actualRecord rate C_star C_h r source t
  · let slot := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p i hi
    have hslot : PlayerPrivateCoordinateProduct.followerPlayer p slot = i :=
      PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p i hi
    have harm : actualDecision rate C_star C_h
        (PlayerPrivateCoordinateProduct.followerPlayer p slot) t
        (source.1,
          (FiniteHorizonRolePrivateLaw.phi p source
            (PlayerPrivateCoordinateProduct.followerPlayer p slot),
            FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p
              (actualPrefix rate C_star C_h r source t.val t.isLt.le)
              (actualPrefix_feedback_mem_Icc rate C_star C_h r source t.val t.isLt.le)
              (PlayerPrivateCoordinateProduct.followerPlayer p slot))) =
        (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt
          rate source r C_star C_h t).actions
            (PlayerPrivateCoordinateProduct.followerPlayer p slot) := by
      rw [actualDecision_follower, actualPrefix_follower_history]
      exact followerBoundedDecision_actualRecord rate C_star C_h r source slot t
    exact hslot ▸ harm

/-- The finite local environment driven by the actual role decisions equals
the existing actual physical execution, for every prefix including `0` and
`T`. The induction identifies the whole own past before each new decision. -/
theorem boundedLocalPrefix_eq_actualPrefix
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ∀ n hn,
      (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p (actualDecision rate C_star C_h)
        source.1 (FiniteHorizonRolePrivateLaw.phi p source) r n hn).val =
          actualPrefix rate C_star C_h r source n hn := by
  intro n
  induction n with
  | zero =>
      intro hn
      apply congrArg₂ (fun a f => (⟨a, f⟩ : RunPrefix p.m p.K 0))
      · funext u
        exact Fin.elim0 u
      · funext u
        exact Fin.elim0 u
  | succ n ih =>
      intro hn
      let hn' : n ≤ p.T := Nat.le_of_succ_le hn
      let t : Fin p.T := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have hprev := ih hn'
      have hhist (i : Fin p.m) :
          FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p
            (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p (actualDecision rate C_star C_h)
              source.1 (FiniteHorizonRolePrivateLaw.phi p source) r n hn').val
            (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p (actualDecision rate C_star C_h)
              source.1 (FiniteHorizonRolePrivateLaw.phi p source) r n hn').property i =
          FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p
            (actualPrefix rate C_star C_h r source t.val t.isLt.le)
            (actualPrefix_feedback_mem_Icc rate C_star C_h r source t.val t.isLt.le) i := by
        funext u
        apply Prod.ext
        · exact congrArg (fun q : RunPrefix p.m p.K n => q.action u i) hprev
        · apply Subtype.ext
          exact congrArg (fun q : RunPrefix p.m p.K n => q.feedback u i) hprev
      have harm (i : Fin p.m) :
          actualDecision rate C_star C_h i t
            (source.1, (FiniteHorizonRolePrivateLaw.phi p source i,
              FiniteHorizonBoundedLocalRollout.boundedHistoryOfRun p
                (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p (actualDecision rate C_star C_h)
                  source.1 (FiniteHorizonRolePrivateLaw.phi p source) r n hn').val
                (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p (actualDecision rate C_star C_h)
                  source.1 (FiniteHorizonRolePrivateLaw.phi p source) r n hn').property i)) =
            (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt rate source r C_star C_h
                t).actions i := by
        rw [hhist]
        exact actualDecision_actualPrefix_history rate C_star C_h r source t i
      apply congrArg₂ (fun a f => (⟨a, f⟩ : RunPrefix p.m p.K (n + 1)))
      · funext u i
        cases u using Fin.lastCases with
        | cast u =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun q : RunPrefix p.m p.K n => q.action u i) hprev
        | last =>
            simp only [Fin.snoc_last]
            exact harm i
      · funext u i
        cases u using Fin.lastCases with
        | cast u =>
            simp only [Fin.snoc_castSucc]
            exact congrArg (fun q : RunPrefix p.m p.K n => q.feedback u i) hprev
        | last =>
            simp only [Fin.snoc_last]
            change playerFeedback _ (r.reward t) i = playerFeedback _ (r.reward t) i
            rw [funext harm]
            rfl

/-- The full ordered physical record list is exactly the finite calendar
enumeration used in the prefix readout. -/
theorem actualRecords_eq_ofFn
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ) (r : RewardMatrix p.T p.K)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ActualCompletePhysicalHistory.physicalHistoryRecords
        (ActualBoundedCoordinatorDecision.actualOriginalHistory rate source r C_star C_h) =
      List.ofFn (ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt
        rate source r C_star C_h) := by
  have hlength := (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
    p rate source (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) r)
    C_star C_h).1
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlength
  · intro k hk hk'
    simp only [List.getElem_ofFn]
    rfl

/-- Full-horizon original payoff agrees with the existing original reward
readout, using the exact ordered list and true record calendar times. -/
theorem actualPrefix_cumulativeReward
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    pathwiseCumulativeReward (actualPrefix rate C_star C_h r source p.T le_rfl) =
      ActualCompleteOriginalRewardRounding.sourceInitializedOriginalTotalReward
        p rate C_star C_h r source := by
  unfold ActualCompleteOriginalRewardRounding.sourceInitializedOriginalTotalReward
  change _ = ((ActualCompletePhysicalHistory.physicalHistoryRecords
    (ActualBoundedCoordinatorDecision.actualOriginalHistory rate source r C_star C_h)).map
      (fun record => ∑ i : Fin p.m,
        playerFeedback record.actions (r.reward record.time) i)).sum
  rw [actualRecords_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  unfold pathwiseCumulativeReward
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [Function.comp_def]
  rw [ActualBoundedCoordinatorDecision.actualCoordinatorPhysicalRecordAt_time]
  rfl

/-- The joint local-policy payoff, at the original source profile, is exactly
the existing original actual payoff. -/
theorem pathwisePayoff_eq_actualReward
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    FiniteHorizonBoundedLocalRollout.pathwisePayoff p
        (actualDecision rate C_star C_h) source.1 (FiniteHorizonRolePrivateLaw.phi p source) r =
      ActualCompleteOriginalRewardRounding.sourceInitializedOriginalTotalReward
        p rate C_star C_h r source := by
  unfold FiniteHorizonBoundedLocalRollout.pathwisePayoff
  rw [boundedLocalPrefix_eq_actualPrefix]
  exact actualPrefix_cumulativeReward rate C_star C_h r source

/-- Ordinary finite action/real-feedback pi coordinates of an existing run. -/
def prefixCoordinates {n : ℕ} (q : RunPrefix p.m p.K n) :
    (Fin n → Fin p.m → Fin p.K) × (Fin n → Fin p.m → ℝ) :=
  (q.action, q.feedback)

local instance roleProfileMeasurableSpace :
    MeasurableSpace (FiniteHorizonRolePrivateLaw.Profile p) := by
  change MeasurableSpace ((i : Fin p.m) → FiniteHorizonRolePrivateLaw.Role p i)
  infer_instance

/-- Coordinates of the existing finite environment for arbitrary public and
role-correct private inputs. -/
def policyPrefixCoordinates
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (n : ℕ) (hn : n ≤ p.T)
    (z : PublishedOutput p × FiniteHorizonRolePrivateLaw.Profile p) :
    (Fin n → Fin p.m → Fin p.K) × (Fin n → Fin p.m → ℝ) :=
  prefixCoordinates (FiniteHorizonBoundedLocalRollout.boundedLocalPrefix p
    (actualDecision rate C_star C_h) z.1 z.2 r n hn).val

/-- Joint measurability comes from the actual decision Borel theorem and the
accepted finite rollout coordinate theorems, with no physical-law premise. -/
theorem measurable_policyPrefixCoordinates
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (policyPrefixCoordinates rate C_star C_h r n hn) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro t
    apply measurable_pi_iff.mpr
    intro i
    exact FiniteHorizonBoundedLocalRollout.boundedLocalPrefix_action_measurable
      p (actualDecision rate C_star C_h) r
      (measurable_actualDecision rate C_star C_h) n hn t i
  · apply measurable_pi_iff.mpr
    intro t
    apply measurable_pi_iff.mpr
    intro i
    exact FiniteHorizonBoundedLocalRollout.boundedLocalPrefix_feedback_measurable
      p (actualDecision rate C_star C_h) r
      (measurable_actualDecision rate C_star C_h) n hn t i

/-- Pointwise whole-prefix identity on the ordinary coordinate carrier. -/
theorem actualPrefix_coordinates_eq_policyPrefixCoordinates
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) :
    prefixCoordinates (actualPrefix rate C_star C_h r source n hn) =
      policyPrefixCoordinates rate C_star C_h r n hn
        (source.1, FiniteHorizonRolePrivateLaw.phi p source) :=
  congrArg prefixCoordinates (boundedLocalPrefix_eq_actualPrefix
    rate C_star C_h r source n hn).symm

/-- The whole joint-source execution law, retaining every public coordinate
and every player's original role-correct private input. It holds for all
prefixes, in particular the complete horizon `n = T`. -/
theorem actualPrefix_joint_execution_law
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (r : RewardMatrix p.T p.K) (n : ℕ) (hn : n ≤ p.T) :
    Measure.map (fun source =>
        prefixCoordinates (actualPrefix rate C_star C_h r source n hn))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) =
      Measure.map (policyPrefixCoordinates rate C_star C_h r n hn)
        ((publishedOutputMeasure p).prod (FiniteHorizonRolePrivateLaw.mu p)) := by
  have hprofile : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source.1, FiniteHorizonRolePrivateLaw.phi p source)) :=
    measurable_fst.prodMk (FiniteHorizonRolePrivateLaw.measurable_phi p)
  calc
    _ = Measure.map
        (policyPrefixCoordinates rate C_star C_h r n hn ∘
          fun source => (source.1, FiniteHorizonRolePrivateLaw.phi p source))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
      congr 1
      funext source
      exact actualPrefix_coordinates_eq_policyPrefixCoordinates rate C_star C_h r source n hn
    _ = Measure.map (policyPrefixCoordinates rate C_star C_h r n hn)
        (Measure.map (fun source => (source.1, FiniteHorizonRolePrivateLaw.phi p source))
          (BootstrapPrivateRoundStreams.sourceInputLaw p)) :=
      (Measure.map_map
        (measurable_policyPrefixCoordinates rate C_star C_h r n hn) hprofile).symm
    _ = _ := by rw [FiniteHorizonRolePrivateLaw.sourcePhiPair_map_sourceInputLaw]

/-- For a fixed complete public output and then an arbitrary whole reward
matrix, only the original private coordinates are integrated. -/
theorem actualPrefix_fixedPublic_execution_law
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (pub : PublishedOutput p) (r : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n ≤ p.T) :
    Measure.map (fun e =>
        prefixCoordinates (actualPrefix rate C_star C_h r (pub, e) n hn))
        (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r) =
      Measure.map (fun rho => policyPrefixCoordinates rate C_star C_h r n hn (pub, rho))
        (FiniteHorizonRolePrivateLaw.mu p) := by
  have hprofile : Measurable
      (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        FiniteHorizonRolePrivateLaw.phi p (pub, e)) :=
    (FiniteHorizonRolePrivateLaw.measurable_phi p).comp
      (measurable_const.prodMk measurable_id)
  have hcoords : Measurable
      (fun rho : FiniteHorizonRolePrivateLaw.Profile p =>
        policyPrefixCoordinates rate C_star C_h r n hn (pub, rho)) :=
    (measurable_policyPrefixCoordinates rate C_star C_h r n hn).comp
      (measurable_const.prodMk measurable_id)
  calc
    _ = Measure.map
        ((fun rho => policyPrefixCoordinates rate C_star C_h r n hn (pub, rho)) ∘
          fun e => FiniteHorizonRolePrivateLaw.phi p (pub, e))
        (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r) := by
      congr 1
      funext e
      exact actualPrefix_coordinates_eq_policyPrefixCoordinates rate C_star C_h r (pub, e) n hn
    _ = Measure.map (fun rho => policyPrefixCoordinates rate C_star C_h r n hn (pub, rho))
        (Measure.map (fun e => FiniteHorizonRolePrivateLaw.phi p (pub, e))
          (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r)) :=
      (Measure.map_map hcoords hprofile).symm
    _ = _ := by rw [FiniteHorizonRolePrivateLaw.phi_map_fixedPublicPrivateLaw]

/-- Expected actual original payoff is the private payoff of the produced
finite local policy under the original role product law. Integrability is
supplied by the rollout's proved bound, without a reward-dependent law. -/
theorem fixedPublic_expected_actualPayoff
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (pub : PublishedOutput p) (r : RewardMatrix p.T p.K) :
    (∫ e, ActualCompleteOriginalRewardRounding.sourceInitializedOriginalTotalReward
        p rate C_star C_h r (pub, e)
        ∂BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r) =
      FiniteHorizonBoundedLocalRollout.expectedPrivatePayoff p
        (actualDecision rate C_star C_h) (FiniteHorizonRolePrivateLaw.nu p) r pub := by
  have hprofile : Measurable
      (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        FiniteHorizonRolePrivateLaw.phi p (pub, e)) :=
    (FiniteHorizonRolePrivateLaw.measurable_phi p).comp
      (measurable_const.prodMk measurable_id)
  have hpay : Integrable
      (fun rho : FiniteHorizonRolePrivateLaw.Profile p =>
        FiniteHorizonBoundedLocalRollout.pathwisePayoff p
          (actualDecision rate C_star C_h) pub rho r)
      (FiniteHorizonRolePrivateLaw.mu p) :=
    FiniteHorizonBoundedLocalRollout.pathwisePayoff_integrable p
      (actualDecision rate C_star C_h) r (measurable_actualDecision rate C_star C_h)
      (FiniteHorizonRolePrivateLaw.nu p) pub
  have hmap := FiniteHorizonRolePrivateLaw.phi_map_fixedPublicPrivateLaw p pub r
  have hpaymap : AEStronglyMeasurable
      (fun rho : FiniteHorizonRolePrivateLaw.Profile p =>
        FiniteHorizonBoundedLocalRollout.pathwisePayoff p
          (actualDecision rate C_star C_h) pub rho r)
      (Measure.map (fun e => FiniteHorizonRolePrivateLaw.phi p (pub, e))
        (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r)) := by
    rw [hmap]
    exact hpay.aestronglyMeasurable
  have hchange := integral_map hprofile.aemeasurable hpaymap
  rw [hmap] at hchange
  calc
    _ = ∫ e, FiniteHorizonBoundedLocalRollout.pathwisePayoff p
        (actualDecision rate C_star C_h) pub (FiniteHorizonRolePrivateLaw.phi p (pub, e)) r
        ∂BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r := by
      apply integral_congr_ae
      exact ae_of_all _ fun e => (pathwisePayoff_eq_actualReward
        rate C_star C_h r (pub, e)).symm
    _ = ∫ rho, FiniteHorizonBoundedLocalRollout.pathwisePayoff p
        (actualDecision rate C_star C_h) pub rho r ∂FiniteHorizonRolePrivateLaw.mu p :=
      hchange.symm
    _ = _ := rfl

/-- The same fixed-reward comparator minus expected actual original payoff
is exactly expected private regret of the actual finite local policy. -/
theorem fixedPublic_actualRegret_eq_expectedPrivateRegret
    (rate : ActualSampledBoundedCoordinatorDecision.RateInput p) (C_star C_h : ℝ)
    (pub : PublishedOutput p) (r : RewardMatrix p.T p.K) :
    bestFixedMSetComparator (ConstructorDimensions.m_pos p) p.m_lt_K.le r -
        (∫ e, ActualCompleteOriginalRewardRounding.sourceInitializedOriginalTotalReward
          p rate C_star C_h r (pub, e)
          ∂BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p pub r) =
      FiniteHorizonBoundedLocalRollout.expectedPrivateRegret p
        (actualDecision rate C_star C_h) (FiniteHorizonRolePrivateLaw.nu p) r pub := by
  rw [fixedPublic_expected_actualPayoff]
  exact (FiniteHorizonBoundedLocalRollout.expectedPrivateRegret_eq_comparator_sub_expectedPrivatePayoff
    p (actualDecision rate C_star C_h) (FiniteHorizonRolePrivateLaw.nu p) r pub
    (measurable_actualDecision rate C_star C_h)).symm

end Bandits.Support.ActualFiniteHorizonLocalPolicyMembership

end
