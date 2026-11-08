/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCoordinatorSampledReplayMeasurability
public import Bandits.Support.ActualBoundedCoordinatorDecision

/-!
# Sampled coordinator on bounded actual histories

This module composes the existing role-correct sampled coordinator replay
with the existing finite quantization of bounded original-reward histories.
The published output, sampled coordinator input, shared constants, capped
rate input, whole original reward matrix, and actual source remain explicit.

The source ranges are `01_introduction.tex:18-36`,
`07_public_setup.tex:55-114`, `06_interruptions.tex:240-296`, and
`appendix_b_communication.tex:94-131`, relative to
`sources/zip4/manuscript/`. These results cover only the coordinator role.
They do not supply the follower sampled branch, all-player local-policy
membership, an own-private-law pushforward, a joint execution measure,
reference conditional moments, an authentic manuscript filtration, or regret.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualCoordinatorSampledPrivateReplay
open Bandits.Support.ActualBoundedCoordinatorDecision
open Bandits.Support.PlayerPrivateSampledProduct
open Bandits.Support.ActualCompleteCoordinatorOwnHistory
open Bandits.Support.ActualInitializationCoordinatorOwnHistory
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActiveRoundActions
open scoped Classical

namespace Bandits.Support.ActualSampledBoundedCoordinatorDecision

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualCoordinatorSampledPrivateReplay.RateInput
abbrev SampledCoordinatorInput :=
  ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput
abbrev BoundedHistory := FiniteBoundedLocalHistoryCode.BoundedHistory

variable {p : Parameters}

/-- The existing role-correct sampled coordinator decision on the whole
published output, its sampled private input, and a bounded original own
history. The history is quantized by the existing `Q` code. -/
def sampledBoundedDecision (rate : RateInput p) (a b : ℝ) (t : Fin p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × BoundedHistory p t.val)) : Fin p.K :=
  ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t
    (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2))

/-- The composed decision is jointly Borel on the genuine published-output,
sampled-input, and bounded-subtype product structures. -/
theorem measurable_sampledBoundedDecision (rate : RateInput p) (a b : ℝ)
    (t : Fin p.T) :
    Measurable (sampledBoundedDecision (p := p) rate a b t) := by
  have hcode : Measurable
      (fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p t.val) =>
        FiniteBoundedLocalHistoryCode.Q p x.2.2) :=
    (FiniteBoundedLocalHistoryCode.Q_measurable p).comp
      (measurable_snd.comp measurable_snd)
  have hinput : Measurable
      (fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p t.val) =>
        (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2))) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk hcode)
  change Measurable
    (ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t ∘
      fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p t.val) =>
        (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2)))
  exact (ActualCoordinatorSampledReplayMeasurability.measurable_sampledGridDecision
    rate a b t).comp hinput

/-- For every published output, original coordinator own tuple, and bounded
history, the sampled decision factors exactly through the existing raw
coordinator sampler and the bounded decision. -/
theorem sampledBoundedDecision_raw_factorization (rate : RateInput p)
    (a b : ℝ) (t : Fin p.T) (published : CompletePublicTable.PublishedOutput p)
    (own : ActualBoundedCoordinatorDecision.OwnCoordinates p)
    (history : BoundedHistory p t.val) :
    sampledBoundedDecision rate a b t
        (published,
          (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p own, history)) =
      ActualBoundedCoordinatorDecision.coordinatorBoundedDecision rate a b t
        (published, (own, history)) := by
  change ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t
      (published,
        (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p own,
          FiniteBoundedLocalHistoryCode.Q p history)) = _
  rw [ActualCoordinatorSampledPrivateReplay.sampledGridDecision_raw_eq rate a b t
    (published,
      (own, FiniteBoundedLocalHistoryCode.Q p history))]
  rfl

/-- The sampled coordinator tuple keeps the source's coordinator role tag;
only its existing row, block-target arms, and own-round scalars are sampled. -/
theorem sampledCoordinatorInput_source_eq
    (source : ActualCoordinatorSampledPrivateReplay.SourceInput p) :
    Sum.inl (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
      (ActualInitializationCoordinatorOwnHistory.ownCoordinates source)) =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
        (ActiveRoundActions.coordinator p.two_le_m) source :=
  ActualCoordinatorSampledPrivateReplay.sampledCoordinatorInput_source_eq
    (p := p) source

/-- At every actual round, the source's original private tuple and whole
original reward table produce the same physical coordinator action when read
through its bounded original own history. -/
theorem sourceInitialized_sampledBoundedDecision (rate : RateInput p)
    (a b : ℝ) (original : RewardMatrix p.T p.K)
    (source : ActualCoordinatorSampledPrivateReplay.SourceInput p)
    (t : Fin p.T) :
    sampledBoundedDecision rate a b t
      (source.1,
        (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source),
          ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
            rate a b original source t.val t.isLt.le)) =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        a b)[t.val]'(by
          change t.val < (ActualCompletePhysicalHistory.playerArmHistory
            (ActualBoundedCoordinatorDecision.actualOriginalHistory
              rate source original a b)
            (ActiveRoundActions.coordinator p.two_le_m)).length
          rw [ActualCompletePhysicalHistory.playerArmHistory,
            List.length_map,
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
              p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
              a b).2.1]
          exact t.isLt) := by
  calc
    _ = ActualBoundedCoordinatorDecision.coordinatorBoundedDecision rate a b t
        (source.1,
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source,
            ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
              rate a b original source t.val t.isLt.le)) :=
      sampledBoundedDecision_raw_factorization rate a b t source.1
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source)
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b original source t.val t.isLt.le)
    _ = (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        a b)[t.val]'(by
          change t.val < (ActualCompletePhysicalHistory.playerArmHistory
            (ActualBoundedCoordinatorDecision.actualOriginalHistory
              rate source original a b)
            (ActiveRoundActions.coordinator p.two_le_m)).length
          rw [ActualCompletePhysicalHistory.playerArmHistory,
            List.length_map,
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
              p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
              a b).2.1]
          exact t.isLt) :=
      ActualBoundedCoordinatorDecision.sourceInitialized_coordinatorBoundedDecision
        rate a b original source t

/-- The sampled finite replay on bounded original histories, with its exact
existing phase-tagged coordinator storage result. -/
def sampledBoundedReplay (rate : RateInput p) (a b : ℝ) (n : ℕ)
    (hn : n ≤ p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × BoundedHistory p n)) :
    ActualCompleteCoordinatorOwnHistory.CoordinatorStorage p rate :=
  ActualCoordinatorSampledPrivateReplay.sampledGridReplay rate a b n hn
    (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2))

/-- The exact existing replay code, composed with bounded-history
quantization. This theorem concerns the code only; no measurability of the
un-coded storage is asserted. -/
def sampledBoundedReplayCode (rate : RateInput p) (a b : ℝ) (n : ℕ)
    (hn : n ≤ p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (SampledCoordinatorInput p × BoundedHistory p n)) :=
  ActualCoordinatorSampledPrivateReplay.sampledGridReplayCode rate a b n hn
    (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2))

/-- Joint Borel measurability of the replay code on the bounded original
history domain, including both the empty prefix and terminal storage prefix. -/
theorem measurable_sampledBoundedReplayCode (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (sampledBoundedReplayCode (p := p) rate a b n hn) := by
  have hcode : Measurable
      (fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p n) =>
        FiniteBoundedLocalHistoryCode.Q p x.2.2) :=
    (FiniteBoundedLocalHistoryCode.Q_measurable p).comp
      (measurable_snd.comp measurable_snd)
  have hinput : Measurable
      (fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p n) =>
        (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2))) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk hcode)
  change Measurable
    (ActualCoordinatorSampledPrivateReplay.sampledGridReplayCode rate a b n hn ∘
      fun x : CompletePublicTable.PublishedOutput p ×
        (SampledCoordinatorInput p × BoundedHistory p n) =>
        (x.1, (x.2.1, FiniteBoundedLocalHistoryCode.Q p x.2.2)))
  exact (ActualCoordinatorSampledReplayMeasurability.measurable_sampledGridReplayCode
    rate a b n hn).comp hinput

/-- At every bounded original-history prefix `n ≤ T`, the sampled replay
reconstructs the same actual before-storage readout. The statement includes
`n = 0` and `n = T`; the latter is terminal storage, with no decision at `T`.
The existing replay raw-factor and bounded-readout reconstruction theorems
are applied without changing either phase tag. -/
theorem sourceInitialized_sampledBoundedReplay (rate : RateInput p)
    (a b : ℝ) (original : RewardMatrix p.T p.K)
    (source : ActualCoordinatorSampledPrivateReplay.SourceInput p)
    (n : ℕ) (hn : n ≤ p.T) :
    sampledBoundedReplay rate a b n hn
      (source.1,
        (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source),
          ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
            rate a b original source n hn)) =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        a b n hn := by
  change ActualCoordinatorSampledPrivateReplay.sampledGridReplay rate a b n hn
      (source.1,
        (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source),
          FiniteBoundedLocalHistoryCode.Q p
            (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
              rate a b original source n hn))) = _
  rw [ActualCoordinatorSampledPrivateReplay.sampledGridReplay_raw_eq rate source.1
    (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) a b n hn
    (FiniteBoundedLocalHistoryCode.Q p
      (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
        rate a b original source n hn))]
  exact ActualBoundedCoordinatorDecision.coordinatorBoundedReplay_actual_reconstruction
    rate a b original source n hn

/-- Equal actual bounded strict-past histories and equal sampled coordinator
inputs determine equal actual coordinator storage and, below the horizon,
equal current physical actions, for arbitrary sources and whole original
reward matrices. The sampled-input premise is kept at its actual factor; it is
not strengthened to equality of raw own-coordinate tuples. -/
theorem same_sampled_actual_bounded_past_storage_and_arm
    (rate : RateInput p) (a b : ℝ)
    (source other : ActualCoordinatorSampledPrivateReplay.SourceInput p)
    (original otherOriginal : RewardMatrix p.T p.K)
    (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1)
    (hsampled :
      PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates source) =
        PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
          (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
    (hpast :
      ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b original source n hn =
        ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b otherOriginal other n hn) :
    ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        a b n hn =
      ActualCompleteCoordinatorOwnHistory.actualBeforeStorage rate other
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
        a b n hn ∧
    ∀ ht : n < p.T,
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
        a b)[n]'(by
          change n < (ActualCompletePhysicalHistory.playerArmHistory
            (ActualBoundedCoordinatorDecision.actualOriginalHistory
              rate source original a b)
            (ActiveRoundActions.coordinator p.two_le_m)).length
          rw [ActualCompletePhysicalHistory.playerArmHistory,
            List.length_map,
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
              p rate source
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
              a b).2.1]
          exact ht) =
      (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate other
        (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
        a b)[n]'(by
          change n < (ActualCompletePhysicalHistory.playerArmHistory
            (ActualBoundedCoordinatorDecision.actualOriginalHistory
              rate other otherOriginal a b)
            (ActiveRoundActions.coordinator p.two_le_m)).length
          rw [ActualCompletePhysicalHistory.playerArmHistory,
            List.length_map,
            (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
              p rate other
              (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) otherOriginal)
              a b).2.1]
          exact ht) := by
  have hcode :
      FiniteBoundedLocalHistoryCode.Q p
          (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
            rate a b original source n hn) =
        FiniteBoundedLocalHistoryCode.Q p
          (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
            rate a b otherOriginal other n hn) :=
    congrArg (FiniteBoundedLocalHistoryCode.Q p) hpast
  have hfeedback : ∀ j : Fin n,
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b original source n hn) j).2 =
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b otherOriginal other n hn) j).2 := by
    intro j
    exact congrArg Prod.snd (congrFun hcode j)
  have hsampledStorage :=
    ActualCoordinatorSampledPrivateReplay.sampledGridReplay_feedback_congr
      rate a b n hn source.1 other.1
      (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source))
      (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b original source n hn))
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b otherOriginal other n hn))
      hpublic hsampled hfeedback
  have hleftStorage := sourceInitialized_sampledBoundedReplay rate a b original source n hn
  have hrightStorage := sourceInitialized_sampledBoundedReplay
    rate a b otherOriginal other n hn
  refine ⟨hleftStorage.symm.trans (hsampledStorage.trans hrightStorage), ?_⟩
  intro ht
  let t : Fin p.T := ⟨n, ht⟩
  have hsampledDecision :=
    ActualCoordinatorSampledPrivateReplay.sampledGridDecision_feedback_congr
      rate a b t source.1 other.1
      (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates source))
      (PlayerPrivateSampledProduct.sampleCoordinatorRawInput p
        (ActualInitializationCoordinatorOwnHistory.ownCoordinates other))
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b original source n hn))
      (FiniteBoundedLocalHistoryCode.Q p
        (ActualBoundedCoordinatorDecision.actualBoundedCoordinatorHistory
          rate a b otherOriginal other n hn))
      hpublic hsampled hfeedback
  have hleftArm := sourceInitialized_sampledBoundedDecision
    rate a b original source t
  have hrightArm := sourceInitialized_sampledBoundedDecision
    rate a b otherOriginal other t
  change (ActualCompleteCoordinatorOwnHistory.sourceOwnArms rate source
      (RoundedLocalRollout.roundedRewardMatrixCode (D p) (D_pos p) original)
      a b)[n]'_ = _
  exact hleftArm.symm.trans (hsampledDecision.trans hrightArm)

end Bandits.Support.ActualSampledBoundedCoordinatorDecision

end
