/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOldDownThresholdSourceTransport

import Lean.Elab.Tactic.Omega

/-!
# Inclusive stopped OLD DOWN allowance at the first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`,
`sources/zip4/manuscript/06_interruptions.tex:246-349,477-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The stop uses only actual accepted DOWN, physical failure, or a retained
decoder-record flag. Its detecting record is included in the same OLD-positive
count, which is clipped at the first such record.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity
open ReferenceFirstReplacementCollectionOldDownCallDates
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionStoppedOldDownQuota

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal stopping readouts on an actual physical record. -/
def literalOldDownStopAt
    (s : ℕ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) : Prop :=
  ReferenceAcceptedUpFollowerHistory.RetainedDown r i M ∨
    ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r ∨
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true

/-- The first literal stopping record, or the collection length if absent. -/
def literalOldDownStopIndex
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) : ℕ := by
  classical
  exact K.findIdx (fun r => decide (literalOldDownStopAt s r i M))

/-- The actual OLD-positive count through the inclusive first stopping record,
restricted further by the requested original prefix. -/
def stoppedOldDownCount
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) : ℕ :=
  ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K
    (min j (literalOldDownStopIndex s K i M + 1)) i M

private theorem oldDownCount_eq_card_literalDateSet
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    oldDownCount K j i M = (oldDownServiceFinset K j i M).card := by
  classical
  have hnodup :
      (ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
        K j i M).Nodup := by
    unfold ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
    exact (List.nodup_finRange K.length).filter _
  calc
    oldDownCount K j i M =
        ((ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
          K j i M).toFinset).card := by
      unfold oldDownCount
      symm
      exact List.toFinset_card_of_nodup hnodup
    _ = (oldDownServiceFinset K j i M).card := by
      simp [ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices,
        ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceAt,
        oldDownServiceFinset, oldDownServiceAt, List.toFinset_filter,
        List.toFinset_finRange]

/-- Monotonicity of the same literal finite date set used by `oldDownCount`. -/
private theorem oldDownCount_mono_local
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j k : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hjk : j ≤ k) : oldDownCount K j i M ≤ oldDownCount K k i M := by
  classical
  rw [oldDownCount_eq_card_literalDateSet, oldDownCount_eq_card_literalDateSet]
  apply Finset.card_le_card
  intro a ha
  simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨by omega, ha.2⟩

/-- At one service date the literal OLD-positive date set gains exactly that
coordinate, with the original strict-past physical-failure exclusion. -/
private theorem oldDownCount_succ_eq_add_one_local
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hj : j < K.length)
    (hservice : oldDownServiceAt K i M ⟨j, hj⟩) :
    oldDownCount K (j + 1) i M = oldDownCount K j i M + 1 := by
  classical
  let x : Fin K.length := ⟨j, hj⟩
  have hset : oldDownServiceFinset K (j + 1) i M =
      insert x (oldDownServiceFinset K j i M) := by
    ext a
    simp only [oldDownServiceFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨ha, hsa⟩
      by_cases heq : a.val = j
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr ⟨by omega, hsa⟩
    · rintro (heq | ⟨ha, hsa⟩)
      · subst a
        exact ⟨by simp [x], hservice⟩
      · exact ⟨by omega, hsa⟩
  have hnot : x ∉ oldDownServiceFinset K j i M := by
    simp only [oldDownServiceFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, x]
    omega
  calc
    oldDownCount K (j + 1) i M =
        (oldDownServiceFinset K (j + 1) i M).card :=
      oldDownCount_eq_card_literalDateSet K (j + 1) i M
    _ = (insert x (oldDownServiceFinset K j i M)).card := by rw [hset]
    _ = (oldDownServiceFinset K j i M).card + 1 :=
      Finset.card_insert_of_notMem hnot
    _ = oldDownCount K j i M + 1 := by
      rw [oldDownCount_eq_card_literalDateSet]

private theorem literalOldDownStopIndex_le_of_readout
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length)
    (hstop : literalOldDownStopAt s (K.get a) i M) :
    literalOldDownStopIndex s K i M ≤ a.val := by
  classical
  by_contra hnot
  have hlt : a.val < literalOldDownStopIndex s K i M := by omega
  have hfalse := List.not_of_lt_findIdx (xs := K)
    (p := fun r => decide (literalOldDownStopAt s r i M)) hlt
  have htrue : decide (literalOldDownStopAt s (K.get a) i M) = true :=
    (decide_eq_true_iff).2 hstop
  have hfalse' : decide (literalOldDownStopAt s (K.get a) i M) = false := by
    simpa using hfalse
  rw [htrue] at hfalse'
  cases hfalse'

/-- A real first-stop certificate, or literal absence of every stop in `K`. -/
theorem literalOldDownStopIndex_certificate
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    (∃ a : Fin K.length,
      literalOldDownStopIndex s K i M = a.val ∧
        literalOldDownStopAt s (K.get a) i M ∧
        ∀ r ∈ K.take a.val, ¬ literalOldDownStopAt s r i M) ∨
    (literalOldDownStopIndex s K i M = K.length ∧
      ∀ r ∈ K, ¬ literalOldDownStopAt s r i M) := by
  classical
  let f := literalOldDownStopIndex s K i M
  have hle : f ≤ K.length := by
    dsimp [f, literalOldDownStopIndex]
    exact List.findIdx_le_length
  by_cases hlt : f < K.length
  · left
    refine ⟨⟨f, hlt⟩, rfl, ?_, ?_⟩
    · have hlt' : K.findIdx
          (fun r => decide (literalOldDownStopAt s r i M)) < K.length := by
        simpa [f, literalOldDownStopIndex] using hlt
      exact of_decide_eq_true (List.findIdx_getElem (w := hlt'))
    · intro r hr
      obtain ⟨b, hb, heq⟩ := List.mem_iff_getElem.mp hr
      have hb' : b < f := by
        simp only [List.length_take] at hb
        omega
      have hbidx : b < K.findIdx
          (fun r => decide (literalOldDownStopAt s r i M)) := by
        simpa [f, literalOldDownStopIndex] using hb'
      have hfalse := List.not_of_lt_findIdx (xs := K)
        (p := fun r => decide (literalOldDownStopAt s r i M)) hbidx
      simp only [List.getElem_take] at heq
      rw [heq] at hfalse
      exact of_decide_eq_false hfalse
  · right
    have heq : f = K.length := by omega
    refine ⟨heq, ?_⟩
    have hf : K.findIdx (fun r => decide (literalOldDownStopAt s r i M)) =
        K.length := by
      simpa [f, literalOldDownStopIndex] using heq
    have hfalse : ∀ r ∈ K,
        decide (literalOldDownStopAt s r i M) = false := by
      exact List.findIdx_eq_length.mp hf
    intro r hr
    exact of_decide_eq_false (hfalse r hr)

private theorem stoppedOldDownCount_le_of_firstThreshold
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (need : ℕ) (_hj : j ≤ K.length)
    (a : Fin K.length) (_haj : a.val < j)
    (hat : oldDownCount K (a.val + 1) i M = need)
    (hbefore : ∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < need)
    (hservice : oldDownServiceAt K i M a)
    (hstop : literalOldDownStopAt s (K.get a) i M) :
    stoppedOldDownCount s K j i M ≤ need := by
  have hf := literalOldDownStopIndex_le_of_readout s K i M a hstop
  have hprefix : min j (literalOldDownStopIndex s K i M + 1) ≤ a.val + 1 := by
    have hmin := Nat.min_le_right j (literalOldDownStopIndex s K i M + 1)
    omega
  have hmono := oldDownCount_mono_local K
    (min j (literalOldDownStopIndex s K i M + 1)) (a.val + 1) i M hprefix
  have hinc := oldDownCount_succ_eq_add_one_local K a.val i M a.isLt hservice
  have hprev := hbefore a.val le_rfl
  have hpreviousThreshold : oldDownCount K a.val i M + 1 = need := by omega
  change oldDownCount K (min j (literalOldDownStopIndex s K i M + 1)) i M ≤ need
  rw [hinc] at hmono
  rw [hpreviousThreshold] at hmono
  exact hmono

/-- The stopped prefix is contained in the prefix stopped by the literal
per-record physical-failure or retained-decoder readout. This is the local
record-mask comparison; source-date alignment remains a separate obligation. -/
theorem stoppedOldDownCount_le_recordFailureDecoderMask
    (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    stoppedOldDownCount s K j i M ≤
      oldDownCount K
        (min j ((K.findIdx (fun r => decide
          (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r ∨
            ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true))) + 1))
        i M := by
  classical
  let maskIndex := K.findIdx (fun r => decide
    (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r ∨
      ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true))
  have hstopLe : literalOldDownStopIndex s K i M ≤ maskIndex := by
    by_cases hlt : maskIndex < K.length
    · have hlt' := hlt
      change K.findIdx (fun r => decide
        (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r ∨
          ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true)) <
          K.length at hlt'
      have hmask := List.findIdx_getElem (w := hlt')
      have hreadout := of_decide_eq_true hmask
      have hstop : literalOldDownStopAt s (K.get ⟨maskIndex, hlt⟩) i M := by
        rcases hreadout with hfailure | hflag
        · exact Or.inr (Or.inl hfailure)
        · exact Or.inr (Or.inr hflag)
      exact literalOldDownStopIndex_le_of_readout s K i M ⟨maskIndex, hlt⟩ hstop
    · have hmaskLe : maskIndex ≤ K.length := by
        dsimp [maskIndex]
        exact List.findIdx_le_length
      have hstopLeLength : literalOldDownStopIndex s K i M ≤ K.length := by
        dsimp [literalOldDownStopIndex]
        exact List.findIdx_le_length
      omega
  have hprefix : min j (literalOldDownStopIndex s K i M + 1) ≤
      min j (maskIndex + 1) := by omega
  change oldDownCount K (min j (literalOldDownStopIndex s K i M + 1)) i M ≤
    oldDownCount K (min j (maskIndex + 1)) i M
  exact oldDownCount_mono_local K _ _ i M hprefix

theorem complete_first_replacement_collection_stopped_old_down_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∀ control0 : ContinuousLearningRows.TimeControl p,
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
              ReferenceCorrectedInitializationLaunch.correctedLaunch
                rate source rewards C_star C_h = some initial ∧
              ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
              ∀ i : Fin (p.m - 1),
                ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
                  (baseMemory : ActiveFollowerLifecycle.LocalMemory p)
                  (span0 : s + c ≤ p.T),
                (Z 0).followers i = .ordinary base baseMemory ∧
                (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s c span0 active
                  ).finalState.followers i = .ordinary base baseMemory ∧
                ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                (base.lastDown = some (M i) → ∀ j : ℕ, j ≤ K.length →
                  oldDownCount K j i (M i) = 0) ∧
                ∀ j : ℕ, j ≤ K.length →
                  let Q := AffineBatchDecoder.quota p
                  let need := (Q - base.downBatch.pending.length) + Q
                  let M := M i
                  need ≤ 2 * Q ∧
                  (oldDownCount K j i M < need ∨
                    ∃ a : Fin K.length, a.val < j ∧
                      oldDownCount K (a.val + 1) i M = need ∧
                      (∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < need) ∧
                      oldDownServiceAt K i M a ∧
                      (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt
                        (K.get a) ∨
                        ((∀ r ∈ K.take (a.val + 1),
                          ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) ∧
                        (∀ b : Fin K.length, b.val ≤ a.val → actualOldAt (K.get b) i M) ∧
                        (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                          (K.take (a.val + 1))).length = need ∧
                        (∀ b : Fin K.length, b.val ≤ a.val →
                          ActiveFollowerDownAcceptance.downSelected p i
                            (K.get b).input.row (K.get b).input.time →
                          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                            (memory : ActiveFollowerLifecycle.LocalMemory p)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration =
                              .ordinary state memory ∧
                            ((K.get b).output.followers i).downInput = some state ∧
                            ((K.get b).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            let input := ActiveFollowerDownAcceptance.currentRoundInput p i
                              (K.get b).input.row (K.get b).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get b) i)
                              rate state
                            ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get b) =
                              some ((K.get b).input.time, input) ∧
                            input.selected = true ∧ input.receiverEnabled = true ∧
                            input.sample = ReferenceDownPhysicalHashRule.originalDownSample (K.get b).input ∧
                            ReferenceActiveAffinePositiveTest.downSent (K.get b).input =
                              some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                              (K.get b).input.time state
                              (ReferenceDownReception.ordinaryParse p rate
                                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)))) ∧
                        (∃ d : Fin K.length, d.val < a.val ∧
                          (K.get d).input.time.val < (K.get a).input.time.val ∧
                          oldDownCount K (d.val + 1) i M = Q - base.downBatch.pending.length ∧
                          (∀ k : ℕ, k ≤ d.val →
                            oldDownCount K k i M < Q - base.downBatch.pending.length) ∧
                          ∃ (firstState : ReferencePrelaunchFollower.State p rate.eta)
                            (firstDiag : ReferenceDownReception.ReferenceDownCutOutput p rate)
                            (reset : ReferencePrelaunchFollower.State p rate.eta)
                            (resetMemory : ActiveFollowerLifecycle.LocalMemory p),
                            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (a.val + 1))
                            let first := base.downBatch.pending ++
                              P.take (Q - base.downBatch.pending.length)
                            ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (d.val + 1)) = P.take (Q - base.downBatch.pending.length) ∧
                            firstState.downBatch =
                              ⟨base.downBatch.pending ++ ReferenceFollowerDownDecoderReplay.actualDownPositives i
                                (K.take d.val), base.downBatch.completed⟩ ∧
                            ((K.get d).output.followers i).downInput = some firstState ∧
                            ((K.get d).output.followers i).down = some firstDiag ∧
                            firstDiag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get d) i = some first ∧
                            firstDiag.raw = AffineBatchDecoder.batchOutput first ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get d).input.row (K.get d).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get d) i)
                              rate firstState).1 = ⟨[], base.downBatch.completed ++ [first]⟩ ∧
                            (Z (d.val + 1)).followers i = .ordinary reset resetMemory ∧
                            reset.downBatch = ⟨[], base.downBatch.completed ++ [first]⟩) ∧
                        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
                          (memory : ActiveFollowerLifecycle.LocalMemory p)
                          (span : s + (c + (a.val + 1)) ≤ p.T),
                          (Z (a.val + 1)).followers i = .ordinary endpoint memory ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).records.drop c = K.take (a.val + 1) ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).finalState = Z (a.val + 1) ∧
                          let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                            (K.take (a.val + 1))
                          let first := base.downBatch.pending ++
                            P.take (Q - base.downBatch.pending.length)
                          let pure := P.drop (Q - base.downBatch.pending.length)
                          endpoint.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                          first.length = Q ∧ pure.length = Q ∧
                          pure.Pairwise (fun x y => x.time.val < y.time.val) ∧
                          (∀ e ∈ base.downBatch.pending, e ∉ pure) ∧
                          (∀ e ∈ P, s + c ≤ e.time.val ∧
                            e.time.val < s + c + (a.val + 1)) ∧
                          ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            ((K.get a).output.followers i).downInput = some logged ∧
                            ((K.get a).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get a) i = some pure ∧
                            diag.raw = AffineBatchDecoder.batchOutput pure ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get a).input.row (K.get a).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                              rate logged).1 = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
                              (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∨
                              (AffineBatchDecoder.batchOutput pure = none ∧
                                ReferenceFirstLiveDownCompletionReadout.multipleSolutions pure ∧
                                ∃ other,
                                  CoordinatorLocalArmChoice.storedDownFlatWord payload i ≠ other ∧
                                  AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
                                  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                                    (K.get a).input.time source = some (K.get a) ∧
                                  ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
                                    s (K.get a) = true ∧
                                  (∃ hn : (K.get a).input.time.val + 1 ≤ p.T,
                                    ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
                                      rate rewards C_star C_h s ((K.get a).input.time.val + 1)
                                      hn source = true) ∧
                                  source ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
                                    rate rewards C_star C_h control0 Q ∧
                                  ∃ (hs : s < p.T)
                                    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                                      rate rewards C_star C_h s hs), x.val = source ∧
                                    let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                                      rate rewards C_star C_h s hs x
                                    let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                                      rate rewards C_star C_h s hs i x
                                    let Rk := fun k : Fin (p.T - s) =>
                                      (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                                          s k.val (by omega) Y,
                                        ReferenceActivePhysicalStep.step
                                          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
                                            s k.val (by omega) Y), rfl⟩ :
                                        ReferenceFollowerDownDecoderReplay.Record p rate)
                                    ∃ n m : Fin (p.T - s), n.val = c + a.val ∧ m < n ∧
                                      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 m) ∧
                                      (∀ k : Fin (p.T - s), k < n →
                                        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                          (O.2 k) → k ≤ m) ∧
                                      (∀ m' : Fin (p.T - s), m' < n →
                                        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                          (O.2 m') →
                                        (∀ k : Fin (p.T - s), k < n →
                                          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                                            (O.2 k) → k ≤ m') → m' = m) ∧
                                      ∃ (hsa : s < s + (m.val + 1))
                                        (haT : s + (m.val + 1) < p.T),
                                        s + (m.val + 1) ≤ (K.get a).input.time.val ∧
                                        ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
                                          rate rewards C_star C_h s hs i (s + (m.val + 1)) hsa haT x ∧
                                        (∃ reset resetMemory,
                                          (ReferenceActiveHorizonMeasurability.runOfInput
                                            s (m.val + 1) (by omega) Y).finalState.followers i =
                                              .ordinary reset resetMemory ∧ reset.downBatch.pending = []) ∧
                                        let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                                          rate rewards C_star C_h s hs i (s + (m.val + 1)) x
                                        tests.map ReferenceGeneratedDownPrefixList.stampedTest = pure ∧
                                        tests.length = Q ∧
                                        (∀ test ∈ tests, ∃ k : Fin (p.T - s), m < k ∧ k ≤ n ∧
                                          ReferenceGeneratedDownBatchCalendar.executedTestOfRound
                                            rate (O.2 k) = some test ∧
                                          test.time = (Rk k).input.time ∧
                                          test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
                                          test.sent = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                                          ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test) ∧
                                        ReferenceGeneratedDownBatchCalendar.generatedDownD rate rewards C_star C_h
                                          s Q hs i (s + (m.val + 1)) hsa haT other x)) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
                              ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M ∧
                              ∃ (accepted : OrdinaryMessageCodec.acceptDown
                                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                                  (ReferencePrelaunchFollower.acceptedStart logged)
                                  ((K.get a).input.time.val + 1) M)
                                (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                                (post : ReferencePrelaunchFollower.State p rate.eta)
                                (memory : ActiveFollowerLifecycle.LocalMemory p),
                                let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
                                  (K.get a).input.time (ActiveFollowerDownAcceptance.acceptedDownStartLE
                                    p rate M (K.get a).input.time logged accepted) (K.get a).input.row
                                scan.endpoint = cut.input.time.val + 1 ∧
                                ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
                                  (cut.input.time.val + 1) = .ok recovered ∧
                                recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                    (cut.input.time.val + 1)) ∧
                                (∀ k : ℕ, ∃ middle,
                                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k) = .ok middle ∧
                                  middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k)) ∧
                                post.lastDown = some M ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
                                post.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                                diag.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                                diag.outcome = .accepted logged post
                                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) M scan
                                  recovered.registers recovered.lastService ∧
                                (K.get a).output.followers i =
                                  ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                                (K.get a).output.next.followers i = .ordinary post memory ∧
                                (Z (a.val + 1)).followers i = .ordinary post memory)))) ∧
                  stoppedOldDownCount s K j i M ≤
                    (AffineBatchDecoder.quota p - base.downBatch.pending.length) +
                      AffineBatchDecoder.quota p
          | _ => True
      | _ => True := by
  classical
  intro control0
  have hSource :=
    ReferenceFirstReplacementCollectionOldDownThresholdSourceTransport.complete_first_replacement_collection_old_down_threshold_source_transport
      rate source rewards C_star C_h control0
  dsimp only at hSource ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    rw [hb] at hSource
    dsimp only at hSource ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hSource
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hSource
        dsimp only at hSource ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hSource
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          obtain ⟨initial, active, hlaunch, hseed, hfollowers⟩ := hSource
          refine ⟨initial, active, hlaunch, hseed, ?_⟩
          intro i
          obtain ⟨base0, baseMemory0, span0, hbase0, hrun0, hend0, hretained, hqueries⟩ :=
            hfollowers i
          refine ⟨base0, baseMemory0, span0, hbase0, hrun0, hend0, hretained, ?_⟩
          intro j hj
          obtain ⟨hneed, hcase⟩ := hqueries j hj
          refine ⟨hneed, hcase, ?_⟩
          change oldDownCount K
            (min j (literalOldDownStopIndex s K i (M i) + 1)) i (M i) ≤
              (AffineBatchDecoder.quota p - base0.downBatch.pending.length) +
                AffineBatchDecoder.quota p
          rcases hcase with hsmall | ⟨a, haj, hat, hbefore, hservice, hcases⟩
          · have hmono := oldDownCount_mono_local K
              (min j (literalOldDownStopIndex s K i (M i) + 1)) j i (M i)
              (Nat.min_le_left j _)
            exact hmono.trans (Nat.le_of_lt hsmall)
          · have hstop : literalOldDownStopAt s (K.get a) i (M i) := by
              rcases hcases with hfailure | hnonfailure
              · exact Or.inr (Or.inl hfailure)
              · rcases hnonfailure with ⟨_, _, _, _, _, hsecond⟩
                rcases hsecond with
                  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                    hsolver, haccept⟩
                rcases hsolver with hsuccess | hambiguous
                · exact Or.inl (haccept hsuccess).1
                · rcases hambiguous with
                    ⟨_, _, _, _, _, _, hflag, _, _, _⟩
                  exact Or.inr (Or.inr hflag)
            exact stoppedOldDownCount_le_of_firstThreshold s K j i (M i)
              ((AffineBatchDecoder.quota p - base0.downBatch.pending.length) +
                AffineBatchDecoder.quota p) hj
              a haj hat hbefore hservice hstop

end Bandits.Support.ReferenceFirstReplacementCollectionStoppedOldDownQuota

end
