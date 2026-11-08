/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCollectionCurrentUpReceiver
public import Bandits.Support.ReferenceOriginalCollectionReplyFormationChronology

import Mathlib.Tactic

/-!
# Actual original-source formed-UP threshold and detector

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-191`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`.

This module derives the current-reply formation boundary from the actual
original-source LIVE cutoff and exposes the exact actual-positive prefix
identity. When the actual formed-UP count reaches its first two-bank
threshold, it identifies the least record prefix reaching that count and the
actual completed second bank. Its raw output forces matching acceptance with
pending removal or the literal original fixed-awaited ambiguity event. The
inherited bank and every zero-positive record remain in the actual prefix.
The all-prefix canonical quota inequality is left to its named successor.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstReplacementCollectionStoppedPureUpQuota

namespace Bandits.Support.ReferenceOriginalCollectionFormedUpThreshold

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

private theorem firstFlatMapPrefix
    {α β : Type} (xs : List α) (f : α → List β)
    (hunit : ∀ x, (f x).length ≤ 1) (N : ℕ)
    (hN : 0 < N) (hcount : N ≤ (xs.flatMap f).length) :
    ∃ k, k < xs.length ∧
      ((xs.take (k + 1)).flatMap f).length = N ∧
      ∀ j, j ≤ k → ((xs.take j).flatMap f).length < N := by
  induction xs generalizing N with
  | nil =>
      simp at hcount
      omega
  | cons x xs ih =>
      have hunitx := hunit x
      cases hfx : f x with
      | nil =>
          have htail : N ≤ (xs.flatMap f).length := by
            simpa [List.flatMap_cons, hfx] using hcount
          obtain ⟨k, hk, hprefix, hbefore⟩ := ih N hN htail
          refine ⟨k + 1, by simp; omega, ?_, ?_⟩
          · simpa [List.flatMap_cons, List.take_succ_cons, hfx] using hprefix
          · intro j hj
            by_cases hj0 : j = 0
            · simpa [hj0] using hN
            · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
              have hm : m ≤ k := by omega
              simpa [List.flatMap_cons, List.take_succ_cons, hfx] using hbefore m hm
      | cons y ys =>
          have hys : ys = [] := by
            cases ys with
            | nil => rfl
            | cons z zs => simp [hfx] at hunitx
          subst ys
          have hfx' : f x = [y] := hfx
          by_cases hNone : N = 1
          · subst N
            refine ⟨0, by simp, ?_, ?_⟩
            · simp [List.flatMap_cons, List.take_succ_cons, hfx']
            · intro j hj
              have hj0 : j = 0 := by omega
              simp [hj0]
          · have hNtail : 0 < N - 1 := by omega
            have htail : N - 1 ≤ (xs.flatMap f).length := by
              have htotal : N ≤ 1 + (xs.flatMap f).length := by
                have := hcount
                simp only [List.flatMap_cons, hfx', List.length_append,
                  List.length_singleton] at this
                omega
              omega
            obtain ⟨k, hk, hprefix, hbefore⟩ := ih (N - 1) hNtail htail
            refine ⟨k + 1, by simp; omega, ?_, ?_⟩
            · have hsplit :
                  ((x :: xs).take (k + 1 + 1)).flatMap f =
                    [y] ++ ((xs.take (k + 1)).flatMap f) := by
                simp [List.flatMap_cons, List.take_succ_cons, hfx']
              rw [hsplit, List.length_append, List.length_singleton, hprefix]
              omega
            · intro j hj
              by_cases hj0 : j = 0
              · simpa [hj0] using hN
              · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
                have hm : m ≤ k := by omega
                have hsplit :
                    ((x :: xs).take (m + 1)).flatMap f =
                      [y] ++ ((xs.take m).flatMap f) := by
                  simp [List.flatMap_cons, List.take_succ_cons, hfx']
                rw [hsplit, List.length_append, List.length_singleton]
                have := hbefore m hm
                omega

private theorem recordUpPositiveEntries_length_le_one
    (rate : RateInput p)
    (record : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i).length ≤ 1 := by
  classical
  unfold ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
  cases h : record.output.coordinator.up with
  | none => simp
  | some diagnostic =>
      dsimp only
      by_cases hi : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower diagnostic = i
      · rw [ite_eq_left hi]
        unfold AffineBatchDecoder.positiveAt
        split <;> simp
      · rw [ite_eq_right hi]
        simp

/-- The actual cutoff determines whether the current reply is inherited at
boundary zero, starts after the first retained current-DOWN acceptance, or
never forms.  In either formed case the returned U is the actual offer and the
counted list is exactly the retained-positive list on every original prefix.
The bank at formation retains its older pending and completed entries. -/
theorem actual_cutoff_formed_up_stage
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let M := registers.payload.downRecord i
        (∀ a : Fin K.length,
          ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
            (K.get a) i M) ∧
          (∀ j : ℕ,
            ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
              (K.take j) i M = []) ∨
        ∃ b, b ≤ K.length ∧
          ∃ (anchor : ReferencePrelaunchFollower.State p rate.eta),
          ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)),
            anchor.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid anchor ∧
            anchor.lastDown = some M ∧
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z b) ∧
            ((Z b).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
            (∀ j : ℕ,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
                (K.take j) i M =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take j).drop b) i) ∧
            (∀ a : Fin K.length, b ≤ a.val →
              ∃ state mem,
                (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                  .ordinary state mem ∧ state.status = .unoccupied ∧
                state.lastDown = some M ∧
                ReferenceFollowerReplyChronology.reply state =
                  ReferenceFollowerReplyChronology.reply anchor ∧
                (ReferenceActivePhysicalStep.upSenderIndex (K.get a).input = i →
                  PublicDiscreteDraws.slotDraw ((K.get a).input.row.2
                    (K.get a).input.time).1 = PublicDiscreteDraws.upSlot →
                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get a).input.row
                    ((K.get a).input.state.activations i) (K.get a).input.time state = .offer U ∧
                  ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare (K.get a).input) =
                      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))) ∧
            (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (K.drop b) i,
              AffineChannelLaw.affineHash entry.sample
                (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)
      | _ => True := by
  classical
  have hformation :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_reply_formation_exhaustion
      rate source rewards C_star C_h e i
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => simp [R, hcut] at hformation ⊢
  | some cut =>
      simp [R, hcut] at hformation ⊢
      cases hcoord : cut.output.preparation.coordinator with
      | first _ => trivial
      | collection _ _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | live registers owned base outcome =>
          cases outcome <;> simp only [hcoord] at hformation ⊢
          rename_i dispatched hstart ledger hinitialization hledger hdomains
            hclock hpending hassignment selection
          let K := cut :: (R.drop (e + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := registers.payload.downRecord i
          rcases hformation with hformed | hretained | hnone
          · cases hchoice :
                (ReferenceFollowerFixedReply.actualChoice cut i).configuration with
              | dagger =>
                  simp [ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt,
                    hchoice] at hformed
              | ordinary anchor memory =>
                  obtain ⟨state, mem, hcfg, hstatus, hlast⟩ := hformed
                  rw [hchoice] at hcfg
                  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hcfg
                  have hstate : state = anchor := heq.1.symm
                  have hmem : mem = memory := heq.2.symm
                  subst state
                  subst mem
                  have hinherited :=
                    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_inherited_current_reply_suffix
                      rate source rewards C_star C_h e i
                  dsimp only at hinherited
                  simp [R, hcut, hcoord, hchoice] at hinherited
                  obtain ⟨hunoccupied, hdomain, U, hfields, hsigma, hsigmapos,
                    hbank, hnU, hoffers, hequations, hentries⟩ := hinherited hlast
                  refine Or.inr ⟨0, by simp, ?_⟩
                  refine ⟨anchor, hunoccupied, hdomain, hlast, U, hfields,
                    hsigma, hsigmapos, ?_, hnU, ?_, ?_, ?_⟩
                  · simpa [Z, ReferenceCollectionSegmentExtraction.endpointState] using hbank
                  · intro j
                    simpa [K, Z, M, List.drop_zero] using hentries j
                  · intro a _
                    exact hoffers a
                  · simpa only [List.drop_zero] using hequations
          · obtain ⟨q, hretained, hfirst⟩ := hretained
            have hsuffix :=
              ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_retained_current_reply_suffix
                rate source rewards C_star C_h e i
            dsimp only at hsuffix
            simp [R, hcut, hcoord] at hsuffix
            obtain ⟨anchor, htail⟩ := hsuffix q hretained
            rcases htail with ⟨_hfollow, hunoccupied, hdomain, hlast, hrest⟩
            rcases hrest with ⟨U, hdata⟩
            rcases hdata with ⟨hfields, hsigma, hsigmapos, hbank, hnU, hrest⟩
            have hentries := hrest.2.1
            refine Or.inr ⟨q.val + 1, by have := q.isLt; simp; omega,
              ?_⟩
            refine ⟨anchor, hunoccupied, hdomain, hlast, U, hfields,
              hsigma, hsigmapos, hbank, hnU, ?_, hrest.2.2.1, hrest.2.2.2.1⟩
            · intro j
              simpa only [M] using hentries j
          · exact Or.inl hnone

/-- The first actual formed-UP threshold is selected from the actual
per-record positives.  Its count is `Q - nU + Q`, where `nU` is the pending
length of the same inherited original bank at formation.  The least prefix
identity is retained for the successor's canonical quota proof. -/
theorem actual_cutoff_formed_up_threshold_count
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let M := registers.payload.downRecord i
        let Q := AffineBatchDecoder.quota p
        (∀ a : Fin K.length,
          ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
            (K.get a) i M) ∧
          (∀ j : ℕ,
            ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
              (K.take j) i M = []) ∨
        ∃ b, b ≤ K.length ∧
          ∃ (anchor : ReferencePrelaunchFollower.State p rate.eta),
          ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)),
            anchor.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid anchor ∧
            anchor.lastDown = some M ∧
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z b) ∧
            ((Z b).upDecoderBank i).pending.length < Q ∧
            (∀ j : ℕ,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
                (K.take j) i M =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take j).drop b) i) ∧
            ((Q - ((Z b).upDecoderBank i).pending.length + Q) >
                (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i).length ∨
            (∃ k, k < (K.drop b).length ∧
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.drop b).take (k + 1)) i).length =
                  Q - ((Z b).upDecoderBank i).pending.length + Q ∧
              ∀ j, j ≤ k →
                (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                  ((K.drop b).take j) i).length <
                    Q - ((Z b).upDecoderBank i).pending.length + Q))
      | _ => True := by
  classical
  have hstage := actual_cutoff_formed_up_stage rate source rewards C_star C_h e i
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => simp [R, hcut] at hstage ⊢
  | some cut =>
      simp [R, hcut] at hstage ⊢
      cases hcoord : cut.output.preparation.coordinator with
      | first _ => trivial
      | collection _ _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | live registers owned base outcome =>
          cases outcome <;> simp only [hcoord] at hstage ⊢
          rename_i dispatched hstart ledger hinitialization hledger hdomains
            hclock hpending hassignment selection
          let K := cut :: (R.drop (e + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := registers.payload.downRecord i
          rcases hstage with hnone | hformed
          · exact Or.inl hnone
          · obtain ⟨b, hb, anchor, U, hunoccupied,
              hdomain, hlast, hfields, hsigma, hsigmapos, hbank, hnU,
              hentries, _hoffers, _hequations⟩ := hformed
            let N := AffineBatchDecoder.quota p -
              ((Z b).upDecoderBank i).pending.length + AffineBatchDecoder.quota p
            have hN : 0 < N := by
              dsimp [N]
              omega
            let xs := K.drop b
            let f := fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
              ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i
            have hunit : ∀ r, (f r).length ≤ 1 := by
              intro r
              exact recordUpPositiveEntries_length_le_one rate r i
            have hcase : N > (xs.flatMap f).length ∨
                ∃ k, k < xs.length ∧
                  ((xs.take (k + 1)).flatMap f).length = N ∧
                  ∀ j, j ≤ k → ((xs.take j).flatMap f).length < N := by
              by_cases hcount : N ≤ (xs.flatMap f).length
              · obtain ⟨k, hk, hprefix, hbefore⟩ :=
                  firstFlatMapPrefix xs f hunit N hN hcount
                exact Or.inr ⟨k, hk, hprefix, hbefore⟩
              · exact Or.inl (by omega)
            refine Or.inr ⟨b, hb, ?_⟩
            refine ⟨anchor, ?_⟩
            refine ⟨U, hunoccupied, hdomain, hlast, hfields, hsigma,
              hsigmapos, hbank, hnU, ?_⟩
            refine ⟨?_, ?_⟩
            · intro j
              have hentry := hentries j
              simpa [xs, f, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
                List.drop_take] using hentry
            · simpa [N, xs, f,
                ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
                List.length_flatMap, List.map_drop, K] using hcase

private theorem choice_of_tail
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      tail = ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  classical
  unfold ReferenceCollectionPhaseHistory.executedTail at htail
  dsimp only at htail
  split at htail <;> try contradiction
  rename_i hselected
  unfold ReferenceCollectionSegmentExtraction.choice
  rw [ite_eq_right hselected]
  cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | first o => cases o <;> simp only [hc] at htail <;> contradiction
  | live registers owned base o =>
    cases o <;> simp only [hc] at htail <;> try contradiction
    cases Option.some.inj htail
    exact ⟨_, rfl, rfl⟩
  | collection payload ledger clock cutoff o =>
    cases o <;> simp only [hc] at htail <;> try contradiction
    cases Option.some.inj htail
    exact ⟨_, rfl, rfl⟩
  | dagger => simp only [hc, reduceCtorEq] at htail
  | invalidCollectionCutoff => simp only [hc, reduceCtorEq] at htail

private theorem choice_frame
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection payload out saved) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      c.payload = payload ∧
      out.pending = ReferenceCollectionPhaseHistory.eraseEvent c.preLedger.pending
        (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
  obtain ⟨tail, htail, hframe, _hsigma⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame r.input payload out saved (by
      rw [← r.output_eq]
      exact hout)
  obtain ⟨c, hc, ht⟩ := choice_of_tail r tail htail
  have hpost : r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights := by
    rw [r.output_eq]
    exact ReferenceCollectionSegmentExtraction.choice_tail r.input c hc
  have hnext : r.output.coordinator.configuration = .collection payload out saved := by
    rw [r.output_eq] at hout ⊢
    exact hout
  have hpayload := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights
  rw [← hpost, hnext] at hpayload
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload, reduceCtorEq,
    Option.some.injEq, false_or] at hpayload
  refine ⟨c, hc, hpayload.symm, ?_⟩
  rw [ht] at hframe
  exact hframe

private theorem actual_record_of_index
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (n : ℕ) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[n]? = some r)
    (htime : r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h ≤ r.input.time.val := by omega
  have hindex : r.input.time.val - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = n := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact hr

private theorem pending_antitone
    (L : ℕ) (P : Fin L → Finset (Fin (p.m - 1)))
    (hstep : ∀ n (hn : n + 1 < L),
      P ⟨n + 1, hn⟩ ⊆ P ⟨n, by omega⟩) :
    ∀ a b : Fin L, a.val ≤ b.val → P b ⊆ P a := by
  intro a ⟨b, hb⟩ hab
  change a.val ≤ b at hab
  induction b with
  | zero =>
    have ha : a = (⟨0, hb⟩ : Fin L) := by
      apply Fin.ext
      change a.val = 0
      omega
    rw [ha]
  | succ b ih =>
    by_cases heq : a.val = b + 1
    · have ha : a = ⟨b + 1, hb⟩ := Fin.ext heq
      rw [ha]
    · exact (hstep b hb).trans (ih (by omega) (by omega))

/-- Join one literal source record to the new receiver API while keeping the
chronology's already constructed offer. All local inputs are explicit here;
the actual-prefix detector below discharges them. -/
private theorem receiver_for_fixed_offer
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt = r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (hstatus : state.status = .unoccupied)
    (hcurrent : state.lastDown = some (c.payload.downRecord i))
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot)
    (hpending : i ∈ c.preLedger.pending)
    (hoffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time state = .offer U) :
    ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      CoordinatorUpReception.receptionGate d.input ∧
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt
        rate rewards C_star C_h source i U r.input.time ∧
      (d.raw = some (ReferenceCollectionUpFailureReadoutV2.enc rate U) →
        ReferenceCollectionPhaseHistory.AcceptedUp r.input i U ∧
        ∃ finished saved, r.output.next.coordinator = .collection c.payload finished saved ∧
          i ∉ finished.pending) := by
  have hreceiver :=
    ReferenceOriginalCollectionCurrentUpReceiver.actual_collection_current_up_receiver
      rate rewards C_star C_h source k
  dsimp only at hreceiver
  rw [hr] at hreceiver
  rcases hreceiver with hnone | ⟨actual, hactual, hdata⟩
  · rw [hc] at hnone
    contradiction
  · have heq : actual = c := Option.some.inj (hactual.symm.trans hc)
    subst actual
    obtain ⟨_birth, _hbefore, _hbirth, _hsigma, _hrows, _hJ, _hrewards,
      _recording, _L, d, _received, _bank, _finished, _clock,
      _htail, _hrecording, _hstart, _hpendingL, _hsigmaL, _hsite, _hcheck,
      hd, _hinput, _hreception, _hnotInvalid, _hcases, _hfinish, _hclock,
      _hraw, _hexpected, _hbankInput, _htime, _hsample, hlocal⟩ := hdata
    obtain ⟨actualU, hactualOffer, _hfields, _hUstart, _hpositive, _hword,
      hi, hgate, _haw, _horiginal, hsource, _haccept, hmatching⟩ :=
      hlocal i state memory hindex hconfiguration hstatus hcurrent hslot hpending
    have hU : actualU = U :=
      ActiveFollowerQueueOperation.UpOfferResult.offer.inj (hactualOffer.symm.trans hoffer)
    subst actualU
    refine ⟨d, hd, hi, hgate, hsource, ?_⟩
    intro hraw
    obtain ⟨ha, saved, hout, hnot⟩ := hmatching hraw
    exact ⟨ha, _finished, saved, hout, hnot⟩

private theorem receiver_ledger_pending
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt = r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.input.ledger.pending = c.preLedger.pending := by
  have hreceiver :=
    ReferenceOriginalCollectionCurrentUpReceiver.actual_collection_current_up_receiver
      rate rewards C_star C_h source k
  dsimp only at hreceiver
  rw [hr] at hreceiver
  rcases hreceiver with hnone | ⟨actual, hactual, hdata⟩
  · rw [hc] at hnone
    contradiction
  · have heq : actual = c := Option.some.inj (hactual.symm.trans hc)
    subst actual
    obtain ⟨_birth, _hbefore, _hbirth, _hsigma, _hrows, _hJ, _hrewards,
      _recording, L, actualD, _received, _bank, _finished, _clock,
      _htail, _hrecording, _hstart, hpendingL, _hsigmaL, _hsite, _hcheck,
      hdiag, hinput, _hrest⟩ := hdata
    have hD : actualD = d := Option.some.inj (hdiag.symm.trans hd)
    subst actualD
    rw [hinput]
    exact hpendingL

/-- At any actually selected two-bank threshold, the original launched run
retains its inherited pending equations, then completes a second bank made
exactly from the postformation positives after the first fill.  The completion
is a physical decoder update, including its detecting entry and raw output.
The count and endpoints are local selectors; no run or bank is supplied. -/
theorem actual_cutoff_up_second_bank
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        ∀ b a : ℕ, b ≤ a → a < K.length →
          let positive := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            ((K.take (a + 1)).drop b) i
          let channel := (Z b).upDecoderBank i
          let Q := AffineBatchDecoder.quota p
          positive.length = Q - channel.pending.length + Q →
          let window := positive.drop (Q - channel.pending.length)
          ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
            (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
            (record : ReferenceCompletePhysicalHistory.RoundRecord p rate)
            (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
            first = channel.pending ++ positive.take (Q - channel.pending.length) ∧
            first.length = Q ∧ window.length = Q ∧
            window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
            record ∈ (K.take (a + 1)).drop b ∧ record.input.time = last.time ∧
            record.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
            ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt record i window ∧
            d.raw = AffineBatchDecoder.batchOutput window ∧
            (Z (a + 1)).upDecoderBank i =
              ⟨[], channel.completed ++ [first, window]⟩ ∧
            AffineBatchDecoder.collected ((Z (a + 1)).upDecoderBank i) =
              AffineBatchDecoder.collected channel ++ positive ∧
            (∀ entry ∈ window,
              ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
                (e + b) ≤ entry.time.val ∧ entry.time.val ≤ last.time.val)
      | _ => True := by
  classical
  have hreplay :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_original_up_bank_replay
      rate source rewards C_star C_h e
  have hframes :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_collection_prefix
      rate source rewards C_star C_h e
  dsimp only at hreplay hframes ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h with hR
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hreplay hframes ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hreplay hframes ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hreplay hframes ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      obtain ⟨initial, active, _hlaunch, _hfirst, _hbank, hinvariant, hseed,
        hRuns, _hbanks⟩ := hreplay
      obtain ⟨_hrecords, _hnoLater, hcollections⟩ := hframes
      intro b a hba ha hcount
      obtain ⟨span, hdrop, hend⟩ := hRuns (a + 1) (by omega)
      obtain ⟨spanB, _hdropB, hendB⟩ := hRuns b (by omega)
      obtain ⟨outLedger, outSaved, hout⟩ := hcollections (a + 1) (by omega) (by omega)
      have hordinary : (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (e + (a + 1)) span active).finalState.coordinator ≠ .dagger := by
        rw [hend, hout]
        exact fun h => nomatch h
      have hinterval : ReferenceCoordinatorUpIntervalWindow.intervalRecords
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (e + b) (e + (a + 1)) span active =
            (K.take (a + 1)).drop b := by
        unfold ReferenceCoordinatorUpIntervalWindow.intervalRecords
        rw [← List.drop_drop, hdrop]
      have hpositive :=
        ReferenceCoordinatorUpIntervalWindow.run_interval_actual_trace_positives_eq_retained
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (e + b) (e + (a + 1)) (by omega) span active
          hinvariant hordinary i
      have hcount' :
          (AffineBatchDecoder.positives p
            (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
              (ReferenceCoordinatorUpIntervalWindow.intervalRecords initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                (e + b) (e + (a + 1)) span active) i)
            (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
              (e + b) (e + (a + 1)) span active)).length =
            AffineBatchDecoder.quota p -
              ((ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                (e + b) spanB active).finalState.upDecoderBank i).pending.length +
              AffineBatchDecoder.quota p := by
        rw [hpositive, hinterval, hendB]
        exact hcount
      let H := (K.take (a + 1)).drop b
      let positive := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries H i
      let channel := (Z b).upDecoderBank i
      let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace H i
      let rounds := H.map (fun r => r.input.time)
      have hintervalRaw := hinterval
      unfold ReferenceCoordinatorUpIntervalWindow.intervalRecords at hintervalRaw
      have hpositiveH : AffineBatchDecoder.positives p trace rounds = positive := by
        simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds, hinterval]
          using hpositive
      dsimp only [trace, rounds, H, positive] at hpositiveH
      have hgeometry := ReferenceCoordinatorUpIntervalWindow.run_interval_two_batch_window
        initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start (e + b) (e + (a + 1)) (by omega) span active
        hinvariant hordinary i (hseed i) hcount'
      dsimp only at hgeometry
      simp only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, hintervalRaw] at hgeometry
      rw [hendB, hend, hpositiveH] at hgeometry
      obtain ⟨first, last, index, _hrun, _hfull, hfirst, hfirstLen, hwindowLen,
        hchronological, _hdisjoint, _hcountBound, hbounds, hlast, hdecision,
        _hindexRound, _hlastEligible, _hlastSample, hmax, _hrawWindow⟩ := hgeometry
      have hsaved := ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
        initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start (e + b) (e + (a + 1)) (by omega) span active
        hinvariant hordinary i (hseed i) hcount'
      dsimp only at hsaved
      simp only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, hintervalRaw] at hsaved
      rw [hendB, hend, hpositiveH] at hsaved
      obtain ⟨first', last', index', record, d, hfirst', _hfirstLen', _hwindowLen',
        _hchronological', hlast', hdecision', _hindex', hrecord, hrecordTime,
        hd, hi, htime, _hlastEntry, _hsample, hcall,
        _hconnected, _hrecordReplay, _hbankInput, hbefore, happend,
        _hcleared, _hcompleted, hafter, _hrawTransition, hraw,
        _htransition, hrun, hrunFull⟩ := hsaved
      have hlastEq : last'.time = last.time := Option.some.inj (hdecision'.symm.trans hdecision)
      have hfirstEq : first' = first := hfirst'.trans hfirst.symm
      rw [hfirstEq] at hrun
      have hbankFinal := hrun.symm.trans hrunFull
      have hreplayed :=
        ReferenceCoordinatorUpIntervalWindow.run_interval_upDecoderBank_replay
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (e + b) (e + (a + 1)) (by omega) span active
          hinvariant hordinary i
      have hcollected := hreplayed.2
      rw [hend, hendB, hintervalRaw] at hcollected
      have hchronRounds :=
        ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (e + b) (e + (a + 1)) (by omega) span active hinvariant hordinary
      have hchronH : H.Pairwise
          (fun r s => r.input.time.val < s.input.time.val) := by
        have h : rounds.Pairwise (fun r s => r.val < s.val) := by
          simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds, hinterval]
            using hchronRounds
        exact (List.pairwise_map (f := fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
          r.input.time) (R := fun u v : Fin p.T => u.val < v.val)).mp h
      have hmemPositive : last' ∈ AffineBatchDecoder.positives p trace rounds := by
        rw [hpositiveH]
        exact List.mem_of_mem_drop hlast'
      have heligible := (AffineBatchDecoder.mem_positives_iff p trace rounds last').mp hmemPositive
      have hat := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
        H i hchronH record hrecord
      have htrace : trace last'.time = CoordinatorUpReception.roundInput d.input := by
        change ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace H i last'.time = _
        rw [← hrecordTime, hat]
        simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hd, hi,
          ↓reduceIte, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
      have hentry : AffineBatchDecoder.entry p trace last'.time =
          AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt d.input) d.input.time := by
        unfold AffineBatchDecoder.entry
        rw [htrace, htime.trans hrecordTime]
        rfl
      have heligibleD : AffineBatchDecoder.eligible
          (CoordinatorUpReception.traceAt d.input d.input.time) := by
        change AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
        rw [← htrace]
        exact heligible.2.1
      rw [hbefore, hentry] at happend
      have hlength : (d.input.upDecoderBank i).pending.length + 1 =
          AffineBatchDecoder.quota p := by
        have h := congrArg List.length happend
        rw [List.length_append, List.length_singleton, hwindowLen] at h
        exact h
      have htransition := AffineBatchDecoder.decodeStep_complete p
        (CoordinatorUpReception.traceAt d.input) (d.input.upDecoderBank i)
        d.input.time heligibleD hlength
      obtain ⟨callLedger, _hsite, hcheck, hinput, _hcallRest⟩ := hcall
      have hcheckD : CoordinatorUpReception.receptionInputCheck d.input = true := by
        rw [hinput]
        exact hcheck
      have hdomain :=
        (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheckD
      have hphysical : ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt
          record i window := by
        refine ⟨d, hd, hi, hdomain, heligibleD, ?_, hwindowLen, ?_, hraw⟩
        · rw [AffineBatchDecoder.positiveAt, ite_eq_left heligibleD]
          exact happend.symm
        · rw [hafter, CoordinatorUpReception.decoderTransition, hi, htransition]
          dsimp only
          rw [happend]
      refine ⟨first, last', record, d, hfirst, hfirstLen, hwindowLen,
        hchronological, hlast', hdecision', hrecord, hrecordTime,
        hd, hi, hphysical, hraw, hbankFinal.symm, hcollected, ?_⟩
      intro entry he
      exact ⟨(hbounds entry he).1, by rw [hlastEq]; exact hmax entry he⟩

private theorem selected_up_fields
    (slice : ContinuousLearningRows.Slice p) (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p slice = some (1, i)) :
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice = i := by
  classical
  unfold ReferenceSelectedAffinePairLaw.selectedChannel
    ReferenceSelectedAffinePairLaw.channelFromDraws at h
  by_cases hd : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.downSlot
  · rw [ite_eq_left hd] at h
    have hdir := congrArg Prod.fst (Option.some.inj h)
    exact False.elim ((show (0 : Fin 2) ≠ 1 by decide) hdir)
  · rw [ite_eq_right hd] at h
    by_cases hu : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot
    · rw [ite_eq_left hu] at h
      exact ⟨hu, congrArg Prod.snd (Option.some.inj h)⟩
    · rw [ite_eq_right hu] at h
      contradiction

/-- The actual formed-UP two-bank threshold forces matching physical
acceptance and pending erasure, or an original fixed-awaited ambiguity event.
The boundary, reply, bank, and all-prefix entry identity are derived from this
same actual cutoff. An exact positive-count equality is a local threshold
selector, not an assumed source law or quota. -/
theorem actual_cutoff_formed_up_threshold_or_source_ambiguity
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let M := registers.payload.downRecord i
        let Q := AffineBatchDecoder.quota p
        (∀ a : Fin K.length, ¬ replyFormedAt (K.get a) i M) ∧
          (∀ j : ℕ, formedPositiveEntries (K.take j) i M = []) ∨
        ∃ b, b ≤ K.length ∧
          ∃ (anchor : ReferencePrelaunchFollower.State p rate.eta)
            (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
            anchor.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid anchor ∧
            anchor.lastDown = some M ∧
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z b) ∧
            ((Z b).upDecoderBank i).pending.length < Q ∧
            (∀ j : ℕ, formedPositiveEntries (K.take j) i M =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take j).drop b) i) ∧
            (let N := Q - ((Z b).upDecoderBank i).pending.length + Q
             (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i).length < N ∨
               ∃ m : ℕ, 0 < m ∧ m ≤ (K.drop b).length ∧
                 (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                   ((K.drop b).take m) i).length = N ∧
                 ∀ n : ℕ, n < m →
                   (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                     ((K.drop b).take n) i).length < N) ∧
            ∀ a : Fin K.length, b ≤ a.val →
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take (a.val + 1)).drop b) i).length =
                  Q - ((Z b).upDecoderBank i).pending.length + Q →
              ∃ q : Fin K.length, b ≤ q.val ∧ q.val ≤ a.val ∧
                ((ReferenceCollectionPhaseHistory.AcceptedUp (K.get q).input i U ∧
                  ∃ ledger saved, (K.get q).output.next.coordinator =
                    .collection registers.payload ledger saved ∧ i ∉ ledger.pending) ∨
                 ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpFixedAwaitedCompletionAt
                   rate rewards C_star C_h source (K.get q).input.time)
      | _ => True := by
  classical
  have hstage := actual_cutoff_formed_up_stage rate source rewards C_star C_h e i
  have hbankCut := actual_cutoff_up_second_bank rate source rewards C_star C_h e i
  have hframes :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_collection_prefix
      rate source rewards C_star C_h e
  dsimp only at hstage hbankCut hframes ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h with hR
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hstage hbankCut hframes ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hstage hbankCut hframes ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hstage hbankCut hframes ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      rcases hstage with hnone | hformed
      · exact Or.inl hnone
      · obtain ⟨b, hb, anchor, U, hunoccupied, hdomain, hlast, hfields,
          hsigma, hsigmapos, hbank, hnU, hentries, hoffers, hequations⟩ := hformed
        refine Or.inr ⟨b, hb, anchor, U, hunoccupied, hdomain, hlast, hfields,
          hsigma, hsigmapos, hbank, hnU, hentries, ?_, ?_⟩
        · exact ReferenceFirstReplacementCollectionPureUpWindowCut.retained_positive_prefix_cut
            (K.drop b) i
            (AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
              AffineBatchDecoder.quota p) (by omega)
        intro a hba hcount
        obtain ⟨hrecords, _hnoLater, hcollections⟩ := hframes
        change (∀ q : Fin K.length,
          R[e + q.val]? = some (K.get q) ∧
          (K.get q).input.time.val = start + (e + q.val) ∧
          (K.get q).input.row = source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
          (K.get q).input.state = Z q.val ∧
          (K.get q).output.next = Z (q.val + 1)) at hrecords
        change (∀ j : ℕ, 1 ≤ j → j ≤ K.length →
          ∃ out saved, (Z j).coordinator = .collection registers.payload out saved) at hcollections
        have hsourceIndex : ∀ q : Fin K.length, e + q.val < R.length := by
          intro q
          exact (List.getElem?_eq_some_iff.mp (hrecords q).1).1
        have hsourceGet : ∀ q : Fin K.length,
            R[e + q.val]'(hsourceIndex q) = K.get q := by
          intro q
          exact (List.getElem?_eq_some_iff.mp (hrecords q).1).2
        have hactual : ∀ q : Fin K.length,
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
              (K.get q).input.time source = some (K.get q) := by
          intro q
          exact actual_record_of_index rate source rewards C_star C_h (e + q.val)
            (K.get q) (hrecords q).1 (hrecords q).2.1
        have houtputs : ∀ q : Fin K.length, ∃ out saved,
            (Z (q.val + 1)).coordinator = .collection registers.payload out saved := by
          intro q
          exact hcollections (q.val + 1) (by omega) (by have := q.isLt; omega)
        choose out saved hout using houtputs
        have hchoiceData : ∀ q : Fin K.length,
            ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
              ReferenceCollectionSegmentExtraction.choice (K.get q).input = some c ∧
              c.payload = registers.payload ∧
              (out q).pending = ReferenceCollectionPhaseHistory.eraseEvent c.preLedger.pending
                (ReferenceCollectionPhaseHistory.acceptedLabel (K.get q).input) := by
          intro q
          apply choice_frame (K.get q) registers.payload (out q) (saved q)
          rw [(hrecords q).2.2.2.2]
          exact hout q
        choose cs hc hpayload hframe using hchoiceData
        let P := fun q : Fin K.length => (cs q).preLedger.pending
        have hstep : ∀ n (hn : n + 1 < K.length),
            P ⟨n + 1, hn⟩ ⊆ P ⟨n, by omega⟩ := by
          intro n hn
          let q : Fin K.length := ⟨n, by omega⟩
          let next : Fin K.length := ⟨n + 1, hn⟩
          have hstate : (K.get next).input.state.coordinator =
              .collection registers.payload (out q) (saved q) := by
            rw [(hrecords next).2.2.2.1]
            exact hout q
          have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
            (K.get next).input registers.payload (out q) (saved q) (cs next) hstate (hc next)
          change (cs next).preLedger.pending ⊆ (cs q).preLedger.pending
          rw [hpre.1, hframe q]
          cases ReferenceCollectionPhaseHistory.acceptedLabel (K.get q).input with
          | none => exact Finset.Subset.refl _
          | some j => exact Finset.erase_subset j _
        have hmono := pending_antitone K.length P hstep
        let H := (K.take (a.val + 1)).drop b
        let positive := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries H i
        let channel := (Z b).upDecoderBank i
        let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
        have hindices : ∀ r ∈ H, ∃ q : Fin K.length,
            b ≤ q.val ∧ q.val ≤ a.val ∧ K.get q = r := by
          intro r hr
          obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hr
          have hn' : b + n < min (a.val + 1) K.length := by
            have h := hn
            simp only [H, List.length_drop, List.length_take] at h
            omega
          have hboundK : b + n < K.length := hn'.trans_le (Nat.min_le_right _ _)
          have hboundA : b + n < a.val + 1 := hn'.trans_le (Nat.min_le_left _ _)
          refine ⟨⟨b + n, hboundK⟩, Nat.le_add_right b n,
            Nat.lt_succ_iff.mp hboundA, ?_⟩
          simpa only [H, List.get_eq_getElem, List.getElem_drop, List.getElem_take] using hget
        obtain ⟨first, last, record, d, _hfirst, _hfirstLen, hwindowLen,
          _hwindowChronology, _hlastWindow, _hdecision, hrecord, hrecordTime,
          hd, hi, hphysical, hraw, _hfinalBank, _hcollected, hbounds⟩ :=
          hbankCut b a.val hba a.isLt hcount
        obtain ⟨q, hbq, hqa, hqRecord⟩ := hindices record hrecord
        have hdq : (K.get q).output.coordinator.up = some d := by rw [hqRecord]; exact hd
        have hpendingEq := receiver_ledger_pending rate source rewards C_star C_h
          ⟨e + q.val, hsourceIndex q⟩ (K.get q) (hsourceGet q) (cs q) (hc q) d hdq
        have hphysicalCompletion := hphysical
        change (∀ entry ∈ window, start + (e + b) ≤ entry.time.val ∧
          entry.time.val ≤ last.time.val) at hbounds
        obtain ⟨physicalD, hphysicalDiag, hphysicalI, _hphysicalDomain,
          heligible, _hphysicalRest⟩ := hphysical
        have hphysicalD : physicalD = d := Option.some.inj (hphysicalDiag.symm.trans hd)
        subst physicalD
        have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1
        have hPendingQ : i ∈ P q := by
          change i ∈ (cs q).preLedger.pending
          rw [← hpendingEq, ← hi]
          exact hgate.2.2
        have hawait : ∀ j : Fin K.length, b ≤ j.val → j.val ≤ q.val →
            ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i →
            PublicDiscreteDraws.slotDraw ((K.get j).input.row.2 (K.get j).input.time).1 =
              PublicDiscreteDraws.upSlot →
            ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
              (K.get j).output.coordinator.up = some diagnostic ∧
              ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt
                rate rewards C_star C_h source i U (K.get j).input.time ∧
              (diagnostic.raw = some (ReferenceCollectionUpFailureReadoutV2.enc rate U) →
                ReferenceCollectionPhaseHistory.AcceptedUp (K.get j).input i U ∧
                ∃ finished saved, (K.get j).output.next.coordinator =
                  .collection registers.payload finished saved ∧ i ∉ finished.pending) := by
          intro j hbj hjq hindex hslot
          obtain ⟨state, memory, hconfiguration, hstatus, hcurrent, _hreply, ho⟩ := hoffers j hbj
          obtain ⟨diagnostic, hdiag, _hi, _hgate, hsource, hmatching⟩ :=
            receiver_for_fixed_offer rate source rewards C_star C_h
              ⟨e + j.val, hsourceIndex j⟩ (K.get j) (hsourceGet j) (cs j) (hc j)
              i state memory U hindex hconfiguration hstatus
              (by rw [hpayload j]; exact hcurrent) hslot
              (hmono j q hjq hPendingQ) (ho hindex hslot).1
          refine ⟨diagnostic, hdiag, hsource, ?_⟩
          intro hraw
          obtain ⟨ha, finished, saved, hfinished, hnot⟩ := hmatching hraw
          rw [hpayload j] at hfinished
          exact ⟨ha, finished, saved, hfinished, hnot⟩
        have hword : ∀ r ∈ H, ∀ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
            r.output.coordinator.up = some diagnostic → diagnostic.input.selectedFollower = i →
            AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) →
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
          intro r hr diagnostic hdiag hselected he
          obtain ⟨j, hbj, _hja, hjr⟩ := hindices r hr
          obtain ⟨_L, _hsite, _hledger, _hbank, _htime, _hobs, hsender, _hsample,
            hslot, _hrest⟩ :=
            ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hdiag
          have hg := (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp he.1
          obtain ⟨_state, _memory, _hc, _hu, _hm, _hr, ho⟩ := hoffers j hbj
          rw [hjr] at ho
          exact (ho (hsender.symm.trans hselected) (hslot.symm.trans hg.2.1)).2
        have hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
          apply (AffineBatchDecoder.satisfies_samples_iff _ _).mpr
          intro entry he
          apply (AffineBatchDecoder.equation_iff_affineHash _ _).mpr
          apply hequations entry
          have hp := List.mem_of_mem_drop he
          unfold ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries at hp ⊢
          obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp hp
          apply List.mem_flatMap.mpr
          refine ⟨r, ?_, he⟩
          dsimp only [H] at hr
          rw [List.drop_take] at hr
          exact List.mem_of_mem_take hr
        have hcases :=
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.batchOutput_eq_sent_or_multiple
            window (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsat
        refine ⟨q, hbq, hqa, ?_⟩
        rcases hcases with hunique | ⟨_hnone, hmultiple, _hother⟩
        · left
          obtain ⟨_L, _hsite, _hledger, _hbank, _htime, _hobs, hsender, _hsample,
            hslot, _hrest⟩ :=
            ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record d hd
          have hindex : ReferenceActivePhysicalStep.upSenderIndex (K.get q).input = i := by
            rw [hqRecord]
            exact hsender.symm.trans hi
          have hslotUp : PublicDiscreteDraws.slotDraw
              ((K.get q).input.row.2 (K.get q).input.time).1 = PublicDiscreteDraws.upSlot := by
            rw [hqRecord]
            exact hslot.symm.trans hgate.2.1
          obtain ⟨diagnostic, hdiag, _hsource, hmatching⟩ := hawait q hbq le_rfl hindex hslotUp
          have hD : diagnostic = d := Option.some.inj (hdiag.symm.trans hdq)
          subst diagnostic
          exact hmatching (hraw.trans hunique)
        · right
          let formation : Fin p.T := (K.get ⟨b, by omega⟩).input.time
          have hformationTime : formation.val = start + (e + b) := (hrecords ⟨b, by omega⟩).2.1
          have hqTime : (K.get q).input.time.val = start + (e + q.val) := (hrecords q).2.1
          have hlastTime : last.time = (K.get q).input.time := by rw [hqRecord]; exact hrecordTime.symm
          refine ⟨i, U, window, formation, ?_, ?_, ?_, ?_, ?_⟩
          · rw [ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpCompletedAt, hactual q]
            rw [hqRecord]
            exact hphysicalCompletion
          · change formation.val ≤ (K.get q).input.time.val
            omega
          · exact (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff window).mp hmultiple
          · intro entry he
            have hePositive : entry ∈ positive := List.mem_of_mem_drop he
            obtain ⟨r, hr, diagnostic, hdiag, hselected, heEligible, heTime,
              hslot, _heSample, _hsample, _hhash⟩ :=
              ReferenceFirstReplacementCollectionUpOfferCut.retained_positive_entry_has_conditional_offer_equation
                H i U hword entry hePositive
            obtain ⟨j, hbj, _hja, hjr⟩ := hindices r hr
            have hentryTime : entry.time = (K.get j).input.time := by rw [hjr]; exact heTime
            have hjTime := (hrecords j).2.1
            have hjq : j.val ≤ q.val := by
              have hbound := (hbounds entry he).2
              rw [hlastTime, hentryTime] at hbound
              omega
            have hg := (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp heEligible.1
            obtain ⟨_L, _hsite, _hledger, _hbank, _htime, _hobs, hsender, _hrest⟩ :=
              ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hdiag
            have hindex : ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i := by
              rw [hjr]
              exact hsender.symm.trans hselected
            have hslotUp : PublicDiscreteDraws.slotDraw
                ((K.get j).input.row.2 (K.get j).input.time).1 = PublicDiscreteDraws.upSlot := by
              rw [hjr]
              exact hslot.symm.trans hg.2.1
            obtain ⟨_diagnostic, _hdiag, haw, _hmatching⟩ := hawait j hbj hjq hindex hslotUp
            rw [ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt, hactual j] at haw
            obtain ⟨_d, _hd, _hi, _hdom, _hcut, _hslot, _hpending, hsent, _hparse, _haccept⟩ := haw
            refine ⟨?_, ?_, ?_⟩
            · have hbound := (hbounds entry he).1
              omega
            · rw [hlastTime] at hbounds
              exact (hbounds entry he).2
            · rw [hentryTime, ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpSentAt, hactual j]
              exact hsent
          · intro v hfv hvq hselected
            change formation.val ≤ v.val at hfv
            change v.val ≤ (K.get q).input.time.val at hvq
            let n := v.val - (start + e)
            have hnv : start + (e + n) = v.val := by dsimp [n]; omega
            have hbn : b ≤ n := by omega
            have hnq : n ≤ q.val := by omega
            let j : Fin K.length := ⟨n, by have := q.isLt; omega⟩
            have htimeEq : (K.get j).input.time = v := Fin.ext (by
              have h := (hrecords j).2.1
              change (K.get j).input.time.val = v.val
              change (K.get j).input.time.val = start + (e + n) at h
              omega)
            obtain ⟨hslotUp, hdraw⟩ := selected_up_fields _ i hselected
            have hrow := (hrecords j).2.2.1
            have hindex : ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i := by
              rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hrow, htimeEq]
              exact hdraw
            have hslot : PublicDiscreteDraws.slotDraw
                ((K.get j).input.row.2 (K.get j).input.time).1 = PublicDiscreteDraws.upSlot := by
              rw [hrow, htimeEq]
              exact hslotUp
            obtain ⟨_d, _hd, haw, _hmatch⟩ := hawait j hbn hnq hindex hslot
            rw [htimeEq] at haw
            exact haw

/-- The first actual threshold and its actual detected outcome are produced
together, with the same formation boundary and reply.  A shortage retains the
whole inherited bank; an empty suffix cannot enter the reached branch. -/
theorem actual_cutoff_formed_up_first_threshold_detector
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let M := registers.payload.downRecord i
        let Q := AffineBatchDecoder.quota p
        (∀ a : Fin K.length, ¬ replyFormedAt (K.get a) i M) ∧
          (∀ j : ℕ, formedPositiveEntries (K.take j) i M = []) ∨
        ∃ b, b ≤ K.length ∧
          ∃ (anchor : ReferencePrelaunchFollower.State p rate.eta)
            (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
            anchor.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid anchor ∧
            anchor.lastDown = some M ∧
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z b) ∧
            ((Z b).upDecoderBank i).pending.length < Q ∧
            (∀ j : ℕ, formedPositiveEntries (K.take j) i M =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take j).drop b) i) ∧
            (let N := Q - ((Z b).upDecoderBank i).pending.length + Q
             (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i).length < N ∨
               ∃ m : ℕ, 0 < m ∧ m ≤ (K.drop b).length ∧
                 (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                   ((K.drop b).take m) i).length = N ∧
                 (∀ n : ℕ, n < m →
                   (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                     ((K.drop b).take n) i).length < N) ∧
                 (formedPositiveEntries (K.take (b + m)) i M).length = N ∧
                 ∃ q : Fin K.length, b ≤ q.val ∧ q.val < b + m ∧
                   ((ReferenceCollectionPhaseHistory.AcceptedUp (K.get q).input i U ∧
                     ∃ ledger saved, (K.get q).output.next.coordinator =
                       .collection registers.payload ledger saved ∧ i ∉ ledger.pending) ∨
                    ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpFixedAwaitedCompletionAt
                      rate rewards C_star C_h source (K.get q).input.time))
      | _ => True := by
  classical
  have hdetector := actual_cutoff_formed_up_threshold_or_source_ambiguity
    rate source rewards C_star C_h e i
  dsimp only at hdetector ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hdetector ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hdetector ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hdetector ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      rcases hdetector with hnone | hformed
      · exact Or.inl hnone
      · obtain ⟨b, hb, anchor, U, hu, hdomain, hlast, hfields, hsigma,
          hpositive, hbank, hnU, hentries, hthreshold, hdetect⟩ := hformed
        refine Or.inr ⟨b, hb, anchor, U, hu, hdomain, hlast, hfields,
          hsigma, hpositive, hbank, hnU, hentries, ?_⟩
        rcases hthreshold with hshort | ⟨m, hmpos, hmlen, hreach, hbefore⟩
        · exact Or.inl hshort
        · have hbound : b + m ≤ K.length := by
            change m ≤ (K.drop b).length at hmlen
            rw [List.length_drop] at hmlen
            change b ≤ K.length at hb
            omega
          let a : Fin K.length := ⟨b + m - 1, by omega⟩
          have hba : b ≤ a.val := by dsimp only [a]; omega
          have hprefix : (K.take (a.val + 1)).drop b = (K.drop b).take m := by
            rw [List.drop_take]
            have hlen : a.val + 1 - b = m := by dsimp only [a]; omega
            rw [hlen]
          have hcount :
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take (a.val + 1)).drop b) i).length =
              AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
                AffineBatchDecoder.quota p := by
            rw [hprefix]
            exact hreach
          obtain ⟨q, hbq, hqa, houtcome⟩ := hdetect a hba hcount
          refine Or.inr ⟨m, hmpos, hmlen, hreach, hbefore, ?_, q, hbq, ?_, houtcome⟩
          · rw [hentries (b + m), List.drop_take]
            have hlen : b + m - b = m := by omega
            rw [hlen]
            exact hreach
          · change q.val ≤ b + m - 1 at hqa
            omega

end Bandits.Support.ReferenceOriginalCollectionFormedUpThreshold

end
