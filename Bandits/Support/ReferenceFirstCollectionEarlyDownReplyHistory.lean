/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffRetainedDownReplySeed

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection fixed reply after an earlier DOWN

Sources: `sources/zip4/manuscript/05_binary_transport.tex:45-53,70-88,100-124`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,192-209,246-295,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.

The result extends the integrated actual first-cutoff seed through the rest of
the same original collection interval. Its suffix conclusions keep the actual
coordinator and follower failure branches; fixed UP words are conditional on
the real checked offer and require no positive receiver observation.

The downstream first-collection awaited-UP receiver trace still needs ordinary
preparations, moving-ledger acceptance, receiver calls on all selected rounds,
enough positives, membership in the same second completed batch, and transport
to the original launch stratum. Identification of the retained numerical tuple
with the manuscript's calendar services is a separate producer.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstCollectionEarlyDownReplyHistory

variable {p : ConstructorDimensions.Parameters}

private theorem connected_endpoint_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial left right : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hl : ReferenceActivePhysicalHorizon.Connected initial records left)
    (hr : ReferenceActivePhysicalHorizon.Connected initial records right) :
    left = right := by
  induction records generalizing initial left right with
  | nil =>
      change left = initial at hl
      change right = initial at hr
      exact hl.trans hr.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hl hr
      exact ih hl.2 hr.2

private theorem run_prefix_records
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records.take k =
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
      (by omega) active).records := by
  revert hspan hk
  induction count with
  | zero =>
      intro hspan hk
      have hkzero : k = 0 := by omega
      subst k
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      intro hspan hk
      by_cases heq : k = count + 1
      · subst k
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hkle : k ≤ count := by omega
        rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
          initial rows selected rewards start count hspan active,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hkle)]
        exact ih (by omega) hkle

/-- Prefix boundaries are the literal inputs and successors of the indexed
records in the original all-active physical run. -/
private theorem run_prefix_endpoints
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) active).finalState =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
          hspan active).records[n]'(by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
      (by omega) active).finalState =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
          hspan active).records[n]'(by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n
    (by omega)
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefix]
    exact htake)
  have hchainPrefix := ReferenceFollowerReplyChronology.connected_take_to_input
    hconnected n hnFull
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] hchainPrefix rfl
  have hrecordsNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hrecordsNext]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem run_record_time_of_lookup
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).records[n]? = some record) :
    record.input.time.val = start + n := by
  have hmap :
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.map fun r => r.input.time.val)[n]? =
        some record.input.time.val := by
    simp only [List.getElem?_map, hget, Option.map_some]
  rw [ReferenceActivePhysicalHorizon.run_time_values] at hmap
  have hn : n < count := by
    have hlen := (List.getElem?_eq_some_iff.mp hget).1
    rw [ReferenceActivePhysicalHorizon.run_record_count] at hlen
    exact hlen
  have hcalendar :
      (ReferenceActivePhysicalHorizon.calendar start count)[n]? = some (start + n) := by
    have hbound : n < (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hn
    rw [List.getElem?_eq_getElem hbound]
    simp [ReferenceActivePhysicalHorizon.calendar]
  rw [hcalendar] at hmap
  exact (Option.some.inj hmap).symm

private theorem run_collection_boundary_choice_for_actual_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.coordinator = .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.followers i = .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1)
    (records early : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hrecords : records =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active).records)
    (hearly : (List.takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active).records.drop b)) = early) :
    ∀ (k : ℕ) (_hk : k ≤ early.length)
      (hrecord : b + k < records.length),
      (k = early.length →
        ReferenceCollectionPhaseHistory.laterChosen (records.get ⟨b + k, hrecord⟩).input = true) ∧
      ((ReferenceFollowerFixedReply.actualChoice (records.get ⟨b + k, hrecord⟩) i).configuration = .dagger ∨
        ∃ state memory,
          (ReferenceFollowerFixedReply.actualChoice (records.get ⟨b + k, hrecord⟩) i).configuration =
            .ordinary state memory ∧ state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) := by
  intro k hk hrecord
  have hkRun : k ≤
      (List.takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ((ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active).records.drop b)).length := by
    simpa [hearly] using hk
  have hrecordRun : b + k <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active).records.length := by
    simpa [hrecords] using hrecord
  have hboundary := ReferenceCollectionUnoccupiedHistory.run_collection_boundary_choice_unoccupied
    p rate initial rows J rewards start total hspan active b hb payload ledger saved
    hcoord i seed seedMemory hseed hunoccupied hseedStart
  have h := hboundary k hkRun hrecordRun
  simpa [hrecords, hearly] using h

private theorem actual_collection_offer_word_equation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (actualChoice record i).configuration = .ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice record i).follower (actualChoice record i).row
      (actualChoice record i).activation (actualChoice record i).time state = .offer offered) :
    ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
      (actualChoice record i) (actualChoice_alignment record i).1
      (actualChoice_alignment record i).2.1 (actualChoice_alignment record i).2.2 =
      some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
          (OrdinaryMessageCodec.encodeUp
            (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) := by
  exact ReferenceUpReception.currentOfferWord_eq_encoded_offer rate record.input.row i
    record.input.time (actualChoice record i) (actualChoice_alignment record i).1
    (actualChoice_alignment record i).2.1 (actualChoice_alignment record i).2.2
    state memory hconfiguration offered hoff

/-- Literal offer fields and pairwise codec equality from actual prepared
configurations with one fixed reply. The fixed-reply hypothesis is supplied by
the collection history below, including at zero receiver observations. -/
private theorem collection_offers_of_fixed_reply
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (B : List (ReferenceCollectionPhaseHistory.Record p rate))
    (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (s : ℕ) (hlast : before.lastDown = some M) (hMstart : M.val.sigma = s + 1)
    (hchoiceReply : ∀ (k : ℕ) (hk : k < B.length)
      (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
      (actualChoice B[k] i).configuration = .ordinary choice choiceMemory →
      choice.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply choice =
          ReferenceFollowerReplyChronology.reply before) :
    (∀ k : Fin B.length,
      let prepared := actualChoice B[k.val] i
      (prepared.configuration = .dagger ∨
        ∃ choice choiceMemory,
          prepared.configuration = .ordinary choice choiceMemory ∧
          choice.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply before ∧
          (ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            prepared.follower prepared.row prepared.activation prepared.time choice = .failure ∨
           ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            prepared.follower prepared.row prepared.activation prepared.time choice = .noOffer ∨
           ∃ offered : OrdinaryMessageCodec.UpRecord
             (ReferencePrelaunchFollower.codecParams p rate.eta),
             ActiveFollowerQueueOperation.checkedUpOffer rate.eta
               prepared.follower prepared.row prepared.activation prepared.time choice =
                 .offer offered ∧
             offered.val = ⟨M.val.sigma, before.S, before.delta, before.backlog⟩ ∧
             offered.val.sigma = s + 1 ∧
             ReferenceUpReception.currentOfferWord rate B[k.val].input.row i
               B[k.val].input.time prepared
               (actualChoice_alignment B[k.val] i).1
               (actualChoice_alignment B[k.val] i).2.1
               (actualChoice_alignment B[k.val] i).2.2 =
               some ((OrdinaryMessageCodec.wordEquivFlat
                 (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                 (OrdinaryMessageCodec.encodeUp
                   (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered))))) ∧
    (∀ (k₁ k₂ : Fin B.length)
        (choice₁ choice₂ : ReferencePrelaunchFollower.State p rate.eta)
        (memory₁ memory₂ : ActiveFollowerLifecycle.LocalMemory p)
        (offered₁ offered₂ : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta)),
        let prepared₁ := actualChoice B[k₁.val] i
        let prepared₂ := actualChoice B[k₂.val] i
        prepared₁.configuration = .ordinary choice₁ memory₁ →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          prepared₁.follower prepared₁.row prepared₁.activation prepared₁.time choice₁ =
            .offer offered₁ →
        prepared₂.configuration = .ordinary choice₂ memory₂ →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          prepared₂.follower prepared₂.row prepared₂.activation prepared₂.time choice₂ =
            .offer offered₂ →
        ReferenceUpReception.currentOfferWord rate B[k₁.val].input.row
          i B[k₁.val].input.time prepared₁
          (actualChoice_alignment B[k₁.val] i).1
          (actualChoice_alignment B[k₁.val] i).2.1
          (actualChoice_alignment B[k₁.val] i).2.2 =
        ReferenceUpReception.currentOfferWord rate B[k₂.val].input.row
          i B[k₂.val].input.time prepared₂
          (actualChoice_alignment B[k₂.val] i).1
          (actualChoice_alignment B[k₂.val] i).2.1
          (actualChoice_alignment B[k₂.val] i).2.2) := by
  classical
  have hoffers : ∀ k : Fin B.length,
      let prepared := actualChoice B[k.val] i
      (prepared.configuration = .dagger ∨
        ∃ choice choiceMemory,
          prepared.configuration = .ordinary choice choiceMemory ∧
          choice.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply before ∧
          (ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            prepared.follower prepared.row prepared.activation prepared.time choice = .failure ∨
           ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            prepared.follower prepared.row prepared.activation prepared.time choice = .noOffer ∨
           ∃ offered : OrdinaryMessageCodec.UpRecord
             (ReferencePrelaunchFollower.codecParams p rate.eta),
             ActiveFollowerQueueOperation.checkedUpOffer rate.eta
               prepared.follower prepared.row prepared.activation prepared.time choice =
                 .offer offered ∧
             offered.val = ⟨M.val.sigma, before.S, before.delta, before.backlog⟩ ∧
             offered.val.sigma = s + 1 ∧
             ReferenceUpReception.currentOfferWord rate B[k.val].input.row i
               B[k.val].input.time prepared
               (actualChoice_alignment B[k.val] i).1
               (actualChoice_alignment B[k.val] i).2.1
               (actualChoice_alignment B[k.val] i).2.2 =
               some ((OrdinaryMessageCodec.wordEquivFlat
                 (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                 (OrdinaryMessageCodec.encodeUp
                   (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)))) := by
    intro k
    dsimp only
    let prepared := actualChoice B[k.val] i
    cases hcfg : prepared.configuration with
    | dagger => exact Or.inl rfl
    | ordinary choice choiceMemory =>
        have hchoiceState := hchoiceReply k.val k.isLt choice choiceMemory hcfg
        rcases hchoiceState with ⟨hstatusChoice, hreplyChoice⟩
        refine Or.inr ⟨choice, choiceMemory, rfl, hstatusChoice,
          hreplyChoice, ?_⟩
        cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            prepared.follower prepared.row prepared.activation prepared.time choice with
        | failure => exact Or.inl rfl
        | noOffer => exact Or.inr (Or.inl rfl)
        | offer offered =>
            right
            right
            refine ⟨offered, rfl, ?_, ?_, ?_⟩
            · have hparts : choice.lastDown = before.lastDown ∧
                  choice.S = before.S ∧ choice.delta = before.delta ∧
                  choice.backlog = before.backlog := by
                simpa only [ReferenceFollowerReplyChronology.reply,
                  Prod.mk.injEq] using hreplyChoice
              rcases hparts with ⟨hdown, hS, hdelta, hbacklog⟩
              have hdownM : choice.lastDown = some M := hdown.trans hlast
              have hsigma : ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma := by
                simp [ReferencePrelaunchFollower.acceptedStart, hdownM]
              have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields
                rate.eta prepared.follower prepared.row prepared.activation prepared.time
                choice offered hoff
              have hfixed : ActiveFollowerQueueOperation.upOfferFields choice =
                  ⟨M.val.sigma, before.S, before.delta, before.backlog⟩ := by
                simp [ActiveFollowerQueueOperation.upOfferFields, hsigma, hS,
                  hdelta, hbacklog]
              rw [hfields, hfixed]
            · have hparts : choice.lastDown = before.lastDown ∧
                  choice.S = before.S ∧ choice.delta = before.delta ∧
                  choice.backlog = before.backlog := by
                simpa only [ReferenceFollowerReplyChronology.reply,
                  Prod.mk.injEq] using hreplyChoice
              rcases hparts with ⟨hdown, hS, hdelta, hbacklog⟩
              have hdownM : choice.lastDown = some M := hdown.trans hlast
              have hsigma : ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma := by
                simp [ReferencePrelaunchFollower.acceptedStart, hdownM]
              have hMstartOffer : M.val.sigma = s + 1 := hMstart
              have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields
                rate.eta prepared.follower prepared.row prepared.activation prepared.time
                choice offered hoff
              rw [hfields]
              simp [ActiveFollowerQueueOperation.upOfferFields, hsigma, hS,
                hdelta, hbacklog, hMstartOffer]
            · exact actual_collection_offer_word_equation rate B[k.val] i choice choiceMemory
                hcfg offered hoff
  have hwords : ∀ (k₁ k₂ : Fin B.length)
        (choice₁ choice₂ : ReferencePrelaunchFollower.State p rate.eta)
        (memory₁ memory₂ : ActiveFollowerLifecycle.LocalMemory p)
        (offered₁ offered₂ : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta)),
        let prepared₁ := actualChoice B[k₁.val] i
        let prepared₂ := actualChoice B[k₂.val] i
        prepared₁.configuration = .ordinary choice₁ memory₁ →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          prepared₁.follower prepared₁.row prepared₁.activation prepared₁.time choice₁ =
            .offer offered₁ →
        prepared₂.configuration = .ordinary choice₂ memory₂ →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          prepared₂.follower prepared₂.row prepared₂.activation prepared₂.time choice₂ =
            .offer offered₂ →
        ReferenceUpReception.currentOfferWord rate B[k₁.val].input.row
          i B[k₁.val].input.time prepared₁
          (actualChoice_alignment B[k₁.val] i).1
          (actualChoice_alignment B[k₁.val] i).2.1
          (actualChoice_alignment B[k₁.val] i).2.2 =
        ReferenceUpReception.currentOfferWord rate B[k₂.val].input.row
          i B[k₂.val].input.time prepared₂
          (actualChoice_alignment B[k₂.val] i).1
          (actualChoice_alignment B[k₂.val] i).2.1
          (actualChoice_alignment B[k₂.val] i).2.2 := by
    intro k₁ k₂ choice₁ choice₂ memory₁ memory₂ offered₁ offered₂ prepared₁ prepared₂
      hcfg₁ hoff₁ hcfg₂ hoff₂
    have hreply₁ := (hchoiceReply k₁.val k₁.isLt choice₁ memory₁ hcfg₁).2
    have hreply₂ := (hchoiceReply k₂.val k₂.isLt choice₂ memory₂ hcfg₂).2
    have hparts₁ : choice₁.lastDown = before.lastDown ∧
        choice₁.S = before.S ∧ choice₁.delta = before.delta ∧
        choice₁.backlog = before.backlog := by
      simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply₁
    have hparts₂ : choice₂.lastDown = before.lastDown ∧
        choice₂.S = before.S ∧ choice₂.delta = before.delta ∧
        choice₂.backlog = before.backlog := by
      simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply₂
    rcases hparts₁ with ⟨hd₁, hS₁, hδ₁, hb₁⟩
    rcases hparts₂ with ⟨hd₂, hS₂, hδ₂, hb₂⟩
    have hregisters : ReferencePrelaunchFollower.acceptedStart choice₁ =
        ReferencePrelaunchFollower.acceptedStart choice₂ ∧
        choice₁.S = choice₂.S ∧ choice₁.delta = choice₂.delta ∧
        choice₁.backlog = choice₂.backlog := by
      refine ⟨?_, ?_⟩
      · simp [ReferencePrelaunchFollower.acceptedStart, hd₁, hd₂, hlast]
      · exact ⟨hS₁.trans hS₂.symm, hδ₁.trans hδ₂.symm, hb₁.trans hb₂.symm⟩
    exact ReferenceFollowerFixedReply.currentOfferWord_eq_of_same_reply_registers
      B[k₁.val] B[k₂.val] i choice₁ choice₂ memory₁ memory₂ hcfg₁ hcfg₂
      hregisters offered₁ offered₂ hoff₁ hoff₂
  exact ⟨hoffers, hwords⟩

private theorem lastDown_of_fixed_reply
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {state before : ReferencePrelaunchFollower.State p rate.eta}
    {M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)}
    (hreply : ReferenceFollowerReplyChronology.reply state =
      ReferenceFollowerReplyChronology.reply before)
    (hlast : before.lastDown = some M) : state.lastDown = some M :=
  (congrArg Prod.fst hreply).trans hlast

private theorem actual_first_collection_early_down_reply_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (I : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart I s)
    (b : ℕ) (hb : b ≤ count)
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hlast : before.lastDown = some M)
    (hMstart : M.val.sigma = s + 1)
    (hcutChoice : (actualChoice cut i).configuration = .dagger ∨
      (actualChoice cut i).configuration =
        .ordinary {before with status := .unoccupied} memory)
    (B : List (ReferenceCollectionPhaseHistory.Record p rate))
    (Wearly : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hBsplit : B = cut :: Wearly)
    (Erun : ReferenceActivePhysicalHorizon.Run I)
    (hRunRecords : Erun.records =
      (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records)
    (hEarlyRun : List.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
      ((ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records.drop b) =
        Wearly)
    (hbW : b + Wearly.length ≤ count)
    (C : (k : ℕ) → k ≤ Wearly.length → ReferenceActivePhysicalHorizon.Run I)
    (hC : ∀ (k : ℕ) (hk : k ≤ Wearly.length),
      C k hk = ReferenceActivePhysicalHorizon.run I rows J rewards s (b + k)
        (by omega) active)
    (hcutPrefix : (ReferenceActivePhysicalHorizon.run I rows J rewards s b
      (by omega) active).finalState = cut.output.next)
    (nextLedger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcollection : cut.output.next.coordinator = .collection P0 nextLedger saved)
    (out : ReferencePrelaunchFollower.State p rate.eta)
    (outMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : cut.output.next.followers i = .ordinary out outMemory)
    (hstatus : out.status = .unoccupied)
    (hreplyOut : ReferenceFollowerReplyChronology.reply out =
      ReferenceFollowerReplyChronology.reply before)
    (haccepted : ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) :
        (∃ _hfinal : (C 0 (by omega)).finalState = cut.output.next,
      ∃ _hcoord : (C 0 (by omega)).finalState.coordinator =
        .collection P0 nextLedger saved,
        ∃ _hseed : (C 0 (by omega)).finalState.followers i =
          .ordinary out outMemory,
          ∃ _hseedStart : ReferencePrelaunchFollower.acceptedStart out =
            P0.sigma.val + 1,
            (∀ (k : ℕ) (hk : k ≤ Wearly.length),
              ((C k hk).finalState.coordinator = .dagger ∨
                ∃ movingLedger movingSaved,
                  (C k hk).finalState.coordinator =
                    .collection P0 movingLedger movingSaved) ∧
              ((C k hk).finalState.followers i = .dagger ∨
                ∃ state stateMemory,
                  (C k hk).finalState.followers i =
                    .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    ReferenceFollowerReplyChronology.reply before ∧
                    state.lastDown = some M))) ∧
            (∀ (k : ℕ), k < Wearly.length →
              ∀ hrecord : b + k < Erun.records.length, ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown
                  (Erun.records.get ⟨b + k, hrecord⟩) i sigma) ∧
            (∀ (k : ℕ) (_hk : k ≤ Wearly.length)
              (hrecord : b + k < Erun.records.length),
              (Erun.records.get ⟨b + k, hrecord⟩).input.time.val = s + b + k ∧
              (k = Wearly.length →
                ReferenceCollectionPhaseHistory.laterChosen
                  (Erun.records.get ⟨b + k, hrecord⟩).input = true) ∧
              ((actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                  .dagger ∨
                ∃ state stateMemory,
                  (actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                    .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    ReferenceFollowerReplyChronology.reply before ∧
                    state.lastDown = some M)) ∧
            ((b + Wearly.length = count ∧
                Erun.records[b + Wearly.length]? = none) ∨
              ∃ endpoint,
                Erun.records[b + Wearly.length]? = some endpoint ∧
                endpoint.input.time.val = s + b + Wearly.length ∧
                ReferenceCollectionPhaseHistory.laterChosen endpoint.input = true) ∧
            (∀ k : Fin B.length,
              let prepared := actualChoice B[k.val] i
              (prepared.configuration = .dagger ∨
                ∃ choice choiceMemory,
                  prepared.configuration = .ordinary choice choiceMemory ∧
                  choice.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply choice =
                    ReferenceFollowerReplyChronology.reply before ∧
                  (ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                    prepared.follower prepared.row prepared.activation
                    prepared.time choice = .failure ∨
                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                      prepared.follower prepared.row prepared.activation
                      prepared.time choice = .noOffer ∨
                    ∃ offered : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta),
                      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                        prepared.follower prepared.row prepared.activation
                        prepared.time choice = .offer offered ∧
                      offered.val =
                        ⟨M.val.sigma, before.S, before.delta, before.backlog⟩ ∧
                      offered.val.sigma = s + 1 ∧
                      ReferenceUpReception.currentOfferWord rate
                        B[k.val].input.row i B[k.val].input.time prepared
                        (actualChoice_alignment B[k.val] i).1
                        (actualChoice_alignment B[k.val] i).2.1
                        (actualChoice_alignment B[k.val] i).2.2 =
                        some ((OrdinaryMessageCodec.wordEquivFlat
                          (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                          (OrdinaryMessageCodec.encodeUp
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                            offered))))) ∧
            (∀ (k₁ k₂ : Fin B.length)
                (choice₁ choice₂ : ReferencePrelaunchFollower.State p rate.eta)
                (memory₁ memory₂ : ActiveFollowerLifecycle.LocalMemory p)
                (offered₁ offered₂ : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta)),
                let prepared₁ := actualChoice B[k₁.val] i
                let prepared₂ := actualChoice B[k₂.val] i
                prepared₁.configuration = .ordinary choice₁ memory₁ →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  prepared₁.follower prepared₁.row prepared₁.activation prepared₁.time choice₁ =
                    .offer offered₁ →
                prepared₂.configuration = .ordinary choice₂ memory₂ →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  prepared₂.follower prepared₂.row prepared₂.activation prepared₂.time choice₂ =
                    .offer offered₂ →
                ReferenceUpReception.currentOfferWord rate B[k₁.val].input.row
                  i B[k₁.val].input.time prepared₁
                  (actualChoice_alignment B[k₁.val] i).1
                  (actualChoice_alignment B[k₁.val] i).2.1
                  (actualChoice_alignment B[k₁.val] i).2.2 =
                ReferenceUpReception.currentOfferWord rate B[k₂.val].input.row
                  i B[k₂.val].input.time prepared₂
                  (actualChoice_alignment B[k₂.val] i).1
                  (actualChoice_alignment B[k₂.val] i).2.1
                  (actualChoice_alignment B[k₂.val] i).2.2) := by
  classical
  have hrecords : Erun.records.length = count := by
    rw [hRunRecords]
    exact ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s count hspan active
  have hprefixBound : s + b ≤ p.T := by omega
  let runPrefix := ReferenceActivePhysicalHorizon.run I rows J rewards s b
    hprefixBound active
  have hfinal : runPrefix.finalState = cut.output.next := by
    simpa [runPrefix] using hcutPrefix
  have hcoord : runPrefix.finalState.coordinator =
      .collection P0 nextLedger saved := by
    simpa [hfinal] using hcollection
  have hseed : runPrefix.finalState.followers i = .ordinary out outMemory := by
    simpa [hfinal] using hout
  have hcoordRun :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s b
        (by omega) active).finalState.coordinator = .collection P0 nextLedger saved := by
    simpa [runPrefix] using hcoord
  have hseedRun :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s b
        (by omega) active).finalState.followers i = .ordinary out outMemory := by
    simpa [runPrefix] using hseed
  have hseedStart : ReferencePrelaunchFollower.acceptedStart out =
      P0.sigma.val + 1 := haccepted
  have hstartPayload : ReferencePrelaunchFollower.acceptedStart out =
      P0.sigma.val + 1 := hseedStart
  have hprefixU := ReferenceCollectionUnoccupiedHistory.run_collection_unoccupied_prefix
    p rate I rows J rewards s count hspan active b hb P0 nextLedger saved
    hcoordRun i out outMemory hseedRun hstatus hstartPayload
  have hnoDown := ReferenceCollectionUnoccupiedHistory.run_collection_no_appliedDown
    p rate I rows J rewards s count hspan active b hb P0 nextLedger saved
    hcoordRun i out outMemory hseedRun hstatus hstartPayload
  let runFull := ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active
  have hrunRecords : Erun.records = runFull.records := by simpa [runFull] using hRunRecords
  let Wrun := (runFull.records.drop b).takeWhile
    fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input
  have hWrun : Wrun = Wearly := by
    simpa [Wrun, runFull] using hEarlyRun
  have hboundary : ∀ (k : ℕ) (hk : k ≤ Wearly.length)
      (hrecord : b + k < Erun.records.length),
      (k = Wearly.length →
        ReferenceCollectionPhaseHistory.laterChosen
          (Erun.records.get ⟨b + k, hrecord⟩).input = true) ∧
      ((actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration = .dagger ∨
        ∃ state stateMemory,
          (actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
            .ordinary state stateMemory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state =
            ReferenceFollowerReplyChronology.reply out) := by
    exact run_collection_boundary_choice_for_actual_suffix (p := p) rate I rows J
      rewards s count hspan active b hb P0 nextLedger saved hcoordRun i out outMemory
      hseedRun hstatus hstartPayload Erun.records Wearly hrunRecords
      (by simpa [runFull] using hWrun)
  have hboundaryReply : ∀ (k : ℕ) (hk : k ≤ Wearly.length)
      (hrecord : b + k < Erun.records.length),
      (Erun.records.get ⟨b + k, hrecord⟩).input.time.val = s + b + k ∧
      (k = Wearly.length →
        ReferenceCollectionPhaseHistory.laterChosen
          (Erun.records.get ⟨b + k, hrecord⟩).input = true) ∧
      ((actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
          .dagger ∨
        ∃ state stateMemory,
          (actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
            .ordinary state stateMemory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state =
            ReferenceFollowerReplyChronology.reply before ∧
            state.lastDown = some M) := by
    intro k hk hrecord
    rcases hboundary k hk hrecord with ⟨htag, hchoice⟩
    let record := Erun.records.get ⟨b + k, hrecord⟩
    have hget : Erun.records[b + k]? = some record := by
      simp [record]
    have hgetFull : (ReferenceActivePhysicalHorizon.run I rows J rewards s count
        hspan active).records[b + k]? = some record := by
      simpa [hRunRecords] using hget
    have htime := run_record_time_of_lookup I rows J rewards s count hspan active
      (b + k) record hgetFull
    have htime' : record.input.time.val = s + b + k := by
      dsimp [record] at htime ⊢
      omega
    refine ⟨htime', htag, ?_⟩
    rcases hchoice with hdag | ⟨state, stateMemory, hconfig, hstatus', hreplySeed⟩
    · exact Or.inl hdag
    · exact Or.inr ⟨state, stateMemory, hconfig, hstatus', hreplySeed.trans hreplyOut,
        lastDown_of_fixed_reply (hreplySeed.trans hreplyOut) hlast⟩
  have hprefixReply : ∀ (k : ℕ) (hk : k ≤ Wearly.length),
      ((C k hk).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          (C k hk).finalState.coordinator =
            .collection P0 movingLedger movingSaved) ∧
      ((C k hk).finalState.followers i = .dagger ∨
        ∃ state stateMemory,
          (C k hk).finalState.followers i =
            .ordinary state stateMemory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state =
            ReferenceFollowerReplyChronology.reply before ∧
            state.lastDown = some M) := by
    intro k hk
    have hkRun : k ≤
        (((ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records.drop b).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := by
      simpa [hEarlyRun] using hk
    have h := hprefixU k hkRun
    rcases h with ⟨hcoordK, hfollowK⟩
    refine ⟨?_, ?_⟩
    · simpa [hC] using hcoordK
    · rcases hfollowK with hdag | ⟨state, stateMemory, hstate, hstatusK, hreplyK⟩
      · exact Or.inl (by simpa [hC] using hdag)
      · exact Or.inr ⟨state, stateMemory, by simpa [hC] using hstate,
          hstatusK, hreplyK.trans hreplyOut,
          lastDown_of_fixed_reply (hreplyK.trans hreplyOut) hlast⟩
  have hnoDown' : ∀ (k : ℕ), k < Wearly.length →
      ∀ hrecord : b + k < Erun.records.length, ∀ sigma,
        ¬ ReferenceFollowerReplyChronology.appliedDown
          (Erun.records.get ⟨b + k, hrecord⟩) i sigma := by
    intro k hk hrecord sigma
    have hkRun : k <
        (((ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records.drop b).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := by
      simpa [hEarlyRun] using hk
    have h := hnoDown k hkRun (by simpa [hrunRecords] using hrecord) sigma
    simpa [hrunRecords] using h
  have hendCase : (b + Wearly.length = count ∧
        Erun.records[b + Wearly.length]? = none) ∨
      ∃ endpoint,
        Erun.records[b + Wearly.length]? = some endpoint ∧
        endpoint.input.time.val = s + b + Wearly.length ∧
        ReferenceCollectionPhaseHistory.laterChosen endpoint.input = true := by
    have hlen : Wearly.length ≤ count - b := by
      have hpref : Wearly.IsPrefix (Erun.records.drop b) := by
        rw [← hEarlyRun, hRunRecords]
        exact List.takeWhile_prefix _
      have hlen := hpref.length_le
      rw [List.length_drop, hrecords] at hlen
      exact hlen
    have hbound : b + Wearly.length ≤ count := by omega
    by_cases heq : b + Wearly.length = count
    · exact Or.inl ⟨heq, List.getElem?_eq_none (by omega)⟩
    · right
      have hlt : b + Wearly.length < Erun.records.length := by
        rw [hrecords]
        omega
      have hlastBoundary := hboundaryReply Wearly.length le_rfl hlt
      have htag := hlastBoundary.2.1 rfl
      refine ⟨Erun.records[b + Wearly.length], ?_, hlastBoundary.1, htag⟩
      rw [List.getElem?_eq_getElem hlt]
  have hchoiceReply : ∀ (k : ℕ) (hk : k < B.length)
      (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
      (actualChoice B[k] i).configuration = .ordinary choice choiceMemory →
      choice.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply choice =
          ReferenceFollowerReplyChronology.reply before := by
    intro k hk choice choiceMemory hchoice
    have hkB := hk
    rw [hBsplit] at hkB
    by_cases hz : k = 0
    · subst k
      have hBzero : B[0] = cut := by
        simp [hBsplit]
      rw [hBzero] at hchoice
      have hactual := hcutChoice
      rcases hactual with hdag | hordinary
      · rw [hdag] at hchoice
        cases hchoice
      · have hstate : {before with status := .unoccupied} = choice := by
          exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hordinary.symm.trans hchoice)).1
        subst choice
        exact ⟨by simp, by simp [ReferenceFollowerReplyChronology.reply]⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hz
      let q := k - 1
      have hkSimp : k ≤ Wearly.length := by simpa using hkB
      have hq : q < Wearly.length := by dsimp [q]; omega
      have hqFin : q < Erun.records.length - b := by
        have hcount' : Erun.records.length = count := hrecords
        have hpref : Wearly.IsPrefix (Erun.records.drop b) := by
          rw [← hEarlyRun, hRunRecords]
          exact List.takeWhile_prefix _
        have hlen := hpref.length_le
        rw [List.length_drop, hcount'] at hlen
        omega
      have hrecordIndex : b + q < Erun.records.length := by omega
      have hBidx : B[k] = Wearly[q] := by
        have hk' : k = q + 1 := by dsimp [q]; omega
        simp [hBsplit, hk']
      have hactualChoice :
          (actualChoice (Erun.records.get ⟨b + q, hrecordIndex⟩) i).configuration =
            .ordinary choice choiceMemory := by
        have hopt : Erun.records[b + q]? = some Wearly[q] := by
          have hqTake : q < ((Erun.records.drop b).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by
            simpa [hEarlyRun, hRunRecords] using hq
          have htake := (List.takeWhile_prefix
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
            (l := Erun.records.drop b)).getElem hqTake
          have hqDrop : q < (Erun.records.drop b).length := by
            simpa [List.length_drop] using hqFin
          have htakeW : (Erun.records.drop b)[q]'hqDrop = Wearly[q] := by
            simpa [hRunRecords, hEarlyRun] using htake.symm
          have hgetDrop : (Erun.records.drop b)[q]? = some Wearly[q] := by
            rw [List.getElem?_eq_getElem hqDrop]
            exact congrArg some htakeW
          rw [List.getElem?_drop] at hgetDrop
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hgetDrop
        rw [List.getElem?_eq_getElem hrecordIndex] at hopt
        have hget : Erun.records.get ⟨b + q, hrecordIndex⟩ = B[k] := by
          calc
            Erun.records.get ⟨b + q, hrecordIndex⟩ = Erun.records[b + q] := by
              simp [List.get_eq_getElem]
            _ = Wearly[q] := Option.some.inj hopt
            _ = B[k] := hBidx.symm
        rw [hget]
        exact hchoice
      have hbr := hboundaryReply q (Nat.le_of_lt hq) hrecordIndex
      rcases hbr.2.2 with hdag | ⟨state, stateMemory, hconfig, hstatus', hreply, _hlast⟩
      · rw [hdag] at hactualChoice
        cases hactualChoice
      · have hstate : state = choice := by
          exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hconfig.symm.trans hactualChoice)).1
        subst state
        exact ⟨hstatus', hreply⟩
  have hmessages := collection_offers_of_fixed_reply
    rate B i before M s hlast hMstart hchoiceReply
  have hC0 : C 0 (by omega) =
      ReferenceActivePhysicalHorizon.run I rows J rewards s b
        (by omega) active := by
    simpa [Nat.add_zero] using hC 0 (by omega)
  have hfinalC : (C 0 (by omega)).finalState = cut.output.next := by
    exact (congrArg (fun run => run.finalState) hC0).trans hfinal
  have hcoordC : (C 0 (by omega)).finalState.coordinator =
      .collection P0 nextLedger saved := by
    rw [hfinalC]
    exact hcollection
  have hseedC : (C 0 (by omega)).finalState.followers i =
      .ordinary out outMemory := by
    rw [hfinalC]
    exact hout
  refine And.intro ?_ ?_
  · exact ⟨hfinalC, hcoordC, hseedC, hseedStart, hprefixReply⟩
  · exact And.intro hnoDown' (And.intro hboundaryReply
      (And.intro hendCase hmessages))

/-- The suffix is taken from the original raw run. Its boundary state is
that run's actual cutoff successor, with no replacement of any equation bank. -/
private theorem first_collection_interval_geometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (I : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart I s)
    (Erun : ReferenceActivePhysicalHorizon.Run I)
    (hRunRecords : Erun.records =
      (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records)
    (W : List (ReferenceCollectionPhaseHistory.Record p rate))
    (cut : ReferenceCollectionPhaseHistory.Record p rate)
    (suffix : List (ReferenceCollectionPhaseHistory.Record p rate))
    (hsplit : Erun.records = W ++ cut :: suffix)
    (hshort : W.length < count)
    (hindex : W.length < Erun.records.length)
    (hcutGet : cut = Erun.records[W.length]'hindex) :
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    let b := w + 1
    let Wearly := (Erun.records.drop b).takeWhile
      fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input
    Erun.records.length = count ∧ b ≤ count ∧
    B = cut :: Wearly ∧
    w + B.length = b + Wearly.length ∧
    b + Wearly.length ≤ count ∧
    s + b + Wearly.length ≤ p.T ∧
    (s + b + Wearly.length = p.T →
      ∀ time : Fin p.T, time.val < s + b + Wearly.length) ∧
    (∀ k : Fin Wearly.length,
      Erun.records[b + k.val]? = some Wearly[k.val] ∧
        Wearly[k.val].input.time.val = u + k.val) ∧
    (ReferenceActivePhysicalHorizon.run I rows J rewards s b (by
      have hcount : Erun.records.length = count := by
        rw [hRunRecords]
        exact ReferenceActivePhysicalHorizon.run_record_count
          I rows J rewards s count hspan active
      dsimp [b, w]
      omega) active).finalState = cut.output.next := by
  intro w B u b Wearly
  have hrecords : Erun.records.length = count := by
    rw [hRunRecords]
    exact ReferenceActivePhysicalHorizon.run_record_count
      I rows J rewards s count hspan active
  have hspanRun : s + count ≤ p.T := hspan
  have hb : b ≤ count := by
    dsimp [b]
    exact Nat.succ_le_of_lt hshort
  have hprefixBound : s + b ≤ p.T := by omega
  have hindexRun : w < Erun.records.length := hindex
  have hwle : w ≤ W.length := by dsimp [w]; exact Nat.le_refl _
  have hdropCut : Erun.records.drop w = cut :: suffix := by
    rw [hsplit]
    rw [List.drop_append_of_le_length hwle]
    simp [w]
  have hdropEarly : Erun.records.drop b = suffix := by
    calc
      Erun.records.drop b = (Erun.records.drop w).drop 1 := by
        change Erun.records.drop (w + 1) = (Erun.records.drop w).drop 1
        rw [List.drop_drop]
      _ = suffix := by rw [hdropCut]; rfl
  have hBsplit : B = cut :: Wearly := by
    dsimp [B, Wearly, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [hdropCut, hdropEarly]
    simp
  have hWearlyBound : b + Wearly.length ≤ count := by
    have hpref : Wearly.IsPrefix (Erun.records.drop b) := List.takeWhile_prefix _
    have hlen := hpref.length_le
    rw [List.length_drop, hrecords] at hlen
    omega
  have hwindowEnd : w + B.length = b + Wearly.length := by
    rw [hBsplit, List.length_cons]
    dsimp [b]
    omega
  have hphysicalEnd : s + b + Wearly.length ≤ p.T := by omega
  have hterminal : s + b + Wearly.length = p.T →
      ∀ time : Fin p.T, time.val < s + b + Wearly.length := by
    intro htime time
    rw [htime]
    exact time.isLt
  have hEarlyIndex : ∀ k : Fin Wearly.length,
      Erun.records[b + k.val]? = some Wearly[k.val] := by
    intro k
    have hdropIndex : Wearly[k.val] = (Erun.records.drop b)[k.val]'(by
        have hpref : Wearly.IsPrefix (Erun.records.drop b) := List.takeWhile_prefix _
        exact Nat.lt_of_lt_of_le k.isLt hpref.length_le) := by
      dsimp [Wearly]
      exact (List.takeWhile_prefix _).getElem k.isLt
    have hget := congrArg (fun xs : List _ => xs[k.val]?) hdropEarly
    rw [List.getElem?_drop] at hget
    have hsome : (Erun.records.drop b)[k.val]? = some Wearly[k.val] := by
      rw [List.getElem?_eq_getElem (by
        have hpref : Wearly.IsPrefix (Erun.records.drop b) := List.takeWhile_prefix _
        exact Nat.lt_of_lt_of_le k.isLt hpref.length_le)]
      exact congrArg some hdropIndex.symm
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsome
  have hEarlyTime : ∀ k : Fin Wearly.length,
      Wearly[k.val].input.time.val = u + k.val := by
    intro k
    let record := Wearly[k.val]
    have hget : Erun.records[b + k.val]? = some record := by
      simpa [record] using hEarlyIndex k
    have hgetRun : (ReferenceActivePhysicalHorizon.run I rows J rewards s count
        hspan active).records[b + k.val]? = some record := by
      rw [← hRunRecords]
      exact hget
    have htime := run_record_time_of_lookup I rows J rewards s count hspan active
      (b + k.val) record hgetRun
    have htime' : Wearly[k.val].input.time.val = s + b + k.val := by
      simpa [record, Nat.add_assoc] using htime
    dsimp [u, b] at htime' ⊢
    omega
  have hprefixCut := run_prefix_endpoints I rows J rewards s count hspan active w
    (Nat.lt_of_lt_of_eq hindexRun hrecords)
  have hcutPrefix :
      (ReferenceActivePhysicalHorizon.run I rows J rewards s b hprefixBound active).finalState =
        cut.output.next := by
    have hcutGet' : cut = Erun.records[w]'hindexRun := hcutGet
    have hrunRecords : Erun.records =
        (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records := hRunRecords
    have hcutGetRun : cut =
        (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records[w]'
          (by rw [← hrunRecords]; exact hindexRun) := by
      simpa [hrunRecords] using hcutGet'
    have hnext := hprefixCut.2
    rw [← hcutGetRun] at hnext
    simpa [b] using hnext
  refine ⟨hrecords, hb, hBsplit, hwindowEnd, hWearlyBound, hphysicalEnd,
    hterminal, ?_, hcutPrefix⟩
  intro k
  exact ⟨hEarlyIndex k, hEarlyTime k⟩

/-- An actual earlier retained DOWN seeds the fixed UP reply through the raw
first collection window. The query includes the adjacent case `j.val + 1 = w`.
Actual dagger alternatives and unsuccessful offers remain in the conclusion. -/
theorem actual_first_collection_early_down_reply_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    let b := w + 1
    let Wearly := (Erun.records.drop b).takeWhile
      fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let C := fun (k : ℕ) (hk : k ≤ Wearly.length) =>
      ReferenceActivePhysicalHorizon.run I rows J rewards s (b + k) (by
        have hrecords : Erun.records.length = count := by
          exact ReferenceActivePhysicalHorizon.run_record_count
            I rows J rewards s count hspan active
        have htake : Wearly.length ≤ (Erun.records.drop b).length :=
          (List.takeWhile_prefix _).length_le
        rw [List.length_drop, hrecords] at htake
        have hWshort : w < count := hshort
        have _hb : b ≤ count := by dsimp [b]; omega
        have hbk : b + k ≤ count := by omega
        have hspan' : s + count ≤ p.T := hspan
        omega) active
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      Erun.records = W ++ cut :: suffix ∧
      ReferenceActivePhysicalHorizon.Connected I W cut.input.state ∧
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) ∧
      cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      Erun.records.length = count ∧ b ≤ count ∧
      B = cut :: Wearly ∧
      w + B.length = b + Wearly.length ∧
      b + Wearly.length ≤ count ∧
      s + b + Wearly.length ≤ p.T ∧
      (s + b + Wearly.length = p.T →
        ∀ time : Fin p.T, time.val < s + b + Wearly.length) ∧
      (∀ k : Fin Wearly.length,
        Erun.records[b + k.val]? = some Wearly[k.val] ∧
          Wearly[k.val].input.time.val = u + k.val) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (let callInput := ReferenceActivePhysicalStep.liveInput cut.input registers owned base
       ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          callInput.registers callInput.ownedRegisters base),
        ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val callInput.registers.time
          callInput.registers.priorClock callInput.registers.clockPending = .ok dispatched.startResult),
        ∃ (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers),
        ∃ (hinit : dispatched.collectionInitialization = .success (some ledger)),
        ∃ (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hclock : dispatched.startResult.clock =
          { callInput.registers.priorClock with u := some callInput.registers.time }),
        ∃ (hpending : dispatched.startResult.pending = Finset.univ),
        ∃ (hnoAssignment : dispatched.startResult.assignmentStart = none),
        ∃ (selected : CoordinatorRoundDispatch.ArmSelection
          callInput.registers.payload dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights callInput.row),
        cut.output.preparation.coordinator = .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
        cut.output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation registers.payload
            (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
            callInput.registers.complementWeights) ∧
      (cut.output.next.coordinator = .dagger ∨
        ∃ nextLedger saved, cut.output.next.coordinator = .collection P0 nextLedger saved) ∧
      (∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (token : ActiveFollowerLifecycle.ProposalRead p),
          cut.input.state.followers i = .ordinary before memory ∧
          before.lastDown = some M ∧ M = P0.downRecord i ∧
          before.status ≠ .unoccupied ∧
          ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
          M.val.sigma = s + 1 ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp ∧
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
            .ok ({before with status := .unoccupied}, memory) ∧
          ((actualChoice cut i).configuration = .dagger ∨
            (actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ∀ arrival,
              ActiveFollowerQueueOperation.serviceOutput rate.n
                {before with status := .unoccupied} arrival =
                  {before with status := .unoccupied}) ∧
          (cut.output.next.followers i = .dagger ∨
            ∃ out outMemory,
              cut.output.next.followers i = .ordinary out outMemory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply before ∧
              out.lastDown = some M ∧
              ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
          (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) ∧
          (cut.output.next.coordinator = .dagger ∨
            ∃ nextLedger saved,
              cut.output.next.coordinator = .collection P0 nextLedger saved ∧
              (cut.output.next.followers i = .dagger ∨
                ∃ out outMemory,
                  cut.output.next.followers i = .ordinary out outMemory ∧
                  out.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply out =
                    ReferenceFollowerReplyChronology.reply before ∧
                  out.lastDown = some M ∧
                  ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1 ∧
                  (∃ _hfinal : (C 0 (by omega)).finalState = cut.output.next,
                    ∃ _hcoord : (C 0 (by omega)).finalState.coordinator =
                      .collection P0 nextLedger saved,
                      ∃ _hseed : (C 0 (by omega)).finalState.followers i =
                        .ordinary out outMemory,
                        ∃ _hseedStart : ReferencePrelaunchFollower.acceptedStart out =
                          P0.sigma.val + 1,
                          (∀ (k : ℕ) (hk : k ≤ Wearly.length),
                            ((C k hk).finalState.coordinator = .dagger ∨
                              ∃ movingLedger movingSaved,
                                (C k hk).finalState.coordinator =
                                  .collection P0 movingLedger movingSaved) ∧
                            ((C k hk).finalState.followers i = .dagger ∨
                              ∃ state stateMemory,
                                (C k hk).finalState.followers i =
                                  .ordinary state stateMemory ∧
                                state.status = .unoccupied ∧
                                ReferenceFollowerReplyChronology.reply state =
                                  ReferenceFollowerReplyChronology.reply before ∧
                                  state.lastDown = some M))) ∧
                          (∀ (k : ℕ), k < Wearly.length →
                            ∀ hrecord : b + k < Erun.records.length, ∀ sigma,
                              ¬ ReferenceFollowerReplyChronology.appliedDown
                                (Erun.records.get ⟨b + k, hrecord⟩) i sigma) ∧
                          (∀ (k : ℕ) (_hk : k ≤ Wearly.length)
                            (hrecord : b + k < Erun.records.length),
                            (Erun.records.get ⟨b + k, hrecord⟩).input.time.val = s + b + k ∧
                            (k = Wearly.length →
                              ReferenceCollectionPhaseHistory.laterChosen
                                (Erun.records.get ⟨b + k, hrecord⟩).input = true) ∧
                            ((actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                                .dagger ∨
                              ∃ state stateMemory,
                                (actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                                  .ordinary state stateMemory ∧
                                state.status = .unoccupied ∧
                                ReferenceFollowerReplyChronology.reply state =
                                  ReferenceFollowerReplyChronology.reply before ∧
                                  state.lastDown = some M)) ∧
                          ((b + Wearly.length = count ∧
                              Erun.records[b + Wearly.length]? = none) ∨
                            ∃ endpoint,
                              Erun.records[b + Wearly.length]? = some endpoint ∧
                              endpoint.input.time.val = s + b + Wearly.length ∧
                              ReferenceCollectionPhaseHistory.laterChosen endpoint.input = true) ∧
                          (∀ k : Fin B.length,
                            let prepared := actualChoice B[k.val] i
                            (prepared.configuration = .dagger ∨
                              ∃ choice choiceMemory,
                                prepared.configuration = .ordinary choice choiceMemory ∧
                                choice.status = .unoccupied ∧
                                ReferenceFollowerReplyChronology.reply choice =
                                  ReferenceFollowerReplyChronology.reply before ∧
                                (ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                                  prepared.follower prepared.row prepared.activation
                                  prepared.time choice = .failure ∨
                                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                                    prepared.follower prepared.row prepared.activation
                                    prepared.time choice = .noOffer ∨
                                  ∃ offered : OrdinaryMessageCodec.UpRecord
                                    (ReferencePrelaunchFollower.codecParams p rate.eta),
                                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                                      prepared.follower prepared.row prepared.activation
                                      prepared.time choice = .offer offered ∧
                                    offered.val =
                                      ⟨M.val.sigma, before.S, before.delta, before.backlog⟩ ∧
                                    offered.val.sigma = s + 1 ∧
                                    ReferenceUpReception.currentOfferWord rate
                                      B[k.val].input.row i B[k.val].input.time prepared
                                      (actualChoice_alignment B[k.val] i).1
                                      (actualChoice_alignment B[k.val] i).2.1
                                      (actualChoice_alignment B[k.val] i).2.2 =
                                      some ((OrdinaryMessageCodec.wordEquivFlat
                                        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                                        (OrdinaryMessageCodec.encodeUp
                                          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                                          offered))))) ∧
                          (∀ (k₁ k₂ : Fin B.length)
                              (choice₁ choice₂ : ReferencePrelaunchFollower.State p rate.eta)
                              (memory₁ memory₂ : ActiveFollowerLifecycle.LocalMemory p)
                              (offered₁ offered₂ : OrdinaryMessageCodec.UpRecord
                                (ReferencePrelaunchFollower.codecParams p rate.eta)),
                              let prepared₁ := actualChoice B[k₁.val] i
                              let prepared₂ := actualChoice B[k₂.val] i
                              prepared₁.configuration = .ordinary choice₁ memory₁ →
                              ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                                prepared₁.follower prepared₁.row prepared₁.activation prepared₁.time choice₁ =
                                  .offer offered₁ →
                              prepared₂.configuration = .ordinary choice₂ memory₂ →
                              ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                                prepared₂.follower prepared₂.row prepared₂.activation prepared₂.time choice₂ =
                                  .offer offered₂ →
                              ReferenceUpReception.currentOfferWord rate B[k₁.val].input.row
                                i B[k₁.val].input.time prepared₁
                                (actualChoice_alignment B[k₁.val] i).1
                                (actualChoice_alignment B[k₁.val] i).2.1
                                (actualChoice_alignment B[k₁.val] i).2.2 =
                              ReferenceUpReception.currentOfferWord rate B[k₂.val].input.row
                                i B[k₂.val].input.time prepared₂
                                (actualChoice_alignment B[k₂.val] i).1
                                (actualChoice_alignment B[k₂.val] i).2.1
                                (actualChoice_alignment B[k₂.val] i).2.2)))) := by
  classical
  intro x0 b0 s I Erun W w B u b Wearly rows J active C
  have hE := ReferenceFirstCutoffRetainedDownReplySeed.actual_first_cutoff_retained_down_reply_seed
    rate source rewards C_star C_h count hcross hspan hshort
  have hE' := hE
  dsimp only [x0, b0, s, I, Erun, W, w, B, u, b] at hE'
  rcases hE' with ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hwindow, hdispatch, hcoordNext, hqueries⟩
  rcases hcutIndex with ⟨hindex, hcutGet⟩
  have hRunRecords : Erun.records =
      (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records := rfl
  have hgeometry := first_collection_interval_geometry rate I rows J rewards s count
    hspan active Erun hRunRecords W cut suffix hsplit hshort hindex hcutGet
  rcases hgeometry with ⟨hrecords, hb, hBsplit, hwindowEnd, hWearlyBound,
    hphysicalEnd, hterminal, hEarly, hcutPrefix⟩
  have hspanRun : s + count ≤ p.T := hspan
  have hWearlyBoundRun : b + Wearly.length ≤ count := hWearlyBound
  refine ⟨cut, suffix, registers, owned, base, P0, birth, hsplit, hconnected,
    ⟨hindex, hcutGet⟩, hcutTime, hcutState, hcutoff, hpayload, hsigma, hqueues,
    hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime, hbirthFirst,
    hrecords, hb, hBsplit, hwindowEnd, hWearlyBound, hphysicalEnd, hterminal,
    ?_, hwindow, hdispatch, hcoordNext, ?_⟩
  · exact hEarly
  · intro i j M hj hretained
    rcases hqueries i j M hj hretained with
      ⟨before, memory, token, hbefore, hlast, hMpayload, hoccupied, hstart,
        hdomain, htoken, htokenTime, htokenBit, hstartRound, hcutChoice,
        hcutFollower, hcutNoDown⟩
    have hMstart : M.val.sigma = s + 1 := by
      simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using hstart
    refine ⟨before, memory, token, hbefore, hlast, hMpayload, hoccupied,
      hstart, hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound, ?_,
      hcutFollower, hcutNoDown, ?_⟩
    · rcases hcutChoice with hdag | hordinary
      · exact Or.inl hdag
      · right
        refine ⟨hordinary, ?_⟩
        intro arrival
        exact ActiveFollowerQueueOperation.serviceOutput_unoccupied_preserves
          rate.n ({before with status := .unoccupied}) rfl arrival
    · rcases hcoordNext with hdag | ⟨nextLedger, saved, hcollection⟩
      · exact Or.inl hdag
      · right
        refine ⟨nextLedger, saved, hcollection, ?_⟩
        rcases hcutFollower with hfd | ⟨out, outMemory, hout, hstatus,
          hreplyOut, hlastOut, haccepted⟩
        · exact Or.inl hfd
        · right
          refine ⟨out, outMemory, hout, hstatus, hreplyOut, hlastOut, haccepted,
            ?_⟩
          let runFull := ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active
          have hRunRecords : Erun.records = runFull.records := by rfl
          have hEarlyRun : List.takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
              (runFull.records.drop b) = Wearly := by
            simp [Wearly, runFull, hRunRecords]
          have hC : ∀ (k : ℕ) (hk : k ≤ Wearly.length),
              C k hk = ReferenceActivePhysicalHorizon.run I rows J rewards s (b + k)
                (by omega) active := by
            intro k hk
            rfl
          have hhistory := @actual_first_collection_early_down_reply_suffix p
            rate I rows J rewards s count hspan active b hb P0 cut i M before memory
            hlast hMstart hcutChoice B Wearly hBsplit Erun
            (by simpa [runFull] using hRunRecords)
            (by simpa [runFull] using hEarlyRun)
            hWearlyBound C hC hcutPrefix nextLedger saved hcollection out outMemory hout hstatus
            hreplyOut haccepted
          exact hhistory

end Bandits.Support.ReferenceFirstCollectionEarlyDownReplyHistory

end
