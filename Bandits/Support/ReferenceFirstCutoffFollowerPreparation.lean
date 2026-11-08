/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceFirstCutoffRecordedService

import Lean.Elab.Tactic.Omega

/-!
# Actual first-cutoff follower preparation

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,41-70,246-256`,
`sources/zip4/manuscript/05_binary_transport.tex:74-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-44,54-60`.

From the explicit complete-table physical boundary, this follows the original
first-live window to its actual first cutoff. It proves the real local
StartRound and PREPARE results for every follower, including retained fields,
the checked UP offer and the literal simultaneous arm and feedback equations.
It proves no observation, finish, collection continuation, or global truth
claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActiveRoundActions
open Bandits.Support.OrderedTupleSampler

namespace Bandits.Support.ReferenceFirstCutoffFollowerPreparation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalHorizon.State

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

/-- Preparation at the first actual public cutoff of the original physical
run. The complete public rows, original private row index, and whole reward
table remain fixed throughout. The only boundary assumptions are the ones
used by `run_first_live_follower_safety`; all cutoff, token, offer, and arm
facts are derived from the run itself.
-/
theorem run_first_cutoff_follower_preparation
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0) (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, downDecoderStateValid (seed i))
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := firstLiveWindow execution.records
    let k := window.length
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start k
      (by
        have hk : k < count := by simpa [window, execution] using hshort
        exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
      cut.input.time.val = start + k ∧
      cut.input.state = prefixRun.finalState ∧
      cut.input.rows = rows ∧ cut.input.selected = J ∧ cut.input.rewards = rewards ∧
      (∀ i : Fin (p.m - 1), ∃ s μ,
        prefixRun.finalState.followers i = .ordinary s μ ∧
        (s.status = .unoccupied →
          s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∧
        (s.status ≠ .unoccupied →
          0 < k ∧ ∃ M token,
            s.lastDown = some M ∧ M.val.sigma = start + 1 ∧
            μ.lastProposalRead = some token ∧
            token.timestamp.val + 1 = start + k ∧
            token.bit = completeRowProposalBit p rate.eta.val (rows J) token.timestamp) ∧
        let c : ReferencePrelaunchFollower.State p rate.eta :=
          { s with status := .unoccupied }
        startRound rate.eta cut.input.time s μ = .ok (c, μ) ∧
        (cut.output.preparation.followers.followers i).configuration = .ordinary c μ ∧
        localStateDomainValid c ∧
        c.S + c.backlog ≤ k * D p ∧
        c.S ≤ p.T * D p ∧ c.delta ≤ D p ∧ c.backlog ≤ p.T * D p ∧
        c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ c.buffer, saved.calendarRound < cut.input.time.val + 1) ∧
        c.S = s.S ∧ c.delta = s.delta ∧ c.backlog = s.backlog ∧
        c.lastDown = s.lastDown ∧ c.buffer = s.buffer ∧ c.downBatch = s.downBatch ∧
        c.initializationFailure = s.initializationFailure ∧
        (s.lastDown = none → upOfferFields c = upPlaceholder) ∧
        (selectedUpRound i cut.input.row
            (cut.input.state.activations i) cut.input.time →
          ∃ offered,
            checkedUpOffer rate.eta i cut.input.row (cut.input.state.activations i)
              cut.input.time c = .offer offered ∧
            offered.val = upOfferFields c ∧
            upAdmissible (codecParams p rate.eta) offered.val ∧
            (offered.val = upPlaceholder ∨
              (1 ≤ offered.val.sigma ∧ offered.val.sigma ≤ p.T ∧
                offered.val.S ≤ p.T * D p ∧ offered.val.delta ≤ D p ∧
                offered.val.q ≤ p.T * D p)) ∧
            cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
              sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m))) ∧
        (¬ selectedUpRound i cut.input.row
            (cut.input.state.activations i) cut.input.time →
          checkedUpOffer rate.eta i cut.input.row (cut.input.state.activations i)
            cut.input.time c = .noOffer) ∧
        (slotDraw (cut.input.row.2 cut.input.time).1 = dataSlot →
          cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
            pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
              (cut.input.row.2 cut.input.time).1) ∧
        (slotDraw (cut.input.row.2 cut.input.time).1 ≠ dataSlot →
          (¬ selectedUpRound i cut.input.row
              (cut.input.state.activations i) cut.input.time →
            cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i)))) ∧
      (∀ player : Fin p.m,
        cut.output.preparation.feedback.feedback player =
          if FiniteBanditModel.collisionFreeFor cut.output.preparation.arms.actions player then
            rewards cut.input.time (cut.output.preparation.arms.actions player) else 0) ∧
      (∀ player : Fin p.m,
        cut.output.ownEntries player =
          (cut.output.preparation.arms.actions player,
            ActualInitializationPhysicalStep.observationOfGrid p
              (cut.output.preparation.feedback.feedback player))) := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := firstLiveWindow execution.records
  let k := window.length
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start k
    (by
      have hk : k < count := by simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active
  have hfirstLive := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  have hFresult :
      (∀ k' : ℕ, k' ≤ window.length → ∃ hprefix : start + k' ≤ p.T,
        ∀ i : Fin (p.m - 1), ∃ s μ,
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start k'
            hprefix active).finalState.followers i = .ordinary s μ ∧
          localStateDomainValid s ∧ s.S + s.backlog ≤ k' * D p ∧
          s.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ s.buffer, saved.calendarRound < start + k' + 1) ∧
          (s.status = .unoccupied → s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∧
          (s.status ≠ .unoccupied → 0 < k' ∧ ∃ M token,
            s.lastDown = some M ∧ M.val.sigma = start + 1 ∧
            μ.lastProposalRead = some token ∧ token.timestamp.val + 1 = start + k' ∧
            token.bit = completeRowProposalBit p rate.eta.val (rows J) token.timestamp)) ∧
      (∀ k' : Fin window.length, ∀ i : Fin (p.m - 1), ∃ choice choiceMemory next nextMemory,
        (window[k'.val].output.preparation.followers.followers i).configuration =
          .ordinary choice choiceMemory ∧
        (window[k'.val].output.followers i).configuration = .ordinary next nextMemory ∧
        (window[k'.val].output.followers i).failure = none ∧
        ∀ selected : ReferenceActivePhysicalStep.Selection window[k'.val].input,
          window[k'.val].output.preparation.coordinator.selection = some selected →
          choice.status ≠ .unoccupied →
          choice.lastDown = some (selected.view.payload.downRecord i)) := by
    simpa [execution, window] using hfirstLive
  rcases hFresult with ⟨hFsafe, _⟩
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial rows J rewards start count hspan active hfirst
      (by simpa [execution, window] using hshort)
  rcases houtside with ⟨cut, suffix, hcutParts⟩
  have hsplit := hcutParts.1
  have hindex := hcutParts.2.1
  have htimeCut := hcutParts.2.2.1
  have hcutActual := hcutParts.2.2.2.1
  have hstateWitness := hcutParts.2.2.2.2
  rcases hstateWitness with ⟨r, q, base, hcutState, hprefixLive, hcall⟩
  dsimp only at hcall
  rcases hcall with ⟨dispatched, hstartCoordinator, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranchRest⟩
  rcases hbranchRest with
    ⟨hbranch, hkPositive, hsigmaStart, hbase, hbirth, hproposal, hqueues, hcutoffFacts⟩
  rcases hcutoffFacts with ⟨huValue, _, _, huGrid, _, _, _, _, hfirstCutoff, _⟩
  have hprefixBound : start + k ≤ p.T := by
    have hk : k < count := by simpa [window, execution] using hshort
    exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan
  have hsafeAtK := hFsafe k (by rfl)
  rcases hsafeAtK with ⟨hFspan, hFfollowers⟩
  have hinputState : cut.input.state = prefixRun.finalState := by
    rw [hcutActual]
    rfl
  have hindex' : cut = execution.records[k]'(by
      simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) := by
    simpa [execution, window, k] using hindex
  have htime' : cut.input.time.val = start + k := by
    simpa [window, k] using htimeCut
  have hcutRows : cut.input.rows = rows := by rw [hcutActual]; rfl
  have hcutSelected : cut.input.selected = J := by rw [hcutActual]; rfl
  have hcutRewards : cut.input.rewards = rewards := by rw [hcutActual]; rfl
  have hcutPrep : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation cut.output_eq
  have hpreparations : ∀ i : Fin (p.m - 1),
      cut.output.preparation.followers.followers i =
        DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) cut.input.time
          (cut.input.active i) (cut.input.state.followers i) := by
    intro i
    rw [hcutPrep]
    change (ReferenceActiveFeedbackCut.prepare
      (ReferenceActivePhysicalStep.followerInput cut.input)).followers i = _
    rfl
  refine ⟨cut, suffix, hsplit, hindex', htime', hinputState, hcutRows, hcutSelected,
    hcutRewards, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨s, μ, hs, hdomainS, hmass, hpairS, hchronS, hstatusFacts⟩ := hFfollowers i
    have hcutInputFollower : cut.input.state.followers i = .ordinary s μ := by
      rw [hinputState]
      exact hs
    let c : ReferencePrelaunchFollower.State p rate.eta := { s with status := .unoccupied }
    have hstartRound : startRound rate.eta cut.input.time s μ = .ok (c, μ) := by
      by_cases hu : s.status = .unoccupied
      · have hc : c = s := by
          cases s with
          | mk lastDown S delta backlog status downBatch buffer initializationFailure =>
              cases status with
              | unoccupied => rfl
              | pending => cases hu
              | released => cases hu
        rw [hc]
        exact startRound_unoccupied rate.eta cut.input.time s μ hdomainS hu
      · obtain ⟨hkpos, M, token, hdown, hsig, hread, hstamp, hbit⟩ := hstatusFacts.2 hu
        have hprior : isPriorProposalRead cut.input.time token := by
          change token.timestamp.val + 1 = cut.input.time.val
          omega
        have haccepted : acceptedStartCoordinate M = r.payload.sigma := by
          apply Fin.ext
          have hcoord := accepted_start_coordinate_one_based M
          omega
        have hfirstValue : firstCutoff p rate.eta.val r.payload.sigma
            (completeRowProposalBit p rate.eta.val (rows J)) = cut.input.time.val + 1 := by
          simpa only using hfirstCutoff
        have hgridMin : cut.input.time.val + 1 ≤
            gridBoundary p rate.eta.val (acceptedStartCoordinate M) := by
          have hcarrier := firstCutoffCarrier_nonempty p rate.eta.val r.payload.sigma
            (completeRowProposalBit p rate.eta.val (rows J))
          have hmin : firstCutoff p rate.eta.val r.payload.sigma
              (completeRowProposalBit p rate.eta.val (rows J)) ≤
              gridBoundary p rate.eta.val r.payload.sigma := by
            change (firstCutoffCarrier p rate.eta.val r.payload.sigma
              (completeRowProposalBit p rate.eta.val (rows J))).min' hcarrier ≤ _
            exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
          calc
            cut.input.time.val + 1 = firstCutoff p rate.eta.val r.payload.sigma
                (completeRowProposalBit p rate.eta.val (rows J)) := hfirstValue.symm
            _ ≤ gridBoundary p rate.eta.val r.payload.sigma := hmin
            _ = gridBoundary p rate.eta.val (acceptedStartCoordinate M) := by
              rw [haccepted]
        have hcause : gridBoundary p rate.eta.val (acceptedStartCoordinate M) =
              cut.input.time.val + 1 ∨ token.bit = true := by
          have hcarrier := firstCutoffCarrier_nonempty p rate.eta.val r.payload.sigma
            (completeRowProposalBit p rate.eta.val (rows J))
          have hmem : cut.input.time.val + 1 ∈
              firstCutoffCarrier p rate.eta.val r.payload.sigma
                (completeRowProposalBit p rate.eta.val (rows J)) := by
            rw [← hfirstValue]
            exact Finset.min'_mem _ hcarrier
          rcases Finset.mem_insert.mp hmem with hgrid | hevent
          · exact Or.inl (by rw [haccepted]; exact hgrid.symm)
          · obtain ⟨stamp, hstampMem, hendpoint⟩ := Finset.mem_image.mp hevent
            have htrue := (Finset.mem_filter.mp hstampMem).2
            have hstampValue : stamp.val + 2 = cut.input.time.val + 1 := by
              simpa [proposalEndpoint] using hendpoint
            have hstampEq : stamp.val + 2 = token.timestamp.val + 2 := by
              calc
                stamp.val + 2 = cut.input.time.val + 1 := hstampValue
                _ = start + k + 1 := by rw [htime']
                _ = (token.timestamp.val + 1) + 1 := by rw [← hstamp]
                _ = token.timestamp.val + 2 := rfl
            have hstampCoordinate : stamp.val = token.timestamp.val :=
              Nat.add_right_cancel hstampEq
            have hsame : stamp = token.timestamp := by
              exact Fin.ext hstampCoordinate
            have htokenTrue : completeRowProposalBit p rate.eta.val
                (rows J) token.timestamp = true := by
              simpa [hsame] using htrue
            exact Or.inr (hbit.trans htokenTrue)
        have hstarted : M.val.sigma ≤ cut.input.time.val := by
          rw [hsig, htime']
          exact Nat.add_le_add_left (Nat.succ_le_of_lt hkpos) start
        have hstartOccupied := startRound_occupied_branch rate.eta cut.input.time s μ
          hu hdomainS M hdown hstarted hgridMin token hread hprior
        simpa [c, hcause] using hstartOccupied
    have hlocalDomain : localStateDomainValid c := by
      change (serviceRegistersValid p s ∧ localBufferValid s ∧ downDecoderStateValid s)
      exact hdomainS
    have hlocalDomainFacts := hlocalDomain
    rcases hlocalDomainFacts with ⟨⟨hSc, hDeltac, hBacklogc⟩, hBufferc, hBatchc⟩
    have hinputDomain : stateInputDomain c :=
      ⟨hSc, hDeltac, hBacklogc, hBufferc.1, hBufferc.2.1⟩
    have hzeroOffer : s.lastDown = none → upOfferFields c = upPlaceholder := by
      intro hnone
      have hu : s.status = .unoccupied := by
        by_contra hnot
        obtain ⟨_, M, _, hdown, _, _, _, _⟩ := hstatusFacts.2 hnot
        rw [hnone] at hdown
        cases hdown
      obtain ⟨_, hS0, hDelta0, hBacklog0⟩ := hstatusFacts.1 hu
      simp [upOfferFields, acceptedStart, c, hnone, hS0, hDelta0, hBacklog0,
        upPlaceholder]
    have hupAdmissible : upAdmissible (codecParams p rate.eta) (upOfferFields c) := by
      by_cases hnone : c.lastDown = none
      · rw [hzeroOffer (by simpa [c] using hnone)]
        exact Or.inl rfl
      · have hu : s.status ≠ .unoccupied := by
          intro hstatus
          obtain ⟨hdown, _, _, _⟩ := hstatusFacts.1 hstatus
          have : c.lastDown = none := by simp [c, hdown]
          exact hnone this
        obtain ⟨_, M, _, hdown, hsig, _, _, _⟩ := hstatusFacts.2 hu
        have hdownC : c.lastDown = some M := by simp [c, hdown]
        have hM := M.property
        simp only [downAdmissible] at hM
        rcases hM with ⟨hsigmaLo, hsigmaHi, _, _, _, _, _, _, _, _, _⟩
        unfold upAdmissible
        right
        refine ⟨?_, ?_, hSc, hDeltac, hBacklogc⟩
        · simpa [upOfferFields, acceptedStart, hdownC] using hsigmaLo
        · simpa [upOfferFields, acceptedStart, hdownC] using hsigmaHi
    have hvalidChoice : upStateDomain c ∧
        offeredUpMatchesState c (⟨upOfferFields c, hupAdmissible⟩ :
          UpRecord (codecParams p rate.eta)) := by
      refine ⟨⟨hSc, hDeltac, hBacklogc⟩, ?_⟩
      simp [offeredUpMatchesState, upOfferFields]
    have hactualConfiguration :
        (cut.output.preparation.followers.followers i).configuration = .ordinary c μ := by
      rw [hpreparations i, hcutInputFollower]
      by_cases hselected : selectedUpRound i cut.input.row
          (cut.input.state.activations i) cut.input.time
      · let offered : UpRecord (codecParams p rate.eta) := ⟨upOfferFields c, hupAdmissible⟩
        have hoff : checkedUpOffer rate.eta i cut.input.row
            (cut.input.state.activations i) cut.input.time c = .offer offered := by
          simp [checkedUpOffer, hinputDomain, hselected, c, hupAdmissible, offered]
        rcases hselected with ⟨_, hslot, hdraw⟩
        have hchoiceCore := followerArmChoiceCore_unoccupied_selected_up c
          (cut.input.row.2 cut.input.time) i offered rfl hslot hdraw
          (by simpa [offered] using hvalidChoice)
        have hchoice : followerArmChoice c cut.input.row cut.input.time i (some offered) =
            some (sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m))) := by
          rw [followerArmChoice_eq_core]
          exact hchoiceCore
        simp [DeclaredFollowerLocalRound.prepare, hstartRound, hoff, hchoice, offered]
      · have hoff : checkedUpOffer rate.eta i cut.input.row
            (cut.input.state.activations i) cut.input.time c = .noOffer :=
          checkedUpOffer_noOffer rate.eta i cut.input.row
            (cut.input.state.activations i) cut.input.time c hinputDomain
            (by intro ⟨hsel, hu⟩; exact hselected hsel)
        by_cases hdata : slotDraw (cut.input.row.2 cut.input.time).1 = dataSlot
        · have hchoiceCore := followerArmChoiceCore_unoccupied_data c
            (cut.input.row.2 cut.input.time) i none rfl hdata
          have hchoice : followerArmChoice c cut.input.row cut.input.time i none =
              some (pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
                (cut.input.row.2 cut.input.time).1) := by
            rw [followerArmChoice_eq_core]
            exact hchoiceCore
          simp [DeclaredFollowerLocalRound.prepare, hstartRound, hoff, hchoice]
        · have hnotSelectedDraw : ¬ (slotDraw (cut.input.row.2 cut.input.time).1 = upSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1 = i) := by
            rintro ⟨hslot, hdraw⟩
            exact hselected ⟨cut.input.active i, hslot, hdraw⟩
          have hchoiceCore := followerArmChoiceCore_unoccupied_other c
            (cut.input.row.2 cut.input.time) i none rfl hdata hnotSelectedDraw
          have hchoice : followerArmChoice c cut.input.row cut.input.time i none =
              some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i)) := by
            rw [followerArmChoice_eq_core]
            exact hchoiceCore
          simp [DeclaredFollowerLocalRound.prepare, hstartRound, hoff, hchoice]
    have hactualArm : cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
        (DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) cut.input.time (cut.input.active i)
          (cut.input.state.followers i)).arm :=
      ReferenceActivePhysicalStep.PreparedRound.action_follower cut.output.preparation i
    rw [hcutInputFollower] at hactualArm
    have hselectedOffer : selectedUpRound i cut.input.row
        (cut.input.state.activations i) cut.input.time →
        ∃ offered,
          checkedUpOffer rate.eta i cut.input.row (cut.input.state.activations i)
            cut.input.time c = .offer offered ∧
          offered.val = upOfferFields c ∧
          upAdmissible (codecParams p rate.eta) offered.val ∧
          (offered.val = upPlaceholder ∨
            (1 ≤ offered.val.sigma ∧ offered.val.sigma ≤ p.T ∧
              offered.val.S ≤ p.T * D p ∧ offered.val.delta ≤ D p ∧
              offered.val.q ≤ p.T * D p)) ∧
          cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
            sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m)) := by
      intro hsel
      let offered : UpRecord (codecParams p rate.eta) := ⟨upOfferFields c, hupAdmissible⟩
      have hoff : checkedUpOffer rate.eta i cut.input.row
          (cut.input.state.activations i) cut.input.time c = .offer offered := by
        simp [checkedUpOffer, hinputDomain, hsel, c, hupAdmissible, offered]
      rcases hsel with ⟨_, hslot, hdraw⟩
      have hchoiceCore := followerArmChoiceCore_unoccupied_selected_up c
        (cut.input.row.2 cut.input.time) i offered rfl hslot hdraw
        (by simpa [offered] using hvalidChoice)
      have hchoice : followerArmChoice c cut.input.row cut.input.time i (some offered) =
          some (sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m))) := by
        rw [followerArmChoice_eq_core]
        exact hchoiceCore
      have hlocalArm : (DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) cut.input.time (cut.input.active i)
          (.ordinary s μ)).arm =
          sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m)) := by
        simp [DeclaredFollowerLocalRound.prepare, hstartRound, hoff, hchoice, offered]
      have harm : cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
          sendArm (offeredUpBit rate.eta (cut.input.row.2 cut.input.time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (coordinator p.two_le_m)) := by
        calc
          _ = (DeclaredFollowerLocalRound.prepare rate i cut.input.row
            (cut.input.state.activations i) cut.input.time (cut.input.active i)
            (.ordinary s μ)).arm := by simpa [hcutInputFollower] using hactualArm
          _ = _ := hlocalArm
      refine ⟨offered, hoff, rfl, ?_, ?_, harm⟩
      · simpa [offered] using hupAdmissible
      · exact hupAdmissible
    have hnoOffer : ¬ selectedUpRound i cut.input.row
        (cut.input.state.activations i) cut.input.time →
        checkedUpOffer rate.eta i cut.input.row (cut.input.state.activations i)
          cut.input.time c = .noOffer := by
      intro hnot
      exact checkedUpOffer_noOffer rate.eta i cut.input.row
        (cut.input.state.activations i) cut.input.time c hinputDomain
        (by intro ⟨hsel, hu⟩; exact hnot hsel)
    have hdataArm : slotDraw (cut.input.row.2 cut.input.time).1 = dataSlot →
        cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
            (cut.input.row.2 cut.input.time).1 := by
      intro hdata
      by_cases hsel : selectedUpRound i cut.input.row
          (cut.input.state.activations i) cut.input.time
      · rcases hsel with ⟨_, hslot, _⟩
        have hne : upSlot ≠ dataSlot := by decide
        exact False.elim (hne (hslot.symm.trans hdata))
      · have hcore := followerArmChoiceCore_unoccupied_data c
          (cut.input.row.2 cut.input.time) i none rfl hdata
        have hchoice : followerArmChoice c cut.input.row cut.input.time i none =
            some (pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
              (cut.input.row.2 cut.input.time).1) := by
          rw [followerArmChoice_eq_core]
          exact hcore
        rw [hactualArm]
        simp [DeclaredFollowerLocalRound.prepare, hstartRound, hnoOffer hsel, hchoice]
    have hotherArm : slotDraw (cut.input.row.2 cut.input.time).1 ≠ dataSlot →
        (¬ selectedUpRound i cut.input.row
            (cut.input.state.activations i) cut.input.time →
          cut.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i)) := by
      intro hnotdata hnotselected
      have hnoSelectedDraw : ¬ (slotDraw (cut.input.row.2 cut.input.time).1 = upSlot ∧
          selectedFollowerDraw p.two_le_m p.m_lt_K
            (cut.input.row.2 cut.input.time).1 = i) := by
        rintro ⟨hslot, hdraw⟩
        exact hnotselected ⟨cut.input.active i, hslot, hdraw⟩
      have hcore := followerArmChoiceCore_unoccupied_other c
        (cut.input.row.2 cut.input.time) i none rfl hnotdata hnoSelectedDraw
      have hchoice : followerArmChoice c cut.input.row cut.input.time i none =
          some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (cut.input.row.2 cut.input.time).1).val (followerPlayer p.two_le_m i)) := by
        rw [followerArmChoice_eq_core]
        exact hcore
      rw [hactualArm]
      simp [DeclaredFollowerLocalRound.prepare, hstartRound, hnoOffer hnotselected, hchoice]
    exact ⟨s, μ, hs, hstatusFacts.1, hstatusFacts.2, hstartRound,
      hactualConfiguration, hlocalDomain,
      by simpa [c] using hmass, hSc, hDeltac, hBacklogc, hpairS,
      by
        intro saved hmem
        have hsaved := hchronS saved hmem
        omega,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, hzeroOffer, hselectedOffer, hnoOffer,
      hdataArm, hotherArm⟩
  · intro player
    rw [← hcutRewards]
    rw [cut.output_eq]
    change (ReferenceActivePhysicalStep.prepare cut.input).feedback.feedback player =
      if FiniteBanditModel.collisionFreeFor
          (ReferenceActivePhysicalStep.prepare cut.input).arms.actions player then
        cut.input.rewards cut.input.time
          ((ReferenceActivePhysicalStep.prepare cut.input).arms.actions player) else 0
    exact ReferenceActivePhysicalStep.PreparedRound.feedback_rule
      (ReferenceActivePhysicalStep.prepare cut.input) player
  · intro player
    rw [cut.output_eq]
    exact ReferenceActivePhysicalStep.step_own_entry cut.input player

end Bandits.Support.ReferenceFirstCutoffFollowerPreparation

end
