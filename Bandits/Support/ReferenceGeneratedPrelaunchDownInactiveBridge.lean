/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport

import Lean.Elab.Tactic.Omega

/-!
# Inactive and stopped generated prelaunch DOWN handoff

This module continues the actual generated prefix only from an inactive or
stopped incoming selector.  Inactive followers acquire no physical observation
before a real block-end declaration or forced launch; stopped boundaries and
their ordinary states remain the actual generated output.  It adds no history,
transition, or decoder state.

Sources: `07_public_setup.tex:60-114,127-142`,
`05_binary_transport.tex:20-42`, and `appendix_a_local_protocol.tex:111-138`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownInactiveBridge

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem roundBlockIndex_succ_eq_or_next (r : Fin p.T)
    (hnext : r.val + 1 < p.T) :
    roundBlockIndex p (⟨r.val + 1, hnext⟩ : Fin p.T) = roundBlockIndex p r ∨
      (roundBlockIndex p (⟨r.val + 1, hnext⟩ : Fin p.T)).val =
        (roundBlockIndex p r).val + 1 := by
  dsimp only [roundBlockIndex]
  let B := B_boot p
  let q := r.val / B
  let rem := r.val % B
  have hB : 0 < B := B_boot_pos p
  have hdecomp : q * B + rem = r.val := by
    dsimp [q, rem, B]
    exact Nat.div_add_mod' r.val (B_boot p)
  have hrem : rem < B := by
    dsimp [rem, B]
    exact Nat.mod_lt _ hB
  have hremSucc : rem + 1 ≤ B := Nat.succ_le_of_lt hrem
  have hsuccBound : r.val + 1 ≤ (q + 1) * B := by
    calc
      r.val + 1 = q * B + rem + 1 := by rw [← hdecomp]
      _ ≤ q * B + B := Nat.add_le_add_left hremSucc _
      _ = (q + 1) * B := by rw [Nat.add_mul, one_mul]
  have hqle : q ≤ (r.val + 1) / B :=
    Nat.div_le_div_right (Nat.le_succ r.val)
  have hnextle : (r.val + 1) / B ≤ q + 1 := by
    by_contra h
    have hlt : q + 1 < (r.val + 1) / B := Nat.lt_of_not_ge h
    have hmul := Nat.mul_lt_mul_of_pos_right hlt hB
    have hdiv := Nat.div_mul_le_self (r.val + 1) B
    omega
  have hcases : (r.val + 1) / B = q ∨ (r.val + 1) / B = q + 1 := by omega
  simpa [q, B] using hcases

private theorem inactive_finishBlock_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inr inactive) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let f := ActualReferenceInitializationBlock.refFollower i
        let b := inactive.val.1.val
        let h := inactive.val.1.property.1
        let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
          ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
            inactive.property.2.1⟩
        let candidate := ReferenceInitializationRun.candidate x b h ui
        let next := ReferenceInitializationRun.finishBlock x b h
        b.crossing = none ∧
          ReferenceInitializationRun.declaredActivation x b h f =
            (if candidate.pending then
              some (ReferenceInitializationRun.boundaryActivation b) else none) ∧
          (next.activation f = none ∧ candidate.pending = false ∧
              ReferenceInitializationRun.crosses x b h = false ∧
              next.forcedFailure f = false ∧
              ReferenceInitializationRun.ordinary x next f =
                ReferencePrelaunchFollower.initial p rate.eta ∨
            ∃ a, next.activation f = some a ∧
              a.val = ReferenceInitializationRun.elapsed p (b.completed + 1) + 1 ∧
              ReferenceInitializationRun.ordinary x next f =
                ReferencePrelaunchFollower.initial p rate.eta ∧
              ((candidate.pending = true ∧ next.forcedFailure f = false) ∨
                (candidate.pending = false ∧
                  ReferenceInitializationRun.forced x b h f = true ∧
                  next.forcedFailure f = true)))
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr inactive =>
          let x := sourceReferenceInput rate rewards C_star C_h z
          let f := ActualReferenceInitializationBlock.refFollower i
          let b := inactive.val.1.val
          let h := inactive.val.1.property.1
          let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
            ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
              inactive.property.2.1⟩
          let candidate := ReferenceInitializationRun.candidate x b h ui
          let next := ReferenceInitializationRun.finishBlock x b h
          have hcross : b.crossing = none := inactive.val.1.property.2.1
          have hcrossRun : (ReferenceInitializationRun.run x
              (roundBlockIndex p r).val).crossing = none := by
            rw [← inactive.val.1.property.2.2]
            exact hcross
          have hforcedBefore : b.forcedFailure f = false := by
            have hrun := ReferenceInitializationRun.run_no_forced_before_launch
              x (roundBlockIndex p r).val hcrossRun f
            change inactive.val.1.val.forcedFailure f = false
            rw [inactive.val.1.property.2.2]
            exact hrun
          have hu : f ∈ ReferenceInitializationRun.uninformed b := ui.property
          have hdecl : ReferenceInitializationRun.declaredActivation x b h f =
              (if candidate.pending then
                some (ReferenceInitializationRun.boundaryActivation b) else none) := by
            simp only [ReferenceInitializationRun.declaredActivation, ui, hu,
              dite_true, candidate]
          refine ⟨hcross, hdecl, ?_⟩
          by_cases hpending : candidate.pending = true
          · right
            refine ⟨ReferenceInitializationRun.boundaryActivation b, ?_, ?_, ?_, ?_⟩
            · change ReferenceInitializationRun.finalActivation x b h f = _
              simp [ReferenceInitializationRun.finalActivation,
                ReferenceInitializationRun.forced, hdecl, hpending]
            · rfl
            · exact ReferenceInitializationRun.ordinary_finishBlock_of_saved
                x b h ui hpending hforcedBefore
            · left
              constructor
              · exact hpending
              · have hnotforced := ReferenceInitializationRun.saved_not_forced
                  x b h ui hpending
                change (b.forcedFailure f ||
                  ReferenceInitializationRun.forced x b h f) = false
                rw [hforcedBefore, hnotforced]
                rfl
          · have hpendingFalse : candidate.pending = false := by
              cases hp : candidate.pending <;> simp_all
            have hdeclNone : ReferenceInitializationRun.declaredActivation x b h f = none := by
              rw [hdecl, hpendingFalse]
              rfl
            by_cases hcrosses : ReferenceInitializationRun.crosses x b h = true
            · right
              refine ⟨ReferenceInitializationRun.boundaryActivation b, ?_, ?_, ?_, ?_⟩
              · change ReferenceInitializationRun.finalActivation x b h f = _
                simp [ReferenceInitializationRun.finalActivation,
                  ReferenceInitializationRun.forced, hdeclNone, hcrosses]
              · rfl
              · have hforced : ReferenceInitializationRun.forced x b h f = true := by
                  simp [ReferenceInitializationRun.forced, hdeclNone, hcrosses]
                change ReferenceInitializationRun.ordinary x next f =
                  ReferencePrelaunchFollower.initial p rate.eta
                rw [ReferenceInitializationRun.forced_ordinary x b h f hforced]
                exact ReferencePrelaunchFollower.forcedAtLaunch_state p rate.eta
              · right
                have hforced : ReferenceInitializationRun.forced x b h f = true := by
                  simp [ReferenceInitializationRun.forced, hdeclNone, hcrosses]
                constructor
                · exact hpendingFalse
                · constructor
                  · exact hforced
                  · change (b.forcedFailure f ||
                      ReferenceInitializationRun.forced x b h f) = true
                    rw [hforcedBefore, hforced]
                    rfl
            · left
              have hcrossFalse : ReferenceInitializationRun.crosses x b h = false := by
                cases hc : ReferenceInitializationRun.crosses x b h with
                | false => rfl
                | true => exact (hcrosses hc).elim
              have hactNone : next.activation f = none := by
                change ReferenceInitializationRun.finalActivation x b h f = none
                simp [ReferenceInitializationRun.finalActivation,
                  ReferenceInitializationRun.forced, hdeclNone, hcrossFalse]
              have hforcedNext : next.forcedFailure f = false := by
                change (b.forcedFailure f ||
                  ReferenceInitializationRun.forced x b h f) = false
                rw [hforcedBefore]
                simp [ReferenceInitializationRun.forced, hdeclNone, hcrossFalse]
              have hordinary : ReferenceInitializationRun.ordinary x next f =
                  ReferencePrelaunchFollower.initial p rate.eta := by
                simp only [ReferenceInitializationRun.ordinary, hforcedNext,
                  Bool.false_eq_true, ↓reduceIte, hactNone]
                simp [x, sourceReferenceInput,
                  ActualReferenceInitializationBlock.referenceInput]
              exact ⟨hactNone, hpendingFalse, hcrossFalse, hforcedNext,
                hordinary⟩
  | inr _ => trivial

private theorem inactive_successor_boundary_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inr inactive) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let s := roundBlockIndex p r
        let b := inactive.val.1.val
        let h := inactive.val.1.property.1
        roundBlockIndex p rNext = s ∨
          ((roundBlockIndex p rNext).val = s.val + 1 ∧
            ReferenceInitializationRun.run x (s.val + 1) =
              ReferenceInitializationRun.finishBlock x b h ∧
            rNext.val = ReferenceInitializationRun.elapsed p (b.completed + 1))
    | _ => True := by
  classical
  let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr inactive =>
          let x := sourceReferenceInput rate rewards C_star C_h z
          let s := roundBlockIndex p r
          let sNext := roundBlockIndex p rNext
          let b := inactive.val.1.val
          let h := inactive.val.1.property.1
          have hindex := roundBlockIndex_succ_eq_or_next r hnext
          rcases hindex with hsame | hnew
          · exact Or.inl hsame
          · have hcross : b.crossing = none := inactive.val.1.property.2.1
            have hboundary : b = ReferenceInitializationRun.run x s.val :=
              inactive.val.1.property.2.2
            have hprogress := ReferenceInitializationRun.run_progress x s.val
              (Nat.le_of_lt s.isLt)
            have hcompleted : b.completed = s.val := by
              rcases hprogress with hcrossed | hcompleted
              · have hcrossedB : b.crossing.isSome = true := by
                  simpa [hboundary] using hcrossed
                simp [hcross] at hcrossedB
              · rw [hboundary]
                exact hcompleted
            have hremain : b.completed < n_boot p := h
            have hfinish : ReferenceInitializationRun.run x (s.val + 1) =
                ReferenceInitializationRun.finishBlock x b h := by
              rw [ReferenceInitializationRun.run_succ]
              rw [hboundary.symm]
              rw [ReferenceInitializationRun.advance_of_no_crossing x b hcross h]
            have hquot : rNext.val / B_boot p = s.val + 1 := by
              change (r.val + 1) / B_boot p = r.val / B_boot p + 1
              exact hnew
            have hstartLower : (s.val + 1) * B_boot p ≤ rNext.val := by
              have hdiv := Nat.div_mul_le_self rNext.val (B_boot p)
              rw [hquot] at hdiv
              simpa [s, roundBlockIndex] using hdiv
            have hrMem := (mem_calendarBlock_iff p s r).1
              (round_mem_quotient_block p r)
            have hrupper : r.val < (s.val + 1) * B_boot p :=
              lt_of_lt_of_le hrMem.2 (Nat.min_le_right _ _)
            have hstartValue : rNext.val = (s.val + 1) * B_boot p := by
              dsimp [rNext] at hstartLower ⊢
              omega
            have hendBlock : ReferenceInitializationRun.elapsed p (s.val + 1) = rNext.val := by
              have hlt : (s.val + 1) * B_boot p < p.T := by
                rw [← hstartValue]
                exact rNext.isLt
              change min p.T ((s.val + 1) * B_boot p) = rNext.val
              rw [Nat.min_eq_right (Nat.le_of_lt hlt), hstartValue]
            have hend : rNext.val = ReferenceInitializationRun.elapsed p
                (b.completed + 1) := by
              calc
                rNext.val = ReferenceInitializationRun.elapsed p (s.val + 1) :=
                  hendBlock.symm
                _ = ReferenceInitializationRun.elapsed p (b.completed + 1) := by
                  rw [hcompleted]
            exact Or.inr ⟨hnew, hfinish, hend⟩
  | inr _ => trivial

/-- An inactive generated prefix has no current DOWN test or earlier census.
The observation at the current physical round is deliberately not supplied. -/
theorem source_prelaunch_down_inactive_current_test
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inr _) =>
        source_prelaunch_down_current_test rate rewards C_star C_h z i r = none ∧
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = []
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr _ => simp [source_prelaunch_down_current_test,
          source_prelaunch_down_prefix_tests, hpref]
  | inr _ => trivial

/-- The actual successor of an inactive generated prefix is still inactive
inside a block. At a block end, the source's real pending declaration or
crossing-force selector is applied before the next prefix; any new activation
starts from `initial`, and the strict-prefix DOWN census remains empty. -/
theorem source_prelaunch_down_inactive_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inr inactive) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let f := ActualReferenceInitializationBlock.refFollower i
        let b := inactive.val.1.val
        let h := inactive.val.1.property.1
        let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
          ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
            inactive.property.2.1⟩
        let candidate := ReferenceInitializationRun.candidate x b h ui
        source_prelaunch_down_current_test rate rewards C_star C_h z i r = none ∧
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = [] ∧
          match source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
          | .inl (.inr nextInactive) =>
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] ∧
                nextInactive.val.1.val.activation f = none ∧
                (nextInactive.val.1.val = b ∨
                  (nextInactive.val.1.val = ReferenceInitializationRun.finishBlock x b h ∧
                    candidate.pending = false ∧
                    ReferenceInitializationRun.crosses x b h = false))
          | .inl (.inl nextActive) =>
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] ∧
                ∃ a, nextActive.val.2.1 = a ∧
                  nextActive.val.1.val = ReferenceInitializationRun.finishBlock x b h ∧
                  nextActive.val.1.val.activation f = some a ∧
                  a.val = r.val + 2 ∧
                  nextActive.val.2.2.2 = ReferencePrelaunchFollower.initial p
                    (sourceReferenceInput rate rewards C_star C_h z).eta ∧
                  candidate.pending = true ∧
                  ReferenceInitializationRun.declaredActivation x b h f = some a
          | .inr nextStopped =>
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] ∧
                ∃ a, nextStopped.val.1 = ReferenceInitializationRun.finishBlock x b h ∧
                  nextStopped.val.1.activation f = some a ∧
                  a.val = r.val + 2 ∧
                  nextStopped.val.2 = ReferencePrelaunchFollower.initial p
                    (sourceReferenceInput rate rewards C_star C_h z).eta ∧
                  ((candidate.pending = true ∧
                      nextStopped.val.1.forcedFailure f = false ∧
                      ReferenceInitializationRun.declaredActivation x b h f = some a) ∨
                    (candidate.pending = false ∧
                      ReferenceInitializationRun.forced x b h f = true ∧
                      nextStopped.val.1.forcedFailure f = true ∧
                      ReferenceInitializationRun.declaredActivation x b h f = none))
    | _ => True := by
  classical
  let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr inactive =>
          let x := sourceReferenceInput rate rewards C_star C_h z
          let f := ActualReferenceInitializationBlock.refFollower i
          let b := inactive.val.1.val
          let h := inactive.val.1.property.1
          let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
            ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
              inactive.property.2.1⟩
          let candidate := ReferenceInitializationRun.candidate x b h ui
          have hcurrent : source_prelaunch_down_current_test rate rewards C_star C_h z i r = none := by
            simp [source_prelaunch_down_current_test, hpref]
          have htests : source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = [] := by
            simp [source_prelaunch_down_prefix_tests, hpref]
          have hboundaryData := inactive_successor_boundary_data
            rate rewards C_star C_h z i r hnext
          simp only [hpref] at hboundaryData
          have hfinishData := inactive_finishBlock_data
            rate rewards C_star C_h z i r
          simp only [hpref] at hfinishData
          rcases hfinishData with ⟨hcross, hdecl, hfinishCase⟩
          rcases hboundaryData with hsame | ⟨hnew, hstep, hend⟩
          · have hsameTransport :=
              source_prelaunch_down_same_block_inactive_transport
                rate rewards C_star C_h z i r hnext hsame
            simp only [hpref] at hsameTransport
            cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
            | inl nextBranch =>
                cases nextBranch with
                | inl nextActive => simp [rNext, hnextPrefix] at hsameTransport
                | inr nextInactive =>
                    simp only [rNext, hnextPrefix] at hsameTransport
                    rcases hsameTransport with
                      ⟨hboundarySame, hactivationNone, _, htestsNext, _⟩
                    simp only [rNext, hnextPrefix]
                    exact ⟨hcurrent, htests, htestsNext, hactivationNone,
                      Or.inl hboundarySame⟩
            | inr nextStopped => simp [rNext, hnextPrefix] at hsameTransport
          · have hnextBoundary :
                ReferenceInitializationRun.run x (roundBlockIndex p rNext).val =
                  ReferenceInitializationRun.finishBlock x b h := by
              have hidx :
                  (roundBlockIndex p rNext).val = (roundBlockIndex p r).val + 1 := hnew
              simpa only [hidx] using hstep
            cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
            | inl nextBranch =>
                cases nextBranch with
                | inr nextInactive =>
                    have hnextRun : nextInactive.val.1.val =
                        ReferenceInitializationRun.finishBlock x b h := by
                      calc
                        nextInactive.val.1.val =
                            ReferenceInitializationRun.run x
                              (roundBlockIndex p rNext).val :=
                          nextInactive.val.1.property.2.2
                        _ = ReferenceInitializationRun.finishBlock x b h := hnextBoundary
                    rcases hfinishCase with hnoActivation | ⟨a, ha, haval,
                      hordinary, horigin⟩
                    · have hact : (ReferenceInitializationRun.finishBlock x b h).activation f = none := by
                        rw [← hnextRun]
                        exact nextInactive.property.2.1
                      have hpending : candidate.pending = false := hnoActivation.2.1
                      have hcrosses : ReferenceInitializationRun.crosses x b h = false :=
                        hnoActivation.2.2.1
                      have htestsNext :
                          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] := by
                        simp [rNext, source_prelaunch_down_prefix_tests, hnextPrefix]
                      simp only [rNext, hnextPrefix]
                      exact ⟨hcurrent, htests, htestsNext,
                        nextInactive.property.2.1,
                        Or.inr ⟨hnextRun, hpending, hcrosses⟩⟩
                    · have hsome : (ReferenceInitializationRun.finishBlock x b h).activation f = some a := by
                        exact ha
                      have hnone : (ReferenceInitializationRun.finishBlock x b h).activation f = none := by
                        rw [← hnextRun]
                        exact nextInactive.property.2.1
                      rw [hnone] at hsome
                      cases hsome
                | inl nextActive =>
                    have hnextRun : nextActive.val.1.val =
                        ReferenceInitializationRun.finishBlock x b h := by
                      calc
                        nextActive.val.1.val =
                            ReferenceInitializationRun.run x
                              (roundBlockIndex p rNext).val :=
                          nextActive.val.1.property.2.2
                        _ = ReferenceInitializationRun.finishBlock x b h := hnextBoundary
                    rcases nextActive.property with ⟨hbefore, hactivation, hstate, _⟩
                    have hsome : (ReferenceInitializationRun.finishBlock x b h).activation f =
                        some nextActive.val.2.1 := by
                      rw [← hnextRun]
                      exact hactivation
                    rcases hfinishCase with hnoActivation | ⟨a, ha, haval,
                      hordinary, horigin⟩
                    · have : (ReferenceInitializationRun.finishBlock x b h).activation f = none := hnoActivation.1
                      simp [this] at hsome
                    · have hactEq : nextActive.val.2.1 = a :=
                        Option.some.inj (hsome.symm.trans ha)
                      have hactivationRound : a.val = r.val + 2 := by
                        rw [← hend] at haval
                        change a.val = rNext.val + 1 at haval
                        dsimp [rNext] at haval
                        omega
                      have hbeforeActivation : rNext.val < a.val := by
                        rw [hactivationRound]
                        dsimp [rNext]
                        omega
                      have hinitial : nextActive.val.2.2.2 =
                          ReferencePrelaunchFollower.initial p x.eta := by
                        rw [hstate, hactEq]
                        exact ReferencePrelaunchFollower.replay_before_activation
                          x.eta i x.row a nextActive.val.2.2.1
                          (Nat.le_of_lt rNext.isLt) hbeforeActivation
                      have hcandidate : candidate.pending = true := by
                        rcases horigin with hpending | hforced
                        · exact hpending.1
                        · have hcrossSome :
                              ReferenceInitializationRun.crosses x b h = true :=
                            (ReferenceInitializationRun.forced_iff x b h f).mp
                              hforced.2.1 |>.1
                          have hfinishNoCrossing :
                              (ReferenceInitializationRun.finishBlock x b h).crossing = none := by
                            rw [← hnextRun]
                            exact nextActive.val.1.property.2.1
                          rcases ReferenceInitializationRun.finishBlock_equations x b h with
                            ⟨_, _, _, _, _, hfinishCrossEq⟩
                          rw [hcrossSome] at hfinishCrossEq
                          have hfinishCrossing :
                              (ReferenceInitializationRun.finishBlock x b h).crossing ≠ none := by
                            rw [hfinishCrossEq]
                            simp
                          exact False.elim (hfinishCrossing hfinishNoCrossing)
                      have hba : a = ReferenceInitializationRun.boundaryActivation b := by
                        apply Subtype.ext
                        exact haval
                      have hdeclared : ReferenceInitializationRun.declaredActivation x b h f = some a := by
                        rw [hdecl, hcandidate]
                        exact congrArg some hba.symm
                      have htestsNext :
                          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] := by
                        have hcensus := source_prelaunch_down_prefix_census
                          rate rewards C_star C_h z i rNext
                        simp only [rNext, hnextPrefix] at hcensus
                        have hmap :
                            (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext).map
                              ReferenceGeneratedPrelaunchDownCohort.testEntry =
                              AffineBatchDecoder.collected nextActive.val.2.2.2.downBatch := hcensus.1
                        have hmapNil :
                            (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext).map
                              ReferenceGeneratedPrelaunchDownCohort.testEntry = [] := by
                          simpa [hinitial, ReferencePrelaunchFollower.initial,
                            AffineBatchDecoder.initial, AffineBatchDecoder.collected] using hmap
                        exact List.map_eq_nil_iff.mp hmapNil
                      simp only [rNext, hnextPrefix]
                      have hsomeNext : nextActive.val.1.val.activation f = some a := by
                        rw [hnextRun]
                        exact hsome.trans (congrArg some hactEq)
                      exact ⟨hcurrent, htests, htestsNext, ⟨a, hactEq,
                        hnextRun, hsomeNext, hactivationRound, hinitial,
                        hcandidate, hdeclared⟩⟩
            | inr nextStopped =>
                have hnextRun : nextStopped.val.1 =
                    ReferenceInitializationRun.finishBlock x b h := by
                  calc
                    nextStopped.val.1 = ReferenceInitializationRun.run x
                        (roundBlockIndex p rNext).val := nextStopped.property.2.1
                    _ = ReferenceInitializationRun.finishBlock x b h := hnextBoundary
                rcases hfinishCase with hnoActivation | ⟨a, ha, haval,
                  hordinary, horigin⟩
                · have hcrossnext : (ReferenceInitializationRun.finishBlock x b h).crossing ≠ none := by
                    rw [← hnextRun]
                    exact nextStopped.property.1
                  have hcrossnone :
                      (ReferenceInitializationRun.finishBlock x b h).crossing = none := by
                    change (if ReferenceInitializationRun.crosses x b h then
                      some (ReferenceInitializationRun.nextBlock b h) else none) = none
                    rw [hnoActivation.2.2.1]
                    rfl
                  exact False.elim (hcrossnext hcrossnone)
                · have hactFinish :
                      (ReferenceInitializationRun.finishBlock x b h).activation f = some a := ha
                  have hactNext : nextStopped.val.1.activation f = some a := by
                    rw [hnextRun]
                    exact hactFinish
                  have hinitialStopped : nextStopped.val.2 =
                      ReferencePrelaunchFollower.initial p x.eta := by
                    rw [nextStopped.property.2.2, hnextRun]
                    exact hordinary
                  have hactivationRound : a.val = r.val + 2 := by
                    rw [← hend] at haval
                    change a.val = rNext.val + 1 at haval
                    dsimp [rNext] at haval
                    omega
                  have htestsNext :
                      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] := by
                    have hcensus := source_prelaunch_down_prefix_census
                      rate rewards C_star C_h z i rNext
                    simp only [rNext, hnextPrefix] at hcensus
                    have hmap :
                        (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext).map
                          ReferenceGeneratedPrelaunchDownCohort.testEntry =
                          AffineBatchDecoder.collected nextStopped.val.2.downBatch := hcensus.1
                    have hmapNil :
                        (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext).map
                          ReferenceGeneratedPrelaunchDownCohort.testEntry = [] := by
                      simpa [hinitialStopped, ReferencePrelaunchFollower.initial,
                        AffineBatchDecoder.initial, AffineBatchDecoder.collected] using hmap
                    exact List.map_eq_nil_iff.mp hmapNil
                  simp only [rNext, hnextPrefix]
                  rcases horigin with hpending | hforced
                  · have hdeclared : ReferenceInitializationRun.declaredActivation x b h f =
                        some a := by
                      rw [hdecl, hpending.1]
                      have hba : a = ReferenceInitializationRun.boundaryActivation b := by
                        apply Subtype.ext
                        exact haval
                      exact congrArg some hba.symm
                    have hnotForcedFailure : nextStopped.val.1.forcedFailure f = false := by
                      rw [hnextRun]
                      exact hpending.2
                    exact ⟨hcurrent, htests, htestsNext, a, hnextRun, hactNext,
                      hactivationRound, hinitialStopped,
                      Or.inl ⟨hpending.1, hnotForcedFailure,
                        hdeclared⟩⟩
                  · have hdeclared : ReferenceInitializationRun.declaredActivation x b h f = none := by
                      rw [hdecl, hforced.1]
                      rfl
                    have hforcedFailure : nextStopped.val.1.forcedFailure f = true := by
                      rw [hnextRun]
                      exact hforced.2.2
                    exact ⟨hcurrent, htests, htestsNext, a, hnextRun, hactNext,
                      hactivationRound, hinitialStopped,
                      Or.inr ⟨hforced.1, hforced.2.1, hforcedFailure,
                        hdeclared⟩⟩
  | inr _ => trivial

/-- At the final physical round, an inactive generated selector has an empty
strict-prefix census and its true run output is either still undeclared or is
the actual block-end activation at `T + 1`. The output boundary retains any
forced-failure bit; the follower initial state carries no fabricated failure. -/
theorem source_prelaunch_down_inactive_terminal_handoff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let rLast : Fin p.T := ⟨p.T - 1, by have := ConstructorDimensions.T_pos p; omega⟩
    match source_prelaunch_down_prefix rate rewards C_star C_h z i rLast with
    | .inl (.inr inactive) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let f := ActualReferenceInitializationBlock.refFollower i
        let b := inactive.val.1.val
        let h := inactive.val.1.property.1
        let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
          ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
            inactive.property.2.1⟩
        let candidate := ReferenceInitializationRun.candidate x b h ui
        source_prelaunch_down_current_test rate rewards C_star C_h z i rLast = none ∧
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rLast = [] ∧
          ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
            rate rewards C_star C_h z i = [] ∧
          ((ReferenceInitializationRun.output x).activation f = none ∧
              candidate.pending = false ∧
              ReferenceInitializationRun.crosses x b h = false ∧
              (ReferenceInitializationRun.output x).forcedFailure f = false ∧
              ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f =
                ReferencePrelaunchFollower.initial p rate.eta ∨
            ∃ a, (ReferenceInitializationRun.output x).activation f = some a ∧
              a.val = p.T + 1 ∧
              ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f =
                ReferencePrelaunchFollower.initial p rate.eta ∧
              ((candidate.pending = true ∧
                  (ReferenceInitializationRun.output x).forcedFailure f = false ∧
                  ReferenceInitializationRun.declaredActivation x b h f = some a) ∨
                (candidate.pending = false ∧
                  ReferenceInitializationRun.forced x b h f = true ∧
                  (ReferenceInitializationRun.output x).forcedFailure f = true ∧
                  ReferenceInitializationRun.declaredActivation x b h f = none)))
    | _ => True := by
  classical
  let rLast : Fin p.T := ⟨p.T - 1, by have := ConstructorDimensions.T_pos p; omega⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i rLast with
  | inl branch =>
      cases branch with
      | inl _ => simp only [rLast, hpref]
      | inr inactive =>
          simp only [rLast, hpref]
          let x := sourceReferenceInput rate rewards C_star C_h z
          let f := ActualReferenceInitializationBlock.refFollower i
          let s := roundBlockIndex p rLast
          let b := inactive.val.1.val
          let h := inactive.val.1.property.1
          let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
            ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
              inactive.property.2.1⟩
          let candidate := ReferenceInitializationRun.candidate x b h ui
          have hcross : b.crossing = none := inactive.val.1.property.2.1
          have hboundary : b = ReferenceInitializationRun.run x s.val :=
            inactive.val.1.property.2.2
          have hcrossRun : (ReferenceInitializationRun.run x s.val).crossing = none := by
            rw [← hboundary]
            exact hcross
          have hprogress := ReferenceInitializationRun.run_progress x s.val
            (Nat.le_of_lt s.isLt)
          have hcompleted : b.completed = s.val := by
            rcases hprogress with hcrossed | hcompleted
            · have hcrossedB : b.crossing.isSome = true := by
                simpa [hboundary] using hcrossed
              simp [hcross] at hcrossedB
            · rw [hboundary]
              exact hcompleted
          have hfinish : ReferenceInitializationRun.run x (s.val + 1) =
              ReferenceInitializationRun.finishBlock x b h := by
            rw [ReferenceInitializationRun.run_succ, hboundary.symm,
              ReferenceInitializationRun.advance_of_no_crossing x b hcross h]
          have hblockMem := (mem_calendarBlock_iff p s rLast).1
            (round_mem_quotient_block p rLast)
          have hblockUpper : rLast.val < (s.val + 1) * B_boot p :=
            lt_of_lt_of_le hblockMem.2 (Nat.min_le_right _ _)
          have hTupper : p.T ≤ (s.val + 1) * B_boot p := by
            dsimp [rLast] at hblockUpper
            omega
          have hTdiv : (p.T : ℝ) / (B_boot p : ℝ) ≤ ((s.val + 1 : ℕ) : ℝ) :=
            (div_le_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).2 (by exact_mod_cast hTupper)
          have hceilReal : (n_boot p : ℝ) < ((s.val + 1 : ℕ) : ℝ) + 1 :=
            lt_of_lt_of_le (n_boot_real_upper_bound p)
              (add_le_add_left hTdiv 1)
          have hceilNat : n_boot p < s.val + 2 := by exact_mod_cast hceilReal
          have hlastBlock : s.val + 1 = n_boot p := by omega
          have hrunOutput : ReferenceInitializationRun.output x =
              ReferenceInitializationRun.finishBlock x b h := by
            change ReferenceInitializationRun.run x (n_boot p) = _
            rw [← hlastBlock]
            exact hfinish
          have hfinishData := inactive_finishBlock_data
            rate rewards C_star C_h z i rLast
          simp only [hpref] at hfinishData
          rcases hfinishData with ⟨_, hdecl, hfinishCase⟩
          have hlastData := source_prelaunch_down_inactive_current_test
            rate rewards C_star C_h z i rLast
          simp only [hpref] at hlastData
          rcases hlastData with ⟨hcurrent, htests⟩
          have hordinaryOutput (hordinary :
              ReferenceInitializationRun.ordinary x
                (ReferenceInitializationRun.finishBlock x b h) f =
                  ReferencePrelaunchFollower.initial p rate.eta) :
              ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f =
                ReferencePrelaunchFollower.initial p rate.eta := by
            rw [hrunOutput]
            exact hordinary
          have htestsOutput : ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
              rate rewards C_star C_h z i = [] := by
            change ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
              x (ReferenceInitializationRun.output x) i = []
            rcases hfinishCase with hnoActivation | ⟨a, ha, hbirth, hstate, horigin⟩
            · have hactivation :
                  (ReferenceInitializationRun.output x).activation f = none := by
                rw [hrunOutput]
                exact hnoActivation.1
              have hforcedOutput :
                  (ReferenceInitializationRun.output x).forcedFailure f = false := by
                rw [hrunOutput]
                exact hnoActivation.2.2.2.1
              change (ReferenceInitializationRun.output x).activation
                  (ActualReferenceInitializationBlock.refFollower i) = none at hactivation
              change (ReferenceInitializationRun.output x).forcedFailure
                  (ActualReferenceInitializationBlock.refFollower i) = false at hforcedOutput
              simp only [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
                hforcedOutput, Bool.false_eq_true, ↓reduceIte, hactivation]
            · rcases horigin with hpending | hforced
              · have hactivation :
                    (ReferenceInitializationRun.output x).activation f = some a := by
                  rw [hrunOutput]
                  exact ha
                have hbirthT : a.val = p.T + 1 := by
                  rw [hcompleted] at hbirth
                  change a.val = ReferenceInitializationRun.elapsed p (s.val + 1) + 1 at hbirth
                  rw [hlastBlock, ReferenceInitializationRun.elapsed_all_blocks] at hbirth
                  exact hbirth
                have houtputCompleted :
                    (ReferenceInitializationRun.output x).completed = n_boot p := by
                  rw [hrunOutput]
                  change b.completed + 1 = n_boot p
                  rw [hcompleted, hlastBlock]
                have hbirthOutput : a.val =
                    ReferenceInitializationRun.elapsed p
                      (ReferenceInitializationRun.output x).completed + 1 := by
                  rw [houtputCompleted, ReferenceInitializationRun.elapsed_all_blocks]
                  exact hbirthT
                exact (ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_cases
                  rate rewards C_star C_h z i).2 a hactivation hbirthOutput |>.2
              · have hforcedOutput :
                    (ReferenceInitializationRun.output x).forcedFailure f = true := by
                  rw [hrunOutput]
                  exact hforced.2.2
                exact (ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_cases
                  rate rewards C_star C_h z i).1 hforcedOutput |>.2.1
          refine ⟨hcurrent, htests, htestsOutput, ?_⟩
          rcases hfinishCase with hnoActivation | ⟨a, ha, hbirth, hstate, horigin⟩
          · have hactivation :
                (ReferenceInitializationRun.output x).activation f = none := by
              rw [hrunOutput]
              exact hnoActivation.1
            have hforcedOutput :
                (ReferenceInitializationRun.output x).forcedFailure f = false := by
              rw [hrunOutput]
              exact hnoActivation.2.2.2.1
            exact Or.inl ⟨hactivation, hnoActivation.2.1,
              hnoActivation.2.2.1, hforcedOutput,
              hordinaryOutput hnoActivation.2.2.2.2⟩
          · have hactivation :
                (ReferenceInitializationRun.output x).activation f = some a := by
              rw [hrunOutput]
              exact ha
            have hbirthT : a.val = p.T + 1 := by
              rw [hcompleted] at hbirth
              change a.val = ReferenceInitializationRun.elapsed p (s.val + 1) + 1 at hbirth
              rw [hlastBlock, ReferenceInitializationRun.elapsed_all_blocks] at hbirth
              exact hbirth
            have hordinary : ReferenceInitializationRun.ordinary x
                (ReferenceInitializationRun.output x) f =
                  ReferencePrelaunchFollower.initial p rate.eta :=
              hordinaryOutput hstate
            rcases horigin with hpending | hforced
            · have hforcedOutput :
                  (ReferenceInitializationRun.output x).forcedFailure f = false := by
                rw [hrunOutput]
                exact hpending.2
              have hba : a = ReferenceInitializationRun.boundaryActivation b := by
                apply Subtype.ext
                exact hbirth
              have hdeclared :
                  ReferenceInitializationRun.declaredActivation x b h f = some a := by
                rw [hdecl, hpending.1]
                exact congrArg some hba.symm
              exact Or.inr ⟨a, hactivation, hbirthT, hordinary,
                Or.inl ⟨hpending.1, hforcedOutput, hdeclared⟩⟩
            · have hforcedOutput :
                  (ReferenceInitializationRun.output x).forcedFailure f = true := by
                rw [hrunOutput]
                exact hforced.2.2
              have hdeclared :
                  ReferenceInitializationRun.declaredActivation x b h f = none := by
                rw [hdecl, hforced.1]
                rfl
              exact Or.inr ⟨a, hactivation, hbirthT, hordinary,
                Or.inr ⟨hforced.1, hforced.2.1, hforcedOutput, hdeclared⟩⟩
  | inr _ => simp only [rLast, hpref]

/-- A stopped selector is the actual output already. Every later source prefix
keeps its same stopped boundary, ordinary state, activation and exact test
census. The terminal census is read from the actual output projection. -/
theorem source_prelaunch_down_stopped_to_terminal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inr stopped =>
        stopped.val = source_prelaunch_down_terminal rate rewards C_star C_h z i ∧
          ((ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).crossing.isSome = true ∨
            n_boot p ≤ (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed) ∧
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r =
            ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
              rate rewards C_star C_h z i ∧
          source_prelaunch_down_current_test rate rewards C_star C_h z i r = none ∧
          ∀ t : Fin p.T, r.val ≤ t.val →
            ∃ stoppedNext,
              source_prelaunch_down_prefix rate rewards C_star C_h z i t =
                .inr stoppedNext ∧
              stoppedNext.val = stopped.val ∧
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i t =
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ∧
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i t =
                ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
                  rate rewards C_star C_h z i ∧
              source_prelaunch_down_current_test rate rewards C_star C_h z i t = none
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch => cases branch <;> trivial
  | inr stopped =>
      let x := sourceReferenceInput rate rewards C_star C_h z
      let f := ActualReferenceInitializationBlock.refFollower i
      let s := roundBlockIndex p r
      let b := stopped.val.1
      have hcross : b.crossing.isSome = true := by
        cases hc : b.crossing with
        | none => exact False.elim (stopped.property.1 hc)
        | some _ => rfl
      have hboundary : b = ReferenceInitializationRun.run x s.val :=
        stopped.property.2.1
      have hcrossRun : (ReferenceInitializationRun.run x s.val).crossing.isSome = true := by
        rw [← hboundary]
        exact hcross
      have hindex (t : Fin p.T) (hrt : r.val ≤ t.val) :
          s.val ≤ (roundBlockIndex p t).val := by
        dsimp only [s, roundBlockIndex]
        exact Nat.div_le_div_right hrt
      have hrunTerminal : ReferenceInitializationRun.run x (n_boot p) =
          ReferenceInitializationRun.run x s.val := by
        have hrun := ReferenceInitializationRun.run_stops_at_crossing x s.val
          (n_boot p - s.val) hcrossRun
        rw [Nat.add_sub_of_le s.isLt.le] at hrun
        exact hrun
      have hbOutput : b = ReferenceInitializationRun.output x := by
        calc
          b = ReferenceInitializationRun.run x s.val := hboundary
          _ = ReferenceInitializationRun.run x (n_boot p) := hrunTerminal.symm
          _ = ReferenceInitializationRun.output x := rfl
      have hstateOutput : stopped.val.2 =
          (source_prelaunch_down_terminal rate rewards C_star C_h z i).2 := by
        change stopped.val.2 = ReferenceInitializationRun.ordinary x
          (ReferenceInitializationRun.output x) f
        rw [← hbOutput]
        exact stopped.property.2.2
      have hpairOutput : stopped.val =
          source_prelaunch_down_terminal rate rewards C_star C_h z i := by
        apply Prod.ext
        · exact hbOutput
        · exact hstateOutput
      have hterminalBoundary := source_prelaunch_down_terminal_boundary
        rate rewards C_star C_h z i
      have houtputProgress :
          (ReferenceInitializationRun.output x).crossing.isSome = true ∨
            n_boot p ≤ (ReferenceInitializationRun.output x).completed := by
        simpa only [hterminalBoundary.1] using hterminalBoundary.2.2.2
      have htestsOutput :
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r =
            ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
              rate rewards C_star C_h z i := by
        simp only [source_prelaunch_down_prefix_tests, hpref]
        change ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
            x b i =
          ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
            x (ReferenceInitializationRun.output x) i
        rw [hbOutput]
      have hcurrentNone :
          source_prelaunch_down_current_test rate rewards C_star C_h z i r = none := by
        simp [source_prelaunch_down_current_test, hpref]
      refine ⟨hpairOutput, houtputProgress, htestsOutput, hcurrentNone, ?_⟩
      intro t hrt
      let sNext := roundBlockIndex p t
      have hrunNext : ReferenceInitializationRun.run x sNext.val =
          ReferenceInitializationRun.run x s.val := by
        have hrun := ReferenceInitializationRun.run_stops_at_crossing x s.val
          (sNext.val - s.val) hcrossRun
        rw [Nat.add_sub_of_le (hindex t hrt)] at hrun
        exact hrun
      cases hnext : source_prelaunch_down_prefix rate rewards C_star C_h z i t with
      | inl branch =>
          cases branch with
          | inl active =>
              have hboundaryNext : active.val.1.val = b := by
                calc
                  active.val.1.val = ReferenceInitializationRun.run x sNext.val :=
                    active.val.1.property.2.2
                  _ = ReferenceInitializationRun.run x s.val := hrunNext
                  _ = b := hboundary.symm
              have hnone : b.crossing = none := by
                simpa [hboundaryNext] using active.val.1.property.2.1
              exact False.elim (stopped.property.1 hnone)
          | inr inactive =>
              have hboundaryNext : inactive.val.1.val = b := by
                calc
                  inactive.val.1.val = ReferenceInitializationRun.run x sNext.val :=
                    inactive.val.1.property.2.2
                  _ = ReferenceInitializationRun.run x s.val := hrunNext
                  _ = b := hboundary.symm
              have hnone : b.crossing = none := by
                simpa [hboundaryNext] using inactive.val.1.property.2.1
              exact False.elim (stopped.property.1 hnone)
      | inr stoppedNext =>
          have hboundaryNext : stoppedNext.val.1 = b := by
            calc
              stoppedNext.val.1 = ReferenceInitializationRun.run x sNext.val :=
                stoppedNext.property.2.1
              _ = ReferenceInitializationRun.run x s.val := hrunNext
              _ = b := hboundary.symm
          have hstateNext : stoppedNext.val.2 = stopped.val.2 := by
            calc
              stoppedNext.val.2 = ReferenceInitializationRun.ordinary x
                  stoppedNext.val.1 f := stoppedNext.property.2.2
              _ = ReferenceInitializationRun.ordinary x b f :=
                congrArg (ReferenceInitializationRun.ordinary x · f) hboundaryNext
              _ = stopped.val.2 := stopped.property.2.2.symm
          have hpairNext : stoppedNext.val = stopped.val :=
            Prod.ext hboundaryNext hstateNext
          have htestsNext :
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i t =
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r := by
            simp only [source_prelaunch_down_prefix_tests, hnext, hpref]
            change ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
                x stoppedNext.val.1 i =
              ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i
            rw [hboundaryNext]
          have htestsTerminal :
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i t =
                ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
                  rate rewards C_star C_h z i := by
            simp only [source_prelaunch_down_prefix_tests, hnext]
            change ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
                x stoppedNext.val.1 i =
              ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
                x (ReferenceInitializationRun.output x) i
            rw [hboundaryNext, hbOutput]
          have hcurrentNext :
              source_prelaunch_down_current_test rate rewards C_star C_h z i t = none := by
            simp [source_prelaunch_down_current_test, hnext]
          exact ⟨stoppedNext, rfl, hpairNext, htestsNext, htestsTerminal,
            hcurrentNext⟩

end Bandits.Support.ReferenceGeneratedPrelaunchDownInactiveBridge

end
