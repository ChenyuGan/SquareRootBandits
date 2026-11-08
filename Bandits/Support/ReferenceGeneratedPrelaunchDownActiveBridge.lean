/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Active prelaunch DOWN transport through block ends and the horizon

Sources: `07_public_setup.tex:60-114,127-142`,
`05_binary_transport.tex:20-42`, and `appendix_a_local_protocol.tex:111-138`.

Only the active incoming selector is treated here. All histories, activations,
ordinary states, and tests are projections of the existing generated run on the
same original source and whole rewards. The prior forced flag is derived from
that run; suppressed DOWN failures remain in the ordinary state. These are
internal deterministic transport results, without a historical-birth,
probability, or manuscript closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownActiveBridge

open ConstructorDimensions BootstrapDimensions ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The only calendar inputs are a real round and its strict successor typing.
Different quotient blocks imply that the current round is the real block end. -/
private theorem calendar_next_block (r : Fin p.T) (hn : r.val + 1 < p.T)
    (hdiff : roundBlockIndex p (⟨r.val + 1, hn⟩ : Fin p.T) ≠ roundBlockIndex p r) :
    ReferenceInitializationRun.elapsed p ((roundBlockIndex p r).val + 1) = r.val + 1 ∧
      (roundBlockIndex p (⟨r.val + 1, hn⟩ : Fin p.T)).val =
        (roundBlockIndex p r).val + 1 := by
  let s := roundBlockIndex p r
  let rn : Fin p.T := ⟨r.val + 1, hn⟩
  have hr := (mem_calendarBlock_iff p s r).mp (round_mem_quotient_block p r)
  have hend : ReferenceInitializationRun.elapsed p (s.val + 1) = r.val + 1 := by
    by_contra he
    have hmem : rn ∈ calendarBlock p s := by
      apply (mem_calendarBlock_iff p s rn).2
      change s.val * B_boot p ≤ r.val + 1 ∧
        r.val + 1 < ReferenceInitializationRun.elapsed p (s.val + 1)
      have hup : r.val < ReferenceInitializationRun.elapsed p (s.val + 1) := hr.2
      omega
    have hs := (mem_calendarBlock_iff_quotient p s rn).mp hmem
    apply hdiff
    apply Fin.ext
    exact hs.symm
  have hmul : (s.val + 1) * B_boot p = r.val + 1 := by
    change min p.T ((s.val + 1) * B_boot p) = r.val + 1 at hend
    omega
  refine ⟨hend, ?_⟩
  change (r.val + 1) / B_boot p = s.val + 1
  rw [← hmul, Nat.mul_div_cancel _ (B_boot_pos p)]

/-- At the last physical round the quotient block is the last bootstrap block.
No round indexed by `T` is constructed. -/
private theorem calendar_terminal_block (r : Fin p.T) (hlast : r.val + 1 = p.T) :
    ReferenceInitializationRun.elapsed p ((roundBlockIndex p r).val + 1) = p.T ∧
      (roundBlockIndex p r).val + 1 = n_boot p := by
  let s := roundBlockIndex p r
  have hr := (mem_calendarBlock_iff p s r).mp (round_mem_quotient_block p r)
  have hend : ReferenceInitializationRun.elapsed p (s.val + 1) = p.T := by
    change min p.T ((s.val + 1) * B_boot p) = p.T
    omega
  refine ⟨hend, ?_⟩
  have hs := s.isLt
  by_contra he
  have hmore : s.val + 1 < n_boot p := by omega
  obtain ⟨t, ht⟩ := calendarBlock_nonempty p ⟨s.val + 1, hmore⟩
  have ht' := (mem_calendarBlock_iff p ⟨s.val + 1, hmore⟩ t).mp ht
  change min p.T ((s.val + 1) * B_boot p) = p.T at hend
  have hT := t.isLt
  dsimp only at ht'
  omega

/-- Pure chronological enumeration: split the last actual observation from
an arbitrary finite history. No equality of histories is an input. -/
private theorem tests_succ (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : Activation p) {n : ℕ}
    (history : LocalHistory p (n + 1)) (hn : n + 1 ≤ p.T) :
    (List.ofFn (fun u : Fin (n + 1) => u)).filterMap
        (fun u => prelaunchTest i row a (calendar hn u) (history u)) =
      (List.ofFn (fun u : Fin n => u)).filterMap
          (fun u => prelaunchTest i row a
            (calendar (Nat.le_trans (Nat.le_succ n) hn) u) (history u.castSucc)) ++
        (prelaunchTest i row a ⟨n, by omega⟩ (history (Fin.last n))).toList := by
  rw [List.ofFn_succ_last, List.filterMap_append]
  have hmap : List.ofFn (fun u : Fin n => u.castSucc) =
      (List.ofFn (fun u : Fin n => u)).map Fin.castSucc := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.filterMap_map]
  have hprefix :
      (List.ofFn (fun u : Fin n => u)).filterMap
          (fun u => prelaunchTest i row a (calendar hn u.castSucc) (history u.castSucc)) =
        (List.ofFn (fun u : Fin n => u)).filterMap
          (fun u => prelaunchTest i row a
            (calendar (Nat.le_trans (Nat.le_succ n) hn) u) (history u.castSucc)) := by
    apply List.filterMap_congr
    intro u _
    rfl
  simp only [Function.comp_def]
  rw [hprefix]
  have hcal : calendar hn (Fin.last n) = (⟨n, by omega⟩ : Fin p.T) := Fin.ext rfl
  rw [List.filterMap_cons, List.filterMap_nil, hcal]
  cases prelaunchTest i row a ⟨n, by omega⟩ (history (Fin.last n)) <;> rfl

/-- Changing only the length proof and its associated finite index leaves the
literal test census unchanged. -/
private theorem tests_cast (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : Activation p) {n m : ℕ}
    (history : LocalHistory p n) (hn : n ≤ p.T) (hm : m ≤ p.T) (e : n = m) :
    (List.ofFn (fun u : Fin m => u)).filterMap
        (fun u => prelaunchTest i row a (calendar hm u) (history (Fin.cast e.symm u))) =
      (List.ofFn (fun u : Fin n => u)).filterMap
        (fun u => prelaunchTest i row a (calendar hn u) (history u)) := by
  subst m
  rfl

/-- Literal boundary census on an active, unforced branch. Both selector
inputs are explicit; consumers below produce them from the actual run. -/
private theorem boundary_tests_of_active (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1)) (a : Activation p)
    (ha : b.activation (ActualReferenceInitializationBlock.refFollower i) = some a)
    (hf : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false) :
    boundaryPrelaunchDownTests x b i =
      (List.ofFn (fun u : Fin (ReferenceInitializationRun.elapsed p b.completed) => u)).filterMap
        (fun u => prelaunchTest i x.row a
          (calendar (ReferenceInitializationRun.elapsed_le_T p b.completed) u)
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) u)) := by
  unfold boundaryPrelaunchDownTests
  dsimp only
  rw [hf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ha]

/-- Literal ordinary state on an active, unforced boundary. The two
selectors are explicit conditional inputs, produced by every consumer. -/
private theorem ordinary_of_active (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1)) (a : Activation p)
    (ha : b.activation (ActualReferenceInitializationBlock.refFollower i) = some a)
    (hf : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false) :
    ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i) =
      ReferencePrelaunchFollower.replay x.eta i x.row a
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p b.completed) := by
  have hidx : BootstrapPhysicalInput.sourceFollowerIndex p
      (ActualReferenceInitializationBlock.refFollower i) = i := Fin.ext rfl
  unfold ReferenceInitializationRun.ordinary
  rw [hf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ha]
  change ReferencePrelaunchFollower.replay x.eta
      (BootstrapPhysicalInput.sourceFollowerIndex p (ActualReferenceInitializationBlock.refFollower i))
      x.row a _ _ = _
  rw [hidx]

/-- Every conditional input here is explicit: an existing generated active
projection and the assertion that its actual endpoint follows the current
round. The public consumers derive that endpoint from quotient membership.
No history, continuation equality, or no-force premise is supplied. -/
private theorem active_finish_block (x : ReferenceInitializationRun.Input p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (v : ActiveProjection p i r.val x.row (Nat.le_of_lt r.isLt) x (roundBlockIndex p r))
    (hend : ReferenceInitializationRun.elapsed p (v.val.1.val.completed + 1) = r.val + 1) :
    let b := v.val.1.val
    let a := v.val.2.1
    let own := ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical x b v.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    let f := ActualReferenceInitializationBlock.refFollower i
    let next := ReferenceInitializationRun.finishBlock x b v.val.1.property.1
    b.completed = (roundBlockIndex p r).val ∧
      b.forcedFailure f = false ∧
      ReferenceInitializationRun.run x ((roundBlockIndex p r).val + 1) = next ∧
      next.activation f = some a ∧ next.forcedFailure f = false ∧
      ReferenceInitializationRun.ordinary x next f =
        ReferencePrelaunchFollower.step i x.row a r own v.val.2.2.2 ∧
      boundaryPrelaunchDownTests x next i =
        (List.ofFn (fun u : Fin r.val => u)).filterMap
            (fun u => prelaunchTest i x.row a (calendar (Nat.le_of_lt r.isLt) u)
              (v.val.2.2.1 u)) ++
          (prelaunchTest i x.row a r own).toList := by
  let b := v.val.1.val
  let a := v.val.2.1
  let f := ActualReferenceInitializationBlock.refFollower i
  let j := PublicDiscreteDraws.followerPlayer p.two_le_m f
  let h := v.val.1.property.1
  let full := ReferenceInitializationRun.extendedHistory x b h j
  let own := ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h) j r
  let next := ReferenceInitializationRun.finishBlock x b h
  rcases v.property with ⟨hbefore, ha, hstate, hhistory⟩
  have hgen : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
    v.val.1.property.2.2
  have hc : b.crossing = none := v.val.1.property.2.1
  have hcompleted : b.completed = (roundBlockIndex p r).val := by
    have hp := ReferenceInitializationRun.run_progress x (roundBlockIndex p r).val
      (roundBlockIndex p r).isLt.le
    rw [← hgen] at hp
    exact hp.resolve_left (by rw [hc]; exact Bool.false_ne_true)
  have hf : b.forcedFailure f = false := by
    rw [hgen]
    exact ReferenceInitializationRun.run_no_forced_before_launch x _
      (by rw [← hgen]; exact hc) f
  have hrun : ReferenceInitializationRun.run x ((roundBlockIndex p r).val + 1) = next := by
    rw [ReferenceInitializationRun.run_succ, ← hgen,
      ReferenceInitializationRun.advance_of_no_crossing x b hc h]
  have hpres := ReferenceSuppressedDownCoverage.run_active_preserved x
    (Nat.le_succ (roundBlockIndex p r).val) f a
    (by rw [← hgen]; exact ha) (by rw [← hgen]; exact hf)
  rw [hrun] at hpres
  have htime : ReferenceInitializationRun.elapsed p b.completed ≤ r.val := by
    rw [hcompleted]
    exact GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
      (s := roundBlockIndex p r) (t := r) (round_mem_quotient_block p r)
  let finalHistory : LocalHistory p (r.val + 1) := fun u => full (Fin.cast hend.symm u)
  have hshort : (fun u : Fin r.val => finalHistory u.castSucc) = v.val.2.2.1 := by
    funext u
    rw [hhistory]
    unfold ReferencePrelaunchLifecycleReplay.prefixHistory
    change full (Fin.cast hend.symm u.castSucc) = full (Fin.castLE hbefore u)
    congr 1
  have hlast : finalHistory (Fin.last r.val) = own := by
    change ReferenceInitializationRun.extendedHistory x b h j
      (Fin.cast hend.symm (Fin.last r.val)) = own
    have hnot : ¬ (Fin.cast hend.symm (Fin.last r.val)).val <
        ReferenceInitializationRun.elapsed p b.completed := by
      change ¬ r.val < ReferenceInitializationRun.elapsed p b.completed
      omega
    rw [ReferenceInitializationRun.extendedHistory, dite_eq_right hnot]
    rfl
  have hcast := ReferenceInitializationRun.replay_cast x.eta i x.row a full
    (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
    (Nat.succ_le_of_lt r.isLt) hend
  have hsucc := ActualReferenceInitializationBlock.replay_succ x.eta i x.row a
    finalHistory (Nat.succ_le_of_lt r.isLt)
  rw [hshort, hlast, ← hstate] at hsucc
  have hstep : ReferencePrelaunchFollower.replay x.eta i x.row a full
      (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) =
        ReferencePrelaunchFollower.step i x.row a r own v.val.2.2.2 :=
    hcast.symm.trans hsucc
  refine ⟨hcompleted, hf, hrun, hpres.1, hpres.2, ?_, ?_⟩
  · have hidx : BootstrapPhysicalInput.sourceFollowerIndex p f = i := Fin.ext rfl
    have hcontinued := ReferenceInitializationRun.replayInput_continued x b h f a ha
    rw [hidx] at hcontinued
    have hh := ReferenceInitializationRun.ordinary_finishBlock_of_activated x b h f a ha hf
    rw [← hcontinued] at hh
    exact hh.trans hstep
  · rw [boundary_tests_of_active x next i a hpres.1 hpres.2]
    change (List.ofFn (fun u : Fin (ReferenceInitializationRun.elapsed p (b.completed + 1)) => u)).filterMap
        (fun u => prelaunchTest i x.row a
          (calendar (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) u) (full u)) = _
    rw [← tests_cast i x.row a full
      (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
      (Nat.succ_le_of_lt r.isLt) hend]
    change (List.ofFn (fun u : Fin (r.val + 1) => u)).filterMap
      (fun u => prelaunchTest i x.row a (calendar (Nat.succ_le_of_lt r.isLt) u)
        (finalHistory u)) = _
    rw [tests_succ i x.row a finalHistory (Nat.succ_le_of_lt r.isLt)]
    simp only [congrFun hshort, hlast]
    rfl

/-- At a real calendar boundary the active strict prefix is exactly the
boundary's own history. The endpoint equality is a conditional helper input;
the public consumer constructs it from the finished predecessor block. -/
private theorem active_at_boundary (x : ReferenceInitializationRun.Input p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (v : ActiveProjection p i r.val x.row (Nat.le_of_lt r.isLt) x (roundBlockIndex p r))
    (hend : ReferenceInitializationRun.elapsed p v.val.1.val.completed = r.val) :
    v.val.2.2.2 = ReferenceInitializationRun.ordinary x v.val.1.val
        (ActualReferenceInitializationBlock.refFollower i) ∧
      (List.ofFn (fun u : Fin r.val => u)).filterMap
          (fun u => prelaunchTest i x.row v.val.2.1 (calendar (Nat.le_of_lt r.isLt) u)
            (v.val.2.2.1 u)) =
        boundaryPrelaunchDownTests x v.val.1.val i := by
  let b := v.val.1.val
  let a := v.val.2.1
  let f := ActualReferenceInitializationBlock.refFollower i
  let j := PublicDiscreteDraws.followerPlayer p.two_le_m f
  let hist := b.history j
  rcases v.property with ⟨hbefore, ha, hstate, hhistory⟩
  have hgen : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
    v.val.1.property.2.2
  have ha0 : b.activation f = some a := ha
  have hf : b.forcedFailure f = false := by
    rw [hgen]
    exact ReferenceInitializationRun.run_no_forced_before_launch x _
      (by rw [← hgen]; exact v.val.1.property.2.1) f
  have hhist : (fun u : Fin r.val => hist (Fin.cast hend.symm u)) = v.val.2.2.1 := by
    funext u
    rw [hhistory]
    unfold ReferencePrelaunchLifecycleReplay.prefixHistory
    change b.history j (Fin.cast hend.symm u) =
      ReferenceInitializationRun.extendedHistory x b v.val.1.property.1 j (Fin.castLE hbefore u)
    have hembed : Fin.castLE hbefore u =
        (⟨(Fin.cast hend.symm u).val,
          Nat.lt_of_lt_of_le (Fin.cast hend.symm u).isLt
            (ReferenceInitializationRun.elapsed_mono p (Nat.le_succ b.completed))⟩ :
          Fin (ReferenceInitializationRun.elapsed p (b.completed + 1))) := Fin.ext rfl
    rw [hembed, ReferenceInitializationRun.extendedHistory_prefix]
  have hcast := ReferenceInitializationRun.replay_cast x.eta i x.row a hist
    (ReferenceInitializationRun.elapsed_le_T p b.completed) (Nat.le_of_lt r.isLt) hend
  have hidx : BootstrapPhysicalInput.sourceFollowerIndex p f = i := Fin.ext rfl
  have hord : ReferenceInitializationRun.ordinary x b f =
      ReferencePrelaunchFollower.replay x.eta i x.row a hist
        (ReferenceInitializationRun.elapsed_le_T p b.completed) := by
    simp only [ReferenceInitializationRun.ordinary, hf, Bool.false_eq_true, ↓reduceIte,
      atLaunch, hidx]
    rw [ha0]
  constructor
  · rw [hhist] at hcast
    exact hstate.trans (hcast.trans hord.symm)
  · rw [boundary_tests_of_active x b i a ha hf]
    have ht := tests_cast i x.row a hist
      (ReferenceInitializationRun.elapsed_le_T p b.completed) (Nat.le_of_lt r.isLt) hend
    simpa only [congrFun hhist] using ht

/-- Active transport across a genuine block end before `T`. The displayed
block-change condition is only this internal result's domain restriction;
`source_prelaunch_down_active_successor` below covers every strict successor.
The full boundary equation retains the crossing, declaration and failure data.
Sources: 07:106-114,129-140 and 05:37-42. -/
theorem source_prelaunch_down_active_block_end
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rn : Fin p.T := ⟨r.val + 1, hnext⟩
    roundBlockIndex p rn ≠ roundBlockIndex p r →
      match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inl (.inl active) =>
          let x := sourceReferenceInput rate rewards C_star C_h z
          let b := active.val.1.val
          let a := active.val.2.1
          let f := ActualReferenceInitializationBlock.refFollower i
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x b active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
          let next := ReferenceInitializationRun.finishBlock x b active.val.1.property.1
          b.completed = (roundBlockIndex p r).val ∧
            b.forcedFailure f = false ∧
            ReferenceInitializationRun.elapsed p (b.completed + 1) = r.val + 1 ∧
            (roundBlockIndex p rn).val = (roundBlockIndex p r).val + 1 ∧
            ReferenceInitializationRun.run x (roundBlockIndex p rn).val = next ∧
            next.activation f = some a ∧ next.forcedFailure f = false ∧
            next.crossing = (if ReferenceInitializationRun.crosses x b active.val.1.property.1
              then some (ReferenceInitializationRun.nextBlock b active.val.1.property.1) else none) ∧
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn =
              source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
                (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList ∧
            match source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
            | .inl (.inl nextActive) =>
                ReferenceInitializationRun.crosses x b active.val.1.property.1 = false ∧
                  nextActive.val.1.val = next ∧ nextActive.val.2.1 = a ∧
                  nextActive.val.2.2.2 =
                    ReferencePrelaunchFollower.step i x.row a r own active.val.2.2.2
            | .inl (.inr _) => False
            | .inr nextStopped =>
                ReferenceInitializationRun.crosses x b active.val.1.property.1 = true ∧
                  nextStopped.val.1 = next ∧ nextStopped.val.2 =
                    ReferencePrelaunchFollower.step i x.row a r own active.val.2.2.2
      | _ => True := by
  classical
  dsimp only
  intro hdiff
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  let x := sourceReferenceInput rate rewards C_star C_h z
  have hcal := calendar_next_block r hnext hdiff
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          let b := active.val.1.val
          let a := active.val.2.1
          let f := ActualReferenceInitializationBlock.refFollower i
          let next := ReferenceInitializationRun.finishBlock x b active.val.1.property.1
          have hgen : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
            active.val.1.property.2.2
          have hcompleted : b.completed = (roundBlockIndex p r).val := by
            have hprogress := ReferenceInitializationRun.run_progress x
              (roundBlockIndex p r).val (roundBlockIndex p r).isLt.le
            rw [← hgen] at hprogress
            exact hprogress.resolve_left
              (by rw [active.val.1.property.2.1]; exact Bool.false_ne_true)
          have hE : ReferenceInitializationRun.elapsed p (b.completed + 1) = r.val + 1 := by
            rw [hcompleted]
            exact hcal.1
          obtain ⟨_, hf, hrun, ha, hff, hstate, htests⟩ := active_finish_block x i r active hE
          have hrunNext : ReferenceInitializationRun.run x (roundBlockIndex p rn).val = next := by
            rw [hcal.2]
            exact hrun
          refine ⟨hcompleted, hf, hE, hcal.2, hrunNext, ha, hff, rfl, ?_, ?_⟩
          · cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
            | inl nb =>
                cases nb with
                | inl na =>
                    have hb : na.val.1.val = next := na.val.1.property.2.2.trans hrunNext
                    have hstart : ReferenceInitializationRun.elapsed p na.val.1.val.completed = rn.val := by
                      rw [hb]
                      exact hE
                    have hid := active_at_boundary x i rn na hstart
                    have hact : na.val.2.1 = a := by
                      have hh := na.property.choose_spec.1
                      rw [hb, ha] at hh
                      exact (Option.some.inj hh).symm
                    have ht := hid.2
                    rw [hact, hb] at ht
                    have hw := ht.trans htests
                    dsimp only [rn] at hnp
                    simpa only [source_prelaunch_down_prefix_tests, hp, hnp, hact,
                      source_prelaunch_down_current_test] using hw
                | inr ni =>
                    have hb : ni.val.1.val = next := ni.val.1.property.2.2.trans hrunNext
                    have hh := ni.property.choose_spec.1
                    rw [hb, ha] at hh
                    cases hh
            | inr ns =>
                have hb : ns.val.1 = next := ns.property.2.1.trans hrunNext
                dsimp only [rn] at hnp
                simpa only [source_prelaunch_down_prefix_tests, hp, hnp,
                  source_prelaunch_down_current_test, hb] using htests
          · cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
            | inl nb =>
                cases nb with
                | inl na =>
                    have hb : na.val.1.val = next := na.val.1.property.2.2.trans hrunNext
                    have hstart : ReferenceInitializationRun.elapsed p na.val.1.val.completed = rn.val := by
                      rw [hb]
                      exact hE
                    have hid := active_at_boundary x i rn na hstart
                    have hact : na.val.2.1 = a := by
                      have hh := na.property.choose_spec.1
                      rw [hb, ha] at hh
                      exact (Option.some.inj hh).symm
                    have hnone : next.crossing = none := by
                      rw [← hb]
                      exact na.val.1.property.2.1
                    have hcross : ReferenceInitializationRun.crosses x b active.val.1.property.1 = false := by
                      change (if ReferenceInitializationRun.crosses x b active.val.1.property.1
                        then some (ReferenceInitializationRun.nextBlock b active.val.1.property.1) else none) = none at hnone
                      cases hx : ReferenceInitializationRun.crosses x b active.val.1.property.1 with
                      | false => rfl
                      | true => simp only [hx, ↓reduceIte, reduceCtorEq] at hnone
                    refine ⟨hcross, hb, hact, ?_⟩
                    exact hid.1.trans (by rw [hb]; exact hstate)
                | inr ni =>
                    have hb : ni.val.1.val = next := ni.val.1.property.2.2.trans hrunNext
                    have hh := ni.property.choose_spec.1
                    rw [hb, ha] at hh
                    cases hh
            | inr ns =>
                have hb : ns.val.1 = next := ns.property.2.1.trans hrunNext
                have hnon : next.crossing ≠ none := by
                  rw [← hb]
                  exact ns.property.1
                have hcross : ReferenceInitializationRun.crosses x b active.val.1.property.1 = true := by
                  cases hx : ReferenceInitializationRun.crosses x b active.val.1.property.1 with
                  | false =>
                      apply False.elim
                      apply hnon
                      change (if ReferenceInitializationRun.crosses x b active.val.1.property.1
                        then some (ReferenceInitializationRun.nextBlock b active.val.1.property.1) else none) = none
                      simp only [hx, Bool.false_eq_true, ↓reduceIte]
                  | true => rfl
                refine ⟨hcross, hb, ?_⟩
                exact ns.property.2.2.trans (by rw [hb]; exact hstate)
      | inr _ => trivial
  | inr _ => trivial

/-- Every active strict successor has the actual stepped state and appends
exactly the current optional test. The calendar disjunction identifies whether
the real boundary stays fixed or advances by `finishBlock`. The successor tag
retains its actual crossing selector and the same activation. There is no
same-block, no-force, successful-solver, or supplied-continuation premise. -/
theorem source_prelaunch_down_active_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rn : Fin p.T := ⟨r.val + 1, hnext⟩
    let x := sourceReferenceInput rate rewards C_star C_h z
    let bn := ReferenceInitializationRun.run x (roundBlockIndex p rn).val
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let b := active.val.1.val
        let a := active.val.2.1
        let f := ActualReferenceInitializationBlock.refFollower i
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
        ((roundBlockIndex p rn = roundBlockIndex p r ∧ bn = b) ∨
          ((roundBlockIndex p rn).val = (roundBlockIndex p r).val + 1 ∧
            ReferenceInitializationRun.elapsed p (b.completed + 1) = r.val + 1 ∧
            bn = ReferenceInitializationRun.finishBlock x b active.val.1.property.1)) ∧
          bn.activation f = some a ∧ bn.forcedFailure f = false ∧
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn =
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
              (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList ∧
          match source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
          | .inl (.inl nextActive) =>
              bn.crossing = none ∧ nextActive.val.1.val = bn ∧ nextActive.val.2.1 = a ∧
                nextActive.val.2.2.2 =
                  ReferencePrelaunchFollower.step i x.row a r own active.val.2.2.2
          | .inl (.inr _) => False
          | .inr nextStopped =>
              bn.crossing ≠ none ∧ nextStopped.val.1 = bn ∧
                nextStopped.val.2 =
                  ReferencePrelaunchFollower.step i x.row a r own active.val.2.2.2
    | _ => True := by
  classical
  dsimp only
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  let x := sourceReferenceInput rate rewards C_star C_h z
  let bn := ReferenceInitializationRun.run x (roundBlockIndex p rn).val
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          let b := active.val.1.val
          let a := active.val.2.1
          let f := ActualReferenceInitializationBlock.refFollower i
          have hgen : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
            active.val.1.property.2.2
          have ha : b.activation f = some a := active.property.choose_spec.1
          by_cases hsame : roundBlockIndex p rn = roundBlockIndex p r
          · have hb : bn = b := by
              change ReferenceInitializationRun.run x (roundBlockIndex p rn).val = b
              rw [hsame, ← hgen]
            have hf : b.forcedFailure f = false := by
              rw [hgen]
              exact ReferenceInitializationRun.run_no_forced_before_launch x _
                (by rw [← hgen]; exact active.val.1.property.2.1) f
            have ht := ReferenceGeneratedPrelaunchDownPrefixTransport.source_prelaunch_down_same_block_active_transport
              rate rewards C_star C_h z i r hnext hsame
            rw [hp] at ht
            refine ⟨Or.inl ⟨hsame, hb⟩, ?_, ?_, ?_, ?_⟩
            · exact (congrArg (fun c => c.activation f) hb).trans ha
            · exact (congrArg (fun c => c.forcedFailure f) hb).trans hf
            · cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
              | inl nb =>
                  cases nb with
                  | inl na =>
                      dsimp only [rn] at hnp
                      rw [hnp] at ht
                      exact ht.2
                  | inr _ =>
                      dsimp only [rn] at hnp
                      rw [hnp] at ht
                      exact ht.elim
              | inr _ =>
                  dsimp only [rn] at hnp
                  rw [hnp] at ht
                  exact ht.elim
            · cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
              | inl nb =>
                  cases nb with
                  | inl na =>
                      have hbn : na.val.1.val = bn := na.val.1.property.2.2
                      have hac : na.val.2.1 = a := by
                        have hh := na.property.choose_spec.1
                        rw [hbn, hb, ha] at hh
                        exact (Option.some.inj hh).symm
                      dsimp only [rn] at hnp
                      rw [hnp] at ht
                      refine ⟨?_, hbn, hac, ht.1⟩
                      exact (congrArg ReferenceInitializationRun.Boundary.crossing hb).trans
                        active.val.1.property.2.1
                  | inr _ =>
                      dsimp only [rn] at hnp
                      rw [hnp] at ht
                      exact ht.elim
              | inr _ =>
                  dsimp only [rn] at hnp
                  rw [hnp] at ht
                  exact ht.elim
          · have ht := source_prelaunch_down_active_block_end
              rate rewards C_star C_h z i r hnext hsame
            rw [hp] at ht
            rcases ht with ⟨_, _, hE, hindex, hrun, han, hfn, _, hw, hcases⟩
            refine ⟨Or.inr ⟨hindex, hE, hrun⟩, ?_, ?_, hw, ?_⟩
            · exact (congrArg (fun c => c.activation f) hrun).trans han
            · exact (congrArg (fun c => c.forcedFailure f) hrun).trans hfn
            · cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
              | inl nb =>
                  cases nb with
                  | inl na =>
                      have hbn : na.val.1.val = bn := na.val.1.property.2.2
                      dsimp only [rn] at hnp
                      rw [hnp] at hcases
                      refine ⟨?_, hbn, hcases.2.2.1, hcases.2.2.2⟩
                      exact (congrArg ReferenceInitializationRun.Boundary.crossing hbn).symm.trans
                        na.val.1.property.2.1
                  | inr _ =>
                      dsimp only [rn] at hnp
                      rw [hnp] at hcases
                      exact hcases.elim
              | inr ns =>
                  have hbn : ns.val.1 = bn := ns.property.2.1
                  dsimp only [rn] at hnp
                  rw [hnp] at hcases
                  refine ⟨?_, hbn, hcases.2.2⟩
                  exact fun hc => ns.property.1
                    ((congrArg ReferenceInitializationRun.Boundary.crossing hbn).trans hc)
      | inr _ => trivial
  | inr _ => trivial

/-- The last active physical action hands its entire ordinary state and test
list to the actual terminal output. The horizon clips the real block; there
is no extra action at `T`. The crossing alternative also retains the existing
corrected payload and its empty physical suffix (07:106-114,129-140). -/
theorem source_prelaunch_down_active_terminal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hlast : r.val + 1 = p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let b := active.val.1.val
        let a := active.val.2.1
        let f := ActualReferenceInitializationBlock.refFollower i
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
        let next := ReferenceInitializationRun.finishBlock x b active.val.1.property.1
        let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
        b.completed = (roundBlockIndex p r).val ∧
          b.forcedFailure f = false ∧ (roundBlockIndex p r).val + 1 = n_boot p ∧
          ReferenceInitializationRun.elapsed p (b.completed + 1) = p.T ∧
          ReferenceInitializationRun.output x = next ∧ terminal.1 = next ∧
          terminal.1.activation f = some a ∧ terminal.1.forcedFailure f = false ∧
          terminal.1.crossing = (if ReferenceInitializationRun.crosses x b active.val.1.property.1
            then some (ReferenceInitializationRun.nextBlock b active.val.1.property.1) else none) ∧
          terminal.2 = ReferencePrelaunchFollower.step i x.row a r own active.val.2.2.2 ∧
          sourcePrelaunchDownTests rate rewards C_star C_h z i =
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
              (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList ∧
          ReferenceInitializationRun.elapsed p terminal.1.completed = p.T ∧
          (terminal.1.crossing.isSome = true →
            ∃ payload, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart payload p.T,
              ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
                some payload ∧
              ReferenceInitializationRun.launchRound x = p.T + 1 ∧
              (ReferenceActivePhysicalHorizon.run payload z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
                (Nat.le_refl _) hmode).finalState = payload ∧
              (ReferenceActivePhysicalHorizon.run payload z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
                (Nat.le_refl _) hmode).records = [])
    | _ => True := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  have hcal := calendar_terminal_block r hlast
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          let b := active.val.1.val
          let a := active.val.2.1
          let f := ActualReferenceInitializationBlock.refFollower i
          let next := ReferenceInitializationRun.finishBlock x b active.val.1.property.1
          have hgen : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
            active.val.1.property.2.2
          have hcompleted : b.completed = (roundBlockIndex p r).val := by
            have hprogress := ReferenceInitializationRun.run_progress x
              (roundBlockIndex p r).val (roundBlockIndex p r).isLt.le
            rw [← hgen] at hprogress
            exact hprogress.resolve_left
              (by rw [active.val.1.property.2.1]; exact Bool.false_ne_true)
          have hET : ReferenceInitializationRun.elapsed p (b.completed + 1) = p.T := by
            rw [hcompleted]
            exact hcal.1
          have hE : ReferenceInitializationRun.elapsed p (b.completed + 1) = r.val + 1 :=
            hET.trans hlast.symm
          obtain ⟨_, hf, hrun, ha, hff, hstate, htests⟩ := active_finish_block x i r active hE
          have hout : ReferenceInitializationRun.output x = next := by
            change ReferenceInitializationRun.run x (n_boot p) = next
            rw [← hcal.2]
            exact hrun
          have hterminal :
              (source_prelaunch_down_terminal rate rewards C_star C_h z i).1 = next := hout
          have htelapsed : ReferenceInitializationRun.elapsed p
              (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.completed = p.T := by
            rw [hterminal]
            exact hET
          refine ⟨hcompleted, hf, hcal.2, hET, hout, hterminal, ?_, ?_, ?_, ?_, ?_, htelapsed, ?_⟩
          · rw [hterminal]
            exact ha
          · rw [hterminal]
            exact hff
          · rw [hterminal]
            rfl
          · change ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f = _
            rw [hout]
            exact hstate
          · change boundaryPrelaunchDownTests x (ReferenceInitializationRun.output x) i = _
            rw [hout]
            simpa only [source_prelaunch_down_prefix_tests, hp,
              source_prelaunch_down_current_test] using htests
          · intro hc
            exact source_prelaunch_down_terminal_crossing rate rewards C_star C_h z hc htelapsed
      | inr _ => trivial
  | inr _ => trivial

/-- Later generated declarations and forcing preserve this follower's entire
ordinary continuation. All old history entries agree literally, and the later
state is the genuine suffix fold starting at the actual finished block state.
The only extra inputs are a later run opportunity and its calendar ordering;
there is no assumed history or ordinary-state equality. This also applies to
`q = n_boot p`, the actual output, and to a stopped tail. -/
theorem source_prelaunch_down_active_continuation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (q : ℕ)
    (hq : (roundBlockIndex p r).val + 1 ≤ q) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let b := active.val.1.val
        let a := active.val.2.1
        let f := ActualReferenceInitializationBlock.refFollower i
        let j := PublicDiscreteDraws.followerPlayer p.two_le_m f
        let next := ReferenceInitializationRun.run x ((roundBlockIndex p r).val + 1)
        let later := ReferenceInitializationRun.run x q
        let E := ReferenceInitializationRun.elapsed p next.completed
        let M := ReferenceInitializationRun.elapsed p later.completed
        ∃ hEM : E ≤ M,
          next = ReferenceInitializationRun.finishBlock x b active.val.1.property.1 ∧
          later.activation f = some a ∧ later.forcedFailure f = false ∧
          (∀ t : Fin E, later.history j (Fin.castLE hEM t) = next.history j t) ∧
          ReferenceInitializationRun.ordinary x later f =
            ReferencePrelaunchFollower.run i x.row a (later.history j)
              (ReferenceInitializationRun.elapsed_le_T p later.completed)
              (List.ofFn (fun v : Fin (M - E) => (⟨E + v.val, by omega⟩ : Fin M)))
              (ReferenceInitializationRun.ordinary x next f)
    | _ => True := by
  classical
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let s := roundBlockIndex p r
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          let b := active.val.1.val
          let a := active.val.2.1
          let f := ActualReferenceInitializationBlock.refFollower i
          let j := PublicDiscreteDraws.followerPlayer p.two_le_m f
          let next := ReferenceInitializationRun.run x (s.val + 1)
          let later := ReferenceInitializationRun.run x q
          let E := ReferenceInitializationRun.elapsed p next.completed
          let M := ReferenceInitializationRun.elapsed p later.completed
          have hgen : b = ReferenceInitializationRun.run x s.val := active.val.1.property.2.2
          have hc : b.crossing = none := active.val.1.property.2.1
          have ha : b.activation f = some a := active.property.choose_spec.1
          have hf : b.forcedFailure f = false := by
            rw [hgen]
            exact ReferenceInitializationRun.run_no_forced_before_launch x s.val
              (by rw [← hgen]; exact hc) f
          have hrun : next = ReferenceInitializationRun.finishBlock x b active.val.1.property.1 := by
            change ReferenceInitializationRun.run x (s.val + 1) = _
            calc
              ReferenceInitializationRun.run x (s.val + 1) =
                  ReferenceInitializationRun.advance x (ReferenceInitializationRun.run x s.val) :=
                ReferenceInitializationRun.run_succ x s.val
              _ = ReferenceInitializationRun.advance x b :=
                congrArg (ReferenceInitializationRun.advance x) hgen.symm
              _ = ReferenceInitializationRun.finishBlock x b active.val.1.property.1 :=
                ReferenceInitializationRun.advance_of_no_crossing x b hc active.val.1.property.1
          have hpres := ReferenceSuppressedDownCoverage.run_active_preserved x
            (show s.val ≤ q by omega) f a
            (by rw [← hgen]; exact ha) (by rw [← hgen]; exact hf)
          have hnPres := ReferenceSuppressedDownCoverage.run_active_preserved x
            (Nat.le_succ s.val) f a
            (by rw [← hgen]; exact ha) (by rw [← hgen]; exact hf)
          have hEM : E ≤ M := ReferenceInitializationRun.elapsed_mono p
            (InitializationFailureProvenance.run_completed_mono x hq)
          refine ⟨hEM, hrun, hpres.1, hpres.2, ?_, ?_⟩
          · intro t
            exact ReferenceSuppressedDownCoverage.run_history_prefix x hq j t.val t.isLt
              (Fin.castLE hEM t).isLt
          · have hord := ordinary_of_active x later i a hpres.1 hpres.2
            have hnOrd := ordinary_of_active x next i a hnPres.1 hnPres.2
            rw [hord, hnOrd]
            have hlist : List.ofFn (fun v : Fin M => v) =
                (List.ofFn (fun u : Fin E => u)).map (Fin.castLE hEM) ++
                  List.ofFn (fun v : Fin (M - E) => (⟨E + v.val, by omega⟩ : Fin M)) := by
              rw [List.ofFn_congr (show M = E + (M - E) by omega), List.ofFn_add]
              simp only [List.map_ofFn, Function.comp_def]
              rfl
            change ReferencePrelaunchFollower.run i x.row a (later.history j)
                (ReferenceInitializationRun.elapsed_le_T p later.completed)
                (List.ofFn (fun v : Fin M => v)) (initial p x.eta) = _
            rw [hlist, ReferencePrelaunchFollower.run_append,
              ReferenceSuppressedDownCoverage.run_generated_prefix x hq]
            rfl
      | inr _ => trivial
  | inr _ => trivial

end Bandits.Support.ReferenceGeneratedPrelaunchDownActiveBridge

end
