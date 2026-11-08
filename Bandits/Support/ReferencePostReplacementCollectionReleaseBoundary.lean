/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterInstallationChoiceHistory
public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedChargeDomination

/-!
# Actual post-replacement collection release boundary

This module consumes the accepted actual later-installation choice history.
Its list split refers to the original complete physical suffix and retains the
literal selected missing-set test.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary

variable {p : ConstructorDimensions.Parameters}

/-- Split the actual later installation at its first choice with no missing
follower. The first prefix has no actual released follower. -/
public theorem actual_later_installation_list_partition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        H ++ Rel = V ∧
        (Rel = [] ↔ ∀ r ∈ V,
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true) ∧
        (∀ r ∈ H, ∀ i (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice r i).configuration =
            .ordinary choice memory → choice.status ≠ .released)
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨_rb, _qb, _beta, _birthSelected, _hnext, _hbirth, _hlater,
        _hbirthSelection, _hbirthPayload, _hbirthPending, _hrbPending,
        _hbirthNoEvent, _hfollowers, _htail, hnoRelease, _hframes⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.takeWhile_append_dropWhile]
    · simp only [List.dropWhile_eq_nil_iff]
    · exact hnoRelease
  · simp only [ite_eq_right hb]

/-- At an actual continuing choice where the literal test is false, the same
selected pending set is empty and every actual follower choice is occupied. -/
public theorem actual_later_installation_empty_choice_is_occupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        ∀ j : Fin W.length,
          if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
            ∃ (selected : ReferenceActivePhysicalStep.Selection W[j.val].input)
              (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
              (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
              W[j.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.pendingAtChoice = ∅ ∧
              (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
                .ordinary (states i) (memories i)) ∧
              ∀ i, (states i).status ≠ .unoccupied
          else True
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨_rb, _qb, _beta, _birthSelected, _hnext, _hbirth, _hlater,
        _hbirthSelection, _hbirthPayload, _hbirthPending, _hrbPending,
        _hbirthNoEvent, _hfollowers, _htail, _hnoRelease, hframes⟩
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    change ∀ j : Fin W.length,
      if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
        ∃ (selected : ReferenceActivePhysicalStep.Selection W[j.val].input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
            .ordinary (states i) (memories i)) ∧
          ∀ i, (states i).status ≠ .unoccupied
      else True
    intro j
    by_cases hmissing :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false
    · simp only [ite_eq_left hmissing]
      obtain ⟨r, q, selected, next, owned, states, memories,
        _hinput, _hpayload, hselection, _hselectedPayload, _hpending,
        _houtput, _hnextPayload, _hupdate, hchoices, homitted, _hclear, _hsteps⟩ :=
        hframes j
      have htest : decide selected.view.pendingAtChoice.Nonempty = false := by
        unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice at hmissing
        rw [hselection] at hmissing
        exact hmissing
      have hempty : selected.view.pendingAtChoice = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (of_decide_eq_false htest)
      have hoccupied : ∀ i, (states i).status ≠ .unoccupied := by
        intro i
        apply homitted i
        rw [hempty]
        exact Finset.notMem_empty i
      exact ⟨selected, states, memories, hselection, hempty, hchoices, hoccupied⟩
    · simp only [ite_eq_right hmissing]
  · simp only [ite_eq_right hb]

/-- Empty pending state persists across the actual adjacent continuing choice.
The update and both selections come from the same records of the original
physical suffix. -/
public theorem actual_later_installation_empty_choice_persists_one_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        ∀ j : Fin W.length, ∀ hj : j.val + 1 < W.length,
          if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
            ∃ selected : ReferenceActivePhysicalStep.Selection
                (W[j.val + 1]'hj).input,
              (W[j.val + 1]'hj).output.preparation.coordinator.selection = some selected ∧
              selected.view.pendingAtChoice = ∅
          else True
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨_rb, _qb, beta, _birthSelected, _hnext, _hbirth, _hlater,
        _hbirthSelection, _hbirthPayload, _hbirthPending, _hrbPending,
        _hbirthNoEvent, _hfollowers, _htail, _hnoRelease, hframes⟩
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    change ∀ j : Fin W.length, ∀ hj : j.val + 1 < W.length,
      if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
        ∃ selected : ReferenceActivePhysicalStep.Selection (W[j.val + 1]'hj).input,
          (W[j.val + 1]'hj).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅
      else True
    intro j hj
    let jNext : Fin W.length := ⟨j.val + 1, hj⟩
    by_cases hmissing :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false
    · simp only [ite_eq_left hmissing]
      obtain ⟨r, q, selected, next, owned, states, memories,
        hinput, _hpayload, hselection, _hselectedPayload, hpending,
        houtput, _hnextPayload, hupdate, _hchoices, _homitted, _hclear,
        _hsteps⟩ := hframes j
      obtain ⟨nextInputRegisters, nextInputOwned, selectedNext, nextNext,
        nextOwnedNext, statesNext, memoriesNext, hinputNext, _hpayloadNext,
        hselectionNext, _hselectedPayloadNext, hpendingNext, _houtputNext,
        _hnextPayloadNext, _hupdateNext, _hchoicesNext, _homittedNext,
        _hclearNext, _hstepsNext⟩ := hframes jNext
      have htest : decide selected.view.pendingAtChoice.Nonempty = false := by
        unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice at hmissing
        rw [hselection] at hmissing
        exact hmissing
      have hempty : selected.view.pendingAtChoice = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (of_decide_eq_false htest)
      have hnoevent :
          ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            W[j.val] selected := by
        intro hevent
        have hnonempty : selected.view.pendingAtChoice.Nonempty := hevent.2.1
        rw [hempty] at hnonempty
        obtain ⟨i, hi⟩ := hnonempty
        exact Finset.notMem_empty i hi
      have hnextEmpty : next.pendingAtChoice = ∅ := by
        rw [hupdate, ite_eq_right hnoevent, hempty]
      have hWle : W.length ≤ (R.drop (b.val + 1)).length := by
        change ((R.drop (b.val + 1)).takeWhile
          ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length ≤ _
        exact (List.takeWhile_prefix _).length_le
      simp only [List.length_drop] at hWle
      have hk : b.val + 1 < R.length := by omega
      let k : Fin R.length := ⟨b.val + 1, hk⟩
      have hprefix :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
          rewards C_star C_h z k
      have hprefixR : k.val + W.length ≤ R.length := by
        simpa only [W, k] using hprefix
      have hrecord :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
          rewards C_star C_h z k j.val j.isLt
      have hrecordNext :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
          rewards C_star C_h z k jNext.val jNext.isLt
      have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z (k.val + j.val) (by
          change k.val + j.val + 1 < R.length
          omega)
      have hstateNext : W[jNext.val].input.state = W[j.val].output.next := by
        rw [hrecordNext, hrecord]
        exact hadj
      have hcoord :
          ReferenceActivePhysicalStep.CoordinatorConfiguration.live
              nextInputRegisters nextInputOwned beta =
            ReferenceActivePhysicalStep.CoordinatorConfiguration.live next owned beta := by
        calc
          _ = W[jNext.val].input.state.coordinator := hinputNext.symm
          _ = W[j.val].output.next.coordinator :=
            congrArg (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
              hstateNext
          _ = _ := houtput
      have hregisters : nextInputRegisters = next :=
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hcoord).1
      refine ⟨selectedNext, hselectionNext, ?_⟩
      rw [hpendingNext, hregisters, hnextEmpty]
    · simp only [ite_eq_right hmissing]
  · simp only [ite_eq_right hb]

/-- Once an actual continuing choice has empty pending state, every later
continuing choice in this same physical prefix also has empty pending state. -/
public theorem actual_later_installation_empty_choice_persists
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        ∀ j k : Fin W.length, j.val ≤ k.val →
          if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[k.val] = false
          else True
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    change ∀ j k : Fin W.length, j.val ≤ k.val →
      if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[k.val] = false
      else True
    have hone :=
      actual_later_installation_empty_choice_persists_one_step
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hone
    change ∀ j : Fin W.length, ∀ hj : j.val + 1 < W.length,
      if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
        ∃ selected : ReferenceActivePhysicalStep.Selection (W[j.val + 1]'hj).input,
          (W[j.val + 1]'hj).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅
      else True at hone
    have hmon : ∀ n i (hi : i < W.length) (hn : n < W.length), i ≤ n →
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (W[i]'hi) = false →
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (W[n]'hn) = false := by
      intro n
      induction n with
      | zero =>
          intro i hi hn hle hfalse
          have hidx : i = 0 := by omega
          simpa only [hidx] using hfalse
      | succ n ih =>
          intro i hi hn hle hfalse
          by_cases heq : i = n + 1
          · simpa only [heq] using hfalse
          · have hile : i ≤ n := by omega
            have hn' : n < W.length := by omega
            have hprev := ih i hi hn' hile hfalse
            let j : Fin W.length := ⟨n, hn'⟩
            have hnext := hone j (by omega)
            rw [ite_eq_left hprev] at hnext
            obtain ⟨selected, hselection, hempty⟩ := hnext
            have hselection' :
                (W[n + 1]'hn).output.preparation.coordinator.selection = some selected := by
              simpa only [j] using hselection
            have hfalseNext :
                ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (W[n + 1]'hn) = false := by
              simp [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
                hselection', hempty]
            exact hfalseNext
    intro j k hjk
    by_cases hfalse :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false
    · simp only [ite_eq_left hfalse]
      exact hmon k.val j.val j.isLt k.isLt hjk hfalse
    · simp only [ite_eq_right hfalse]
  · simp only [ite_eq_right hb]

/-- Every record retained after the first empty-pending continuing choice has
the literal false missing-set test. The proof uses the actual continuing
prefix and its adjacent-update persistence. -/
public theorem actual_later_installation_release_suffix_test_false
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ∀ r ∈ Rel,
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    change ∀ r ∈ Rel,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨_rb, _qb, _beta, _birthSelected, _hnext, _hbirth, _hlater,
        hbirthSelection, _hbirthPayload, hbirthPending, _hrbPending,
        _hbirthNoEvent, _hfollowers, _htail, _hnoRelease, _hframes⟩
    have hbirthMissing :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice R[b.val] = true := by
      have hne : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty :=
        ⟨⟨0, by have hm := p.two_le_m; omega⟩, Finset.mem_univ _⟩
      unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [hbirthSelection]
      change decide _birthSelected.view.pendingAtChoice.Nonempty = true
      rw [hbirthPending]
      exact decide_eq_true hne
    have hWpersist :=
      actual_later_installation_empty_choice_persists rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hWpersist
    change ∀ j k : Fin W.length, j.val ≤ k.val →
      if ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false then
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[k.val] = false
      else True at hWpersist
    have hVpersist : ∀ i j (hi : i < V.length) (hj : j < V.length), i ≤ j →
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[i]'hi) = false →
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[j]'hj) = false := by
      intro i j hi hj hij hfalse
      by_cases hi0 : i = 0
      · subst i
        have hindex : V[0]'hi = R[b.val] := by simp [V]
        have htest :
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[0]'hi) = true := by
          rw [hindex]
          exact hbirthMissing
        rw [htest] at hfalse
        cases hfalse
      · have hiW : i - 1 < W.length := by
          simp only [V, List.length_cons] at hi
          omega
        have hjW : j - 1 < W.length := by
          simp only [V, List.length_cons] at hj
          omega
        have hindexI : V[i]'hi = W[i - 1]'hiW := by
          have hbase : V[i - 1 + 1]'(by omega) = W[i - 1]'hiW := by
            simp only [V, List.getElem_cons_succ]
          calc
            V[i]'hi = V[i - 1 + 1]'(by omega) := getElem_congr_idx (by omega)
            _ = W[i - 1]'hiW := hbase
        have hindexJ : V[j]'hj = W[j - 1]'hjW := by
          have hbase : V[j - 1 + 1]'(by omega) = W[j - 1]'hjW := by
            simp only [V, List.getElem_cons_succ]
          calc
            V[j]'hj = V[j - 1 + 1]'(by omega) := getElem_congr_idx (by omega)
            _ = W[j - 1]'hjW := hbase
        let iW : Fin W.length := ⟨i - 1, hiW⟩
        let jW : Fin W.length := ⟨j - 1, hjW⟩
        have hfalseW :
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[iW.val] = false := by
          simpa only [iW, hindexI] using hfalse
        have hstep := hWpersist iW jW (by dsimp only [iW, jW]; omega)
        rw [ite_eq_left hfalseW] at hstep
        simpa only [jW, hindexJ] using hstep
    let h := V.findIdx (fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r)
    have hRel : Rel = V.drop h := by
      dsimp only [Rel, h]
      exact List.dropWhile_eq_drop_findIdx_not
    have hfirst : ∀ hlt : h < V.length,
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[h]'hlt) = false := by
      intro hlt
      have hfind := List.findIdx_getElem
        (xs := V) (p := fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r)
        (w := hlt)
      cases ht : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[h]'hlt) with
      | false => rfl
      | true =>
          rw [ht] at hfind
          cases hfind
    intro r hr
    rw [hRel, List.mem_iff_getElem] at hr
    obtain ⟨i, hi, hget⟩ := hr
    have hidx : h + i < V.length := by
      simp only [List.length_drop] at hi
      omega
    have hdrop : (V.drop h)[i]'hi = V[h + i]'hidx := by simp
    have hlt : h < V.length := by omega
    have htest := hVpersist h (h + i) hlt hidx (by omega) (hfirst hlt)
    have hrEq : r = V[h + i]'hidx := hget.symm.trans hdrop
    rw [hrEq]
    exact htest
  · simp only [ite_eq_right hb]

/-- Each retained record is an actual record of the continuing prefix; its
selected pending set is empty and every ordinary follower choice is occupied. -/
public theorem actual_later_installation_release_suffix_actual_occupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ∀ i (hi : i < Rel.length),
          ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
              (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
              selected.view.pendingAtChoice = ∅ ∧
              ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
                  .ordinary choice memory → choice.status ≠ .unoccupied
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    change ∀ i (hi : i < Rel.length),
      ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
          (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
              .ordinary choice memory → choice.status ≠ .unoccupied
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨_rb, _qb, _beta, _birthSelected, _hnext, _hbirth, _hlater,
        hbirthSelection, _hbirthPayload, hbirthPending, _hrbPending,
        _hbirthNoEvent, _hfollowers, _htail, _hnoRelease, _hframes⟩
    have hbirthMissing :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice R[b.val] = true := by
      have hne : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty :=
        ⟨⟨0, by have hm := p.two_le_m; omega⟩, Finset.mem_univ _⟩
      unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [hbirthSelection]
      change decide _birthSelected.view.pendingAtChoice.Nonempty = true
      rw [hbirthPending]
      exact decide_eq_true hne
    have hfalse := actual_later_installation_release_suffix_test_false
      rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hfalse
    change ∀ r ∈ Rel,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false at hfalse
    have hRelW : Rel = W.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
      dsimp only [Rel, V]
      exact List.dropWhile_cons_of_pos hbirthMissing
    have hmemDrop : ∀ {xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p)
        (rate := rate))} {r},
        r ∈ xs.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice →
        r ∈ xs := by
      intro xs
      induction xs with
      | nil => simp
      | cons head tail ih =>
          intro r hr
          by_cases hhead :
              ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice head = true
          · have htail :
                r ∈ tail.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
              simpa only [List.dropWhile_cons_of_pos hhead] using hr
            exact List.mem_cons_of_mem head (ih htail)
          · have hnot :
                ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice head = false := by
              cases heq : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice head with
              | false => rfl
              | true => exact (hhead heq).elim
            have hnotTrue :
                ¬ ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice head = true := by
              simp [hnot]
            simpa only [List.dropWhile_cons_of_neg hnotTrue] using hr
    have hoccupied :=
      actual_later_installation_empty_choice_is_occupied rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hoccupied
    intro i hi
    have hmemRel : Rel[i]'hi ∈ Rel := List.getElem_mem hi
    have hmemW : Rel[i]'hi ∈ W := by
      have hmemDropWhile :
          Rel[i]'hi ∈ W.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
        simpa only [hRelW] using hmemRel
      exact hmemDrop hmemDropWhile
    obtain ⟨jNat, hj, hrecordW⟩ := (List.mem_iff_getElem).mp hmemW
    let j : Fin W.length := ⟨jNat, hj⟩
    have hfalseRel := hfalse (Rel[i]'hi) (List.getElem_mem hi)
    have hfalseW :
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice W[j.val] = false := by
      simpa only [j] using (hrecordW ▸ hfalseRel)
    have hoccupiedJ := hoccupied j
    rw [ite_eq_left hfalseW] at hoccupiedJ
    obtain ⟨selected, states, memories, hselection, hempty, hchoices, hstatus⟩ := hoccupiedJ
    have hrecord : Rel[i]'hi = W[j.val]'j.isLt := by
      simpa only [j] using hrecordW.symm
    refine ⟨j.val, j.isLt, hrecord, selected, ?_, hempty, ?_⟩
    · simpa only [j] using hselection
    · intro follower choice memory hchoice
      rw [hchoices follower] at hchoice
      cases hchoice
      exact hstatus follower
  · simp only [ite_eq_right hb]

/-- The actual event test at any retained suffix record cannot confirm after
its selected pending set has already become empty. -/
public theorem actual_later_installation_release_suffix_has_no_confirmation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ∀ i (hi : i < Rel.length),
          ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
              (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
              selected.view.pendingAtChoice = ∅ ∧
              ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                  (W[j]'hj) selected
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    change ∀ i (hi : i < Rel.length),
      ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
          (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent (W[j]'hj) selected
    have hoccupied := actual_later_installation_release_suffix_actual_occupied
      rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hoccupied
    change ∀ i (hi : i < Rel.length),
      ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
          (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
              .ordinary choice memory → choice.status ≠ .unoccupied at hoccupied
    intro i hi
    obtain ⟨j, hj, hrecord, selected, hselection, hempty, _hoccupied⟩ := hoccupied i hi
    have hnoevent :
        ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          (W[j]'hj) selected := by
      intro hevent
      have hnonempty : selected.view.pendingAtChoice.Nonempty := hevent.2.1
      simp [hempty] at hnonempty
    exact ⟨j, hj, hrecord, selected, hselection, hempty, hnoevent⟩
  · simp only [ite_eq_right hb]

open scoped Classical

private theorem stage_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    ∀ i (hi : i < V.length), ∃ hbi : b.val + i < R.length,
      V[i]'hi = R[b.val + i]'hbi := by
  intro R W V i hi
  have hw : W.length ≤ R.length - (b.val + 1) := by
    change ((R.drop (b.val + 1)).takeWhile
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length ≤ _
    simpa only [List.length_drop] using
      (List.takeWhile_prefix (l := R.drop (b.val + 1))
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
  cases i with
  | zero => exact ⟨b.isLt, by simp [V]⟩
  | succ i =>
    have hiw : i < W.length := by simp only [V, List.length_cons] at hi; omega
    have hbi : b.val + (i + 1) < R.length := by omega
    refine ⟨hbi, ?_⟩
    change W[i]'hiw = _
    change ((R.drop (b.val + 1)).takeWhile
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest)[i] = _
    rw [(List.takeWhile_prefix _).getElem hiw, List.getElem_drop]
    congr 1; omega

private theorem stage_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    ∀ i : Fin V.length,
      ∃ (selected : ReferenceActivePhysicalStep.Selection V[i.val].input)
        (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
        (beta : Fin (p.m - 1) → ℕ),
        V[i.val].output.preparation.coordinator.selection = some selected ∧
        V[i.val].output.next.coordinator = .live next owned beta ∧
        next.pendingAtChoice =
          (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[i.val] selected then
            selected.view.pendingAtChoice.erase
              (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (V[i.val].input.row.2 V[i.val].input.time).1)
          else selected.view.pendingAtChoice) ∧
        ∀ hn : i.val + 1 < V.length,
          ∃ selectedNext : ReferenceActivePhysicalStep.Selection (V[i.val + 1]'hn).input,
            (V[i.val + 1]'hn).output.preparation.coordinator.selection = some selectedNext ∧
            selectedNext.view.pendingAtChoice = next.pendingAtChoice := by
  classical
  intro R W V i
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨rb, qb, beta, birthSelected, hout, _hbirth, _hlater, hbs, _hbp,
    hbm, hrbm, hbe, _hfollowers, _htail, _hnoRelease, hframes⟩ := hh
  have next_frame : ∀ (n : ℕ) (hn : n < W.length),
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (selected : ReferenceActivePhysicalStep.Selection (W[n]'hn).input),
        (W[n]'hn).input.state.coordinator = .live r q beta ∧
        (W[n]'hn).output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice = r.pendingAtChoice := by
    intro n hn
    obtain ⟨r, q, selected, next, owned, states, memories, hin, _hp, hs, _hsp,
      hm, _ho, _hop, _hu, _hc, _homit, _hclear, _hsteps⟩ := hframes ⟨n, hn⟩
    exact ⟨r, q, selected, hin, hs, hm⟩
  have adjacency : ∀ n (hn : n + 1 < V.length),
      (V[n + 1]'hn).input.state = (V[n]'(by omega)).output.next := by
    intro n hn
    obtain ⟨hnR, heqn⟩ := stage_index rate rewards C_star C_h z b n (by change n < V.length; omega)
    obtain ⟨hnR', heqn'⟩ := stage_index rate rewards C_star C_h z b (n + 1) hn
    rw [heqn, heqn']
    simpa only [Nat.add_assoc] using
      ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z (b.val + n) (by omega)
  have next_pending : ∀ (n : ℕ) (hn : n + 1 < V.length)
      (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters next),
      (V[n]'(by omega)).output.next.coordinator = .live next owned beta →
      ∃ selectedNext : ReferenceActivePhysicalStep.Selection (V[n + 1]'hn).input,
        (V[n + 1]'hn).output.preparation.coordinator.selection = some selectedNext ∧
        selectedNext.view.pendingAtChoice = next.pendingAtChoice := by
    intro n hn next owned ho
    have hnw : n < W.length := by simp only [V, List.length_cons] at hn; omega
    obtain ⟨r, q, selected, hin, hs, hm⟩ := next_frame n hnw
    have ha := congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
      (adjacency n hn)
    change (W[n]'hnw).input.state.coordinator = _ at ha
    rw [hin, ho] at ha
    have hr : r = next := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj ha).1
    exact ⟨selected, hs, hm.trans (congrArg (fun r => r.pendingAtChoice) hr)⟩
  rcases i with ⟨n, hn⟩
  cases n with
  | zero =>
    refine ⟨birthSelected, rb, qb, beta, hbs, hout, ?_, ?_⟩
    · dsimp only [Fin.val_mk, V, List.getElem_cons_zero]
      rw [ite_eq_right hbe, hbm, hrbm]
    · intro hnext
      exact next_pending 0 hnext rb qb hout
  | succ n =>
    have hnw : n < W.length := by simp only [V, List.length_cons] at hn; omega
    obtain ⟨r, q, selected, next, owned, states, memories, _hin, _hp, hs, _hsp,
      _hm, ho, _hop, hu, _hc, _homit, _hclear, _hsteps⟩ := hframes ⟨n, hnw⟩
    refine ⟨selected, next, owned, beta, hs, ho, hu, ?_⟩
    intro hnext
    exact next_pending (n + 1) hnext next owned ho

/-- Literal clearing event: an actual selected DOWN confirmation whose actual
live output has empty pending. This includes a clearing event at the last
retained record, whether or not a release choice follows. -/
def clearingConfirmation {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  match r.output.preparation.coordinator.selection, r.output.next.coordinator with
  | some selected, .live next _ _ =>
      ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ∧ next.pendingAtChoice = ∅
  | _, _ => False

private theorem missing_false_iff
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false ↔
      selected.view.pendingAtChoice = ∅ := by
  simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hs,
    decide_eq_false_iff_not, Finset.not_nonempty_iff_eq_empty]

/-- The actual handover/release partition, with selected-empty occupancy on
all retained release records and every actual confirmation in handover. -/
public theorem actual_later_installation_stage_partition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        H ++ Rel = V ∧
        (Rel = [] ↔ ∀ r ∈ V,
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true) ∧
        (∀ i (hi : i < Rel.length),
          ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
              (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
              selected.view.pendingAtChoice = ∅ ∧
              ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
                  .ordinary choice memory → choice.status ≠ .unoccupied) ∧
        (∀ r ∈ V, ∀ selected : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some selected →
          ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected → r ∈ H)
      else True := by
  classical
  intro R b
  split
  · rename_i hb
    have hp := actual_later_installation_list_partition rate rewards C_star C_h z b
    have ho := actual_later_installation_release_suffix_actual_occupied rate rewards C_star C_h z b
    have hf := actual_later_installation_release_suffix_test_false rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hp ho hf
    refine ⟨hp.1, hp.2.1, ho, ?_⟩
    intro r hr selected hs he
    have hm : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true := by
      simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hs]
      exact decide_eq_true he.2.1
    rw [← hp.1, List.mem_append] at hr
    rcases hr with hr | hr
    · exact hr
    · have hfalse := hf r hr
      rw [hm] at hfalse
      cases hfalse
  · trivial

private theorem stage_empty_persists
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    ∀ j k (hj : j < V.length) (hk : k < V.length), j ≤ k →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[j]'hj) = false →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[k]'hk) = false := by
  intro R W V j k hj hk hjk hempty
  have hf := stage_frame rate rewards C_star C_h z b hb
  change ∀ i : Fin V.length, _ at hf
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact hempty
  | succ k ih =>
    by_cases heq : j = k + 1
    · subst j; exact hempty
    · have hk' : k < V.length := by omega
      have hp := ih hk' (by omega)
      obtain ⟨selected, next, owned, beta, hs, _ho, hu, hn⟩ := hf ⟨k, hk'⟩
      have hm := (missing_false_iff _ selected hs).mp hp
      have he : ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          (V[k]'hk') selected := by
        intro he
        have := he.2.1
        simp only [hm, Finset.not_nonempty_empty] at this
      have hnempty : next.pendingAtChoice = ∅ := by rw [hu, ite_eq_right he, hm]
      obtain ⟨selectedNext, hsNext, hmNext⟩ := hn hk
      exact (missing_false_iff _ selectedNext hsNext).mpr (hmNext.trans hnempty)

private theorem clearing_pending_followers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let H := (R[b.val] :: W).takeWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    ∀ j : Fin W.length, ∀ hn : j.val + 1 < W.length,
      W[j.val] ∈ H → clearingConfirmation W[j.val] →
      ∀ i, ∃ (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
        (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
          .ordinary choice memory ∧ choice.status = .pending ∧
        (ReferenceFollowerFixedReply.actualChoice (W[j.val + 1]'hn) i).configuration =
          .ordinary nextChoice nextMemory ∧ nextChoice.status = .pending := by
  classical
  intro R W H j hn hmem hclear
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨_rb, _qb, _beta, _birthSelected, _hout, _hbirth, _hlater, _hbs, _hbp,
    _hbm, _hrbm, _hbe, _hfollowers, _htail, hnoRelease, hframes⟩ := hh
  obtain ⟨r, q, selected, next, owned, states, memories, _hin, _hp, hs, _hsp,
    _hm, ho, _hop, hu, hc, _homit, hlast, hsteps⟩ := hframes j
  have hclear' : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[j.val] selected ∧
      next.pendingAtChoice = ∅ := by
    unfold clearingConfirmation at hclear
    rw [hs, ho] at hclear
    exact hclear
  have herase : selected.view.pendingAtChoice.erase
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[j.val].input.row.2 W[j.val].input.time).1) = ∅ := by
    rw [hu, ite_eq_left hclear'.1] at hclear'
    exact hclear'.2
  have hoccupied := hlast hclear'.1 herase
  intro i
  have hstatus : (states i).status = .pending := by
    have hnr := hnoRelease W[j.val] hmem i (states i) (memories i) (hc i)
    cases hst : (states i).status with
    | unoccupied => exact (hoccupied i hst).elim
    | pending => rfl
    | released => exact (hnr hst).elim
  obtain hun | ⟨nextFollower, nextMemory, _houtf, _hocc, _hword, _hrel, hpend, hchoice⟩ := hsteps i
  · exact (hoccupied i hun).elim
  · exact ⟨states i, nextFollower, memories i, nextMemory, hc i, hstatus,
      hchoice hn, hpend hclear'.1.2.1 hstatus⟩

private theorem stage_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let h := V.findIdx (fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r)
    0 < h ∧
    (¬ clearingConfirmation (V[0]'(by simp only [V, List.length_cons]; omega))) ∧
    (∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = h) ∧
    (∀ hh : h < V.length, clearingConfirmation (V[h - 1]'(by omega))) ∧
    (∀ j : Fin V.length, h ≤ j.val →
      ∀ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
        V[j.val].output.preparation.coordinator.selection = some selected →
        ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[j.val] selected) := by
  classical
  intro R W V h
  have hle : h ≤ V.length := List.findIdx_le_length
  have hbefore : ∀ n (hn : n < h),
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[n]'(by omega)) = true := by
    intro n hn
    have ht := List.not_of_lt_findIdx (xs := V)
      (p := fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r) hn
    simpa only [Bool.not_eq_false'] using ht
  have hfirst : ∀ hn : h < V.length,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[h]'hn) = false := by
    intro hn
    have ht := List.findIdx_getElem (xs := V)
      (p := fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r) (w := hn)
    cases he : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[h]'hn) with
    | false => rfl
    | true =>
      change (!ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[h]'hn)) = true at ht
      rw [he] at ht
      cases ht
  have hf : ∀ i : Fin V.length,
    ∃ (selected : ReferenceActivePhysicalStep.Selection V[i.val].input)
      (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
      (beta : Fin (p.m - 1) → ℕ),
      V[i.val].output.preparation.coordinator.selection = some selected ∧
      V[i.val].output.next.coordinator = .live next owned beta ∧
      next.pendingAtChoice =
        (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[i.val] selected then
          selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (V[i.val].input.row.2 V[i.val].input.time).1)
        else selected.view.pendingAtChoice) ∧
      ∀ hn : i.val + 1 < V.length,
        ∃ selectedNext : ReferenceActivePhysicalStep.Selection (V[i.val + 1]'hn).input,
          (V[i.val + 1]'hn).output.preparation.coordinator.selection = some selectedNext ∧
          selectedNext.view.pendingAtChoice = next.pendingAtChoice :=
    stage_frame rate rewards C_star C_h z b hb
  have hper : ∀ j k (hj : j < V.length) (hk : k < V.length), j ≤ k →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[j]'hj) = false →
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[k]'hk) = false :=
    stage_empty_persists rate rewards C_star C_h z b hb
  have clear_index : ∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = h := by
    intro j hc
    obtain ⟨selected, next, owned, beta, hs, ho, _hu, hn⟩ := hf j
    unfold clearingConfirmation at hc
    rw [hs, ho] at hc
    have ht : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice V[j.val] = true := by
      unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [hs]
      exact decide_eq_true hc.1.2.1
    have hjh : j.val < h := by
      by_contra hh
      have hfalse := hper h j.val (by omega) j.isLt (by omega) (hfirst (by omega))
      rw [ht] at hfalse
      cases hfalse
    by_cases hjn : j.val + 1 < V.length
    · obtain ⟨selectedNext, hsNext, hmNext⟩ := hn hjn
      have htNext := (missing_false_iff _ selectedNext hsNext).mpr (hmNext.trans hc.2)
      by_contra hh
      have htrue := hbefore (j.val + 1) (by omega)
      rw [htNext] at htrue
      cases htrue
    · omega
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨_rb, _qb, _beta, birthSelected, _hout, _hbirth, _hlater, hbs, _hbp,
    hbm, _hrbm, hbe, _hfollowers, _htail, _hnr, _hframes⟩ := hh
  have hbirth : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (V[0]'(by simp only [V, List.length_cons]; omega)) = true := by
    change ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice R[b.val] = true
    unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    rw [hbs]
    change decide birthSelected.view.pendingAtChoice.Nonempty = true
    rw [hbm]
    have hne : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty :=
      ⟨⟨0, by have hm := p.two_le_m; omega⟩, Finset.mem_univ _⟩
    exact decide_eq_true hne
  have hpos : 0 < h := by
    by_contra hh
    have ht := hfirst (by simp only [V, List.length_cons]; omega)
    have hz : h = 0 := by omega
    have ht0 : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        (V[0]'(by simp only [V, List.length_cons]; omega)) = false := by
      simpa only [hz] using ht
    rw [hbirth] at ht0
    cases ht0
  have first_clear : ∀ hh : h < V.length,
      clearingConfirmation (V[h - 1]'(by omega)) := by
    intro hh
    let j : Fin V.length := ⟨h - 1, by omega⟩
    obtain ⟨selected, next, owned, beta, hs, ho, hu, hn⟩ := hf j
    obtain ⟨selectedNext, hsNext, hmNext⟩ := hn (by dsimp only [j]; omega)
    have heq : j.val + 1 = h := by dsimp only [j]; omega
    have hnextFalse : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        (V[j.val + 1]'(by dsimp only [j]; omega)) = false := by
      simpa only [heq] using hfirst hh
    have hnextEmpty := (missing_false_iff _ selectedNext hsNext).mp hnextFalse
    have hafter : next.pendingAtChoice = ∅ := hmNext.symm.trans hnextEmpty
    have htrue := hbefore j.val (by dsimp only [j]; omega)
    have hevent : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[j.val] selected := by
      by_contra he
      have hempty : selected.view.pendingAtChoice = ∅ := by
        rw [hu, ite_eq_right he] at hafter
        exact hafter
      have ht := (missing_false_iff _ selected hs).mpr hempty
      rw [ht] at htrue
      cases htrue
    unfold clearingConfirmation
    rw [hs, ho]
    exact ⟨hevent, hafter⟩
  have hnoBirth : ¬ clearingConfirmation (V[0]'(by simp only [V, List.length_cons]; omega)) := by
    intro hc
    unfold clearingConfirmation at hc
    dsimp only [V, List.getElem_cons_zero] at hc
    rw [hbs, _hout] at hc
    exact hbe hc.1
  refine ⟨hpos, hnoBirth, clear_index, first_clear, ?_⟩
  intro j hj selected hs he
  have ht := hper h j.val (by omega) j.isLt hj (hfirst (by omega))
  have hm := (missing_false_iff _ selected hs).mp ht
  have := he.2.1
  simp only [hm, Finset.not_nonempty_empty] at this

/-- The final clearing confirmation and the first retained release CHOICE
are adjacent actual physical records. A terminal clear is permitted without
any release record; all followers are pending at both boundary choices.
Source dates are input coordinates plus one, so the first release date is
the confirming date plus one. -/
public theorem actual_later_installation_release_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let V := R[b.val] :: W
        let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        let h := H.length
        (∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = h) ∧
        (∀ j k : Fin V.length,
          clearingConfirmation V[j.val] → clearingConfirmation V[k.val] → j = k) ∧
        (Rel ≠ [] ↔ ∃ j : Fin V.length,
          clearingConfirmation V[j.val] ∧ j.val + 1 < V.length) ∧
        (∀ j : Fin V.length, h ≤ j.val →
          ∀ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
            V[j.val].output.preparation.coordinator.selection = some selected →
            ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[j.val] selected) ∧
        (Rel ≠ [] → ∃ j : Fin V.length, ∃ hn : j.val + 1 < V.length,
          j.val = h - 1 ∧ 2 ≤ h ∧ clearingConfirmation V[j.val] ∧
          ∃ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
            V[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.pendingAtChoice =
              {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (V[j.val].input.row.2 V[j.val].input.time).1} ∧
            R[b.val + j.val]? = some V[j.val] ∧
            R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
            Rel.head? = some (V[j.val + 1]'hn) ∧
            (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
            ∀ i, ∃ (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
              (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
                .ordinary choice memory ∧ choice.status = .pending ∧
              (ReferenceFollowerFixedReply.actualChoice (V[j.val + 1]'hn) i).configuration =
                .ordinary nextChoice nextMemory ∧ nextChoice.status = .pending)
      else True := by
  classical
  intro R b
  split
  · rename_i hb
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    let h := V.findIdx (fun r => !ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r)
    have hle : h ≤ V.length := List.findIdx_le_length
    have hH : H.length = h := by
      simp only [H, List.takeWhile_eq_take_findIdx_not, List.length_take, Nat.min_eq_left hle, h]
    have hRel : Rel = V.drop h := List.dropWhile_eq_drop_findIdx_not
    have hnonempty : Rel ≠ [] ↔ h < V.length := by
      rw [hRel, ne_eq, List.drop_eq_nil_iff]
      omega
    obtain ⟨hpos, hnoBirth, clear_index, first_clear, hnoLater⟩ :=
      stage_cut rate rewards C_star C_h z b hb
    change 0 < h at hpos
    change ∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = h at clear_index
    change ∀ hh : h < V.length, clearingConfirmation (V[h - 1]'(by omega)) at first_clear
    change (∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = H.length) ∧
        (∀ j k : Fin V.length,
          clearingConfirmation V[j.val] → clearingConfirmation V[k.val] → j = k) ∧
        (Rel ≠ [] ↔ ∃ j : Fin V.length,
          clearingConfirmation V[j.val] ∧ j.val + 1 < V.length) ∧
        (∀ j : Fin V.length, H.length ≤ j.val →
          ∀ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
            V[j.val].output.preparation.coordinator.selection = some selected →
            ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent V[j.val] selected) ∧
        (Rel ≠ [] → ∃ j : Fin V.length, ∃ hn : j.val + 1 < V.length,
          j.val = H.length - 1 ∧ 2 ≤ H.length ∧ clearingConfirmation V[j.val] ∧
          ∃ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
            V[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.pendingAtChoice =
              {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (V[j.val].input.row.2 V[j.val].input.time).1} ∧
            R[b.val + j.val]? = some V[j.val] ∧
            R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
            Rel.head? = some (V[j.val + 1]'hn) ∧
            (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
            ∀ i, ∃ (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
              (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
                .ordinary choice memory ∧ choice.status = .pending ∧
              (ReferenceFollowerFixedReply.actualChoice (V[j.val + 1]'hn) i).configuration =
                .ordinary nextChoice nextMemory ∧ nextChoice.status = .pending)
    rw [hH]
    refine ⟨clear_index, ?_, ?_, ?_, ?_⟩
    · intro j k hj hk
      apply Fin.ext
      have := clear_index j hj
      have := clear_index k hk
      omega
    · rw [hnonempty]
      constructor
      · intro hh
        exact ⟨⟨h - 1, by omega⟩, first_clear hh, by change h - 1 + 1 < V.length; omega⟩
      · rintro ⟨j, hc, hjn⟩
        have := clear_index j hc
        omega
    · exact hnoLater
    · intro hne
      have hh := hnonempty.mp hne
      let j : Fin V.length := ⟨h - 1, by omega⟩
      have hc := first_clear hh
      have hjh : j.val + 1 = h := by dsimp only [j]; omega
      have htwo : 2 ≤ h := by
        by_contra ht
        have heq : h - 1 = 0 := by omega
        have hc0 : clearingConfirmation (V[0]'(by simp only [V, List.length_cons]; omega)) := by
          simpa only [heq] using hc
        exact hnoBirth hc0
      have hn : j.val + 1 < V.length := by omega
      obtain ⟨selected, next, owned, beta, hs, ho, hu, _hn⟩ :=
        stage_frame rate rewards C_star C_h z b hb j
      have hc' := hc
      unfold clearingConfirmation at hc'
      rw [hs, ho] at hc'
      have herase := hc'.2
      rw [hu, ite_eq_left hc'.1] at herase
      have hsingle : selected.view.pendingAtChoice =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (V[j.val].input.row.2 V[j.val].input.time).1} := by
        rcases (Finset.erase_eq_empty_iff _ _).mp herase with he | he
        · have := hc'.1.2.1
          simp only [he, Finset.not_nonempty_empty] at this
        · exact he
      obtain ⟨hjR, hjEq⟩ := stage_index rate rewards C_star C_h z b j.val j.isLt
      obtain ⟨hnR, hnEq⟩ := stage_index rate rewards C_star C_h z b (j.val + 1) hn
      refine ⟨j, hn, rfl, htwo, hc, selected, hs, hsingle, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hjEq]
        exact List.getElem?_eq_getElem hjR
      · rw [hnEq]
        simpa only [Nat.add_assoc] using List.getElem?_eq_getElem hnR
      · rw [hRel, List.head?_drop, ← hjh]
        exact List.getElem?_eq_getElem hn
      · rw [hnEq, hjEq,
          ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z ⟨_, hnR⟩,
          ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z ⟨_, hjR⟩]
        dsimp only [Fin.val_mk]
        omega
      · have hjw : h - 2 < W.length := by simp only [V, List.length_cons] at hh; omega
        have hnw : h - 2 + 1 < W.length := by simp only [V, List.length_cons] at hh; omega
        have hje : j.val = h - 2 + 1 := by dsimp only [j]; omega
        have hrec : V[j.val] = W[h - 2]'hjw := by simp only [hje, V, List.getElem_cons_succ]
        have hnrec : (V[j.val + 1]'hn) = W[h - 2 + 1]'hnw := by
          simp only [hje, V, List.getElem_cons_succ]
        have hmem : W[h - 2]'hjw ∈ H := by
          have hp := List.takeWhile_prefix (l := V)
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
          have hiH : j.val < H.length := by rw [hH]; omega
          have hget := hp.getElem hiH
          rw [← hrec, ← hget]
          exact List.getElem_mem hiH
        have hcW : clearingConfirmation (W[h - 2]'hjw) := by rw [← hrec]; exact hc
        have hfollows := clearing_pending_followers rate rewards C_star C_h z b hb
          ⟨h - 2, hjw⟩ hnw hmem hcW
        rw [hrec, hnrec]
        exact hfollows
  · trivial

private theorem raw_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
    ∀ birth payload cut, R[v]? = some birth → ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload →
      R[c]? = some cut → ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true →
      match R[c + K.length]? with
      | none => c + K.length = R.length
      | some next => ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
          ∃ ledger saved, next.input.state.coordinator = .collection payload ledger saved ∧
            ledger.pending = ∅ := by
  intro R w v c K birth payload cut hb hp hc hcut
  have hp0 := hp
  have hcut0 := hcut
  have ht := ReferenceFirstReplacementCollectionRawPendingTotal.complete_first_replacement_raw_calendar_pending_nonempty
    rate rewards C_star C_h z
  dsimp only at ht
  change R[v]? = some birth at hb
  rw [hb] at ht
  dsimp only at ht
  cases hprep : birth.output.preparation.coordinator with
  | first _ => simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hprep, reduceCtorEq] at hp
  | live _ _ _ _ => simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hprep, reduceCtorEq] at hp
  | dagger => simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hprep, reduceCtorEq] at hp
  | invalidCollectionCutoff => simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hprep, reduceCtorEq] at hp
  | collection _ _ _ _ outcome =>
    cases outcome <;> simp only [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload, hprep, reduceCtorEq] at hp
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    rw [hprep] at ht
    dsimp only at ht
    rw [hc] at ht
    dsimp only at ht
    cases hcp : cut.output.preparation.coordinator with
    | first _ => simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcp, Bool.false_eq_true] at hcut
    | collection _ _ _ _ _ => simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcp, Bool.false_eq_true] at hcut
    | dagger => simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcp, Bool.false_eq_true] at hcut
    | invalidCollectionCutoff => simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcp, Bool.false_eq_true] at hcut
    | live _ _ _ outcome =>
      cases outcome <;> simp only [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff, hcp, Bool.false_eq_true] at hcut
      rw [hcp] at ht
      dsimp only at ht
      obtain ⟨_stream, _initializer, _hseg, _hrecords, _hremaining, _hpayload,
        _hinit, _hstart, _hsigma, _hcutoff, _hfreeze, _hcursor, _hpending,
        _hincrement, _hgamma, _hraw, _hphase, _hchecked, _hcompleted, _hcells,
        _hstate, hend⟩ := ht
      have hk : K = cut :: (R.drop (c + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
        change ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK _ _ _ _ _ = _
        rw [ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_eq, hb]
        dsimp only
        rw [hp0]
        dsimp only [Option.isSome_some]
        rw [hc]
        dsimp only
        rw [hcut0]
        rfl
      rw [hk]
      cases he : R[c + (cut :: (R.drop (c + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length]? with
      | none =>
        rw [he] at hend
        exact hend.1
      | some next =>
        rw [he] at hend
        obtain ⟨_hstate, hchosen, ledger, saved, hcoord, hempty⟩ := hend
        exact ⟨hchosen, ledger, saved, by simpa only [Option.some.inj hp] using hcoord, hempty⟩

/-- The literal raw collection endpoint is either the true horizon or an
actual next installation. The stage split and release boundary below consume
that very installation, on the unchanged source and physical suffix. -/
public theorem raw_collection_next_installation_release_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
    (K = [] ↔ R[v]? = none ∨ ∃ birth payload,
      R[v]? = some birth ∧
      ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload ∧
      (R[c]? = none ∨ ∃ cut, R[c]? = some cut ∧
        ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false)) ∧
    (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none → K = []) ∧
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T → K = []) ∧
    match R[v]? with
    | none => v = R.length
    | some birth => ∃ payload,
        ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload ∧
        c ≤ R.length ∧
        match R[c]? with
        | none => c = R.length ∧ tail = R.drop (v + 1) ∧
            ∀ r ∈ R.drop (v + 1),
              ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r = false
        | some cut =>
          if ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true then
            c + K.length = R.length ∨
            ∃ b : Fin R.length, b.val = c + K.length ∧
              ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
              ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
                (saved : Option (Fin p.T × Bool))
                (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
                (beta : Fin (p.m - 1) → ℕ)
                (selected : ReferenceActivePhysicalStep.Selection R[b.val].input),
                R[b.val].input.state.coordinator = .collection payload ledger saved ∧
                ledger.pending = ∅ ∧
                R[b.val].output.next.coordinator = .live rb qb beta ∧
                R[b.val].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = rb.payload ∧
                let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                  rate rewards C_star C_h z (b.val + 1)
                let V := R[b.val] :: W
                let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
                let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
                let h := H.length
                H ++ Rel = V ∧
                (Rel = [] ↔ ∀ r ∈ V,
                  ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true) ∧
                (∀ i (hi : i < Rel.length),
                  ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
                    ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
                      (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
                      selected.view.pendingAtChoice = ∅ ∧
                      ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
                        (memory : ActiveFollowerLifecycle.LocalMemory p),
                        (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
                          .ordinary choice memory → choice.status ≠ .unoccupied) ∧
                (∀ r ∈ V, ∀ selected : ReferenceActivePhysicalStep.Selection r.input,
                  r.output.preparation.coordinator.selection = some selected →
                  ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected → r ∈ H) ∧
                (∀ j : Fin V.length, clearingConfirmation V[j.val] → j.val + 1 = h) ∧
                (Rel = [] ∨ ∃ j : Fin V.length, ∃ hn : j.val + 1 < V.length,
                  j.val = h - 1 ∧ 2 ≤ h ∧ clearingConfirmation V[j.val] ∧
                  ∃ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice =
                      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (V[j.val].input.row.2 V[j.val].input.time).1} ∧
                    R[b.val + j.val]? = some V[j.val] ∧
                    R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
                    Rel.head? = some (V[j.val + 1]'hn) ∧
                    (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
                    ∀ i, ∃ (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
                      (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                      (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
                        .ordinary choice memory ∧ choice.status = .pending ∧
                      (ReferenceFollowerFixedReply.actualChoice (V[j.val + 1]'hn) i).configuration =
                        .ordinary nextChoice nextMemory ∧ nextChoice.status = .pending)
          else cut.output.next.coordinator = .dagger ∧
            ∀ r ∈ R.drop (c + 1), r.input.state.coordinator = .dagger ∧
              ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r = false := by
  classical
  intro R w v tail c K
  refine ⟨ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_absence_cases
    rate rewards C_star C_h z,
    ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_of_no_launch
      rate rewards C_star C_h z,
    ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_of_terminal_start
      rate rewards C_star C_h z, ?_⟩
  have hvend := ReferenceFirstReplacementCollectionGlobalDecoderCharge.birth_endpoint rate R
  cases hb : R[v]? with
  | none => exact (hvend.2.1 hb).1
  | some birth =>
    have htag := hvend.2.2 birth hb
    obtain ⟨payload, hp⟩ : ∃ payload,
        ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload := by
      cases he : ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at htag
      | some payload => exact ⟨payload, rfl⟩
    have hsearch := ReferenceFirstReplacementCollectionGlobalDecoderCharge.replacement_search_endpoint
      rate rewards C_star C_h z birth payload hb hp
    refine ⟨payload, hp, hsearch.1, ?_⟩
    cases hc : R[c]? with
    | none => exact hsearch.2.1 hc
    | some cut =>
      by_cases hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true
      · simp only [ite_eq_left hcut]
        have hend := raw_endpoint rate rewards C_star C_h z birth payload cut hb hp hc hcut
        cases he : R[c + K.length]? with
        | none =>
          rw [he] at hend
          exact Or.inl hend
        | some next =>
          rw [he] at hend
          obtain ⟨hchosen, ledger, saved, hcoord, hempty⟩ := hend
          obtain ⟨hbn, hrecord⟩ := List.getElem?_eq_some_iff.mp he
          let b : Fin R.length := ⟨c + K.length, hbn⟩
          have hbchosen : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
            rw [show R[b.val] = next from hrecord]
            exact hchosen
          have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
            rate rewards C_star C_h z b
          rw [ite_eq_left hbchosen] at hh
          obtain ⟨rb, qb, beta, selected, hout, _hbirth, _hlater, hs, hpay, _hrest⟩ := hh
          have hpartition := actual_later_installation_stage_partition rate rewards C_star C_h z b
          have hboundary := actual_later_installation_release_boundary rate rewards C_star C_h z b
          rw [ite_eq_left hbchosen] at hpartition hboundary
          refine Or.inr ⟨b, rfl, hbchosen, ledger, saved, rb, qb, beta, selected,
            ?_, hempty, hout, hs, hpay, hpartition.1, hpartition.2.1,
            hpartition.2.2.1, hpartition.2.2.2, hboundary.1, ?_⟩
          · rw [show R[b.val] = next from hrecord]
            exact hcoord
          · by_cases hrel :
                ((R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                  rate rewards C_star C_h z (b.val + 1)).dropWhile
                    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice) = []
            · exact Or.inl hrel
            · exact Or.inr (hboundary.2.2.2.2 hrel)
      · have hfalse : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false :=
          Bool.eq_false_iff.mpr hcut
        simp only [ite_eq_right hcut]
        exact (hsearch.2.2 cut hc).2.2 hfalse

end Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary
