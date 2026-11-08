/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionFollowerPrefix

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile

/-!
# Actual first replacement collection seed and endpoints

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The seed consumes the actual replacement cutoff's logging, four DOWN outcomes,
and FINISH. Skips and rejections retain older registers, including nonzero
ones. The endpoint calculation uses the original complete physical suffix and
its actual connectivity. It includes the empty window and terminal boundary.
No follower survival along the collection window is asserted here.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionSeedEndpoint

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_endpoint_at
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final) (j : ℕ) :
    match records[j]? with
    | some r => r.input.state =
        ReferenceCollectionSegmentExtraction.endpointState initial (records.take j)
    | none => final =
        ReferenceCollectionSegmentExtraction.endpointState initial (records.take j) := by
  induction records generalizing initial j with
  | nil =>
      simpa only [List.getElem?_nil, List.take_nil,
        ReferenceCollectionSegmentExtraction.endpointState, List.foldl_nil,
        ReferenceActivePhysicalHorizon.Connected] using hconnected
  | cons head tail ih =>
      cases j with
      | zero =>
          simpa only [List.getElem?_cons_zero, List.take_zero,
            ReferenceCollectionSegmentExtraction.endpointState, List.foldl_nil] using hconnected.1
      | succ j =>
          simpa only [List.getElem?_cons_succ, List.take_succ_cons,
            ReferenceCollectionSegmentExtraction.endpointState, List.foldl_cons] using
            ih hconnected.2 j

private theorem takeWhile_first_excluded {α : Type} (predicate : α → Bool)
    (xs : List α) (item : α)
    (hget : xs[(xs.takeWhile predicate).length]? = some item) :
    predicate item = false := by
  induction xs with
  | nil =>
      simp only [List.takeWhile_nil, List.length_nil, List.getElem?_nil] at hget
      cases hget
  | cons head tail ih =>
      cases hp : predicate head with
      | false =>
          have heq : head = item := by simpa only [List.takeWhile_cons, hp,
            Bool.false_eq_true, ↓reduceIte, List.length_nil, List.getElem?_cons_zero,
            Option.some.injEq] using hget
          simpa only [← heq] using hp
      | true =>
          apply ih
          simpa only [List.takeWhile_cons, hp, ↓reduceIte, List.length_cons,
            List.getElem?_cons_succ] using hget

private theorem complete_record_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val ∧
    r.input.rows = source.1.2 ∧
    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    r.input.rewards = rewards := by
  obtain ⟨hc, hspan, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Conditional geometry for an actual indexed cutoff record. The sole local
premise is its original suffix index; launch and all state links are produced
from the complete source execution. No follower invariant is an input. -/
theorem actual_collection_endpoint_geometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (c : ℕ) (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[c]? = some cut) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let W := (R.drop (c + 1)).takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    let E := fun j => ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j)
    ReferenceCollectionPhaseHistory.collectionWindow R c = cut :: W ∧
    E 0 = cut.output.next ∧ cut.input.time.val = s + c ∧
    ∀ j : ℕ, j ≤ W.length →
      match R[c + 1 + j]? with
      | some r => r.input.state = E j ∧ r.input.time.val = cut.input.time.val + 1 + j ∧
          r.input.rows = source.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          r.input.rewards = rewards ∧
          (j < W.length → W[j]? = some r ∧ E (j + 1) = r.output.next) ∧
          (j = W.length → ReferenceCollectionPhaseHistory.laterChosen r.input = true)
      | none => j = W.length ∧ c + 1 + j = R.length ∧
          ReferenceCompletePhysicalHistory.completeTerminalState
            rate source rewards C_star C_h = some (E j) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let W := (R.drop (c + 1)).takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  change R[c]? = some cut at hcut
  obtain ⟨hc, hcutEq⟩ := List.getElem?_eq_some_iff.mp hcut
  have hcutRecord : R.get ⟨c, hc⟩ = cut := hcutEq
  have hcutFields := complete_record_fields rate source rewards C_star C_h ⟨c, hc⟩
  rw [hcutRecord] at hcutFields
  dsimp only at hcutFields
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow R c = cut :: W := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [List.take_one_drop_eq_of_lt_length hc, hcutRecord]
    rfl
  refine ⟨hwindow, rfl, hcutFields.1, ?_⟩
  have hprefix : W <+: R.drop (c + 1) := List.takeWhile_prefix _
  have hlen : W.length ≤ R.length - (c + 1) := by
    simpa only [List.length_drop] using hprefix.length_le
  have htake (j : ℕ) (hj : j ≤ W.length) :
      W.take j = (R.drop (c + 1)).take j := by
    calc
      W.take j = ((R.drop (c + 1)).take W.length).take j :=
        congrArg (List.take j) (List.prefix_iff_eq_take.mp hprefix)
      _ = (R.drop (c + 1)).take j := by rw [List.take_take, Nat.min_eq_left hj]
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none => simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hcut
  | some active =>
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h active hlaunch
      have hafter : ReferenceCollectionSegmentExtraction.endpointState active (R.take (c + 1)) =
          cut.output.next := by
        rw [List.take_add_one, hcut]
        simp only [ReferenceCollectionSegmentExtraction.endpointState, Option.toList_some,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hendpoint (j : ℕ) (hj : j ≤ W.length) :
          ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j) =
            ReferenceCollectionSegmentExtraction.endpointState active (R.take (c + 1 + j)) := by
        rw [List.take_add]
        unfold ReferenceCollectionSegmentExtraction.endpointState
        rw [List.foldl_append]
        change _ = ((R.drop (c + 1)).take j).foldl _
          (ReferenceCollectionSegmentExtraction.endpointState active (R.take (c + 1)))
        rw [hafter, htake j hj]
      intro j hj
      change j ≤ W.length at hj
      have hat := connected_endpoint_at hconnected (c + 1 + j)
      cases hget : R[c + 1 + j]? with
      | none =>
          have hbound := List.getElem?_eq_none_iff.mp hget
          change R.length ≤ c + 1 + j at hbound
          have hend : c + 1 + j = R.length := by omega
          have hjend : j = W.length := by omega
          rw [hget] at hat
          refine ⟨hjend, hend, ?_⟩
          rw [ReferenceCompletePhysicalHistory.completeTerminalState_on_launch
            rate source rewards C_star C_h active hlaunch]
          exact congrArg some (hat.trans (hendpoint j hj).symm)
      | some r =>
          rw [hget] at hat
          obtain ⟨hk, hr⟩ := List.getElem?_eq_some_iff.mp hget
          have hrRecord : R.get ⟨c + 1 + j, hk⟩ = r := hr
          have hfields := complete_record_fields rate source rewards C_star C_h
            ⟨c + 1 + j, hk⟩
          rw [hrRecord] at hfields
          dsimp only at hfields
          refine ⟨hat.trans (hendpoint j hj).symm, ?_, hfields.2.1,
            hfields.2.2.1, hfields.2.2.2, ?_, ?_⟩
          · omega
          · intro hjlt
            have hsource := ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
              R c j hjlt
            have hWRecord : W.get ⟨j, hjlt⟩ = r :=
              Option.some.inj (hsource.symm.trans hget)
            have hW : W[j]? = some r := by
              rw [List.getElem?_eq_getElem hjlt]
              exact congrArg some hWRecord
            refine ⟨hW, ?_⟩
            rw [List.take_add_one, hW]
            simp only [ReferenceCollectionSegmentExtraction.endpointState, Option.toList_some,
              List.foldl_append, List.foldl_cons, List.foldl_nil]
          · intro hjend
            have hexcluded : (R.drop (c + 1))[W.length]? = some r := by
              rw [List.getElem?_drop, ← hjend]
              exact hget
            have hfalse := takeWhile_first_excluded
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
              (R.drop (c + 1)) r hexcluded
            simpa only [Bool.not_eq_false'] using hfalse

/-- The complete actual first replacement cutoff seed together with every
physical endpoint of its subsequent collection window. The telescope contains
only the original dimensions, rate, source, whole reward table, and constants.
The cutoff producer supplies every local conditional input. -/
theorem complete_first_replacement_collection_seed_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let c := v + 1 + tail.length
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let M := fun i => payload.downRecord i
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := ReferenceCollectionPhaseHistory.collectionWindow R c
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            K = cut :: W ∧ E 0 = cut.output.next ∧ cut.input.time.val = s + c ∧
            3 ≤ u ∧ u ≤ p.T ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row) = u ∧
            (∀ i : Fin (p.m - 1),
              (M i).val.sigma ≤ u - 1 ∧
              (M i).val.q ≤ ((M i).val.sigma - 1) * D p ∧
              ∃ old state : ReferencePrelaunchFollower.State p rate.eta,
                ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                  cut.input.state.followers i = .ordinary old memory ∧
                  (cut.output.followers i).configuration = .ordinary state memory ∧
                  (cut.output.followers i).failure = none ∧
                  (E 0).followers i = .ordinary state memory ∧
                  state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
                  state.S + state.backlog ≤ (u - 1) * D p ∧ state.delta ≤ D p ∧
                  (state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
                  (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                    state.lastDown = some (M i)) ∧
                  state.initializationFailure = old.initializationFailure ∧
                  state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                  (∀ z ∈ state.buffer, z.calendarRound < u + 1)) ∧
            (∀ j : ℕ, j ≤ W.length →
              match R[c + 1 + j]? with
              | some r => r.input.state = E j ∧ r.input.time.val = u + j ∧
                  r.input.rows = source.1.2 ∧
                  r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                  r.input.rewards = rewards ∧
                  (j < W.length → W[j]? = some r ∧ E (j + 1) = r.output.next) ∧
                  (j = W.length → ReferenceCollectionPhaseHistory.laterChosen r.input = true)
              | none => j = W.length ∧ c + 1 + j = R.length ∧
                  ReferenceCompletePhysicalHistory.completeTerminalState
                    rate source rewards C_star C_h = some (E j))
          | _ => True
      | _ => True := by
  classical
  have hcutoff := ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
    rate source rewards C_star C_h
  dsimp only at hcutoff ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hbirthGet] at hcutoff ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection _ _ _ _ outcome =>
          rw [hbirthCoord] at hcutoff
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed birthArm
          dsimp only at hcutoff ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          cases hcutGet : R[v + 1 + tail.length]? with
          | none => trivial
          | some cut =>
              simp only [tail, hcutGet] at hcutoff ⊢
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live registers owned base outcome =>
                  rw [hcutCoord] at hcutoff
                  cases outcome <;> try trivial
                  rename_i dispatched hs ledger hi he hd hc hp hn chosen
                  dsimp only at hcutoff ⊢
                  rcases hcutoff.2 with ⟨hpayload, htimeBirth, htimeSource, hrows,
                    hselectedRow, hrewards, hsigmaPayload, hsourceStart, hfirst, hgrid,
                    hcause, selected, hselection, hselectedPayload, hpending, hcutoff, hfollower⟩
                  have hgeometry := actual_collection_endpoint_geometry rate source rewards
                    C_star C_h (v + 1 + tail.length) cut hcutGet
                  rcases hgeometry with ⟨hwindow, hzeroEndpoint, htime, hendpoints⟩
                  have hsourceBirth : s < birth.input.time.val := by
                    simpa only [hsigmaPayload] using hsourceStart
                  have hu : 3 ≤ cut.input.time.val + 1 := by omega
                  have huT : cut.input.time.val + 1 ≤ p.T := by
                    have := cut.input.time.isLt
                    omega
                  refine ⟨hwindow, hzeroEndpoint, htime, hu, huT, hfirst, ?_, hendpoints⟩
                  intro i
                  rcases hfollower i with ⟨old, memory, hinput, hdomainOld, hmassOld,
                    hzeroOld, hstrict, hbusy, hdecision, hstart, hprepared, hdomainChoice,
                    hmassChoice, hpair, hdates, hup, hstarted, hcredit, logged, post,
                    hlogging, hbuffer, hoperation, hlast, hS, hdelta, hbacklog, hflag,
                    hloggedStatus, hloggedPair, hloggedDates, hnoAppend, hconsume,
                    hstatus, hdomain, hmass, hdeltaBound, hpostFlag, hbranches,
                    hrecord, hdownInput, hdown, hrelease, hfinish, hreleaseFinish, houtput⟩
                  have hlastOld : logged.lastDown = old.lastDown := hlast
                  have hS' : logged.S = old.S := hS
                  have hdelta' : logged.delta = old.delta := hdelta
                  have hbacklog' : logged.backlog = old.backlog := hbacklog
                  have hloggedZero : logged.lastDown = none →
                      logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0 := by
                    intro hnone
                    have hz := hzeroOld (hlastOld.symm.trans hnone)
                    exact ⟨hS'.trans hz.1, hdelta'.trans hz.2.1, hbacklog'.trans hz.2.2⟩
                  have hloggedOrigin : ReferencePrelaunchFollower.acceptedStart logged <
                        (payload.downRecord i).val.sigma ∨
                      logged.lastDown = some (payload.downRecord i) := by
                    by_cases hfree : old.status = .unoccupied
                    · left
                      have heq : ReferencePrelaunchFollower.acceptedStart logged =
                          ReferencePrelaunchFollower.acceptedStart old := by
                        unfold ReferencePrelaunchFollower.acceptedStart
                        rw [hlastOld]
                      rw [heq]
                      exact hstrict hfree
                    · right
                      exact hlastOld.trans (hbusy hfree).1
                  have hpostFacts :
                      (post.lastDown = none → post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
                      (ReferencePrelaunchFollower.acceptedStart post <
                        (payload.downRecord i).val.sigma ∨
                        post.lastDown = some (payload.downRecord i)) ∧
                      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ z ∈ post.buffer, z.calendarRound < cut.input.time.val + 2) := by
                    rcases hbranches with hskip | hreject | hunaccepted | haccepted
                    · rcases hskip with ⟨_, _, hpost⟩
                      rw [hpost]
                      exact ⟨hloggedZero, hloggedOrigin, hloggedPair, hloggedDates⟩
                    · rcases hreject with ⟨_, _, _, _, _, _, _, _, _, hpost⟩
                      rw [hpost]
                      exact ⟨hloggedZero, hloggedOrigin, hloggedPair, hloggedDates⟩
                    · rcases hunaccepted with ⟨_, _, _, _, _, _, _, _, hpost, _⟩
                      rw [hpost]
                      exact ⟨hloggedZero, hloggedOrigin, hloggedPair, hloggedDates⟩
                    · rcases haccepted with ⟨_, _, _, _, _, _, _, accepted, recovered,
                        _, _, _, _, _, _, _, _, _, hpost⟩
                      rw [hpost]
                      refine ⟨?_, Or.inr rfl, ?_, ?_⟩
                      · intro hnone
                        cases hnone
                      · exact List.Pairwise.nil
                      · intro z hz
                        simp only [List.not_mem_nil] at hz
                  have hnext : cut.output.next.followers i = .ordinary post memory := by
                    calc
                      cut.output.next.followers i = (cut.output.followers i).configuration := by
                        rw [cut.output_eq]
                        rfl
                      _ = .ordinary post memory := by rw [houtput]
                  refine ⟨?_, hcredit, old, post, memory, hinput, ?_, ?_, ?_,
                    hstatus, hdomain, ?_, hdeltaBound, hpostFacts.1, hpostFacts.2.1,
                    hpostFlag, hpostFacts.2.2.1, ?_⟩
                  · simpa only [Nat.add_sub_cancel] using hstarted
                  · rw [houtput]
                  · rw [houtput]
                  · exact hnext
                  · simpa only [Nat.add_sub_cancel] using hmass
                  · simpa only [Nat.add_assoc] using hpostFacts.2.2.2

end Bandits.Support.ReferenceFirstReplacementCollectionSeedEndpoint

end
