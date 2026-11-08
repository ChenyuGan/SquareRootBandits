/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix

/-!
# Actual generated prelaunch DOWN birth bounds

The results here bound the birth read from the actual generated prelaunch
prefix, stopped ordinary state, and terminal ordinary state. A nonempty
completed bank is witnessed by its actual last quota batch and stamped last
entry. No calendar transport or historical cohort characterization is claimed.

Source ranges: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownBirthBounds

open ConstructorDimensions BootstrapDimensions
open ReferenceInitializationRun ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open GeneratedBootstrapRoundLaw ActualReferenceInitializationBlock
open AffineBatchDecoder
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem last_list_index {α : Type} (l : List α) (hne : l ≠ []) :
    ∃ k : Fin l.length, k.val + 1 = l.length ∧
      l[k] = l.getLast hne ∧ l.getLast? = some l[k] := by
  let k : Fin l.length := ⟨l.length - 1, by
    have hlength : 0 < l.length := (List.length_pos_iff_ne_nil).2 hne
    omega⟩
  have hlength : 0 < l.length := (List.length_pos_iff_ne_nil).2 hne
  have hget : l[k] = l.getLast hne := by
    dsimp [k]
    exact List.get_length_sub_one k.isLt
  refine ⟨k, ?_, hget, ?_⟩
  · change (l.length - 1) + 1 = l.length
    omega
  · calc
      l.getLast? = some (l.getLast hne) :=
        List.getLast?_eq_getLast_of_ne_nil hne
      _ = some l[k] := congrArg some hget.symm

private theorem run_completed_le (x : ReferenceInitializationRun.Input p) (n : ℕ) :
    (ReferenceInitializationRun.run x n).completed ≤ n := by
  induction n with
  | zero => simp [ReferenceInitializationRun.run, ReferenceInitializationRun.initial]
  | succ n ih =>
      rw [ReferenceInitializationRun.run_succ]
      by_cases hc : (ReferenceInitializationRun.run x n).crossing.isSome = true
      · rw [ReferenceInitializationRun.advance_of_crossing x _ hc]
        exact Nat.le_succ_of_le ih
      · have hcross : (ReferenceInitializationRun.run x n).crossing = none := by
          cases h : (ReferenceInitializationRun.run x n).crossing <;> simp_all
        by_cases h : (ReferenceInitializationRun.run x n).completed < n_boot p
        · rw [ReferenceInitializationRun.advance_of_no_crossing x _ hcross h]
          change (ReferenceInitializationRun.run x n).completed + 1 ≤ n + 1
          omega
        · rw [ReferenceInitializationRun.advance_of_exhausted x _
            (Nat.le_of_not_gt h)]
          exact Nat.le_succ_of_le ih

private theorem replay_bank_birth_bound
    (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : Activation p)
    (n : ℕ) (history : LocalHistory p n) (hn : n ≤ p.T)
    (ha : a.val ≤ n + 1) :
    ∃ beta,
      bankBirth a (ReferencePrelaunchFollower.replay eta i row a history hn).downBatch =
        some beta ∧
      beta ≤ n ∧
      ((ReferencePrelaunchFollower.replay eta i row a history hn).downBatch.completed =
          [] ∧ beta = a.val - 1 ∨
        ∃ batch e,
            (ReferencePrelaunchFollower.replay eta i row a history hn).downBatch.completed.getLast? =
              some batch ∧
            batch ∈ (ReferencePrelaunchFollower.replay eta i row a history hn).downBatch.completed ∧
            batch.length = AffineBatchDecoder.quota p ∧
            batch.getLast? = some e ∧ e ∈ batch ∧
            beta = e.time.val + 1 ∧ e.time.val < n) := by
  classical
  let replay := ReferencePrelaunchFollower.replay eta i row a history hn
  let bank := replay.downBatch
  by_cases hempty : bank.completed = []
  · refine ⟨a.val - 1, ?_, ?_, Or.inl ⟨hempty, rfl⟩⟩
    · unfold bankBirth
      rw [hempty]
      rfl
    · omega
  · let batch := bank.completed.getLast hempty
    have hlast := List.getLast?_eq_getLast_of_ne_nil hempty
    have hbatch : batch ∈ bank.completed := List.getLast_mem hempty
    have hbatchSpec := ReferencePrelaunchFollower.replay_completed_provenance
      eta i row a history hn batch hbatch
    have hbatchLength : batch.length = AffineBatchDecoder.quota p := by
      exact hbatchSpec.1
    have hbatchNe : batch ≠ [] :=
      (List.length_pos_iff_ne_nil).mp (by rw [hbatchLength]; exact AffineBatchDecoder.quota_pos p)
    let entry := batch.getLast hbatchNe
    have hentryLast : batch.getLast? = some entry :=
      List.getLast?_eq_getLast_of_ne_nil hbatchNe
    have hentryMem : entry ∈ batch := List.getLast_mem hbatchNe
    have hentryOrigin := hbatchSpec.2 entry hentryMem
    rcases hentryOrigin with ⟨u, _, _, _, _, htime, _⟩
    have htimeBound : entry.time.val < n := by
      rw [htime]
      exact u.isLt
    have hbirth : bankBirth a bank = some (entry.time.val + 1) := by
      have hnotEmpty : bank.completed.isEmpty = false := by
        cases h : bank.completed with
        | nil => exact False.elim (hempty h)
        | cons head tail => rfl
      unfold bankBirth
      rw [hnotEmpty, hlast]
      simp only [Option.bind_some]
      change Option.map (fun e => e.time.val + 1) batch.getLast? = _
      rw [hentryLast]
      rfl
    refine ⟨entry.time.val + 1, ?_, ?_, Or.inr ⟨batch, entry, hlast,
      hbatch, hbatchLength, hentryLast, hentryMem, rfl, htimeBound⟩⟩
    · exact hbirth
    · omega

private theorem terminal_bank_birth_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (a : Activation p)
    (ha : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).activation
        (refFollower i) = some a) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let bank := (ReferenceInitializationRun.ordinary x b (refFollower i)).downBatch
    ∃ beta, bankBirth a bank = some beta ∧
      beta ≤ ReferenceInitializationRun.elapsed p b.completed ∧
      ((bank.completed = [] ∧ beta = a.val - 1) ∨
        ∃ batch e,
            bank.completed.getLast? = some batch ∧
            batch ∈ bank.completed ∧ batch.length = AffineBatchDecoder.quota p ∧
            batch.getLast? = some e ∧ e ∈ batch ∧
            beta = e.time.val + 1 ∧ e.time.val < ReferenceInitializationRun.elapsed p b.completed) := by
  classical
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  let f := refFollower i
  let bank := (ReferenceInitializationRun.ordinary x b f).downBatch
  have hcohorts := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
    rate rewards C_star C_h z i
  rcases hcohorts with ⟨_, _, hquota, _⟩
  have horigins := source_prelaunch_down_terminal_actual_origins
    rate rewards C_star C_h z i
  rcases horigins with ⟨_, horigin⟩
  by_cases hempty : bank.completed = []
  · refine ⟨a.val - 1, ?_, ?_, Or.inl ⟨hempty, rfl⟩⟩
    · unfold bankBirth
      rw [hempty]
      rfl
    · have hactivation := (ReferenceInitializationRun.output x).activation_le f a ha
      have hbound : a.val - 1 ≤ ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output x).completed := by
        omega
      simpa only [b] using hbound
  · obtain ⟨k, hklast, _, hlast⟩ := last_list_index bank.completed hempty
    let batch := bank.completed[k.val]'k.isLt
    have hbatch : batch ∈ bank.completed := by
      dsimp [batch]
      exact List.getElem_mem k.isLt
    have hbatchLength : batch.length = AffineBatchDecoder.quota p :=
      (hquota k.val k.isLt).2
    rcases horigin k.val k.isLt with ⟨t, ht, hentryLast, _⟩
    let entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
      ⟨t, (x.row.2 t).2 (0, i)⟩
    have hentryLast' : batch.getLast? = some entry := by
      simpa only [batch, entry] using hentryLast
    have hbatchNe : batch ≠ [] :=
      (List.length_pos_iff_ne_nil).mp (by rw [hbatchLength]; exact AffineBatchDecoder.quota_pos p)
    have hentryEq : entry = batch.getLast hbatchNe :=
      Option.some.inj (hentryLast'.symm.trans
        (List.getLast?_eq_getLast_of_ne_nil hbatchNe))
    have hentryMem : entry ∈ batch := hentryEq ▸ List.getLast_mem hbatchNe
    have hbirth : bankBirth a bank = some (entry.time.val + 1) := by
      have hnotEmpty : bank.completed.isEmpty = false := by
        cases h : bank.completed with
        | nil => exact False.elim (hempty h)
        | cons head tail => rfl
      unfold bankBirth
      rw [hnotEmpty, hlast]
      simp only [Option.bind_some]
      change Option.map (fun e => e.time.val + 1) batch.getLast? = _
      rw [hentryLast']
      rfl
    have htimeBound : entry.time.val < ReferenceInitializationRun.elapsed p b.completed := by
      change t.val < ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed
      exact ht
    refine ⟨entry.time.val + 1, hbirth, Nat.succ_le_of_lt htimeBound,
      Or.inr ⟨batch, entry, hlast, hbatch, hbatchLength,
        hentryLast', hentryMem, rfl, htimeBound⟩⟩

/-- The actual prefix bank has a bounded birth. Empty completed banks retain
the activation birth; otherwise the witness is the real last quota batch and
its real last stamped test. Inactive prefixes retain absence. -/
theorem source_prelaunch_down_prefix_birth_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let a := active.val.2.1
        let bank := active.val.2.2.2.downBatch
        ∃ beta, bankBirth a bank = some beta ∧ beta ≤ r.val ∧
          ((bank.completed = [] ∧ beta = a.val - 1) ∨
            ∃ batch e,
                bank.completed.getLast? = some batch ∧
                batch ∈ bank.completed ∧ batch.length = AffineBatchDecoder.quota p ∧
                batch.getLast? = some e ∧ e ∈ batch ∧
                beta = e.time.val + 1 ∧ e.time.val < r.val)
    | .inl (.inr _) =>
        source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r = none
    | .inr stopped =>
        (stopped.val.1.activation (refFollower i) = none →
          source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r = none) ∧
        (∀ a, stopped.val.1.activation (refFollower i) = some a →
          ∃ beta, bankBirth a stopped.val.2.downBatch = some beta ∧
            beta ≤ ReferenceInitializationRun.elapsed p stopped.val.1.completed ∧
            ReferenceInitializationRun.elapsed p stopped.val.1.completed ≤ r.val ∧
            ((stopped.val.2.downBatch.completed = [] ∧ beta = a.val - 1) ∨
              ∃ batch e,
                  stopped.val.2.downBatch.completed.getLast? = some batch ∧
                  batch ∈ stopped.val.2.downBatch.completed ∧
                  batch.length = AffineBatchDecoder.quota p ∧
                  batch.getLast? = some e ∧ e ∈ batch ∧
                  beta = e.time.val + 1 ∧
                  e.time.val < ReferenceInitializationRun.elapsed p stopped.val.1.completed)) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := refFollower i
  cases hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          let a := active.val.2.1
          let history := active.val.2.2.1
          let state := active.val.2.2.2
          have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
          rw [hprefix] at hcensus
          rcases hcensus with ⟨_, _, hquota, _⟩
          rcases active.property with ⟨_, hactivation, hstate, _⟩
          have hcompleted : active.val.1.val.completed =
              (roundBlockIndex p r).val := by
            have hrun := active.val.1.property.2.2
            have hboundaryCross := congrArg
              (fun b : ReferenceInitializationRun.Boundary p => b.crossing) hrun
            have hcross : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing = none := by
              rw [← hboundaryCross]
              exact active.val.1.property.2.1
            have hprogress := ReferenceInitializationRun.run_progress x
              (roundBlockIndex p r).val (roundBlockIndex p r).isLt.le
            have hrunCompleted := hprogress.resolve_left (by simp [hcross])
            exact (congrArg ReferenceInitializationRun.Boundary.completed hrun).trans hrunCompleted
          have hblock := round_mem_quotient_block p r
          have hstart := GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
            (s := roundBlockIndex p r) (t := r) hblock
          have hactivationLe := active.val.1.val.activation_le f a hactivation
          rw [hcompleted] at hactivationLe
          have ha : a.val ≤ r.val + 1 := by
            exact hactivationLe.trans (Nat.add_le_add_right hstart 1)
          obtain ⟨beta, hbirth, hbound, horigin⟩ :=
            replay_bank_birth_bound rate.eta i x.row a r.val history
              (Nat.le_of_lt r.isLt) ha
          have hbank : state.downBatch =
              (ReferencePrelaunchFollower.replay rate.eta i x.row a history
                (Nat.le_of_lt r.isLt)).downBatch := congrArg State.downBatch hstate
          rw [← hbank] at hbirth horigin
          refine ⟨beta, hbirth, hbound, ?_⟩
          rcases horigin with hinitial | ⟨batch, entry, hbatchLast, hbatchMem,
            _, hentryLast, hentryMem, hbeta, htime⟩
          · exact Or.inl (by simpa only [a, state] using hinitial)
          · have hquotaBatch : batch.length = AffineBatchDecoder.quota p :=
              hquota batch hbatchMem
            exact Or.inr ⟨batch, entry, hbatchLast, hbatchMem, hquotaBatch,
              hentryLast, hentryMem, hbeta, htime⟩
      | inr inactive =>
          simp [source_prelaunch_down_prefix_birth, hprefix]
  | inr stopped =>
      have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
      rw [hprefix] at hcensus
      rcases hcensus with ⟨_, _, hquota, _⟩
      have hrun := stopped.property.2.1
      have hboundaryCross := congrArg
        (fun b : ReferenceInitializationRun.Boundary p => b.crossing) hrun
      have hcross : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing.isSome = true := by
        rw [← hboundaryCross]
        cases hc : stopped.val.1.crossing with
        | none => exact False.elim (stopped.property.1 hc)
        | some c => rfl
      have houtput : ReferenceInitializationRun.output x = stopped.val.1 := by
        have hindex : (roundBlockIndex p r).val +
            (n_boot p - (roundBlockIndex p r).val) = n_boot p := by omega
        change ReferenceInitializationRun.run x (n_boot p) = stopped.val.1
        calc
          ReferenceInitializationRun.run x (n_boot p) =
              ReferenceInitializationRun.run x
                ((roundBlockIndex p r).val + (n_boot p - (roundBlockIndex p r).val)) := by
                  rw [hindex]
          _ = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
            ReferenceInitializationRun.run_stops_at_crossing x
              (roundBlockIndex p r).val (n_boot p - (roundBlockIndex p r).val) hcross
          _ = stopped.val.1 := hrun.symm
      have hcompletedLe : stopped.val.1.completed ≤ (roundBlockIndex p r).val := by
        rw [congrArg (fun b : ReferenceInitializationRun.Boundary p => b.completed) hrun]
        exact run_completed_le x (roundBlockIndex p r).val
      have hcalendar := GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
        (s := roundBlockIndex p r) (t := r) (round_mem_quotient_block p r)
      have hElapsedLe : ReferenceInitializationRun.elapsed p stopped.val.1.completed ≤ r.val :=
        (ReferenceInitializationRun.elapsed_mono p hcompletedLe).trans hcalendar
      constructor
      · intro ha
        simp [source_prelaunch_down_prefix_birth, hprefix, ha]
      · intro a ha
        have hactivation : stopped.val.1.activation f = some a := ha
        have hactivationOutput :
            (ReferenceInitializationRun.output x).activation f = some a := by
          exact (congrArg (fun b : ReferenceInitializationRun.Boundary p => b.activation f)
            houtput).trans hactivation
        have hterminal' := terminal_bank_birth_bound rate rewards C_star C_h z i a
          hactivationOutput
        rcases hterminal' with ⟨beta, hbirth, hbound, horigin⟩
        have hstate : stopped.val.2 =
            ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f := by
          simpa only [houtput] using stopped.property.2.2
        have hbank : stopped.val.2.downBatch =
            (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) f).downBatch :=
          congrArg State.downBatch hstate
        rw [← hbank] at hbirth
        have hcompletedOutput := congrArg
          (fun b : ReferenceInitializationRun.Boundary p => b.completed) houtput
        have hboundStopped : beta ≤ ReferenceInitializationRun.elapsed p stopped.val.1.completed := by
          rw [hcompletedOutput] at hbound
          exact hbound
        refine ⟨beta, hbirth, hboundStopped, hElapsedLe, ?_⟩
        rcases horigin with hinitial | ⟨batch, entry, hbatchLast, hbatchMem,
          _, hentryLast, hentryMem, hbeta, htime⟩
        · exact Or.inl (by simpa only [hbank] using hinitial)
        · have hquotaBatch : batch.length = AffineBatchDecoder.quota p :=
            hquota batch (by simpa only [hbank] using hbatchMem)
          have hnonempty :
              stopped.val.2.downBatch.completed.getLast? = some batch := by
            simpa only [hbank] using hbatchLast
          have hbatchMemStopped : batch ∈ stopped.val.2.downBatch.completed := by
            simpa only [hbank] using hbatchMem
          have htimeStopped := htime
          rw [hcompletedOutput] at htimeStopped
          exact Or.inr ⟨batch, entry, hnonempty, hbatchMemStopped, hquotaBatch,
            hentryLast, hentryMem, hbeta, htimeStopped⟩

/-- At the natural endpoint, every activated ordinary DOWN bank has a bounded
birth and an explicit actual initial or last-completion origin. -/
theorem source_prelaunch_down_terminal_birth_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let f := refFollower i
    let bank := (ReferenceInitializationRun.ordinary x b f).downBatch
    ∀ a, b.activation f = some a →
      ∃ beta, bankBirth a bank = some beta ∧
        beta ≤ ReferenceInitializationRun.elapsed p b.completed ∧
        ReferenceInitializationRun.elapsed p b.completed ≤ p.T ∧
        ((bank.completed = [] ∧ beta = a.val - 1) ∨
          ∃ batch e,
              bank.completed.getLast? = some batch ∧
              batch ∈ bank.completed ∧ batch.length = AffineBatchDecoder.quota p ∧
              batch.getLast? = some e ∧ e ∈ batch ∧
              beta = e.time.val + 1 ∧ e.time.val <
                ReferenceInitializationRun.elapsed p b.completed) := by
  classical
  dsimp only
  intro a ha
  obtain ⟨beta, hbirth, hbound, horigin⟩ :=
    terminal_bank_birth_bound rate rewards C_star C_h z i a ha
  exact ⟨beta, hbirth, hbound, ReferenceInitializationRun.elapsed_le_T p _, horigin⟩

/-- A stopped prefix cannot record a new birth at its own later calendar
boundary. The bound comes from the actual unchanged ordinary bank. -/
theorem source_prelaunch_down_stopped_prefix_no_late_birthAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (stopped : StoppedProjection p (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r) i)
    (hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inr stopped)
    (hlate : ReferenceInitializationRun.elapsed p stopped.val.1.completed < r.val) :
    ∀ k, ¬ birthAt rate rewards C_star C_h z i r.val (Nat.le_of_lt r.isLt) k := by
  classical
  intro k hbirthAt
  have hbounds := source_prelaunch_down_prefix_birth_bounds rate rewards C_star C_h z i r
  rw [hprefix] at hbounds
  rw [ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos r.isLt, hprefix] at hbirthAt
  rcases hbirthAt with ⟨a, ha, _, _, hbirth⟩
  rcases hbounds with ⟨_, hboundAtStopped⟩
  rcases hboundAtStopped a ha with ⟨beta, hbank, hbound, _, _⟩
  have hEq : beta = r.val := Option.some.inj (hbank.symm.trans hbirth)
  omega

/-- If the actual run stopped before `T`, its terminal constant bank cannot
masquerade as a new birth at the terminal boundary. -/
theorem source_prelaunch_down_terminal_no_late_birthAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hlate : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).completed < p.T) :
    ∀ k, ¬ birthAt rate rewards C_star C_h z i p.T (Nat.le_refl p.T) k := by
  classical
  intro k hbirthAt
  rw [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
    dif_neg (Nat.lt_irrefl p.T)] at hbirthAt
  rcases hbirthAt with ⟨a, ha, _, _, hbirth⟩
  have hterminal := source_prelaunch_down_terminal_birth_bounds rate rewards C_star C_h z i
  dsimp only at hterminal
  have hbounds := hterminal a ha
  rcases hbounds with ⟨beta, hbank, hbound, _, _⟩
  have hEq : beta = p.T := Option.some.inj (hbank.symm.trans hbirth)
  omega

end Bandits.Support.ReferenceGeneratedPrelaunchDownBirthBounds

end
