/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerTerminalReplyAssembly
import Lean.Elab.Tactic.Omega

/-!
# Numerical replay at the actual accepted terminal UP reply

This joins the accepted terminal reply assembly to the exact finite-list
replay of the same complete-row cells. The replay starts from the retained
DOWN queue field `M.val.q`; it does not identify that payload-relative field
with a global queue. Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-168`,
`sources/zip4/manuscript/05_binary_transport.tex:64-70`, and
`sources/zip4/manuscript/06_interruptions.tex:192-233,329-348`.
-/
@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerTerminalUpNumericalReplay

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

private theorem take_split_at {α : Type} (xs : List α) (d n : ℕ)
    (hdn : d ≤ n) (hn : n ≤ xs.length) :
    xs.take n = xs.take d ++ (xs.drop d).take (n - d) := by
  have hdl : d ≤ xs.length := hdn.trans hn
  rw [← List.take_append_drop d xs, List.take_append]
  rw [List.take_of_length_le (show (xs.take d).length ≤ n by
    simp [List.length_take, Nat.min_eq_left hdl, hdn])]
  simp [List.length_take, Nat.min_eq_left hdl]

private theorem replay_suffix_eq_prefix (capacity : ℕ)
    (initial : ℕ × ℕ) (xs : List (Bool × ℕ))
    (d n : ℕ) (hdn : d ≤ n) (hn : n ≤ xs.length) :
    QueueReplay.replay capacity
        (QueueReplay.replay capacity initial (xs.take d))
        ((xs.drop d).take (n - d)) =
      QueueReplay.replay capacity initial (xs.take n) := by
  rw [← QueueReplay.replay_append]
  congr 1
  exact (take_split_at xs d n hdn hn).symm

/-- The actual accepted terminal UP reply, with its original recovery,
calendar, choice, and source-cell witnesses, has the numerical fields given
by replaying its complete-row list from the queue in the selected DOWN
payload. The same selected terminal choice supplies both the protocol and
replay identifications. -/
theorem complete_accepted_up_terminal_up_numerical_replay
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      let P := c.payload
      let M := P.downRecord i
      let a := P.assignment.assigned i
      let sigma := P.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
      let ell := min u (R[j.val].input.time.val + 2)
      let N := u - sigma
      let d := ell - sigma
      let z := max (b.val + N) (j.val + 1)
      let L := (R.drop b.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = P.queues a ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun r => r.input.time.val + 1) = List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ n : Fin N, Selection
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
        (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
        (∀ n, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload
              (v n).view.cutoff (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
        (∀ n f, (ReferenceFollowerFixedReply.actualChoice
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
          .ordinary
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
            (ReferenceLaterLiveNumericalReadout.preparedMemories
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)) ∧
        let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
          ReferenceFirstWindowNumericalStream.sourceCell
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
            (v n).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
            (v n).view.complementWeights (v n).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
        let A := List.ofFn (fun n : Fin N =>
          ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        let Ed := ((R.drop b.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
        ∃ hz : z < R.length, z ≤ k.val ∧
          ∃ (terminal : ReferencePrelaunchFollower.State p rate.eta)
            (terminalMemory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
              .ordinary terminal terminalMemory ∧
            terminal.status = .unoccupied ∧ terminal.lastDown = some M ∧
            (terminal.S, terminal.backlog) = W N ∧
            terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) ∧
            U.val.sigma = sigma ∧ U.val.S = terminal.S ∧
            U.val.delta = terminal.delta ∧ U.val.q = terminal.backlog ∧
            (U.val.S, U.val.q) = QueueReplay.replay cap (0, M.val.q) A ∧
            U.val.delta =
              (QueueReplay.replay cap (0, M.val.q) A).1 -
                (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal⟩ :=
    ReferenceCompleteFollowerTerminalReplyAssembly.complete_accepted_up_terminal_reply
      (rate := rate) rewards C_star C_h source k i U hacc
  let P := c.payload
  let M := P.downRecord i
  let a := P.assignment.assigned i
  let sigma := P.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let ell := min u (R[j.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
      (v n).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
      (v n).view.complementWeights (v n).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
  let A := List.ofFn (fun n : Fin N =>
    ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
  let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
  let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
  change d ≤ N at hdle
  change A.length = N at hAlen
  change registers = V d at hregisters
  have hregistersExplicit : registers =
      QueueReplay.replay cap (0, M.val.q) (A.take d) := hregisters
  change lastService = (V d).1 - (V (d - 1)).1 at hlastService
  change (terminal.S, terminal.backlog) = W N at hterminalRegisters
  change terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService)
    at hterminalDelta
  have hW_eq (n : ℕ) (hdn : d ≤ n) (hn : n ≤ N) : W n = V n := by
    dsimp only [W, V]
    rw [hregistersExplicit]
    exact replay_suffix_eq_prefix cap (0, M.val.q) A d n hdn
      (by rw [hAlen]; exact hn)
  have htakeN : A.take N = A := List.take_of_length_le (by rw [hAlen])
  have hVN : V N = QueueReplay.replay cap (0, M.val.q) A := by
    simp only [V, htakeN]
  have hVprev : V (N - 1) =
      QueueReplay.replay cap (0, M.val.q) (A.take (N - 1)) := rfl
  have hNpos : 0 < N := lt_of_lt_of_le hdpos hdle
  have hNprev : N - 1 < N := by omega
  have hWN := hW_eq N hdle le_rfl
  have hterminalReplay : (terminal.S, terminal.backlog) =
      QueueReplay.replay cap (0, M.val.q) A := by
    calc
      (terminal.S, terminal.backlog) = W N := hterminalRegisters
      _ = V N := hWN
      _ = QueueReplay.replay cap (0, M.val.q) A := hVN
  have hUNumerical : (U.val.S, U.val.q) =
      QueueReplay.replay cap (0, M.val.q) A := by
    rw [hUSterminal, hUqterminal]
    exact hterminalReplay
  have hUDNumerical : U.val.delta =
      (QueueReplay.replay cap (0, M.val.q) A).1 -
        (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := by
    by_cases htail : d < N
    · have hdprev : d ≤ N - 1 := by omega
      have hWprev := hW_eq (N - 1) hdprev hNprev.le
      calc
        U.val.delta = terminal.delta := hUdterminal
        _ = (W N).1 - (W (N - 1)).1 := by
          simpa only [ite_eq_left htail] using hterminalDelta
        _ = (V N).1 - (V (N - 1)).1 := by rw [hWN, hWprev]
        _ = (QueueReplay.replay cap (0, M.val.q) A).1 -
              (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := by
          rw [hVN, hVprev]
    · have hdEq : d = N := by omega
      calc
        U.val.delta = terminal.delta := hUdterminal
        _ = lastService := by
          simpa only [ite_eq_right htail] using hterminalDelta
        _ = (V N).1 - (V (N - 1)).1 := by
          simpa only [hdEq] using hlastService
        _ = (QueueReplay.replay cap (0, M.val.q) A).1 -
              (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 := by
          rw [hVN, hVprev]
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical⟩

end Bandits.Support.ReferenceCompleteFollowerTerminalUpNumericalReplay
