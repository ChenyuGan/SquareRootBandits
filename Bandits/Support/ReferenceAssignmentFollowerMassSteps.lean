/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown
public import Bandits.Support.ReferenceFirstReplacementInstalledCredit

import Mathlib.Algebra.Order.BigOperators.Group.List
import Lean.Elab.Tactic.Omega

/-!
# Conditional numerical and status steps for actual assignment followers

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64` and
`sources/zip4/manuscript/06_interruptions.tex:255-282,303-348,355-390`.

This module proves only local follower-side induction steps and actual
launch/no-DOWN base cases. Birth credit is explicit and paired with the same
stored record; the simultaneous all-assignment fold and its historical
installation join remain outside this module.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceAssignmentFollowerMassSteps

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual crossing produces the first numerical seed on the computed
launch state. All original buffers and private inputs are retained. -/
theorem actual_launch_mass_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hc
    let s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    initial.coordinator = .first ∧ allActiveAtStart initial s ∧
      ∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        initial.followers i = .ordinary F memory →
        F.lastDown = none ∧ F.S = 0 ∧ F.delta = 0 ∧ F.backlog = 0 ∧
          F.status = .unoccupied := by
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  refine ⟨seed.coordinatorFirst, seed.activeAtStart, ?_⟩
  intro i F memory hconfiguration
  have hsame := (seed.configuration i).symm.trans hconfiguration
  have hF : seed.followers i = F :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hsame).1
  subst F
  exact ⟨seed.lastDown_none i, seed.S_zero i, seed.delta_zero i,
    seed.backlog_zero i, seed.unoccupied i⟩

private theorem accepted_total_le
    (records : List (Bool × ℕ)) (bound : ℕ)
    (hcap : ∀ record ∈ records, record.2 ≤ bound) :
    RecordedQueueRun.acceptedTotal records ≤ records.length * bound := by
  have hsum : RecordedQueueRun.acceptedTotal records =
      (records.map RecordedQueueRun.acceptedArrival).sum := by
    clear hcap
    induction records with
    | nil => rfl
    | cons head tail ih =>
        simp only [RecordedQueueRun.acceptedTotal, List.map_cons, List.sum_cons, ih]
  rw [hsum]
  have hbound : ∀ amount ∈ records.map RecordedQueueRun.acceptedArrival,
      amount ≤ bound := by
    intro amount hmem
    obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hmem
    unfold RecordedQueueRun.acceptedArrival
    split
    · exact hcap record hrecord
    · exact Nat.zero_le _
  simpa [nsmul_eq_mul] using
    List.sum_le_length_nsmul (records.map RecordedQueueRun.acceptedArrival) bound hbound

/-- Conservation for the actual carried-buffer recovery. Its checked success
supplies every arrival cap, including the entries with zero arrival. The
only numerical input is the incoming birth credit with its retained base. -/
theorem checked_recovery_mass
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (ell beta : ℕ) (final : ActiveFollowerDownAcceptance.ReplayRegisters)
    (hinterval : M.val.sigma ≤ ell)
    (hcredit : beta + M.val.q ≤ (M.val.sigma - 1) * D p)
    (hchecked : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final) :
    beta + final.registers.1 + final.registers.2 ≤ (ell - 1) * D p ∧
      final.lastService ≤ D p := by
  obtain ⟨hdomain, hregisters, harrivals⟩ :=
    ActiveFollowerDownAcceptance.checkedRecovery_success p rate M logged ell final hchecked
  let records := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
  have hcap : ∀ record ∈ records, record.2 ≤ D p := by
    intro record hrecord
    obtain ⟨arrival, ha, rfl⟩ := List.mem_map.mp hrecord
    exact harrivals arrival ha
  have hlength : records.length = ell - M.val.sigma := by
    dsimp only [records, ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals]
    rw [List.length_map, List.length_map,
      ActiveFollowerDownAcceptance.recoveryRounds_length]
  have htotal := RecordedQueueRun.replay_total (4 * rate.n) (0, M.val.q) records
  have hmass : final.registers.1 + final.registers.2 =
      M.val.q + RecordedQueueRun.acceptedTotal records := by
    rw [hregisters]
    simpa only [ActiveFollowerDownAcceptance.recoveredRegisters, Nat.zero_add] using htotal
  have ha := accepted_total_le records (D p) hcap
  rw [hlength] at ha
  have hsigma := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
  have htimes : M.val.sigma - 1 + (ell - M.val.sigma) = ell - 1 := by omega
  refine ⟨?_, hdomain.2.1⟩
  calc
    beta + final.registers.1 + final.registers.2 =
        (beta + M.val.q) + RecordedQueueRun.acceptedTotal records := by omega
    _ ≤ (M.val.sigma - 1) * D p + (ell - M.val.sigma) * D p :=
      Nat.add_le_add hcredit ha
    _ = (ell - 1) * D p := by rw [← Nat.add_mul, htimes]

/-- An accepted operation retains the actual first-cutoff scan, rather than
an arbitrary endpoint satisfying its box bounds. -/
theorem accepted_down_scan_endpoint
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted : ActiveFollowerDownAcceptance.downTransition
      p i row t observation rate logged =
        .accepted logged after raw M scan registers lastService) :
    scan.endpoint = min
      (FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)) (t.val + 2) := by
  unfold ActiveFollowerDownAcceptance.downTransition at haccepted
  split at haccepted
  · split at haccepted
    · split at haccepted
      · split at haccepted
        · split at haccepted
          · dsimp only at haccepted
            split at haccepted
            · contradiction
            · split at haccepted
              · rename_i haccept
                split at haccepted
                · contradiction
                · cases haccepted
                  exact FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff
                    p rate.eta.val _ t
                    (ActiveFollowerDownAcceptance.acceptedDownStartLE
                      p rate M t logged haccept) _
              · contradiction
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · contradiction

/-- A genuine accepted DOWN simultaneously establishes numerical credit,
the last-service cap, and cutoff status at the output elapsed time. This
includes the round detecting the cutoff and never assumes ordinary survival. -/
theorem accepted_down_mass
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService beta : ℕ)
    (hcredit : beta + M.val.q ≤ (M.val.sigma - 1) * D p)
    (haccepted : ActiveFollowerDownAcceptance.downTransition
      p i row t observation rate logged =
        .accepted logged after raw M scan registers lastService) :
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
    after.lastDown = some M ∧
      beta + after.S + after.backlog ≤ min (t.val + 1) (u - 1) * D p ∧
      after.delta ≤ D p ∧ (after.status = .unoccupied ↔ u ≤ t.val + 1) := by
  have hscan := accepted_down_scan_endpoint i row t observation logged after raw M scan
    registers lastService haccepted
  obtain ⟨_hparsed, hchecked, hinterval, _hcurrent, _hhorizon, _hraw, hafter⟩ :=
    ActiveFollowerDownAcceptance.downTransition_accepted_checked
      p i row t observation rate logged after raw M scan registers lastService haccepted
  obtain ⟨hmass, hdelta⟩ := checked_recovery_mass M logged scan.endpoint beta
    ⟨registers, lastService⟩ hinterval.le hcredit hchecked
  dsimp only at hmass hdelta ⊢
  have hpred : scan.endpoint - 1 = min (t.val + 1)
      (FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) - 1) := by
    rw [hscan]
    omega
  rw [hafter]
  refine ⟨rfl, ?_, hdelta, ?_⟩
  · change beta + registers.1 + registers.2 ≤ _
    rw [← hpred]
    exact hmass
  · dsimp only
    split
    · rename_i heq
      have hnot : ¬ FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val + 1 := by
        omega
      constructor
      · intro h
        cases h
      · intro h
        exact (hnot h).elim
    · rename_i hne
      have hle : FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val + 1 := by
        omega
      exact iff_of_true rfl hle

/-- The same calculation on an actual retained diagnostic. The row and time
are the original physical record's inputs; no replay run is substituted. -/
theorem record_accepted_down_mass
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService beta : ℕ)
    (hcredit : beta + M.val.q ≤ (M.val.sigma - 1) * D p)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService) :
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)
    after.lastDown = some M ∧
      beta + after.S + after.backlog ≤ min (record.input.time.val + 1) (u - 1) * D p ∧
      after.delta ≤ D p ∧
      (after.status = .unoccupied ↔ u ≤ record.input.time.val + 1) := by
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    record i logged cut after raw M scan registers lastService hinput hdown haccepted
  have halignment := record.output.preparation.follower_alignment i
  rw [halignment.1, halignment.2.1, halignment.2.2.1] at htransition
  exact accepted_down_mass i record.input.row record.input.time _ logged after raw M
    scan registers lastService beta hcredit htransition

/-- Accepted UP fields use the ordinary CHOICE state and its input frame.
Ordinariness of the sender's output on the receipt round is unnecessary.
The input inequality is an explicit local numerical induction hypothesis. -/
theorem accepted_up_mass_of_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (u beta : ℕ)
    (hinput : ∀ (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      record.input.state.followers i = .ordinary F memory →
      beta + F.S + F.backlog ≤ min record.input.time.val (u - 1) * D p ∧ F.delta ≤ D p)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M) :
    beta + M.val.S + M.val.q ≤ (u - 1) * D p ∧ M.val.delta ≤ D p := by
  obtain ⟨sender, state, memory, hsender, hindex, hconfiguration, _hunoccupied,
    _hoffer, _hsigma, _hledger, hS, hdelta, hq, _hprior, _hpositive, _hslot⟩ :=
    ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  have hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
    rw [hindex, ← hsender]
    exact hconfiguration
  obtain ⟨before, beforeMemory, hbefore, hreply, _hstatus⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice record i state memory hchoice
  have hscore : state.S = before.S := congrArg (fun value => value.2.1) hreply
  have hservice : state.delta = before.delta := congrArg (fun value => value.2.2.1) hreply
  have hqueue : state.backlog = before.backlog := congrArg (fun value => value.2.2.2) hreply
  obtain ⟨hmass, hcap⟩ := hinput before beforeMemory hbefore
  rw [hS, hq, hscore, hqueue, hdelta, hservice]
  exact ⟨hmass.trans (Nat.mul_le_mul_right (D p) (min_le_right _ _)), hcap⟩

/-- Checked online service preserves the base-coupled cutoff budget. An
unoccupied CHOICE freezes numerical fields; an occupied CHOICE consumes one
arrival, including enabled zero arrivals. The cutoff status is a local input,
to be proved jointly with the original-run numerical induction. -/
theorem service_mass_of_choice_cutoff
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n
      i row activation t observation choice)
    (u beta : ℕ)
    (hcredit : beta + choice.S + choice.backlog ≤ min t.val (u - 1) * D p)
    (hcutoff : choice.status = .unoccupied ↔ u ≤ t.val + 1) :
    beta + result.output.S + result.output.backlog ≤ min (t.val + 1) (u - 1) * D p ∧
      result.output.delta ≤ D p := by
  classical
  by_cases hunoccupied : choice.status = .unoccupied
  · have houtput : result.output = choice := by
      rw [result.queueUpdate]
      simp [ActiveFollowerQueueOperation.serviceOutput, hunoccupied,
        ActiveRoundActions.FollowerStatus.occupied]
    rw [houtput]
    exact ⟨hcredit.trans (Nat.mul_le_mul_right (D p) (min_le_min (Nat.le_succ _) le_rfl)),
      result.inputDomain.2.1⟩
  · have hnotcutoff : ¬ u ≤ t.val + 1 := fun h => hunoccupied (hcutoff.mpr h)
    have hinputMin : min t.val (u - 1) = t.val := min_eq_left (by omega)
    have houtputMin : min (t.val + 1) (u - 1) = t.val + 1 := min_eq_left (by omega)
    rw [hinputMin] at hcredit
    rw [houtputMin]
    have houtput : result.output =
        ActiveFollowerQueueOperation.serviceUpdate rate.n choice result.arrival := by
      rw [result.queueUpdate]
      unfold ActiveFollowerQueueOperation.serviceOutput
      cases hs : choice.status with
      | unoccupied => exact (hunoccupied hs).elim
      | pending => simp [ActiveRoundActions.FollowerStatus.occupied]
      | released => simp [ActiveRoundActions.FollowerStatus.occupied]
    rw [houtput]
    obtain ⟨hS, hdelta, hbacklog⟩ :=
      ActiveFollowerQueueOperation.serviceUpdate_register_equations rate.n choice result.arrival
    have htotal : beta +
        (ActiveFollowerQueueOperation.serviceUpdate rate.n choice result.arrival).S +
        (ActiveFollowerQueueOperation.serviceUpdate rate.n choice result.arrival).backlog =
        beta + choice.S + choice.backlog + result.arrival := by omega
    constructor
    · rw [htotal, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add hcredit result.arrival_le_D
    · rw [hdelta]
      exact (min_le_left _ _).trans (ActiveFollowerDownAcceptance.four_n_le_D p rate)

private theorem first_cutoff_at_next_iff
    (sigma t stamp : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (hstamp : stamp.val + 1 = t.val) (hstarted : sigma.val < t.val)
    (hbefore : t.val < FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)) :
    FollowerCutoffScan.firstCutoff p rate.eta.val sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val + 1 ↔
      FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp = true := by
  constructor
  · intro hle
    have heq : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = t.val + 1 := by omega
    have hmem : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ∈
        FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := Finset.min'_mem _ _
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with hgrid | hproposal
    · exact Or.inl hgrid.symm
    · obtain ⟨index, hindex, hend⟩ := Finset.mem_image.mp hproposal
      have hbit := (Finset.mem_filter.mp hindex).2
      have hindexEq : index = stamp := by
        apply Fin.ext
        change index.val + 2 = t.val + 1 at hend
        omega
      exact Or.inr (hindexEq ▸ hbit)
  · intro hcause
    apply Finset.min'_le
    rcases hcause with hgrid | hbit
    · rw [← hgrid]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨stamp, Finset.mem_filter.mpr ⟨?_, hbit⟩, ?_⟩
      · simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor <;> omega
      · change stamp.val + 2 = t.val + 1
        omega

/-- A successful CHOICE uses exactly the original previous proposal token.
Its cutoff status advances from `u ≤ e` to `u ≤ e + 1`, including the
detecting round, while the numerical reply fields remain framed by the
existing start-round theorem. -/
theorem start_round_cutoff_status
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : before.lastDown = some M)
    (hstatus : before.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val)
    (htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = t.val ∧ memory.lastProposalRead = some ⟨stamp,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t before memory = .ok (choice, choiceMemory)) :
    choice.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val + 1 := by
  classical
  have hregs : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hnot
    simp [ActiveFollowerLifecycle.startRound, ActiveFollowerLifecycle.interruptionDecision, hnot] at hstart
  by_cases hunoccupied : before.status = .unoccupied
  · rw [ActiveFollowerLifecycle.startRound_unoccupied rate.eta t before memory hregs hunoccupied]
      at hstart
    have hchoice := (Prod.mk.inj (Except.ok.inj hstart)).1.symm
    rw [hchoice]
    exact iff_of_true hunoccupied ((hstatus.mp hunoccupied).trans (Nat.le_succ _))
  · obtain ⟨stamp, hstamp, hread⟩ := htoken hunoccupied
    have hbound : t.val < FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := by
      have hnot : ¬ FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val :=
        fun h => hunoccupied (hstatus.mpr h)
      omega
    have hstarted : M.val.sigma ≤ t.val := by
      by_contra hnot
      have hfailure := ActiveFollowerLifecycle.interruptionDecision_incompatible_start
        rate.eta t before memory hunoccupied hregs M hdown (Nat.lt_of_not_ge hnot)
      simp [ActiveFollowerLifecycle.startRound, hfailure] at hstart
    have hfirst := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
      rate.sourceCap (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
    have hnotmissed : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
      change t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
      omega
    have hstartEq := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta t before memory
      hunoccupied hregs M hdown hstarted hnotmissed
      ⟨stamp, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩ hread hstamp
    rw [hstartEq] at hstart
    have hchoice := (Prod.mk.inj (Except.ok.inj hstart)).1.symm
    rw [hchoice]
    dsimp only
    have hsigma := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    have hcutoff := first_cutoff_at_next_iff (ActiveFollowerDownAcceptance.downStart p rate M)
      t stamp row hstamp (by omega) hbound
    change (if decide (FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M) = t.val + 1) ||
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp then
        ActiveRoundActions.FollowerStatus.unoccupied else before.status) = .unoccupied ↔ _
    by_cases hcut : FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ t.val + 1
    · rcases hcutoff.mp hcut with hgrid | hbit
      · simp [hgrid, hcut]
      · simp [hbit, hcut]
    · have hgrid : ¬ FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M) = t.val + 1 :=
        fun h => hcut (hcutoff.mpr (Or.inl h))
      have hbit : ¬ FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp = true :=
        fun h => hcut (hcutoff.mpr (Or.inr h))
      simp [hgrid, hbit, hunoccupied, hcut]

/-- Successful occupied FINISH produces its proposal token from the actual
row coordinate. No token, record, or register-domain premise is supplied. -/
theorem finish_round_occupied_token
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (before next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : ActiveFollowerLifecycle.finishRound rate.eta t row before memory = .ok (next, nextMemory))
    (hoccupied : next.status ≠ .unoccupied) :
    nextMemory.lastProposalRead =
      some ⟨t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩ := by
  have hstate := ActiveFollowerLifecycle.finishRound_frame rate.eta t row before next
    memory nextMemory hfinish
  subst next
  classical
  by_cases hregs : ActiveFollowerLifecycle.localStateDomainValid before
  · cases hdown : before.lastDown with
    | none =>
        rw [ActiveFollowerLifecycle.finishRound_missing_record rate.eta t row before
          memory hoccupied hregs hdown] at hfinish
        cases hfinish
    | some M =>
        by_cases htime : M.val.sigma ≤ t.val + 1
        · rw [ActiveFollowerLifecycle.finishRound_occupied_read rate.eta t row before memory
            hoccupied hregs M hdown htime] at hfinish
          have hmemory := (Prod.mk.inj (Except.ok.inj hfinish)).2
          exact congrArg ActiveFollowerLifecycle.LocalMemory.lastProposalRead hmemory.symm
        · rw [ActiveFollowerLifecycle.finishRound_incompatible_start rate.eta t row before
            memory hoccupied hregs M hdown (Nat.lt_of_not_ge htime)] at hfinish
          cases hfinish
  · rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta t row before memory hregs] at hfinish
    cases hfinish

/-- The occupied output of an actual round saves the actual row bit, even
when release changes pending into released. Dagger outputs are not asserted
to survive this or any subsequent round. -/
theorem record_output_proposal_token
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hoccupied : next.status ≠ .unoccupied) :
    nextMemory.lastProposalRead = some ⟨record.input.time,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩ := by
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration = _ at hout
  obtain ⟨choice, memory, post, _hchoice, _hrecord, hrelease, _hdownInput, _hdown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  have halignment := (ReferenceActivePhysicalStep.prepare input).follower_alignment i
  rw [halignment.1, halignment.2.1, halignment.2.2.1] at hrelease
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hrelease
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i input.time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow input.row input.time)
      ((ReferenceActivePhysicalStep.prepare input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post with
  | error reason => simp only [hr] at hrelease; cases hrelease
  | ok released =>
      have hfinish : ActiveFollowerLifecycle.finishRound rate.eta input.time input.row
          released memory = .ok (next, nextMemory) := by
        cases he : ActiveFollowerLifecycle.finishRound rate.eta input.time input.row released memory with
        | error reason => simp only [hr, he] at hrelease; cases hrelease
        | ok pair =>
            exact congrArg Except.ok (by
              simpa only [hr, he, Except.ok.injEq] using hrelease)
      exact finish_round_occupied_token input.time input.row released next memory nextMemory
        hfinish hoccupied

/-- Original computed prefix timestamps, without a launch or survival input.
The finite index already excludes empty no-launch and terminal suffixes. -/
theorem complete_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  have hvalues := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hk : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h]
    exact k.isLt
  have hget := congrArg (fun values : List ℕ => values[k.val]?) hvalues
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hk, Nat.one_mul] at hget
  exact Option.some.inj hget

/-- On every ordinary original-run input without an accepted DOWN, all three
numerical registers remain zero and the follower remains unoccupied. The
actual launch supplies the seed and ordinary chronology supplies the frame;
no zero-register or survival family is a root input. -/
theorem complete_no_down_input
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (i : Fin (p.m - 1))
    (F : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary F memory)
    (hnone : F.lastDown = none) :
    F.S = 0 ∧ F.delta = 0 ∧ F.backlog = 0 ∧ F.status = .unoccupied := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hempty : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = [] := by
        simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch, ↓reduceDIte]
      have hk := k.isLt
      simp only [hempty, List.length_nil] at hk
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have span : s + (p.T - s) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
        dsimp only [s]
        omega
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      let execution := run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (p.T - s) span seed.activeAtStart
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hk : k.val < execution.records.length := by rw [← hrun]; exact k.isLt
      have hinput : execution.records[k.val].input.state.followers i = .ordinary F memory := by
        simpa only [hrun] using hordinary
      have chain := ReferenceFollowerReplyChronology.connected_take_to_input execution.connected k.val hk
      obtain ⟨old, oldMemory, hconfiguration, _hstart, hkeep, _horigin⟩ :=
        ReferenceFollowerReplyChronology.connected_ordinary_chronology chain i F memory hinput
      have hsame : seed.followers i = old :=
        (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          ((seed.configuration i).symm.trans hconfiguration)).1
      subst old
      have hzeroStart : ReferencePrelaunchFollower.acceptedStart F = 0 := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hnone]
      obtain ⟨hunoccupied, hreply⟩ := hkeep (seed.unoccupied i)
        ((seed.acceptedStart_zero i).trans hzeroStart.symm)
      have hS : F.S = (seed.followers i).S := congrArg (fun value => value.2.1) hreply
      have hdelta : F.delta = (seed.followers i).delta := congrArg (fun value => value.2.2.1) hreply
      have hqueue : F.backlog = (seed.followers i).backlog := congrArg (fun value => value.2.2.2) hreply
      exact ⟨hS.trans (seed.S_zero i), hdelta.trans (seed.delta_zero i),
        hqueue.trans (seed.backlog_zero i), hunoccupied⟩

end Bandits.Support.ReferenceAssignmentFollowerMassSteps

end
