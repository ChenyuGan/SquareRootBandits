/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterCollectionArrivalReadout

import Lean.Elab.Tactic.Omega

/-!
# Actual occupied follower cutoff bounds

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,197-209,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:72-88`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-60`.

The induction follows the existing physical run, retaining the actual DOWN
record and the timestamped proposal token produced by its own FINISH. All
claims about ordinary configurations are conditional on those constructors;
failed local operations and dagger remain possible. These are internal timing
bounds, with no numerical recovery identity or manuscript closure claim.

At a zero-based prefix boundary `b`, the invariant is `b + 1 ≤ firstCutoff`.
Its auxiliary token has timestamp `stamp.val + 1 = b`; the first-cutoff
carrier uses one-based endpoints, so a tight proposal endpoint has timestamp
`b - 1`. The final boundary `b = T` is included as a natural number.

The private local helpers explicitly take successful local-call equalities,
occupied statuses, and, for an existing assignment, its prior bound and token.
The physical-record proof obtains those call equalities by ordinary-output
inversion. The run helpers take span, activation, and unoccupied-seed inputs;
the public theorem supplies them from the same actual corrected launch.
No helper input is added to the public root telescope.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceOccupiedFollowerCutoffHistory

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A tight cutoff comes from the grid or the immediately preceding actual
proposal coordinate. This is membership in the literal minimum carrier. -/
private theorem firstCutoff_eq_next_cases
    (sigma t stamp : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (hstamp : stamp.val + 1 = t.val)
    (heq : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = t.val + 1) :
    FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp = true := by
  have hm : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ∈
      FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := Finset.min'_mem _ _
  rw [heq] at hm
  rcases Finset.mem_insert.mp hm with hgrid | hproposal
  · exact Or.inl hgrid.symm
  · obtain ⟨index, hindex, hend⟩ := Finset.mem_image.mp hproposal
    have hbit := (Finset.mem_filter.mp hindex).2
    have hi : index = stamp := by
      apply Fin.ext
      change index.val + 2 = t.val + 1 at hend
      omega
    exact Or.inr (hi ▸ hbit)

/-- Successful occupied FINISH supplies both a real retained record and the
actual current token. No token provenance is assumed by this lemma. -/
private theorem finishRound_occupied_token
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (before next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : ActiveFollowerLifecycle.finishRound rate.eta t row before memory = .ok (next, nextMemory))
    (hoccupied : next.status ≠ .unoccupied) :
    (∃ M, next.lastDown = some M) ∧
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
      · rw [ActiveFollowerLifecycle.finishRound_occupied_read rate.eta t row before memory hoccupied hregs M
          hdown htime] at hfinish
        have hm := (Prod.mk.inj (Except.ok.inj hfinish)).2
        exact ⟨⟨M, rfl⟩, congrArg ActiveFollowerLifecycle.LocalMemory.lastProposalRead hm.symm⟩
      · rw [ActiveFollowerLifecycle.finishRound_incompatible_start rate.eta t row before
          memory hoccupied hregs M hdown (Nat.lt_of_not_ge htime)] at hfinish
        cases hfinish
  · rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta t row before memory hregs] at hfinish
    cases hfinish

/-- An occupied state surviving its actual start-round check cannot have a
tight cutoff: either contributing endpoint would force interruption. -/
private theorem startRound_surviving_bound
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : before.lastDown = some M) (hold : before.status ≠ .unoccupied)
    (hbound : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
    (stamp : Fin p.T) (hstamp : stamp.val + 1 = t.val)
    (hread : memory.lastProposalRead =
      some ⟨stamp, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t before memory = .ok (choice, choiceMemory))
    (hchoice : choice.status ≠ .unoccupied) :
    t.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := by
  classical
  have hfalse : ActiveFollowerLifecycle.interruptionDecision rate.eta t before memory = .ok false := by
    unfold ActiveFollowerLifecycle.startRound at hstart
    cases hd : ActiveFollowerLifecycle.interruptionDecision rate.eta t before memory with
    | error reason => simp [hd] at hstart
    | ok interrupted =>
      cases interrupted with
      | false => rfl
      | true =>
        simp [hd] at hstart
        have hs := congrArg ReferencePrelaunchFollower.State.status hstart.1
        exact (hchoice hs.symm).elim
  have hne : FollowerCutoffScan.firstCutoff p rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≠ t.val + 1 := by
    intro heq
    have hcause := firstCutoff_eq_next_cases (rate := rate) (ActiveFollowerDownAcceptance.downStart p rate M)
      t stamp row hstamp heq
    unfold ActiveFollowerLifecycle.interruptionDecision at hfalse
    split at hfalse
    · simp only [hdown] at hfalse
      split at hfalse
      · split at hfalse
        · rw [hread] at hfalse
          simp only [hstamp, ↓reduceDIte] at hfalse
          rcases hcause with hgrid | hbit
          · change FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate M) = t.val + 1 at hgrid
            simp [hgrid] at hfalse
          · simp [hbit] at hfalse
        · cases hfalse
      · cases hfalse
    · cases hfalse
  omega

/-- Inverting an actual accepted filtered DOWN exposes its computed scan.
An occupied accepted result therefore has the full next-boundary bound. -/
private theorem referenceDownCut_occupied_bound
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
      .accepted before after raw M scan registers lastService)
    (hoccupied : after.status ≠ .unoccupied) :
    t.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := by
  classical
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · dsimp only at h
              split at h
              · cases h
              · split at h
                next ha =>
                  split at h
                  · cases h
                  · cases h
                    dsimp only at hoccupied
                    have hend : (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
                        (ActiveFollowerDownAcceptance.acceptedDownStartLE
                          p rate M t before ha) row).endpoint =
                        t.val + 2 := by
                      by_contra hne
                      simp only [hne, ite_false, ne_eq, not_true_eq_false] at hoccupied
                    have hscan := FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff p
                      rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate M) t
                      (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t before ha)
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
                    change (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
                      (ActiveFollowerDownAcceptance.acceptedDownStartLE
                        p rate M t before ha) row).endpoint = _ at hscan
                    rw [hend] at hscan
                    exact hscan.le.trans (min_le_left _ _)
                · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- The actual release/FINISH composition produces the occupied token even
when release changes pending into released. -/
private theorem releaseAndFinish_occupied_token
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation choice memory post =
      .ok (next, nextMemory)) (hoccupied : next.status ≠ .unoccupied) :
    nextMemory.lastProposalRead =
      some ⟨t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩ := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choice post with
  | error reason => simp only [hr] at h; cases h
  | ok released =>
    have hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
        .ok (next, nextMemory) := by
      cases he : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error reason => simp only [hr, he] at h; cases h
      | ok pair =>
        exact congrArg Except.ok (by simpa only [hr, he, Except.ok.injEq] using h)
    exact (finishRound_occupied_token t row released next memory nextMemory hf hoccupied).2

/-- One actual physical transition propagates the lower bound and produces
its token provenance. The only conditional input is the preceding bound and
token on the same physical input configuration. -/
private theorem record_occupied_bound_and_token
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hprior : match record.input.state.followers i with
      | .dagger => True
      | .ordinary old memory => old.status ≠ .unoccupied →
          ∃ M, old.lastDown = some M ∧
            record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ∧
            ∃ stamp : Fin p.T, stamp.val + 1 = record.input.time.val ∧
              memory.lastProposalRead = some ⟨stamp,
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩) :
    match record.output.next.followers i with
    | .dagger => True
    | .ordinary next nextMemory => next.status ≠ .unoccupied →
        ∃ M, next.lastDown = some M ∧
          record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ∧
          ∃ stamp : Fin p.T, stamp.val + 1 = record.input.time.val + 1 ∧
            nextMemory.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ := by
  classical
  rcases record with ⟨x, output, houtput⟩
  cases houtput
  cases hout : (ReferenceActivePhysicalStep.step x).next.followers i with
  | dagger => trivial
  | ordinary next nextMemory =>
    intro hoccupied
    have hout' : (ReferenceActivePhysicalStep.finishFollower
        (ReferenceActivePhysicalStep.prepare x).coordinator.downView
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration =
        .ordinary next nextMemory := hout
    obtain ⟨choice, memory, post, hc, hr, hf, _, _⟩ :=
      ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hout'
    obtain ⟨hrow, hi, ht, ha⟩ := (ReferenceActivePhysicalStep.prepare x).follower_alignment i
    simp only [hrow, hi, ht, ha] at hr hf
    have htoken := releaseAndFinish_occupied_token _ _ _ _ choice post next memory
      nextMemory hf hoccupied
    have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame _ _ _ _
      choice post next memory nextMemory hf
    have hlast : next.lastDown = post.lastDown := congrArg Prod.fst hframe.1
    have hc' := hc
    rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i] at hc'
    obtain ⟨before, beforeMemory, hinput, hstart, hreply, hunoccupied⟩ :=
      ReferenceFollowerReplyChronology.prepare_ordinary_inversion i x.row
        (x.state.activations i) x.time (x.active i) (x.state.followers i) choice memory hc'
    have hrecord := ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      _ _ _ _ _ _ _ _ choice post hr
    have hresult : ∃ M, next.lastDown = some M ∧
        x.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) := by
      by_cases hu : choice.status = .unoccupied
      -- An unoccupied choice can become occupied only through actual acceptance.
      · have hpost : post.status ≠ .unoccupied := by
          intro h
          exact hoccupied ((hframe.2 hu).trans h)
        rcases hrecord with ⟨_, hkeep⟩ | ⟨logged, cut, raw, M, scan, registers,
            lastService, _, _, hcut, haccepted, _, hpostDown⟩
        · exact (hpost (hkeep hu).2).elim
        · rw [hcut] at haccepted
          exact ⟨M, hlast.trans hpostDown,
            referenceDownCut_occupied_bound _ _ _ _ _ logged post raw M scan registers
              lastService haccepted hpost⟩
      · have hold : before.status ≠ .unoccupied := fun h => hu (hunoccupied h)
        rw [hinput] at hprior
        obtain ⟨M, hdown, hbound, stamp, hstamp, hread⟩ := hprior hold
        have hchoiceBound := startRound_surviving_bound x.time x.row before choice
          beforeMemory memory M hdown hold hbound stamp hstamp hread hstart hu
        have hchoiceDown : choice.lastDown = some M :=
          (congrArg Prod.fst hreply).trans hdown
        rcases hrecord with ⟨hpostDown, _⟩ | ⟨logged, cut, raw, accepted, scan, registers,
            lastService, hlogged, _, _, _, _, _⟩
        · exact ⟨M, hlast.trans (hpostDown.trans hchoiceDown), hchoiceBound⟩
        · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hu] at hlogged
          cases hlogged
    obtain ⟨M, hdown, hbound⟩ := hresult
    exact ⟨M, hdown, hbound, x.time, rfl, htoken⟩

/-- Prefix boundaries include the final endpoint, which need not be a
`Fin T` round. The seed premise is only an initially unoccupied ordinary
configuration; the actual launch below supplies it. -/
private theorem run_final_occupied_bound_and_token
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (hseed : match initial.followers i with
      | .dagger => True
      | .ordinary old _ => old.status = .unoccupied) :
    match (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).finalState.followers i with
    | .dagger => True
    | .ordinary old memory => old.status ≠ .unoccupied →
        ∃ M, old.lastDown = some M ∧
          start + count + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected)) ∧
          ∃ stamp : Fin p.T, stamp.val + 1 = start + count ∧
            memory.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected) stamp⟩ := by
  induction count with
  | zero =>
    rw [ReferenceActivePhysicalHorizon.run_zero_final]
    cases hconfig : initial.followers i with
    | dagger => trivial
    | ordinary old memory =>
      rw [hconfig] at hseed
      intro hoccupied
      exact (hoccupied hseed).elim
  | succ count ih =>
    -- The actual next input is the same prefix final state, with the same row.
    have hprior := ih (by omega)
    let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
      rewards start count hspan hmode
    have hinput : match record.input.state.followers i with
      | .dagger => True
      | .ordinary old memory => old.status ≠ .unoccupied →
          ∃ M, old.lastDown = some M ∧
            record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ∧
            ∃ stamp : Fin p.T, stamp.val + 1 = record.input.time.val ∧
              memory.lastProposalRead = some ⟨stamp,
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ :=
      hprior
    have hnext := record_occupied_bound_and_token record i hinput
    rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
    simpa only [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt, ReferenceActivePhysicalStep.RoundInput.row,
      Nat.add_assoc, Nat.reduceAdd] using hnext

/-- Discarding the auxiliary token leaves the requested input/output timing
bounds of one actual record. The auxiliary input is explicitly conditional
and is produced by the prefix theorem, not supplied at the source root. -/
private theorem record_occupied_source_bounds
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hprior : match record.input.state.followers i with
      | .dagger => True
      | .ordinary old memory => old.status ≠ .unoccupied →
          ∃ M, old.lastDown = some M ∧
            record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ∧
            ∃ stamp : Fin p.T, stamp.val + 1 = record.input.time.val ∧
              memory.lastProposalRead = some ⟨stamp,
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩) :
    (match record.input.state.followers i with
    | .dagger => True
    | .ordinary old _ => old.status ≠ .unoccupied →
        ∃ M, old.lastDown = some M ∧
          record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) ∧
    (match record.output.next.followers i with
    | .dagger => True
    | .ordinary next _ => next.status ≠ .unoccupied →
        ∃ M, next.lastDown = some M ∧
          record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) := by
  have hnext := record_occupied_bound_and_token record i hprior
  constructor
  · cases hconfig : record.input.state.followers i with
    | dagger => trivial
    | ordinary old memory =>
      rw [hconfig] at hprior
      intro hoccupied
      obtain ⟨M, hdown, hbound, _⟩ := hprior hoccupied
      exact ⟨M, hdown, hbound⟩
  · cases hconfig : record.output.next.followers i with
    | dagger => trivial
    | ordinary next memory =>
      rw [hconfig] at hnext
      intro hoccupied
      obtain ⟨M, hdown, hbound, _⟩ := hnext hoccupied
      exact ⟨M, hdown, hbound⟩

/-- Every member record is reached from the same actual initial state, row,
selected index, and reward table. The successor appends precisely the next
computed record; no supplied trace or successful-history assumption appears. -/
private theorem run_record_occupied_source_bounds
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (hseed : match initial.followers i with
      | .dagger => True
      | .ordinary old _ => old.status = .unoccupied) :
    ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records,
    (match record.input.state.followers i with
    | .dagger => True
    | .ordinary old _ => old.status ≠ .unoccupied →
        ∃ M, old.lastDown = some M ∧
          record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) ∧
    (match record.output.next.followers i with
    | .dagger => True
    | .ordinary next _ => next.status ≠ .unoccupied →
        ∃ M, next.lastDown = some M ∧
          record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) := by
  induction count with
  | zero =>
    rw [ReferenceActivePhysicalHorizon.run_zero_records]
    intro record hrecord
    exact False.elim (List.not_mem_nil hrecord)
  | succ count ih =>
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprevious | hcurrent
    · exact ih (by omega) record hprevious
    · have heq := List.mem_singleton.mp hcurrent
      subst record
      apply record_occupied_source_bounds
      exact run_final_occupied_bound_and_token initial rows selected rewards start count
        (by omega) hmode i hseed

/-- At every actual complete-suffix record, an occupied ordinary input or
output retains a DOWN whose source cutoff is beyond its respective boundary.
The original private source, whole reward table and shared constants are the
only root inputs. Empty/no-launch and terminal suffixes are included. -/
theorem complete_occupied_follower_cutoff_source_bounds
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    (match record.input.state.followers i with
    | .dagger => True
    | .ordinary old _ => old.status ≠ .unoccupied →
        ∃ M, old.lastDown = some M ∧
          record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) ∧
    (match record.output.next.followers i with
    | .dagger => True
    | .ordinary next _ => next.status ≠ .unoccupied →
        ∃ M, next.lastDown = some M ∧
          record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)) := by
  classical
  rcases ReferenceLaterCollectionArrivalReadout.source_launch_split rate rewards C_star C_h source
    with ⟨_, hempty, _⟩ | ⟨active, hlaunch, hrecords, hc, hactive, seed, _, _, _⟩
  · have hk := k.isLt
    have hlength := congrArg List.length hempty
    simp only [List.length_nil] at hlength
    omega
  · subst active
    have hseed : match (ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc).followers i with
        | .dagger => True
        | .ordinary old _ => old.status = .unoccupied := by
      rw [seed.configuration i]
      exact seed.unoccupied i
    have hmember : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k ∈
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate source rewards C_star C_h _ hlaunch)).records := by
      rw [← hrecords]
      exact List.get_mem _ _
    exact run_record_occupied_source_bounds _ _ _ _ _ _ _ _ i hseed _ hmember

end Bandits.Support.ReferenceOccupiedFollowerCutoffHistory
