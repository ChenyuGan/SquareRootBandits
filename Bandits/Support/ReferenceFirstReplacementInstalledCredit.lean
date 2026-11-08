/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionExecution
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lean.Elab.Tactic.Omega

/-!
# Scalar credit at the first reached replacement

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/05_binary_transport.tex:60-78`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,123-233,246-295,355-390`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This is an internal pathwise credit calculation on the original execution.
The collection execution producer supplies the whole chronological segment,
its checked prefixes, and the actual incoming ledger. Accepted messages are
joined to the same physical records before using their numerical fields.
Enabled zero arrivals still serve; disabled inputs preserve queues.

The indices used below have two different origins. The suffix starts at the
actual initialization elapsed time `s`. Its first live interval has length
`w`, and the collection has length `C.length`. The replacement therefore has
physical index `s + w + C.length`. Payload start indices are zero based;
the DOWN record stores the corresponding index plus one. The final DOWN
queue bound consequently uses `(M.sigma - 1) * D`, including a nonzero
initial queue when the first replacement is reached.

The numerical argument uses the following actual producers.

* The first-cutoff outside initializer gives the old complement's literal
  diagnostic replay, zero retained base scores, and zero initial increments.
  Each diagnostic has arrival at most `D` by its stored recorder output.
* The checked execution and empty pending set yield a first successful UP
  decode for every old assigned follower. The retained completed preledger
  and the checked prefix identify that decode with the same physical cell.
* The first-collection follower-prefix theorem gives an ordinary next state
  at every such cell, with served sum plus backlog at most `w * D`. The
  accepted-UP output frame preserves its reply, so the very accepted message
  has `M.S + M.q` at most `w * D`.
* Each completed collection input retains its actual recorder. Its per-arm
  arrival cap applies to the whole raw collection, including the cutoff,
  rejected UPs, zero arrivals, and disabled rounds.
* Full-input replay for old assigned arms and known-queue continuation for
  old complement arms account for the same collection once. Conservation
  gives credit for every present final cutoff/current register pair.
* The actual carried-ledger equality and operation-ledger field equations
  transport those pairs to the successful reconstruction. The later-install
  equations then give the new complement and new follower-arm restrictions.

The conditional inputs of private helpers are written in their telescopes.
The complete-source theorem produces each from the original run. In
particular, it supplies no accepted-message budget, successful-operation
family, matching parser trace, numerical queue identity, or survival premise
at its root. The ordinary endpoint facts used for UP credit concern the old
assignment; the replacement's own post-choice tail need not succeed.

Only the execution producer is a direct public project import. Its public
transitives provide the operational, reconstruction, and installation APIs.
No definition of a source score or queue is replaced by this scalar bound.
The next consumer is the first replacement's actual nonzero-queue DOWN
observation and recovery, followed by genuine later ordinary survival.
Those results and the main regret theorem require further proofs.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementInstalledCredit

open ConstructorDimensions
open CoordinatorCollectionLedger
open CollectionCheckedExecution
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A finite-sum bound for the existing accepted-arrival projection.
The local cap is later supplied by actual recorder outputs. -/
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
    exact (by
      unfold RecordedQueueRun.acceptedArrival
      split
      · exact hcap record hrecord
      · exact Nat.zero_le _)
  simpa [nsmul_eq_mul] using
    List.sum_le_length_nsmul (records.map RecordedQueueRun.acceptedArrival) bound hbound

/-- Gate absence and a gate naming another arm give zero local arrival.
A present gate uses the same output's checked raw-arrival bound. -/
private theorem recording_arrival_le
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (a : Fin p.K) :
    localArrival (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a ≤ D p := by
  unfold ReferenceCollectionRawBufferHistory.rawDiagnostic
  cases hrecording : record.output.coordinator.recording with
  | none => exact Nat.zero_le _
  | some output =>
      simp only [Option.bind_some]
      cases hgate : output.gateArm with
      | none => exact Nat.zero_le _
      | some arm =>
          simp only [Option.map_some, localArrival]
          split
          · exact output.rawArrival_le_D
          · exact Nat.zero_le _

/-- The successful extractor loses no position in a list whose every cell
completed. This is a list-index identity, not another execution. -/
private theorem completed_input_at
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (k : ℕ) (hk : k < records.length) :
    ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound (records[k]'hk) = some completed ∧
      (ReferenceCollectionSegmentExtraction.inputs records)[k]? = some completed.input := by
  induction records generalizing k with
  | nil =>
      simp only [List.length_nil] at hk
      omega
  | cons head tail ih =>
      have hhead := hgood head (List.mem_cons_self)
      have htail : ∀ record ∈ tail,
          (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true :=
        fun record hmem => hgood record (List.mem_cons_of_mem _ hmem)
      cases he : ReferenceCollectionSegmentExtraction.extractRound head with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hhead
      | some completed =>
          cases k with
          | zero =>
              exact ⟨completed, he, by
                simp only [ReferenceCollectionSegmentExtraction.inputs,
                  ReferenceCollectionSegmentExtraction.completed, List.filterMap_cons,
                  he, List.map_cons, List.getElem?_cons_zero]⟩
          | succ k =>
              obtain ⟨next, hn, hi⟩ := ih htail k (by simpa using hk)
              refine ⟨next, hn, ?_⟩
              simpa only [ReferenceCollectionSegmentExtraction.inputs,
                ReferenceCollectionSegmentExtraction.completed, List.filterMap_cons,
                he, List.map_cons, List.getElem?_cons_succ] using hi

/-- Every mapped queue input names an extracted physical cell. No successful
decode or positive arrival is required for its raw-arrival cap. -/
private theorem collection_records_cap
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (a : Fin p.K) :
    ∀ record ∈ CollectionKnownQueueContinuation.inputQueueRecords
      segment.context.preLedger a segment.inputs, record.2 ≤ D p := by
  intro queueRecord hmem
  obtain ⟨input, hinput, rfl⟩ := List.mem_map.mp hmem
  change input ∈ (ReferenceCollectionSegmentExtraction.completed segment.records).map
    ReferenceCollectionSegmentExtraction.CompletedRound.input at hinput
  obtain ⟨completed, hcompleted, rfl⟩ := List.mem_map.mp hinput
  obtain ⟨record, _, hextract⟩ := List.mem_filterMap.mp hcompleted
  obtain ⟨output, _, hraw, _⟩ :=
    ReferenceCollectionRawBufferHistory.actual_completed_input_recording record completed hextract
  unfold localQueueRecord
  split
  · dsimp only
    rw [hraw]
    cases hg : output.gateArm with
    | none => exact Nat.zero_le _
    | some arm =>
        simp only [Option.map_some, localArrival]
        split
        · exact output.rawArrival_le_D
        · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- Match the two existing projections of the same successful dispatch.
The explicit choice equality includes its actual arm-selection guard. -/
private theorem choice_executed_tail
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice x = some choice) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨choice.payload, choice.preLedger, choice.started, choice.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  unfold ReferenceCollectionPhaseHistory.executedTail
  split at hc
  · contradiction
  next hguard =>
    rw [ite_eq_right hguard]
    cases hd : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals contradiction
    | live registers owned base outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals first | contradiction | (cases Option.some.inj hc; rfl)
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals first | contradiction | (cases Option.some.inj hc; rfl)
    | invalidCollectionCutoff =>
        simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        contradiction
    | dagger =>
        simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        contradiction

/-- The ledger decode here is the extracted full-input replay's real decode.
Its preledger equality and START equation are explicit local inputs. -/
private theorem accepted_up_of_completed_decode
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed)
    (before started decoded : ReferenceActivePhysicalStep.Ledger rate)
    (hbefore : completed.context.preLedger = before)
    (hstart : startRound before (sourceRound completed.input.round)
      completed.input.enabled completed.input.raw = .success started)
    (hdecode : decodeUp started completed.input.selectedFollower completed.input.parsed =
      .success decoded)
    (M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val))
    (hparsed : completed.input.parsed = some M) :
    ReferenceCollectionPhaseHistory.AcceptedUp record.input completed.input.selectedFollower M := by
  obtain ⟨recording, actualStarted, actualDecoded, bank, _, hrecording,
    hactualStart, hinput, hreceived, _⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_inputs record completed hextract
  have hstarted : actualStarted = started := by
    have hsame := hactualStart
    rw [hbefore] at hsame
    have hexact : startRound before (sourceRound completed.input.round)
        completed.input.enabled completed.input.raw = .success actualStarted := by
      simpa only [hinput, ReferenceCollectionSegmentExtraction.inputOf, sourceRound, hbefore]
        using hsame
    exact Checked.success.inj (hexact.symm.trans hstart)
  subst actualStarted
  have hselected : completed.input.selectedFollower =
      ReferenceActivePhysicalStep.upSenderIndex record.input := by rw [hinput]; rfl
  have hparse : ReferenceCollectionPhaseHistory.filteredParsed record.input started = some M := by
    simpa only [hinput, ReferenceCollectionSegmentExtraction.inputOf,
      ReferenceCollectionSegmentExtraction.effectiveParse,
      ReferenceCollectionPhaseHistory.filteredParsed] using hparsed
  have haccepted : completed.accepted = true := by
    cases ha : completed.accepted with
    | true => rfl
    | false =>
        have hspec := ReferenceCollectionSegmentExtraction.receiveUp_decode_result record.input started
        simp only [ha, Bool.false_eq_true, ↓reduceIte] at hreceived
        rw [hreceived] at hspec
        have hd : decodeUp started (ReferenceActivePhysicalStep.upSenderIndex record.input)
            (ReferenceCollectionSegmentExtraction.effectiveParse record.input started) =
              .success decoded := by
          simpa only [hinput, ReferenceCollectionSegmentExtraction.inputOf] using hdecode
        rw [hd] at hspec
        cases hspec
  have hchoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
    record completed hextract).1
  refine ⟨⟨completed.context.payload, completed.context.preLedger,
    completed.context.started, completed.context.weights⟩,
    recording, started, actualDecoded, bank,
    choice_executed_tail record.input completed.context hchoice,
    hrecording, hactualStart, ?_, hparse, hselected⟩
  simpa only [haccepted, ↓reduceIte] using hreceived

/-- Conditional only on literal acceptance and the ordinary next endpoint.
Both are produced on the same cell before this helper is applied. The reply
frame keeps the accepted offer's served sum and terminal queue unchanged. -/
private theorem accepted_message_mass
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next memory)
    (bound : ℕ) (hmass : next.S + next.backlog ≤ bound) :
    M.val.S + M.val.q ≤ bound := by
  obtain ⟨sender, state, μ, hsender, hindex, hconfig, _, _, _, _, hS, _, hq, _⟩ :=
    ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  obtain ⟨choice, ν, hchoice, _, _, hreply⟩ :=
    ReferenceAcceptedUpFollowerHistory.record_acceptedUp_output_frame haccepted hout
  have hactual : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state μ := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
    rw [hindex, ← hsender]
    exact hconfig
  have hstate : choice = state := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans hactual)).1
  rw [hstate] at hreply
  have hscore : next.S = state.S := congrArg (fun value => value.2.1) hreply
  have hqueue : next.backlog = state.backlog := congrArg (fun value => value.2.2.2) hreply
  rw [hS, hq, ← hscore, ← hqueue]
  exact hmass

/-- The segment context is the context actually selected at its first cell. -/
private theorem segment_context_at_cut
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (offset : ℕ) (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hdrop : records.drop offset = cut :: rest)
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt records offset = some segment)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice cut.input = some choice) :
    segment.context = choice := by
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    records offset segment hsegment).1
  rw [hdrop] at hbranch
  simp only [ReferenceCollectionSegmentExtraction.segment, hchoice, Option.map_some] at hbranch
  split at hbranch <;> cases Option.some.inj hbranch <;> rfl

/-- Only the accepted first-cutoff initializer is used here. Its zero base
and outside registers are produced by the original first live run. -/
private theorem first_segment_initial_credit
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (run initial rows J rewards start count span active).records).length < count)
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (a : ReferenceCollectionSegmentExtraction.Initializer p)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (run initial rows J rewards start count span active).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (run initial rows J rewards start count span active).records).length = some segment)
    (ha : segment.context.initializer = some a) :
    (∀ i, a.base i = 0) ∧
    ∀ arm : Fin p.K,
      (∃ i, segment.context.preLedger.assignment.arm i = arm) ∨
      ∃ cutoff current,
        segment.context.preLedger.cutoffRegisters arm = some cutoff ∧
        segment.context.preLedger.currentRegisters arm = some current ∧
        segment.context.preLedger.increment arm = 0 ∧
        cutoff.score + current.queue ≤
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (run initial rows J rewards start count span active).records).length * D p := by
  classical
  let R := (run initial rows J rewards start count span active).records
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R
  let w := window.length
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial rows J rewards start count span active hfirst hshort
  obtain ⟨cut, suffix, hsplit, _, _, _, r, q, base, _, _, dispatched, hstart,
    ledger, hinit, hledger, hdomain, hclock, hpending, hno, selected, _,
    _hpositive, _hsigma, hzero, _hbirth, _hbits, _hreplay, htail⟩ := houtside
  dsimp only at htail
  obtain ⟨_hu, _husigma, _huT, _hugrid, _hgridT, _hlsigma, _hlcut,
    _hlfreeze, _hscan, _habsent, hpresent, hcutregs, hcurrentregs, _hbase,
    _hpending, hincrement, _hgamma, _hraw, _hhistory, _hcursor, _hphase,
    hsharedCut, hsharedCurrent, hsharedIncrement, _hsharedGamma, _hsharedRaw,
    _hsharedHistory, _hsharedCursor, _hsharedPhase, initializer, choice,
    hinitializer, hchoice, hchoiceInitializer, hchecked⟩ := htail
  have hdrop : R.drop w = cut :: suffix := by
    change R = window ++ cut :: suffix at hsplit
    rw [hsplit]
    exact List.drop_left
  have hcontext := segment_context_at_cut R w cut suffix hdrop
    segment hsegment choice hchoice
  have hpre : segment.context.preLedger = ReferenceActivePhysicalStep.sharedLedger ledger := by
    rw [hcontext]
    exact Checked.success.inj
      ((ReferenceCollectionSegmentExtraction.choice_initializer cut.input choice initializer
        hchoice hchoiceInitializer).symm.trans hchecked)
  have haeq : a = initializer := by
    rw [hcontext] at ha
    exact Option.some.inj (ha.symm.trans hchoiceInitializer)
  constructor
  · intro i
    rw [haeq, hinitializer]
    exact hzero i
  · intro arm
    by_cases hfast : arm ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet
    · right
      let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨arm, hfast⟩
      let diagnostics := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords
        r.payload arm window w
      let replayed := QueueReplay.replay (4 * r.payload.n) (0, 0) diagnostics
      have hcap : ∀ record ∈ diagnostics, record.2 ≤ D p := by
        intro record hmem
        obtain ⟨physical, _, rfl⟩ := List.mem_map.mp hmem
        exact recording_arrival_le physical arm
      have htotal := RecordedQueueRun.replay_total (4 * r.payload.n) (0, 0) diagnostics
      have hlength : diagnostics.length = w := by
        simp only [diagnostics, ReferenceFirstComplementReplay.liveDiagnosticQueueRecords,
          List.length_map, List.length_take, w, Nat.min_self]
      have hmass : replayed.1 + replayed.2 ≤ w * D p := by
        dsimp only at htotal
        rw [htotal]
        simpa only [Nat.zero_add, hlength] using accepted_total_le diagnostics (D p) hcap
      refine ⟨⟨replayed.1, replayed.2,
        CollectionKnownQueueContinuation.replayLastService (4 * r.payload.n) (0, 0) 0 diagnostics⟩,
        ⟨replayed.2,
          CollectionKnownQueueContinuation.replayLastService (4 * r.payload.n) (0, 0) 0 diagnostics⟩,
        ?_, ?_, ?_, hmass⟩
      · rw [hpre, hsharedCut, hcutregs]
        exact hpresent j
      · rw [hpre, hsharedCurrent, hcurrentregs]
        exact congrArg (Option.map fun reg =>
          (⟨reg.queue, reg.lastService⟩ : CurrentRegister)) (hpresent j)
      · rw [hpre, hsharedIncrement, hincrement]
    · left
      have hslow : arm ∈ r.payload.slowSet.val := by
        simpa only [CanonicalFastSampling.fastArmFinset, Finset.mem_sdiff,
          Finset.mem_univ, true_and, not_not] using hfast
      rw [← r.payload.assignment_image] at hslow
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hslow
      refine ⟨i, ?_⟩
      rw [hpre, hledger]
      exact hi

/-- Conditional calculation on the actual segment. The complete-source proof
produces the zero base, initial outside credit, and ordinary next endpoints.
No accepted-message budget is supplied: it is obtained at the real accepting
cell using the checked prefix and the actual receiver. -/
private theorem segment_final_credit
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (offset : ℕ)
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (a : ReferenceCollectionSegmentExtraction.Initializer p)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (run initial rows J rewards start count span active).records offset = some segment)
    (hgood : ∀ record ∈ segment.records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (hRun : startAndRunChecked p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside segment.inputs =
        .success ⟨segment.context.preLedger, segment.accepted, segment.final⟩)
    (hempty : segment.final.pending = ∅)
    (hprefix : ∀ k, k ≤ segment.records.length → ∃ accepted,
      checkedRounds segment.context.preLedger (segment.inputs.take k) =
        some (accepted, ReferenceCollectionSegmentExtraction.endpointLedger
          segment.context.preLedger (segment.records.take k)))
    (w : ℕ) (hzero : ∀ i, a.base i = 0)
    (hinitial : ∀ arm : Fin p.K,
      (∃ i, segment.context.preLedger.assignment.arm i = arm) ∨
      ∃ cutoff current,
        segment.context.preLedger.cutoffRegisters arm = some cutoff ∧
        segment.context.preLedger.currentRegisters arm = some current ∧
        segment.context.preLedger.increment arm = 0 ∧
        cutoff.score + current.queue ≤ w * D p)
    (hpost : ∀ k, ∀ hk : k < segment.records.length, ∀ i : Fin (p.m - 1),
      ∃ next memory,
        (segment.records[k]'hk).output.next.followers i = .ordinary next memory ∧
        next.S + next.backlog ≤ w * D p) :
    ∀ arm : Fin p.K, ∃ cutoff current,
      segment.final.cutoffRegisters arm = some cutoff ∧
      segment.final.currentRegisters arm = some current ∧
      cutoff.score + segment.final.increment arm + current.queue ≤
        (w + segment.records.length) * D p := by
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    _ offset segment hsegment).1
  have hlength := ReferenceCollectionSegmentExtraction.segment_input_count
    _ segment hbranch
  obtain ⟨accepted, _hinit, hfold⟩ :=
    CollectionBufferProvenance.startAndRunChecked_success_components
      a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside segment.inputs
      ⟨segment.context.preLedger, segment.accepted, segment.final⟩ hRun
  intro arm
  have hcap := accepted_total_le
    (CollectionKnownQueueContinuation.inputQueueRecords segment.context.preLedger arm segment.inputs)
    (D p) (collection_records_cap segment arm)
  have hrecordsLength :
      (CollectionKnownQueueContinuation.inputQueueRecords segment.context.preLedger arm
        segment.inputs).length = segment.records.length := by
    simpa only [CollectionKnownQueueContinuation.inputQueueRecords, List.length_map] using hlength
  rw [hrecordsLength] at hcap
  rcases hinitial arm with ⟨i, hi⟩ | ⟨cutoff, current, hcutoff, hcurrent, hinczero, hmass⟩
  · obtain ⟨pre, input, suffix, prefixAccepted, before, started, decoded,
      finished, suffixAccepted, M, hsplit, hselected, hparsed, hprefixFold,
      _hunknown, hstart, hdecode, _hfinish, _hsuffix, _hunique, hfinalCurrent,
      hfinalIncrement, hfinalCutoff, _hcursor, _hend, _hchron, _hraw,
      _henabled, _hassignment, _hcut, _hfreeze⟩ :=
      CollectionFullInputReplay.assigned_follower_full_input_queue_replay_of_empty_pending
        a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside segment.inputs
        ⟨segment.context.preLedger, segment.accepted, segment.final⟩ i hRun hempty
    have hk : pre.length < segment.records.length := by
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at hlen
      omega
    obtain ⟨completed, hextract, hinputAt⟩ := completed_input_at segment.records hgood pre.length hk
    have hinput : completed.input = input := by
      have hget : segment.inputs[pre.length]? = some input := by
        rw [hsplit, List.getElem?_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem?_cons_zero]
      exact Option.some.inj (hinputAt.symm.trans hget)
    obtain ⟨priorAccepted, hprior⟩ := hprefix pre.length (Nat.le_of_lt hk)
    have htake : segment.inputs.take pre.length = pre := by
      rw [hsplit]
      exact List.take_left
    rw [htake] at hprior
    have hbefore : completed.context.preLedger = before := by
      have hretained := ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
        initial rows J rewards start count span active offset segment hsegment
        pre.length hk completed hextract
      exact hretained.trans ((Prod.mk.inj (Option.some.inj
        (hprior.symm.trans hprefixFold))).2)
    have haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
        (segment.records[pre.length]'hk).input i M := by
      have hactual := accepted_up_of_completed_decode
        (segment.records[pre.length]'hk) completed hextract before started decoded
        hbefore (hinput ▸ hstart) (hinput ▸ hdecode) M (hinput ▸ hparsed)
      simpa only [hinput, hselected] using hactual
    obtain ⟨next, memory, hout, hnext⟩ := hpost pre.length hk i
    have hmessage := accepted_message_mass (segment.records[pre.length]'hk)
      i M haccepted next memory hout (w * D p) hnext
    dsimp only at hfinalCurrent hfinalIncrement hfinalCutoff
    rw [hi] at hfinalCurrent hfinalIncrement hfinalCutoff
    refine ⟨⟨a.base i + M.val.S, M.val.q, M.val.delta⟩, _,
      hfinalCutoff, hfinalCurrent, ?_⟩
    have htotal := RecordedQueueRun.replay_total (4 * rate.n) (0, M.val.q)
      (CollectionKnownQueueContinuation.inputQueueRecords segment.context.preLedger arm segment.inputs)
    dsimp only at htotal ⊢
    rw [hzero, Nat.zero_add, hfinalIncrement]
    calc
      M.val.S + _ + _ = (M.val.S + M.val.q) +
          RecordedQueueRun.acceptedTotal
            (CollectionKnownQueueContinuation.inputQueueRecords
              segment.context.preLedger arm segment.inputs) := by omega
      _ ≤ w * D p + segment.records.length * D p := Nat.add_le_add hmessage hcap
      _ = (w + segment.records.length) * D p := (Nat.add_mul _ _ _).symm
  · have hknown := CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
      segment.context.preLedger segment.final arm current segment.inputs accepted hcurrent hfold
    obtain ⟨hfinalCurrent, hfinalIncrement, _, _, _, _, hfinalCutoff⟩ := hknown
    refine ⟨cutoff, _, hfinalCutoff.trans hcutoff, hfinalCurrent, ?_⟩
    have htotal := RecordedQueueRun.replay_total (4 * rate.n)
      (segment.context.preLedger.increment arm, current.queue)
      (CollectionKnownQueueContinuation.inputQueueRecords segment.context.preLedger arm segment.inputs)
    dsimp only at htotal ⊢
    rw [hfinalIncrement]
    calc
      cutoff.score + _ + _ = (cutoff.score + current.queue) +
          RecordedQueueRun.acceptedTotal
            (CollectionKnownQueueContinuation.inputQueueRecords
              segment.context.preLedger arm segment.inputs) := by omega
      _ ≤ w * D p + segment.records.length * D p := Nat.add_le_add hmass hcap
      _ = (w + segment.records.length) * D p := (Nat.add_mul _ _ _).symm

/-- The ordinary endpoint used for an accepted offer is the actual next
prefix, with the acceptance round included exactly once. -/
private theorem record_next_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (index : ℕ) (hi : index < count) :
    ((run initial rows J rewards start count span active).records[index]'(by
      rw [run_record_count]; exact hi)).output.next =
      (run initial rows J rewards start (index + 1) (by omega) active).finalState := by
  obtain ⟨suffix, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards start (index + 1) (count - (index + 1)) (by omega) active
  have hcount : index + 1 + (count - (index + 1)) = count := by omega
  simp only [hcount] at hsplit
  have hget : (run initial rows J rewards start count span active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start index (by omega) active) := by
    rw [hsplit, List.getElem?_append_left (by rw [run_record_count]; omega),
      ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
    simp [run_record_count]
  rw [List.getElem?_eq_getElem (by rw [run_record_count]; exact hi)] at hget
  rw [Option.some.inj hget]
  exact (ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    initial rows J rewards start index (by omega) active).symm

/-- F supplies all ordinary next endpoints, including the cutoff cell. The
segment and its whole raw record list come from the admitted execution theorem. -/
private theorem launched_segment_post_credit
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome =
        true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (span : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc s hsElapsed count span).records).length < count)
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc s hsElapsed count span).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hc s hsElapsed count span).records).length = some segment)
    (hrecords : segment.records = ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc s hsElapsed count span).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hc s hsElapsed count span).records).length) :
    ∀ k, ∀ hk : k < segment.records.length, ∀ i : Fin (p.m - 1),
      ∃ next memory,
        (segment.records[k]'hk).output.next.followers i = .ordinary next memory ∧
        next.S + next.backlog ≤
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hc s hsElapsed count span).records).length * D p := by
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate source rewards C_star C_h hc s hsElapsed
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let R := (run initial source.1.2 J rewards s count span active).records
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let b := w + 1
  let W := (R.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hlenR : R.length = count := run_record_count initial source.1.2 J rewards s count span active
  have hw : w < R.length := by rw [hlenR]; exact hshort
  have hdrop : R.drop w = R[w]'hw :: R.drop b := List.drop_eq_getElem_cons hw
  have hC : segment.records = R[w]'hw :: W := by
    change segment.records = ReferenceCollectionPhaseHistory.collectionWindow R w at hrecords
    rw [hrecords]
    dsimp only [ReferenceCollectionPhaseHistory.collectionWindow]
    rw [hdrop]
    rfl
  have hpartition := ReferenceCollectionSegmentExtraction.segmentAt_partition R w segment hsegment
  have hpref : segment.records <+: R.drop w := by
    rw [← hpartition]
    exact List.prefix_append _ _
  have hF :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hc s hsElapsed count span hshort
  obtain ⟨_r, _q, _base, _hpre, _hsigma, _hzero, _dispatched, _hstart,
    _ledger, _hinit, _hledger, _hdomain, _hclock, _hallPending, _hnoAssignment,
    _chosen, _hcutoff, _hu, _huT, _huGrid, _hlSigma, _hlCut, _hscan,
    _hsuccessor, _hpostCut, hboundaries, _hsteps⟩ := hF
  intro k hk i
  have hkW : k ≤ W.length := by
    rw [hC, List.length_cons] at hk
    omega
  obtain ⟨next, memory, hout, _hstatus, _hdomain, _hbuffer, _hdecoder,
    _hS, _hdelta, _hbacklog, hmass, _htail⟩ := (hboundaries k hkW).2 i
  have hkR : w + k < count := by
    have hlen := hpref.length_le
    simp only [List.length_drop, hlenR] at hlen
    omega
  have hindex : (segment.records[k]'hk) = R[w + k]'(by omega) := by
    simpa only [List.getElem_drop] using hpref.getElem hk
  have hnext := record_next_prefix initial source.1.2 J rewards s count span active
    (w + k) hkR
  refine ⟨next, memory, ?_, hmass⟩
  rw [hindex, hnext]
  have hindexEnd : w + k + 1 = b + k := by
    dsimp only [b]
    omega
  change (run initial source.1.2 J rewards s (b + k) (by omega) active).finalState.followers i =
    .ordinary next memory at hout
  simpa only [hindexEnd] using hout

/-- On the original complete source, the first reached replacement installs
all-arm score-plus-queue credit. The actual new DOWN records may have nonzero
queues. The replacement round itself is excluded from the collection replay.

All other option/constructor branches are explicitly outside this internal
claim. No replacement existence, source score/queue identity, subsequent DOWN
recovery, probability law, or regret conclusion is asserted. -/
theorem complete_first_replacement_installed_credit
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let C := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + C.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection old _ledger _ _
          (.laterChosen _ _ _ _ _ _ output _ clockData installed _) =>
          installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          old.sigma.val = s ∧ record.input.time.val = s + v ∧
          installed.registers.payload.sigma.val = record.input.time.val ∧
          (∀ a : Fin p.K,
            AssignmentScoreReconstruction.sourceScore output.reconstruction a +
              AssignmentScoreReconstruction.initialQueue output.reconstruction a ≤ v * D p) ∧
          (∀ a : Fin p.K,
            installed.registers.payload.queues a =
                AssignmentScoreReconstruction.initialQueue output.reconstruction a ∧
              installed.registers.payload.queues a ≤ installed.registers.payload.sigma.val * D p) ∧
          (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
            installed.registers.complementScores j + installed.ownedRegisters.queue j ≤ v * D p) ∧
          (∀ i : Fin (p.m - 1), let M := installed.registers.payload.downRecord i
            M.val.sigma = s + v + 1 ∧
            M.val.q = AssignmentScoreReconstruction.initialQueue output.reconstruction
              (installed.registers.payload.assignment.assigned i) ∧
            installed.retainedBaseScore i + M.val.q ≤ v * D p ∧
            M.val.q ≤ (M.val.sigma - 1) * D p)
      | _ => True := by
  classical
  have execution :=
    ReferenceFirstReplacementCollectionExecution.complete_first_replacement_collection_execution
      rate source rewards C_star C_h
  have prefixes :=
    ReferenceFirstReplacementCollectionExecution.complete_first_replacement_collection_prefix_checked
      rate source rewards C_star C_h
  dsimp only at execution prefixes ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set C := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + C.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    simp only [hget] at execution prefixes
    dsimp only
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hcut] at execution prefixes
      cases outcome <;> dsimp only at execution prefixes ⊢
      rename_i core consistent started hs instruction hi output hl clockData installed selected
      obtain ⟨hwR, holdSigma, htime, segment, a, hsegment, hrecords,
        _hremaining, hinitializer, hfinal, hempty, hgood, _hlength,
        _hcalendar, hRun, _hexecutionPrefixes⟩ := execution
      obtain ⟨prefixSegment, hprefixSegment, _hprefixRecords, _hprefixFinal, hprefixes⟩ := prefixes
      have hsame : prefixSegment = segment :=
        Option.some.inj (hprefixSegment.symm.trans hsegment)
      subst prefixSegment
      have hprefix : ∀ k, k ≤ segment.records.length → ∃ accepted,
          checkedRounds segment.context.preLedger (segment.inputs.take k) =
            some (accepted, ReferenceCollectionSegmentExtraction.endpointLedger
              segment.context.preLedger (segment.records.take k)) := by
        simpa only [hrecords] using hprefixes
      have hfinalCredit : ∀ arm : Fin p.K, ∃ cutoff current,
          ledger.cutoffRegisters arm = some cutoff ∧
          ledger.currentRegisters arm = some current ∧
          cutoff.score + ledger.increment arm + current.queue ≤ v * D p := by
        cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate source rewards C_star C_h with
        | none =>
            have hemptyR : R = [] := by
              simp only [R, ReferenceCompletePhysicalHistory.completeSuffixRecords,
                hlaunch, ↓reduceDIte]
            rw [hemptyR, List.getElem?_nil] at hget
            contradiction
        | some launched =>
            have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
              rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
            let initial :=
              ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
            let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
              rate source rewards C_star C_h hc
            have active : allActiveAtStart initial s := seed.activeAtStart
            let J := ActualInitializationPhysicalStep.selectedRowIndex p source
            let count := p.T - s
            have span : s + count ≤ p.T := by
              have hbound := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate source rewards C_star C_h
              dsimp only [s, count]
              omega
            have hactual := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
              rate source rewards C_star C_h hc
            have hrun : R = (run initial source.1.2 J rewards s count span active).records :=
              ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
                rate source rewards C_star C_h initial hactual
            have hcount : R.length = count := by
              rw [hrun, run_record_count]
            have hgenerated :
                (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
                  rate source rewards C_star C_h hc s rfl count span).records = R := by
              change (run initial source.1.2 J rewards s count span active).records = R
              exact hrun.symm
            have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                (run initial source.1.2 J rewards s count span active).records).length < count := by
              rw [← hrun, ← hcount]
              exact hwR
            have hsegRun : ReferenceCollectionSegmentExtraction.segmentAt
                (run initial source.1.2 J rewards s count span active).records w = some segment := by
              rw [← hrun]
              exact hsegment
            have hinitial := first_segment_initial_credit initial source.1.2 J rewards s count
              span active seed.coordinatorFirst hshort segment a
              (by simpa only [← hrun] using hsegRun) hinitializer
            rw [← hrun] at hinitial
            have hpost := launched_segment_post_credit rate source rewards C_star C_h hc
              s rfl count span (by
                rw [hgenerated, ← hcount]
                exact hwR) segment
              (by rw [hgenerated]; exact hsegment)
              (by rw [hgenerated]; exact hrecords)
            rw [hgenerated] at hpost
            have hcredit := segment_final_credit initial source.1.2 J rewards s count span active w
              segment a hsegRun (by simpa only [hrecords] using hgood)
              hRun (hfinal ▸ hempty) hprefix w hinitial.1 hinitial.2 hpost
            simpa only [hfinal, hrecords] using hcredit
      -- Reconstruction uses the incoming READY ledger, before this new
      -- assignment round has run recorder, queue service, or reception.
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
          record.output.preparation.coordinator := by
        rw [record.output_eq]
        rfl
      have provenance :=
        ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance record.input
      rw [hdispatch, hcut] at provenance
      obtain ⟨hinstalled, _hpayload, hsigma, hdownQueue⟩ := provenance
      have ledgerFields := CoordinatorRoundDispatch.collectionOperationLedger_fields
        (ReferenceActivePhysicalStep.collectionInput record.input old ledger clock cutoff)
        core.payload_n_eq
      obtain ⟨_hassignment, _hsigma, _hcutoff, _hfreeze, _hbase, _hpending,
        hcutoffRegisters, hcurrentRegisters, hincrement, _hrest⟩ := ledgerFields
      have equations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
        _ instruction output.reconstruction output.reconstruction_eq
      obtain ⟨_hchecks, hcutoff, hcurrent, hscore, hqueue, _hotherEquations⟩ := equations
      rw [hcutoffRegisters] at hcutoff
      rw [hcurrentRegisters] at hcurrent
      rw [hincrement] at hscore
      have hcredit : ∀ arm : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction arm +
            AssignmentScoreReconstruction.initialQueue output.reconstruction arm ≤ v * D p := by
        intro arm
        obtain ⟨cutoff, current, hc, hq, hmass⟩ := hfinalCredit arm
        have hcEq : cutoff = output.reconstruction.registers.cutoff arm :=
          Option.some.inj (hc.symm.trans (hcutoff arm))
        have hqEq : current = output.reconstruction.registers.current arm :=
          Option.some.inj (hq.symm.trans (hcurrent arm))
        rw [hcEq, hqEq] at hmass
        rw [hscore arm, hqueue arm]
        exact hmass

      -- Establish all K coordinates before restricting to the newly chosen
      -- slow set. A newly assigned arm may have been an old complement arm.
      subst installed
      have hqueues : ∀ arm : Fin p.K,
          (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.queues
              arm =
              AssignmentScoreReconstruction.initialQueue output.reconstruction arm ∧
          (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.queues
              arm ≤
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.sigma.val *
              D p := by
        intro arm
        have hq :=
          CoordinatorAssignmentRegisterInstall.later_payload_queue_eq_initial_queue
            output clockData arm
        refine ⟨hq, ?_⟩
        rw [hq, hsigma, htime]
        exact le_trans (Nat.le_trans (Nat.le_add_left _ _) (hcredit arm))
          (Nat.mul_le_mul_right (D p) (Nat.le_add_left v s))
      refine ⟨rfl, holdSigma, htime, hsigma, hcredit, hqueues, ?_, ?_⟩
      · intro j
        calc
          _ = AssignmentScoreReconstruction.sourceScore output.reconstruction j.val +
              AssignmentScoreReconstruction.initialQueue output.reconstruction j.val :=
            congrArg₂ Nat.add
              (CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
                output clockData j)
              (CoordinatorAssignmentRegisterInstall.later_owned_queue_eq_initial_queue
                output clockData j)
          _ ≤ v * D p := hcredit j.val
      · intro i
        have hrecordFields :=
          (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.downRecord_fields
            i
        have hrecordQueue :=
          (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.downRecord_initialQueue
            i
        have hdsigma :
            ((CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.downRecord
              i).val.sigma =
              s + v + 1 := by
          rw [hrecordFields]
          dsimp only
          rw [hsigma, htime]
        refine ⟨hdsigma, hdownQueue i, ?_, ?_⟩
        · rw [CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
              output clockData i,
            hdownQueue i]
          exact hcredit (output.payload.assignment.assigned i)
        · rw [hrecordQueue]
          have hq := (hqueues
            ((CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.assignment.assigned
              i)).2
          simpa only [hrecordFields, Nat.add_sub_cancel] using hq

end Bandits.Support.ReferenceFirstReplacementInstalledCredit
end
