/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEmptyInstallationNumericalStep
public import Bandits.Support.ReferenceFirstCorrectedReplacementCollectionBoundaryHistory

/-!
# Canonical readout on the first corrected replacement collection

Internal physical-history joins for ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,246-299`, and `05_binary_transport.tex:354-396`.
The old freeze boundary and the actual recorder are retained literally.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedReplacementCollectionReadout

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceCollectionSegmentExtraction ReferenceLaterCollectionArrivalReadout
open ReferenceCollectionRawBufferHistory

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Disabled canonical collection cells have no marker. This says nothing
about arbitrary numerical round inputs. -/
private theorem readout_disabled (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout s r = some c) (hdisabled : c.enabled = false) :
    c.recordedArm = none ∧ ∀ a, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
  classical
  have hmarker : c.recordedArm = none := by
    unfold laterCollectionReadout at hread
    split at hread
    next =>
      cases hc : r.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc] at hread
      | invalidCollectionCutoff => simp [hc] at hread
      | dagger => simp [hc] at hread
      | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next core snapshot hcontinue selected =>
          cases Option.some.inj hread
          change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
          change (continuingCollectionInput r payload ledger clock cutoff snapshot).enabled = false at hdisabled
          dsimp only [continuingCollectionInput] at hdisabled
          rw [hdisabled]
          exact SnapshotRecordingKernel.recordingMap_disabled ..
      | live registers owned base outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next dispatched hs ledger hi he hd hclock hp hn selected =>
          split at hread
          next =>
            cases Option.some.inj hread
            change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
            change (laterCutoffCollectionInput r registers owned base dispatched selected).enabled = false at hdisabled
            dsimp only [laterCutoffCollectionInput] at hdisabled
            rw [hdisabled]
            exact SnapshotRecordingKernel.recordingMap_disabled ..
          next => contradiction
    next => contradiction
  refine ⟨hmarker, ?_⟩
  intro a
  simp only [RecordedQueueRun.quantizedArrival, hmarker, reduceCtorEq, ite_false]

/-- The partial readout and extractor name the very same physical call. -/
private theorem readout_call_context (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K) (done : CompletedRound rate)
    (hread : laterCollectionReadout s r = some c)
    (hextract : extractRound r = some done) :
    laterCollectionCall s r = some ⟨done.context.payload, done.context.preLedger,
      done.context.started, done.context.weights⟩ := by
  classical
  have hchoice := (actual_collection_round_checked r done hextract).1
  have hdomain := (laterCollectionReadout_domain s r).mp (by rw [hread]; rfl)
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice
    unfold laterCollectionCall
    rw [ite_eq_left hdomain.1]
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals first | contradiction | (rw [← Option.some.inj hchoice])
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        have hlater : s < registers.payload.sigma.val := by simpa only [hc] using hdomain.2
        simp only [ite_eq_left hlater]

/-- A retained collection choice has a real selected payload, with the same
whole payload as its extractor context. -/
private theorem choice_selection (r : RoundRecord (p := p) (rate := rate))
    (ctx : Choice rate) (hchoice : choice r.input = some ctx) :
    ∃ v : Selection r.input,
      r.output.preparation.coordinator.selection = some v ∧ v.view.payload = ctx.payload := by
  classical
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice hn
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next core snapshot hboundary hchecked =>
        rw [← Option.some.inj hchoice]
        exact ⟨_, rfl, rfl⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        simp only [DispatchCut.selection, selectionAt, dite_true]
        exact ⟨_, rfl, rfl⟩

/-- At an original retained row after the selected payload's true cutoff,
actual START and retained-DOWN phase force every ordinary choice unoccupied.
A current DOWN first accepted during collection is included. -/
private theorem completed_prepared_unoccupied
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (done : CompletedRound rate)
    (hextract : extractRound (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] = some done)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.row) ≤
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.time.val + 1) :
    preparedFollowersUnoccupied (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val] := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]
  have hchoice := (actual_collection_round_checked r done hextract).1
  obtain ⟨v, hv, hpayload⟩ := choice_selection r done.context hchoice
  obtain ⟨states, memories, hstates, hdown, _, _⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h z k v hv
  intro i
  change match (ReferenceFollowerFixedReply.actualChoice r i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False
  rw [hstates i]
  by_contra hoccupied
  have hcurrent := hdown i hoccupied
  rw [hpayload] at hcurrent
  obtain ⟨before, memory, chosen, hbefore, hdomain, hstart, hchosen, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z k i
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hstates i).symm.trans hchosen)
  have hchosenEq : chosen = states i := heq.1.symm
  rw [hchosenEq] at hstart
  have hbeforeDown : before.lastDown = some (done.context.payload.downRecord i) :=
    (ActiveFollowerLifecycle.startRound_frame rate.eta r.input.time before (states i)
      memory memory hstart).1.symm.trans hcurrent
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h z k i before memory hbefore
      (done.context.payload.downRecord i) hbeforeDown
  have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
    rate rewards C_star C_h z k i before memory hbefore
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    (rate := rate) r.input.time r.input.row before (states i) memory memory
      (done.context.payload.downRecord i) hbeforeDown hphase htoken hstart
  have hstartEq : ActiveFollowerDownAcceptance.downStart p rate
      (done.context.payload.downRecord i) = done.context.payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
      (done.context.payload.downRecord i)
    change _ + 1 = done.context.payload.sigma.val + 1 at hval
    omega
  apply hoccupied
  apply hstatus.mpr
  rw [hstartEq]
  exact hcut

/-- Accepted and rejected UP decoding preserve all three old dates. -/
private theorem decode_frame (l result : Ledger rate)
    (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (h : CoordinatorCollectionLedger.decodeUp l i parsed = .success result ∨
      CoordinatorCollectionLedger.decodeUp l i parsed = .rejected result) :
    (result.sigma, result.cutoff, result.freezeAt) = (l.sigma, l.cutoff, l.freezeAt) := by
  rcases h with hs | hr
  · cases parsed with
    | none =>
      unfold CoordinatorCollectionLedger.decodeUp at hs
      split at hs
      next =>
        dsimp only at hs
        split at hs <;> contradiction
      next => contradiction
    | some M =>
      obtain ⟨_, _, _, _, _, _, _, _, heq⟩ :=
        CollectionCheckedExecution.decodeUp_success_candidate l result i M hs
      rw [heq]
      rfl
  · rw [CollectionKnownQueueContinuation.decodeUp_rejected_candidate l result i parsed hr]

/-- This is a structural frame of one actual checked round, independent of
known queues and of every numerical replay equation. -/
private theorem checked_one_frame (l result : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (accepted : Bool)
    (h : CollectionCheckedExecution.checkedRounds l [input] = some ([accepted], result)) :
    (result.sigma, result.cutoff, result.freezeAt) = (l.sigma, l.cutoff, l.freezeAt) := by
  cases hs : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw with
  | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at h
  | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at h
  | success started =>
    have hstart := CollectionCheckedExecution.startRound_success_candidate l started
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw hs
    have hframe : (started.sigma, started.cutoff, started.freezeAt) =
        (l.sigma, l.cutoff, l.freezeAt) := by rw [hstart]; rfl
    cases hd : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed with
    | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, reduceCtorEq] at h
    | success decoded | rejected decoded =>
      have hdframe : (decoded.sigma, decoded.cutoff, decoded.freezeAt) =
          (started.sigma, started.cutoff, started.freezeAt) := by
        apply decode_frame
        first | exact Or.inl hd | exact Or.inr hd
      cases hf : CoordinatorCollectionLedger.finishRound decoded with
      | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at h
      | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at h
      | success finished =>
        have hfinish := CollectionCheckedExecution.finishRound_success_candidate decoded finished hf
        simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, Option.some.injEq,
          Prod.mk.injEq, List.cons.injEq, and_true] at h
        have hresult : finished = result := h.2
        rw [← hresult, hfinish]
        exact hdframe.trans hframe

/-- Transport the fixed dates only along the literal continuing prefix. -/
private theorem continuing_frames
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hcoord : initial.coordinator = .collection P l saved) :
    ∀ r ∈ records.takeWhile continuing, ∀ done : CompletedRound rate,
      extractRound r = some done →
      (done.context.preLedger.sigma, done.context.preLedger.cutoff,
        done.context.preLedger.freezeAt) = (l.sigma, l.cutoff, l.freezeAt) := by
  induction records generalizing initial P l saved with
  | nil => simp only [List.takeWhile_nil, List.not_mem_nil, false_implies, implies_true]
  | cons r rest ih =>
    by_cases hc : continuing r = true
    · rw [List.takeWhile_cons, hc]
      obtain ⟨done, hext⟩ := Option.isSome_iff_exists.mp (continuing_isSome r hc)
      obtain ⟨hchoice, _, hchecked, Pnext, savedNext, hnext⟩ :=
        actual_collection_round_checked r done hext
      have hpre := (choice_collection_pre r.input P l saved done.context
        (by rw [hchain.1]; exact hcoord) hchoice).1
      have hframe := checked_one_frame done.context.preLedger done.final done.input done.accepted hchecked
      have htail := ih r.output.next Pnext done.final savedNext hchain.2 hnext
      intro r' hr done' hext'
      rcases List.mem_cons.mp hr with hsame | hrest
      · subst r'
        have hd : done' = done := Option.some.inj (hext'.symm.trans hext)
        rw [hd, hpre]
      · exact (htail r' hrest done' hext').trans (by simpa only [hpre] using hframe)
    · have hc' : continuing r = false := Bool.eq_false_iff.mpr hc
      simp only [List.takeWhile_cons, hc', Bool.false_eq_true, ↓reduceIte,
        List.not_mem_nil, false_implies, implies_true]

/-- The actual segment's per-row contexts retain its entry dates. -/
private theorem segment_frames
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (seg : Segment rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hseg : segment records = some seg) :
    ∀ r ∈ seg.records, ∀ done : CompletedRound rate, extractRound r = some done →
      (done.context.preLedger.sigma, done.context.preLedger.cutoff,
        done.context.preLedger.freezeAt) =
      (seg.context.preLedger.sigma, seg.context.preLedger.cutoff, seg.context.preLedger.freezeAt) := by
  cases records with
  | nil => simp only [ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hseg
  | cons entry rest =>
    unfold ReferenceCollectionSegmentExtraction.segment at hseg
    cases hc : choice entry.input with
    | none => simp only [hc, Option.map_none, reduceCtorEq] at hseg
    | some ctx =>
      simp only [hc, Option.map_some] at hseg
      cases he : extractRound entry with
      | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hseg
        cases Option.some.inj hseg
        simp only [List.not_mem_nil, false_implies, implies_true]
      | some done =>
        simp only [he, Option.isSome_some, ↓reduceIte] at hseg
        cases Option.some.inj hseg
        obtain ⟨hchoice, _, hchecked, Pnext, savedNext, hnext⟩ :=
          actual_collection_round_checked entry done he
        have hctx : done.context = ctx := Option.some.inj (hchoice.symm.trans hc)
        have hframe := checked_one_frame done.context.preLedger done.final done.input done.accepted hchecked
        have htail := continuing_frames rest entry.output.next final Pnext done.final savedNext hchain.2 hnext
        intro r hr done' hext
        rcases List.mem_cons.mp hr with hsame | hrest
        · subst r
          have hd : done' = done := Option.some.inj (hext.symm.trans he)
          rw [hd, hctx]
        · exact (htail r hrest done' hext).trans (by simpa only [hctx] using hframe)

private theorem readout_exists (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (done : CompletedRound rate) (hextract : extractRound r = some done)
    (hunoccupied : preparedFollowersUnoccupied r) (hlater : s < done.context.payload.sigma.val) :
    ∃ c, laterCollectionReadout s r = some c := by
  classical
  have hchoice := (actual_collection_round_checked r done hextract).1
  apply Option.isSome_iff_exists.mp
  apply (laterCollectionReadout_domain s r).mpr
  refine ⟨hunoccupied, ?_⟩
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals first | contradiction | trivial
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice] at hlater
        exact hlater

/-- On the canonical SOME, the literal recorder and old-boundary physical
record agree on every arm, first with the guard and then without it. -/
private theorem readout_record (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K) (l0 : Ledger rate)
    (hextract : extractRound r = some done) (hread : laterCollectionReadout s r = some c)
    (hframe : (done.context.preLedger.sigma, done.context.preLedger.cutoff,
      done.context.preLedger.freezeAt) = (l0.sigma, l0.cutoff, l0.freezeAt))
    (hsigma : 0 < l0.sigma) (hcutoff : l0.cutoff ≤ r.input.time.val + 1) :
    c.enabled = collectionEnabled l0 r.input.time ∧
    c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
    c.rate = done.context.payload.rate ∧
    c.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
    ∃ out : CoordinatorRecordingOperation.Output p,
      laterCollectionCall s r = some ⟨done.context.payload, done.context.preLedger,
        done.context.started, done.context.weights⟩ ∧
      CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
        done.context.payload done.context.started done.context.weights) = some out ∧
      r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
      rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) ∧
      (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
      (∀ a, physicalQueueRecord l0 a r = (c.enabled,
        if r.input.time.val + 1 < l0.freezeAt then
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a else 0)) ∧
      (c.enabled = false → c.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
      (∀ a, physicalQueueRecord l0 a r = (c.enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) := by
  classical
  obtain ⟨P, l, started, weights, out, hcall, hdiag, hrun, henabled, hclock,
    hrate, hreward, hrecording, hgate, harrival⟩ := laterCollectionReadout_call s r c hread
  have hcanonical := readout_call_context s r c done hread hextract
  have heq := Option.some.inj (hcall.symm.trans hcanonical)
  cases heq
  have hfields := Prod.mk.inj hframe
  have hs : done.context.preLedger.sigma = l0.sigma := hfields.1
  have hc : done.context.preLedger.cutoff = l0.cutoff := (Prod.mk.inj hfields.2).1
  have hg : done.context.preLedger.freezeAt = l0.freezeAt := (Prod.mk.inj hfields.2).2
  have henabled0 : c.enabled = collectionEnabled l0 r.input.time := by
    rw [henabled]
    simp only [collectionEnabled, hs, hc, hg]
  have henabledFreeze : c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) := by
    rw [henabled0]
    simp only [collectionEnabled, hsigma, hcutoff, true_and]
  change r.output.coordinator.recording = some out at hrecording
  have hraw : rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) := by
    simp only [rawDiagnostic, hrecording, Option.bind_some]
  have harr : ∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
    intro a
    rw [hraw]
    exact harrival a
  have hgated : ∀ a, physicalQueueRecord l0 a r = (c.enabled,
      if r.input.time.val + 1 < l0.freezeAt then
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a else 0) := by
    intro a
    simp only [physicalQueueRecord, ← henabled0, ← henabledFreeze, Bool.and_self, harr a]
  have hdisabled := readout_disabled s r c hread
  refine ⟨henabled0, henabledFreeze, hrate, hreward, out, hcanonical, hrun,
    hrecording, hgate, hraw, harr, hgated, hdisabled, ?_⟩
  intro a
  rw [hgated]
  by_cases hfreeze : r.input.time.val + 1 < l0.freezeAt
  · rw [ite_eq_left hfreeze]
  · have he : c.enabled = false := by simp only [henabledFreeze, hfreeze, decide_false]
    rw [ite_eq_right hfreeze, (hdisabled he).2 a]

/-- The actual empty-pending installation has its actual live successor.
This consumes E on the same original index, without a numerical seed. -/
private theorem empty_birth_live
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input = true) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ∃ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout) (beta : Fin (p.m - 1) → ℕ),
      r.output.next.coordinator = .live rout qout beta ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth r rout.payload ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < rout.payload.sigma.val := by
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨P, l, saved, hstate, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hlater
  have hE := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z k
  dsimp only at hE
  rw [hstate] at hE
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
    hkind, consistent, output, hlocal, hoperation, clockData, installation, selected,
    hinstall, hresult, hdispatch, hprepared, hpayload, hvector, hown, hbase, hqueues,
    hanchor, v, hselection, hvpayload, hvcutoff, hlive, hstrict,
    c, ho, cell, hreadout, hcell, hcellSelected, hstates, hmemories, hunoccupied,
    henabled, hrate, hreward, hmarker, hrows, hJ, hrewards, hquant, hsaved,
    hoccupied, howner, out, serviced, pending, finished, hrun, hrecording, hserviced,
    hraw, hnum, hconfirm, hfinish, hpost, hdiag, hnext, hbank⟩ := hE hempty
  rw [hpost] at hnext
  refine ⟨_, _, _, hnext, ?_, hstrict⟩
  simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hprepared]
  refine ⟨trivial, ?_⟩
  rw [hpayload, output.payload_start, htime]


private theorem readout_rebase (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K)
    (hchoice : choice r.input = some done.context)
    (hread : laterCollectionReadout 0 r = some c)
    (hlater : s < done.context.payload.sigma.val) :
    laterCollectionReadout s r = some c := by
  classical
  have hunoccupied := ((laterCollectionReadout_domain 0 r).mp (by rw [hread]; rfl)).1
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice
    unfold laterCollectionReadout at hread ⊢
    rw [dite_eq_left hunoccupied] at hread ⊢
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals first | contradiction | (simpa only [hc] using hread)
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice] at hlater
        change s < registers.payload.sigma.val at hlater
        have hzero : 0 < registers.payload.sigma.val := by omega
        simpa only [hc, dite_eq_left hlater, dite_eq_left hzero] using hread

/-- A local join on the exact segment returned by `segmentAt`. All localizers
here are produced by the root's single outside-cutoff elimination. -/
private theorem firstCell_segment_cover
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (e : ℕ) (seg : Segment rate) (I : Initializer p)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (hinit : I.checkedStart rate = .success seg.context.preLedger)
    (hsigma : I.sigma = t.val + 1)
    (hcutoff : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))))
    (hdate : I.cutoff = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (hcalendar : seg.records.map (fun r => r.input.time.val) =
      List.range' (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e)
        seg.records.length)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
      seg.context.payload.sigma.val)
    (hentry : ∃ c, laterCollectionReadout 0 seg.entry = some c) :
    ∀ r ∈ seg.records, ∃ (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K),
      extractRound r = some done ∧ preparedFollowersUnoccupied r ∧
      laterCollectionReadout (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some c ∧
      done.context.payload = seg.context.payload ∧
      done.context.preLedger.sigma = seg.context.preLedger.sigma ∧
      done.context.preLedger.cutoff = seg.context.preLedger.cutoff ∧
      done.context.preLedger.freezeAt = seg.context.preLedger.freezeAt ∧
      c.enabled = collectionEnabled seg.context.preLedger r.input.time ∧
      c.enabled = decide (r.input.time.val + 1 < seg.context.preLedger.freezeAt) ∧
      c.rate = seg.context.payload.rate ∧
      c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      ∃ out : CoordinatorRecordingOperation.Output p,
        laterCollectionCall (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r =
          some ⟨done.context.payload, done.context.preLedger, done.context.started, done.context.weights⟩ ∧
        CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
          done.context.payload done.context.started done.context.weights) = some out ∧
        r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
        rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) ∧
        (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (∀ a, physicalQueueRecord seg.context.preLedger a r = (c.enabled,
          if r.input.time.val + 1 < seg.context.preLedger.freezeAt then
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a else 0)) ∧
        (c.enabled = false → c.recordedArm = none ∧ ∀ a,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
        (∀ a, physicalQueueRecord seg.context.preLedger a r = (c.enabled,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hbranch := (segmentAt_branch R e seg hseg).1
  have hgood := segment_all_completed (R.drop e) seg hbranch
  have hpart := segmentAt_partition R e seg hseg
  have hB := ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
    rate rewards C_star C_h u t z hz e seg hseg hne hcut
  obtain ⟨hc, _⟩ := ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
    rate rewards C_star C_h u t z hz.1
  obtain ⟨initial, hlaunch, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hc
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h initial hlaunch
  have hdrop := connected_drop R initial _ e hchain
  have hframes := segment_frames (R.drop e) _ _ seg hdrop hbranch
  have hinitFields := CollectionBufferProvenance.startCollectionChecked_success_context
    I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside seg.context.preLedger hinit
  have hpositive : 0 < seg.context.preLedger.sigma := by rw [hinitFields.2.1, hsigma]; omega
  intro r hr
  obtain ⟨done, hext⟩ := Option.isSome_iff_exists.mp (hgood r hr)
  have hchoice := (actual_collection_round_checked r done hext).1
  have hpay : done.context.payload = seg.context.payload := hB.2.2.1 r hr done.context hchoice
  have hrR : r ∈ R := List.mem_of_mem_drop (by
    rw [← hpart]
    exact List.mem_append.mpr (Or.inl hr))
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hrR
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k] = r at hkr
  have hinputs := hB.2.1 r hrR
  have hrow : r.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change r.input.rows r.input.selected = _
    rw [hinputs.1, hinputs.2.1]
  have htimeMem : r.input.time.val ∈ List.range' (s + e) seg.records.length := by
    rw [← hcalendar]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have hdateLe := (List.mem_range'_1.mp htimeMem).1
  have hcutLe : seg.context.preLedger.cutoff ≤ r.input.time.val + 1 := by
    rw [hinitFields.2.2.2.1, hdate]
    omega
  have htrueCut : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤ r.input.time.val + 1 := by
    rw [hpay, hrow, ← hcutoff, hdate]
    omega
  have hunoccupied : preparedFollowersUnoccupied r := by
    by_cases heq : r = seg.entry
    · rw [heq]
      obtain ⟨c0, hc0⟩ := hentry
      exact ((laterCollectionReadout_domain 0 seg.entry).mp (by rw [hc0]; rfl)).1
    · have hactual := completed_prepared_unoccupied rewards C_star C_h z ⟨k, hk⟩ done
        (by simpa only [hkr] using hext) (by simpa only [hkr] using htrueCut)
      simpa only [hkr] using hactual
  have hlater' : s < done.context.payload.sigma.val := by rw [hpay]; exact hlater
  obtain ⟨c, hread⟩ : ∃ c, laterCollectionReadout s r = some c := by
    by_cases heq : r = seg.entry
    · obtain ⟨c0, hc0⟩ := hentry
      exact ⟨c0, readout_rebase s r done c0 hchoice (by rw [heq]; exact hc0) hlater'⟩
    · exact readout_exists s r done hext hunoccupied hlater'
  have hframe := hframes r hr done hext
  have hfields := Prod.mk.inj hframe
  obtain ⟨henabled, hfreeze, hrate, hreward, hrecorder⟩ :=
    readout_record s r done c seg.context.preLedger hext hread hframe hpositive hcutLe
  refine ⟨done, c, hext, hunoccupied, hread, hpay, hfields.1,
    (Prod.mk.inj hfields.2).1, (Prod.mk.inj hfields.2).2,
    henabled, hfreeze, ?_, ?_, hinputs.1, hinputs.2.1, hinputs.2.2, hrecorder⟩
  · rw [hrate, hpay]
  · rw [hreward, hinputs.2.2]

/-- Canonical all-arm readout on the actual first-corrected replacement
collection. The horizon branch demands no later round or installation.
All witnesses are those of the one actual outside-cutoff frontier. -/
theorem firstCell_collection_readout_cover
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∃ (birth : RoundRecord (p := p) (rate := rate))
      (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout) (beta : Fin (p.m - 1) → ℕ),
      R[b]? = some birth ∧ s + b = t.val ∧ birth.input.time = t ∧
      birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth rout.payload ∧
      rout.payload.sigma = t ∧ s < rout.payload.sigma.val ∧
      birth.output.next.coordinator = .live rout qout beta ∧
      ∀ _hq : t.val + 1 < p.T,
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1)
        let e := b + 1 + W.length
        e ≤ R.length ∧ t.val + 1 + W.length ≤ p.T ∧
        ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
          rE.payload = rout.payload ∧
          (∀ he : e < R.length, (R[e]'he).input.state.coordinator = .live rE qE beta) ∧
          (e = R.length ∨ ∃ (he : e < R.length) (seg : Segment rate)
            (I : Initializer p) (l0 : Ledger rate),
            segmentAt R e = some seg ∧ seg.entry = R[e] ∧
            seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
            seg.context.initializer = some I ∧
            I = cutoffInitializer (liveRegistersAt rE (R[e]'he).input.time)
              (liveOwnedAt rE qE (R[e]'he).input.time) beta (R[e]'he).input.time ∧
            I.checkedStart rate = .success l0 ∧
            I.assignment.arm = rout.payload.assignment.assigned ∧
            I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
            I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
            I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
            ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
            (∃ during, seg.records = seg.entry :: during) ∧
            seg.records ++ seg.remaining = R.drop e ∧
            seg.records.map (fun r => r.input.time.val) = List.range' (s + e) seg.records.length ∧
            ∀ r ∈ seg.records, ∃ (done : CompletedRound rate) (c : RecordedQueueRun.RoundInput p.K),
              extractRound r = some done ∧ preparedFollowersUnoccupied r ∧
              laterCollectionReadout s r = some c ∧
              done.context.payload = rout.payload ∧
              done.context.preLedger.sigma = l0.sigma ∧
              done.context.preLedger.cutoff = l0.cutoff ∧
              done.context.preLedger.freezeAt = l0.freezeAt ∧
              c.enabled = collectionEnabled l0 r.input.time ∧
              c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
              c.rate = rout.payload.rate ∧
              c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
              r.input.rows = z.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
              r.input.rewards = rewards ∧
              ∃ out : CoordinatorRecordingOperation.Output p,
                laterCollectionCall s r =
                  some ⟨done.context.payload, done.context.preLedger, done.context.started, done.context.weights⟩ ∧
                CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
                  done.context.payload done.context.started done.context.weights) = some out ∧
                r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
                rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) ∧
                (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
                (∀ a, physicalQueueRecord l0 a r = (c.enabled,
                  if r.input.time.val + 1 < l0.freezeAt then
                    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a else 0)) ∧
                (c.enabled = false → c.recordedArm = none ∧ ∀ a,
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                (∀ a, physicalQueueRecord l0 a r = (c.enabled,
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) := by
  classical
  intro R s b
  obtain ⟨L, cbirth, birth, hL, hcbirth, hprefix, hLb, hbsub, hdate,
    henabled, hb, har, ht, hrows, hJ, hrewards, hcurrent, hnext, hcont⟩ :=
    ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin.firstCell_outside_cutoff_numerical_join
      rate rewards C_star C_h u t z hz
  obtain ⟨r', har', hlaterBirth⟩ :=
    (ReferenceFirstCollectionCurrentNumericalCell.currentCell_isSome_iff
      rate rewards C_star C_h u t z hz.1).mp (by rw [hcbirth]; rfl)
  have hsameBirth : r' = birth := Option.some.inj (har'.symm.trans har)
  rw [hsameBirth] at hlaterBirth
  obtain ⟨hbindex, hbirthIndex⟩ := List.getElem?_eq_some_iff.mp hb
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b] = birth at hbirthIndex
  obtain ⟨rout, qout, beta, hlive, hborn, hlater⟩ :=
    empty_birth_live rewards C_star C_h z ⟨b, hbindex⟩ (by
      change ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b].input = true
      rw [hbirthIndex]
      exact hlaterBirth)
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b].output.next.coordinator =
    .live rout qout beta at hlive
  change ReferenceAssignmentPayloadPersistence.InstallationBirth
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b] rout.payload at hborn
  rw [hbirthIndex] at hlive hborn
  dsimp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] at hcont
  obtain ⟨hsigma, htail⟩ := hcont rout qout beta hlive
  refine ⟨birth, rout, qout, beta, hb, hdate, ht, hrows, hJ, hrewards,
    hborn, hsigma, hlater, hlive, ?_⟩
  intro hq
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let e := b + 1 + W.length
  obtain ⟨next, hk, hstate, hlater', hn, hnstate, hB, hbound, hT, htimes, hends, hend⟩ := htail hq
  obtain ⟨hAprefix, hAlength, hAdate, rE, qE, hp, hout, hin, hvalues, hboundary⟩ := hend
  refine ⟨hbound, hT, rE, qE, hp, hin, ?_⟩
  rcases hboundary with hhorizon | ⟨he, chosen, hchosen, hprepared, hbranch⟩
  · exact Or.inl hhorizon
  · apply Or.inr
    cases chosen <;> try contradiction
    next dispatched hs ledger hi heq hd hclock hpending hno selected =>
      obtain ⟨htau, htau', huc, htrueCut, seg, I, hseg, hentry, hpay, hpre,
        hsomeI, hI, hinit, harm, hIsigma, hIcut, hIfreeze, hIbase,
        hnonempty, hpartition, hexit, hrun, hcalendar, hcount, hpositive,
        houtnum, hassigned, ccut, hcell0, hread0, hprefixCut, hcutEnabled,
        hcutRate, hcutReward, hrest⟩ := hbranch
      have hne : seg.records ≠ [] := by
        obtain ⟨tail, hrecords⟩ := hnonempty
        rw [hrecords]
        exact List.cons_ne_nil _ _
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
        rw [hentry]
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        have hprep : (prepare (R[e]'he).input).coordinator = (R[e]'he).output.preparation.coordinator := by
          rw [(R[e]'he).output_eq]; rfl
        rw [hprep, hprepared]
      have hgood := segment_all_completed (R.drop e) seg (segmentAt_branch R e seg hseg).1
      have hcal : seg.records.map (fun r => r.input.time.val) =
          List.range' (s + e) seg.records.length := by
        rw [← inputs_calendar seg.records hgood]
        exact hcalendar.trans (by rw [htau])
      have hcover := firstCell_segment_cover rewards C_star C_h u t z hz e seg I hseg hne hcut
        (by rw [hpre]; exact hinit) hIsigma
        (by rw [hpay, hIcut]; exact htrueCut)
        (hIcut.trans huc) hcal (by rw [hpay]; exact hlater)
        ⟨ccut, by rw [hentry]; exact hread0⟩
      refine ⟨he, seg, I, _, hseg, hentry, hpay, hpre, hsomeI, hI, hinit, harm,
        hIsigma, hIcut.trans huc, hIcut.trans htrueCut, hIfreeze, hIbase, hcut,
        ?_, hpartition, hcal, ?_⟩
      · obtain ⟨tail, hrecords⟩ := hnonempty
        exact ⟨tail, hentry.symm ▸ hrecords⟩
      · simpa only [hpay, hpre] using hcover

end Bandits.Support.ReferenceFirstCorrectedReplacementCollectionReadout
