/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCalendarReplay
public import Bandits.Support.ReferenceFirstCollectionOfferedSenderReplay

import Lean.Elab.Tactic.Omega

/-!
# Filtered first-collection UP budgets

For an actually selected first-collection input, a successful filtered UP
parse and the actual local acceptance check identify the current ordinary
offer and supply its incoming numeric budgets. The same query is joined to the
existing prefix and pure-candidate calendar replay exports.

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`. These are
internal actual-operation results; they do not assert receiver success,
checked-start/finish success, source queue truth, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstCollectionParsedUpBudgets

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

private theorem validLedgerCheck_of_actual_choice
    (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    CoordinatorCollectionLedger.validLedgerCheck c.preLedger = true := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next _ =>
    cases hcut : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome =>
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] at hchoice
    | live registers owned base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart ledger hinitialization _hledger hdomains
            hclock hpending hnoAssignment selected =>
          have hselected :
              (⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                dispatched.startResult,
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights,
                some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
                  base x.time)⟩ : ReferenceCollectionSegmentExtraction.Choice rate) = c := by
            simpa [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] using hchoice
          cases hselected
          rcases hdomains with ⟨_, _, _, _, _, _, _, _, _, _, _, hdomainLedgerValid⟩
          have hledgerValid :
              CoordinatorCollectionLedger.validLedgerCheck ledger = true := by
            simpa [_hledger] using hdomainLedgerValid
          rcases ReferenceActivePhysicalStep.sharedLedger_fields
              (rate := rate) ledger with
            ⟨hassignment, hsigma, hcutoff, hfreezeAt, hbaseScore, hpending,
              hcutoffRegisters, hcurrentRegisters, hincrement, hgammaLoc,
              hrawBuffer, henabledHistory, hcursor, hphase⟩
          change CoordinatorCollectionLedger.validLedgerCheck
            (ReferenceActivePhysicalStep.sharedLedger ledger) = true
          simpa only [CoordinatorCollectionLedger.validLedgerCheck,
            CoordinatorCollectionLedger.readyHistoryCheck,
            CoordinatorCollectionLedger.startedHistoryCheck,
            CoordinatorCollectionLedger.registerDomainsCheck,
            CoordinatorCollectionLedger.rawEntryDomainsCheck,
            CoordinatorCollectionLedger.armPendingCheck,
            hassignment, hsigma, hcutoff, hfreezeAt, hbaseScore, hpending,
            hcutoffRegisters, hcurrentRegisters, hincrement, hgammaLoc,
            hrawBuffer, henabledHistory, hcursor, hphase] using hledgerValid
        | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] at hchoice
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary currentScores =>
          have hselected :
              (⟨payload, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
                none⟩ : ReferenceCollectionSegmentExtraction.Choice rate) = c := by
            simpa [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] using hchoice
          cases hselected
          exact core.ledger_valid
        | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] at hchoice
    | invalidCollectionCutoff =>
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] at hchoice
    | dagger =>
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcut] at hchoice

private theorem armPendingCheck_eq_true_iff_local
    (rate : RateInput p)
    (l : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem armPendingCheck_eq_true_of_member
    (rate : RateInput p)
    (l : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (i : Fin (p.m - 1)) (hi : i ∈ l.pending) :
    CoordinatorCollectionLedger.armPendingCheck l (l.assignment.arm i) = true := by
  exact (armPendingCheck_eq_true_iff_local rate l _).2 ⟨i, hi, rfl⟩

private theorem accepted_arm_registers_unknown
    (rate : RateInput p)
    (l : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (i : Fin (p.m - 1)) (hi : i ∈ l.pending)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true) :
    l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none := by
  have hchecks :=
    ReferenceFirstCutoffRecordedService.validLedger_pendingChecks l hvalid
  have hpendingCheck := armPendingCheck_eq_true_of_member rate l i hi
  have hcurrentNone :
      (l.currentRegisters (l.assignment.arm i)).isNone = true := by
    rw [hchecks.1 (l.assignment.arm i), hpendingCheck]
  have hcutoffNone :
      (l.cutoffRegisters (l.assignment.arm i)).isNone = true := by
    rw [hchecks.2 (l.assignment.arm i), hpendingCheck]
  constructor
  · cases h : l.currentRegisters (l.assignment.arm i) <;> simp_all
  · cases h : l.cutoffRegisters (l.assignment.arm i) <;> simp_all

private theorem filterRawByExpected_some
    {α : Type} {raw expected : Option α} {value : α}
    (h : ReferenceUpReception.filterRawByExpected raw expected = some value) :
    raw = some value ∧ expected = some value := by
  by_cases heq : raw = expected
  · have hraw : raw = some value := by
      simpa [ReferenceUpReception.filterRawByExpected, heq] using h
    exact ⟨hraw, heq.symm.trans hraw⟩
  · simp [ReferenceUpReception.filterRawByExpected, heq] at h

/-- The actual selected choice fixes the source assignment, cutoff context,
and ready ledger. Actual acceptance then makes its assigned arm pending and
both ledger register options unknown. `validLedgerCheck` is recovered from
the actual cutoff/continuing dispatcher constructors. -/
theorem actual_first_collection_accepted_arm_domain
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    let u := start + w + 1
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
    let x := B[n].input
    let i := ReferenceActivePhysicalStep.upSenderIndex x
    let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
    let arm := c.preLedger.assignment.arm i
    ∀ (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      CoordinatorCollectionLedger.acceptUpCheck lplus i M = true →
    ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
      initializer.sigma = start + 1 ∧
      initializer.cutoff = u ∧
      initializer.freezeAt = c.preLedger.freezeAt ∧
      initializer.assignment.arm = c.payload.assignment.assigned ∧
      CollectionBufferProvenance.collectionContext c.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) ∧
      c.preLedger.sigma = start + 1 ∧
      c.preLedger.cutoff = u ∧
      c.preLedger.assignment.arm = c.payload.assignment.assigned ∧
      c.preLedger.phase = .ready ∧
      c.preLedger.cursor = u + n.val ∧
      CoordinatorCollectionLedger.validLedgerCheck c.preLedger = true ∧
      i ∈ c.preLedger.pending ∧
      M.val.sigma = lplus.sigma ∧
      c.preLedger.currentRegisters arm = none ∧
      c.preLedger.cutoffRegisters arm = none ∧
      lplus.assignment = c.preLedger.assignment ∧
      lplus.sigma = start + 1 ∧
      lplus.cutoff = u ∧
      lplus.freezeAt = c.preLedger.freezeAt ∧
      lplus.baseScore = c.preLedger.baseScore ∧
      lplus.phase = .started ∧
      lplus.cursor = x.time.val + 1 ∧
      lplus.currentRegisters arm = none ∧
      lplus.cutoffRegisters arm = none := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  let u := start + w + 1
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  let arm := c.preLedger.assignment.arm i
  intro M haccept
  have hE := ReferenceFirstCollectionEnabledPrefix.actual_first_collection_enabled_history_prefix
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  rcases hE with ⟨hbranch, _hhistory, hphase, hcursor, _henabled, _hcandidateHistory⟩
  rcases hbranch with ⟨_cut, _suffix, _registers, _owned, _base, _c0, initializer,
    _segment, _hsplit, _hcutTime, _hc0Payload, _hinitializerDef, _hsegmentAt,
    _hentry, _hsegmentContext, _hcutChoice, _hc0Initializer, _hchecked,
    hinitSigma, hinitCutoff, _hinitFreeze, _hinitGrid, _hinitBase,
    _hinitAssignedOld, hinitAssigned, _hwpos, hpayload, hcontext, _htimeCurrent⟩
  have hcontextParts := hcontext
  simp only [CollectionBufferProvenance.collectionContext, Prod.mk.injEq]
    at hcontextParts
  rcases hcontextParts with ⟨hassignment, hsigma, hcutoff, hfreezeAt, _hbase⟩
  have hinitializerAssignment :
      initializer.assignment.arm = c.payload.assignment.assigned := by
    simpa only [hpayload] using hinitAssigned
  have hledgerSigma : c.preLedger.sigma = start + 1 := by
    rw [hsigma]
    exact hinitSigma
  have hledgerCutoff : c.preLedger.cutoff = u := by
    rw [hcutoff]
    exact hinitCutoff
  have hledgerAssignment :
      c.preLedger.assignment.arm = c.payload.assignment.assigned := by
    rw [hassignment]
    exact hinitializerAssignment
  have hvalid := validLedgerCheck_of_actual_choice rate x c hchoice
  have haccepted : lplus.cutoff ≤ lplus.cursor ∧
      i ∈ lplus.pending ∧ M.val.sigma = lplus.sigma := by
    simpa only [CoordinatorCollectionLedger.acceptUpCheck,
      Bool.and_eq_true, decide_eq_true_eq] using haccept
  have hpending : i ∈ c.preLedger.pending := by
    simpa only [lplus, CoordinatorCollectionLedger.startRoundCandidate] using haccepted.2.1
  have hsigmaAccepted : M.val.sigma = lplus.sigma := haccepted.2.2
  have hunknown := accepted_arm_registers_unknown rate c.preLedger i hpending hvalid
  have hlplusAssignment : lplus.assignment = c.preLedger.assignment := by
    rfl
  have hlplusSigma : lplus.sigma = start + 1 := by
    change c.preLedger.sigma = start + 1
    exact hledgerSigma
  have hlplusCutoff : lplus.cutoff = u := by
    change c.preLedger.cutoff = u
    exact hledgerCutoff
  have hlplusFreeze : lplus.freezeAt = c.preLedger.freezeAt := rfl
  have hlplusBase : lplus.baseScore = c.preLedger.baseScore := rfl
  have hlplusPhase : lplus.phase = .started := rfl
  have hlplusCursor : lplus.cursor = x.time.val + 1 := rfl
  have hlplusCurrent : lplus.currentRegisters arm = none := by
    simp [lplus, CoordinatorCollectionLedger.startRoundCandidate, arm,
      hunknown.1]
  have hlplusCutoffRegisters : lplus.cutoffRegisters arm = none := by
    change c.preLedger.cutoffRegisters arm = none
    exact hunknown.2
  refine ⟨initializer, hinitSigma, hinitCutoff, hfreezeAt.symm,
    hinitializerAssignment, hcontext, hledgerSigma, hledgerCutoff,
    hledgerAssignment, hphase, (by simpa [u] using hcursor),
    hvalid, hpending, hsigmaAccepted, hunknown.1, hunknown.2,
    hlplusAssignment, hlplusSigma, hlplusCutoff, hlplusFreeze, hlplusBase,
    hlplusPhase, hlplusCursor, hlplusCurrent, hlplusCutoffRegisters⟩

/-- Invert the exact current filtered parser. A returned record forces a
nonempty expected current word; that word is produced only by the actual
ordinary choice's checked offer. The accepted record is identified as the
whole subtype by `parseUp_encode`. -/
theorem actual_first_collection_filtered_parse_current_offer
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
    let x := B[n].input
    let i := ReferenceActivePhysicalStep.upSenderIndex x
    let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
    ∀ (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      ReferenceCollectionSegmentExtraction.effectiveParse x lplus = some M →
    ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (offered : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      (ReferenceFollowerFixedReply.actualChoice B[n] i).configuration =
        .ordinary state memory ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice B[n] i).follower
        (ReferenceFollowerFixedReply.actualChoice B[n] i).row
        (ReferenceFollowerFixedReply.actualChoice B[n] i).activation
        (ReferenceFollowerFixedReply.actualChoice B[n] i).time state = .offer offered ∧
      offered = M ∧
      ReferenceUpReception.currentOfferWord rate x.row i x.time
        (ReferenceFollowerFixedReply.actualChoice B[n] i)
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).1
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.1
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.2 =
      some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) M)) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  intro M hparse
  let preparedRound := ReferenceActivePhysicalStep.prepare x
  let preparedFollower := preparedRound.followers.followers i
  let raw := (CoordinatorUpReception.decoderTransition
    (ReferenceUpReception.receptionInputAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs preparedRound lplus) x.time)).2
  let expected := ReferenceActivePhysicalStep.upExpected preparedRound
  have hparser : CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected raw expected) = some M := by
    simpa [ReferenceCollectionSegmentExtraction.effectiveParse, raw,
      expected, preparedRound, x, i, lplus] using hparse
  cases hfiltered : ReferenceUpReception.filterRawByExpected raw expected with
  | none =>
      have hparseNone := hparser
      rw [hfiltered] at hparseNone
      change OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
          ((none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))).map
            (OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) =
        some M at hparseNone
      dsimp only [Option.map] at hparseNone
      simp only [OrdinaryMessageCodec.parseUp] at hparseNone
      cases hparseNone
  | some word =>
      have hrawExpected := filterRawByExpected_some hfiltered
      have hparseUp : OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
          (some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm word)) =
          some M := by
        have h := hparser
        rw [hfiltered] at h
        change OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
            ((some word : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))).map
              (OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) =
          some M at h
        dsimp only [Option.map] at h
        exact h
      have hcurrentExpected :
          ReferenceUpReception.currentOfferWord rate x.row i x.time preparedFollower
            (preparedRound.follower_alignment i).1
            (preparedRound.follower_alignment i).2.1
            (preparedRound.follower_alignment i).2.2.1 = some word := by
        simpa [expected, preparedFollower, preparedRound, i,
          ReferenceActivePhysicalStep.upExpected] using hrawExpected.2
      cases hconfiguration : preparedFollower.configuration with
      | dagger =>
          simp [ReferenceUpReception.currentOfferWord, hconfiguration]
            at hcurrentExpected
      | ordinary state memory =>
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              preparedFollower.follower preparedFollower.row preparedFollower.activation
              preparedFollower.time state with
          | failure =>
              simp [ReferenceUpReception.currentOfferWord, hconfiguration, hoff]
                at hcurrentExpected
          | noOffer =>
              simp [ReferenceUpReception.currentOfferWord, hconfiguration, hoff]
                at hcurrentExpected
          | offer offered =>
              have hflat : word =
                  (OrdinaryMessageCodec.wordEquivFlat
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered) := by
                have hsome := hcurrentExpected
                simp [ReferenceUpReception.currentOfferWord, hconfiguration, hoff]
                  at hsome
                exact (Option.some.inj hsome).symm
              let offeredC : OrdinaryMessageCodec.UpRecord
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) := offered
              have hflatC : word =
                  (OrdinaryMessageCodec.wordEquivFlat
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val) offeredC) := by
                simpa only [offeredC] using hflat
              have hencoded := OrdinaryMessageCodec.parseUp_some_sound
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) hparseUp
              let equiv := OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val)
              have hwordM : word = equiv
                  (OrdinaryMessageCodec.encodeUp
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val) M) := by
                have hflatM := congrArg (OrdinaryMessageCodec.wordEquivFlat
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val)) hencoded
                have hleft : word = equiv (equiv.symm word) :=
                  Eq.symm (equiv.apply_symm_apply word)
                exact hleft.trans hflatM
              have hencodeEq : OrdinaryMessageCodec.encodeUp
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val) offeredC =
                  OrdinaryMessageCodec.encodeUp
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val) M :=
                equiv.injective (hflatC.symm.trans hwordM)
              have hoffered : offeredC = M := by
                have hroundTrip := OrdinaryMessageCodec.parseUp_encode
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) offeredC
                rw [hencodeEq] at hroundTrip
                exact Option.some.inj (hroundTrip.symm.trans
                  (OrdinaryMessageCodec.parseUp_encode
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val) M))
              have houtput : B[n].output.preparation = preparedRound := by
                change B[n].output.preparation =
                  ReferenceActivePhysicalStep.prepare B[n].input
                rw [B[n].output_eq]
                simp [ReferenceActivePhysicalStep.step]
              have hactual :
                  ReferenceFollowerFixedReply.actualChoice B[n] i = preparedFollower := by
                change B[n].output.preparation.followers.followers i = _
                rw [houtput]
              have hconfigurationActual :
                  (ReferenceFollowerFixedReply.actualChoice B[n] i).configuration =
                    .ordinary state memory := by
                rw [hactual]
                exact hconfiguration
              have hoffActual : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  (ReferenceFollowerFixedReply.actualChoice B[n] i).follower
                  (ReferenceFollowerFixedReply.actualChoice B[n] i).row
                  (ReferenceFollowerFixedReply.actualChoice B[n] i).activation
                  (ReferenceFollowerFixedReply.actualChoice B[n] i).time state =
                    .offer offered := by
                simpa only [hactual] using hoff
              have hword := ReferenceUpReception.currentOfferWord_eq_encoded_offer
                rate x.row i x.time (ReferenceFollowerFixedReply.actualChoice B[n] i)
                (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).1
                (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.1
                (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.2
                state memory hconfigurationActual offered hoffActual
              refine ⟨state, memory, offeredC, hconfigurationActual, ?_,
                hoffered, ?_⟩
              · simpa only [offeredC] using hoffActual
              simpa only [x, i, offeredC, hoffered] using hword

/-- Join the original filtered parser and actual accepted-offer inputs to the
offered sender's first-collection replay, then attach both actual-choice
calendar replays at the same unknown assigned arm. All outputs remain local
to this observed query; the current candidate is pure and does not assert a
checked start, receive, or finish success. -/
theorem actual_first_collection_parsed_up_budget_calendar_replay_join
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    let u := start + w + 1
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice B[n].input = some c →
    let x := B[n].input
    let i := ReferenceActivePhysicalStep.upSenderIndex x
    let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
    let arm := c.preLedger.assignment.arm i
    ∀ (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      ReferenceCollectionSegmentExtraction.effectiveParse x lplus = some M →
      CoordinatorCollectionLedger.acceptUpCheck lplus i M = true →
    let Pn := W.take n.val
    let v := u + n.val
    let g := c.preLedger.freezeAt
    let hprefixBound : u - 1 + n.val ≤ p.T := by
      have htime : W[n].input.time.val + 1 = u + n.val := by
        simpa [u] using (ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
          rate source rewards C_star C_h count hcross hspan hshort n).2
      have hlast := W[n].input.time.isLt
      have hu : 1 ≤ u := by dsimp [u]; omega
      omega
    let prefixIndices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) n.val
      hprefixBound
    let prefixSequence :=
      ReferenceFirstCollectionCalendarReplay.prefixDiagnosticSequence rate Pn
    let prefixRows := fun chosenArm => Pn.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival prefixSequence chosenArm record.input.time
        else 0)
    let longer := Pn ++ [W[n]]
    let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
      ReferenceFirstCollectionCalendarReplay.first_collection_current_end_bound
        rate source rewards C_star C_h count hcross hspan hshort n
    let longerIndices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1)
      hlongerBound
    let candidateSequence :=
      ReferenceFirstCollectionCalendarReplay.prefixDiagnosticSequence rate longer
    let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
      W[n].input.time (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
    let candidateRows := fun chosenArm => longer.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival candidateSequence chosenArm record.input.time
        else 0)
    ∃ (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (offered : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
      (j : Fin execution.records.length)
      (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)),
      (∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
        initializer.sigma = start + 1 ∧
        initializer.cutoff = u ∧
        initializer.assignment.arm = c.payload.assignment.assigned ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base)) ∧
      c.preLedger.sigma = start + 1 ∧
      c.preLedger.cutoff = u ∧
      c.preLedger.assignment.arm = c.payload.assignment.assigned ∧
      CoordinatorCollectionLedger.validLedgerCheck c.preLedger = true ∧
      i ∈ c.preLedger.pending ∧
      c.preLedger.currentRegisters arm = none ∧
      c.preLedger.cutoffRegisters arm = none ∧
      lplus.sigma = start + 1 ∧
      lplus.cutoff = u ∧
      P0.sigma.val = start ∧
      (∀ a, P0.queues a = 0) ∧
      birth ∈ execution.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = start ∧
      (ReferenceFollowerFixedReply.actualChoice B[n] i).configuration =
        .ordinary state memory ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice B[n] i).follower
        (ReferenceFollowerFixedReply.actualChoice B[n] i).row
        (ReferenceFollowerFixedReply.actualChoice B[n] i).activation
        (ReferenceFollowerFixedReply.actualChoice B[n] i).time state = .offer offered ∧
      offered = M ∧
      ReferenceUpReception.currentOfferWord rate x.row i x.time
        (ReferenceFollowerFixedReply.actualChoice B[n] i)
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).1
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.1
        (ReferenceFollowerFixedReply.actualChoice_alignment B[n] i).2.2 =
        some ((OrdinaryMessageCodec.wordEquivFlat
          (CoordinatorCollectionLedger.codecParams p rate.eta.val))
          (OrdinaryMessageCodec.encodeUp
            (CoordinatorCollectionLedger.codecParams p rate.eta.val) M)) ∧
      state.lastDown = some message ∧
      j.val < w + n.val ∧
      (j.val < w ∨ w ≤ j.val ∧ j.val < w + n.val) ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown execution.records[j.val] i message ∧
      message = P0.downRecord i ∧
      message.val.sigma = start + 1 ∧
      message.val.q = 0 ∧
      M.val.sigma = start + 1 ∧
      M.val.S = (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          execution.records i j.val message w)).1 ∧
      M.val.q = (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          execution.records i j.val message w)).2 ∧
      M.val.delta =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            execution.records i j.val message w)).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            execution.records i j.val message (w - 1))).1 ∧
      (let Frec := ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          execution.records i j.val message w
       let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            execution.records i j.val message h)
       Frec.length = w ∧
       (∀ r ∈ Frec, r.2 ≤ ConstructorDimensions.D p) ∧
       (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * ConstructorDimensions.D p) ∧
       (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
       4 * rate.n ≤ ConstructorDimensions.D p) ∧
      M.val.S + M.val.q ≤ (lplus.cutoff - lplus.sigma) * ConstructorDimensions.D p ∧
      M.val.S ≤ (4 * rate.n) * (lplus.cutoff - lplus.sigma) ∧
      M.val.delta ≤ 4 * rate.n ∧
      4 * rate.n ≤ ConstructorDimensions.D p ∧
      u - 1 + (n.val + 1) ≤ p.T ∧
      prefixIndices = Pn.map (fun record => record.input.time) ∧
      prefixIndices.length = n.val ∧
      CoordinatorCollectionLedger.replayRecords? c.preLedger arm prefixIndices =
        some (prefixRows arm) ∧
      (∀ row, row ∈ prefixRows arm → row.2 ≤ ConstructorDimensions.D p) ∧
      longerIndices = longer.map (fun record => record.input.time) ∧
      longerIndices.length = n.val + 1 ∧
      CoordinatorCollectionLedger.replayRecords? candidate arm longerIndices =
        some (candidateRows arm) ∧
      (∀ row, row ∈ candidateRows arm → row.2 ≤ ConstructorDimensions.D p) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  let u := start + w + 1
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin B.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice B[n].input = some c → _
  intro n c hchoice
  dsimp only
  let x := B[n].input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n])
  let arm := c.preLedger.assignment.arm i
  intro M hparse haccept
  let Pn := W.take n.val
  let g := c.preLedger.freezeAt
  let hprefixBound : u - 1 + n.val ≤ p.T := by
    have htime : W[n].input.time.val + 1 = u + n.val := by
      simpa [u, start, execution, firstWindow, w, W] using
        (ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
          rate source rewards C_star C_h count hcross hspan hshort n).2
    have hlast := W[n].input.time.isLt
    have hu : 1 ≤ u := by dsimp [u]; omega
    omega
  let prefixIndices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) n.val
    hprefixBound
  let prefixSequence :=
    ReferenceFirstCollectionCalendarReplay.prefixDiagnosticSequence rate Pn
  let prefixRows := fun chosenArm => Pn.map fun record =>
    (decide (record.input.time.val + 1 < g),
      if record.input.time.val + 1 < g then
        CoordinatorCollectionLedger.explicitArrival prefixSequence chosenArm record.input.time
      else 0)
  let longer := Pn ++ [W[n]]
  let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
    ReferenceFirstCollectionCalendarReplay.first_collection_current_end_bound
      rate source rewards C_star C_h count hcross hspan hshort n
  let longerIndices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1)
    hlongerBound
  let candidateSequence :=
    ReferenceFirstCollectionCalendarReplay.prefixDiagnosticSequence rate longer
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    W[n].input.time (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
  let candidateRows := fun chosenArm => longer.map fun record =>
    (decide (record.input.time.val + 1 < g),
      if record.input.time.val + 1 < g then
        CoordinatorCollectionLedger.explicitArrival candidateSequence chosenArm record.input.time
      else 0)
  have hdomainRoot := actual_first_collection_accepted_arm_domain
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice M haccept
  rcases hdomainRoot with
    ⟨initializer, hinitSigma, hinitCutoff, _hinitFreeze, hinitializerAssignment,
      hcontext, hledgerSigma, hledgerCutoff, hledgerAssignment, _hphase, _hcursor,
      hvalid, hpending, hsigmaAccepted, hcurrentUnknown, hcutoffUnknown,
      _hlplusAssignment, hlplusSigma, hlplusCutoff, _hlplusFreeze, _hlplusBase,
      _hlplusPhase, _hlplusCursor, _hlplusCurrent, _hlplusCutoffRegisters⟩
  have hparseRoot := actual_first_collection_filtered_parse_current_offer
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice M hparse
  rcases hparseRoot with ⟨state, memory, offered, hconfiguration, hoff, hoffered, hword⟩
  have hprefixRoot := ReferenceFirstCollectionCalendarReplay.actual_first_collection_calendar_prefix_replay
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  rcases hprefixRoot with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprefixForArm⟩
  rcases hprefixForArm arm hcurrentUnknown with
    ⟨hprefixIndices, hprefixLength, _hprefixChronology, _hprefixRaw,
      hprefixReplay, hprefixRowsBound, _hprefixQueues, _hprefixScores⟩
  have hcandidateRoot := ReferenceFirstCollectionCalendarReplay.actual_first_collection_calendar_candidate_replay
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have hcandidate := hcandidateRoot arm hcurrentUnknown
  rcases hcandidate with
    ⟨hcandidateUnknown, _hcandidateRaw, hlongerIndices, hlongerLength,
      hlongerReplay, hcandidateRowsBound, _candidateQueues, _candidateScores⟩
  have hOroot := ReferenceFirstCollectionOfferedSenderReplay.run_first_collection_offered_sender_replay
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hOroot with
    ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hcutIndex, hcutTime, hcutState, hcutChosen, hP0, hP0sigma,
      hP0queues, _hfirstCutoff, hbirthMember, hbirthInstall, hbirthTime,
      _hbirthFirst, _hwindowLookup, hqueries⟩
  have htemp := hoff
  rw [hoffered] at htemp
  have hOquery := hqueries n i state memory M hconfiguration htemp
  rcases hOquery with ⟨_hOword, _hOfields, _hOstatus, hdownBranch⟩
  have hMpositive : M.val.sigma = start + 1 := by
    rw [hsigmaAccepted, hlplusSigma]
  rcases hdownBranch with hplaceholder | hprior
  · have hsigma := congrArg OrdinaryMessageCodec.UpFields.sigma hplaceholder.2
    rw [hMpositive] at hsigma
    simp [OrdinaryMessageCodec.upPlaceholder] at hsigma
  · rcases hprior with
      ⟨j, message, hj, hretained, hmessage, hlastDown, hmessageSigma,
        hmessageQ, hnumeric⟩
    let Frec := ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
      execution.records i j.val message w
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
        execution.records i j.val message h)
    rcases hnumeric with
      ⟨hMsigma, hMS, hMq, hMdelta, hFrecLength, harrivals, hjoint,
        hdeltaBound, hcapacity⟩
    have hMsigma' : M.val.sigma = start + 1 := hMsigma
    have hMdelta' : M.val.delta = (V w).1 - (V (w - 1)).1 := hMdelta
    have hwindowLength : lplus.cutoff - lplus.sigma = w := by
      rw [hlplusCutoff, hlplusSigma]
      change start + w + 1 - (start + 1) = w
      omega
    have hscoreRows : (V w).1 ≤ 4 * rate.n * Frec.length := by
      have h := ReplayWeightStability.replay_score_envelope (4 * rate.n) 0 0 Frec
      simpa [V, Frec] using h.2
    have hscoreEnvelope : (V w).1 ≤ 4 * rate.n * w := by
      rw [hFrecLength] at hscoreRows
      exact hscoreRows
    have hMS' : M.val.S = (V w).1 := hMS
    have hMq' : M.val.q = (V w).2 := hMq
    have hjointBudget : M.val.S + M.val.q ≤
        (lplus.cutoff - lplus.sigma) * ConstructorDimensions.D p := by
      rw [hMS', hMq', hwindowLength]
      exact hjoint w le_rfl
    have hscoreBudget : M.val.S ≤
        (4 * rate.n) * (lplus.cutoff - lplus.sigma) := by
      rw [hMS', hwindowLength]
      exact hscoreEnvelope
    have hMdeltaBound : M.val.delta ≤ 4 * rate.n := by
      rw [hMdelta']
      exact hdeltaBound
    have hnumericOutput :
        (let Frec := ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            execution.records i j.val message w
         let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              execution.records i j.val message h)
         Frec.length = w ∧
         (∀ r ∈ Frec, r.2 ≤ ConstructorDimensions.D p) ∧
         (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * ConstructorDimensions.D p) ∧
         (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
         4 * rate.n ≤ ConstructorDimensions.D p) := by
      exact ⟨hFrecLength, harrivals, hjoint, hdeltaBound, hcapacity⟩
    have hjSplit : j.val < w ∨ w ≤ j.val ∧ j.val < w + n.val := by
      by_cases hjw : j.val < w
      · exact Or.inl hjw
      · exact Or.inr ⟨by omega, by omega⟩
    have hinitializerContext :
        ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
          initializer.sigma = start + 1 ∧
          initializer.cutoff = u ∧
          initializer.assignment.arm = c.payload.assignment.assigned ∧
          CollectionBufferProvenance.collectionContext c.preLedger =
            (initializer.assignment, initializer.sigma, initializer.cutoff,
              initializer.freezeAt, initializer.base) := by
      exact ⟨initializer, hinitSigma, hinitCutoff, hinitializerAssignment, hcontext⟩
    refine ⟨P0, birth, state, memory, offered, j, message,
      hinitializerContext, hledgerSigma, hledgerCutoff, hledgerAssignment,
      hvalid, hpending, hcurrentUnknown, hcutoffUnknown, hlplusSigma,
      hlplusCutoff, ?_, hP0queues, hbirthMember, hbirthInstall,
      hbirthTime, hconfiguration, hoff, hoffered, hword, hlastDown, hj,
      hjSplit, hretained, hmessage,
      hmessageSigma, hmessageQ, hMsigma', hMS', hMq', hMdelta',
      hnumericOutput,
      hjointBudget, hscoreBudget, hMdeltaBound, hcapacity, hlongerBound,
      hprefixIndices, hprefixLength, hprefixReplay, hprefixRowsBound,
      hlongerIndices, hlongerLength, hlongerReplay,
      hcandidateRowsBound⟩
    · simpa [start, execution, firstWindow, w, W] using hP0sigma
