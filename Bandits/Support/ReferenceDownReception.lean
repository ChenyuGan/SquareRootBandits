/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.ActiveFollowerLogging
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CoordinatorLocalArmChoice
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.OrdinaryMessageCodec

/-!
# Reference-only DOWN receiver cut

This module compares one actual returned DOWN decoder word with the word
derived from the coordinator's concrete choice-time payload, pending set,
cutoff, complement weights, time, and the same complete row. It performs the
comparison before any cutoff scan, queue recovery, installation, or output
check. A choice view is only a local snapshot: it asserts no physical
provenance or chronology.

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,123-177,192-209,235-297`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceDownReception

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CoordinatorLocalArmChoice

variable {p : Parameters} {eta : LearningRate}

/-- Existing coordinator data read at this round's choice point. The actual
row and calendar slot are separate inputs, so this view adds no mutable clock
or score store and cannot substitute an arbitrary sent word. -/
structure ChoiceTimeView (p : Parameters) (eta : LearningRate) where
  payload : AssignmentStartPayload.Input p eta
  pendingAtChoice : Finset (ActiveRoundActions.Follower p.m)
  cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)
  complementWeights :
    (j : CanonicalFastSampling.FastArm payload.slowSet) → ℝ

/-- The ordinary coordinator's selected-DOWN branch for this follower. -/
def selectedDownSenderBranch (view : ChoiceTimeView p eta)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T) : Prop :=
  slotDraw (row.2 t).1 = downSlot ∧
    selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i ∧
    i ∈ view.pendingAtChoice

/-- The expected channel word is derived by running the accepted coordinator
choice on the same row and time. A missing view denotes the coordinator's
failure/dagger branch. Only its successful selected-DOWN-to-pending branch
has an encoded ordinary word. -/
noncomputable def expectedDownFlatWord
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) := by
  classical
  exact match view with
  | none => none
  | some view =>
      if CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
          view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none ∧
          selectedDownSenderBranch view i row t then
        some (CoordinatorLocalArmChoice.storedDownFlatWord view.payload i)
      else none

/-- The expected word is present exactly when the concrete coordinator choice
succeeds and its local branch sends DOWN to this pending follower. -/
theorem expectedDownFlatWord_eq_some_iff
    (view : ChoiceTimeView p eta) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) :
    expectedDownFlatWord (some view) i row t =
        some (CoordinatorLocalArmChoice.storedDownFlatWord view.payload i) ↔
      CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
        view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none ∧
        selectedDownSenderBranch view i row t := by
  classical
  by_cases h : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
      view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none ∧
      selectedDownSenderBranch view i row t
  · constructor
    · intro _
      exact h
    · intro _
      simp [expectedDownFlatWord, h]
      rfl
  · constructor
    · intro hEq
      simp [expectedDownFlatWord, h] at hEq
    · intro hFalse
      exact False.elim (h hFalse)

/-- The coordinator's exact returned-arm equation on its selected DOWN
branch. This is derived from the checked `coordinatorArmChoice`; validity is
not an extra argument. -/
theorem coordinatorArmChoice_eq_sendArm_of_selectedDownSenderBranch
    (view : ChoiceTimeView p eta) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T)
    (hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
      view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none)
    (hbranch : selectedDownSenderBranch view i row t) :
    CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
        view.pendingAtChoice view.cutoff t view.complementWeights row =
      some (ActiveRoundActions.sendArm
        (CoordinatorLocalArmChoice.currentDownHash view.payload (row.2 t) i)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
          (coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
          (followerPlayer p.two_le_m i))) := by
  rcases hbranch with ⟨hdown, hselected, hpending⟩
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload
      view.cutoff t view.complementWeights := by
    by_contra hinvalid
    apply hchoice
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
    exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
      view.payload view.pendingAtChoice view.cutoff t view.complementWeights
      (row.2 t) hinvalid
  have hnotfast :
      ¬ (CoordinatorLocalArmChoice.assignmentIsLive view.payload view.cutoff t ∧
        view.pendingAtChoice = ∅) := by
    have hnotempty : view.pendingAtChoice ≠ ∅ :=
      Finset.Nonempty.ne_empty ⟨i, hpending⟩
    rintro ⟨_, hempty⟩
    exact hnotempty hempty
  have hselectedPending :
      selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 ∈ view.pendingAtChoice := by
    rw [hselected]
    exact hpending
  have hnotdata : slotDraw (row.2 t).1 ≠ dataSlot := by
    rw [hdown]
    decide
  rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
  simpa only [hselected] using
    (CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down
      view.payload view.pendingAtChoice view.cutoff t view.complementWeights
      (row.2 t) hvalid hnotfast hnotdata hdown hselectedPending)

/-- A missing coordinator choice produces no expected word. -/
theorem expectedDownFlatWord_eq_none_of_coordinatorFailure
    (view : ChoiceTimeView p eta) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T)
    (hfailure : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
      view.pendingAtChoice view.cutoff t view.complementWeights row = none) :
    expectedDownFlatWord (some view) i row t = none := by
  simp [expectedDownFlatWord, hfailure]

/-- The ordinary parser applied to the returned raw word, retained for the
ordinary local acceptance/event test before reference suppression. -/
noncomputable def ordinaryParse (p : Parameters)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :=
  OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (raw.map
      (OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm)

/-- The ordinary receiver's local acceptance predicate on its retained parse. -/
def ordinaryLocalAcceptanceTest (p : Parameters)
    (rate : ActiveFollowerDownAcceptance.RateInput p) (t : Fin p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (parsed : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) : Prop :=
  match parsed with
  | none => False
  | some M => OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M

/-- One actual decoder result together with ordinary diagnostic observations
and the separately filtered reference result. `rawComparison = none` means
the receiver skipped or failed a pre-call check, so no decoder decision was
made. -/
structure ReferenceDownCutOutput (p : Parameters)
    (rate : ActiveFollowerDownAcceptance.RateInput p) where
  outcome : ActiveFollowerDownAcceptance.LocalDownResult p rate
  expectedWord : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  filteredRaw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  ordinaryParse : Option (OrdinaryMessageCodec.DownRecord
    (ReferencePrelaunchFollower.codecParams p rate.eta))
  ordinaryAcceptance : Prop
  rawComparison : Option Bool

/-- Whether an actual decoder output differs from the computed channel word.
This is not the manuscript's `E_false`: raw absence and ambiguous batches are
not classified as false acceptances by this predicate. -/
def rawMismatch {p : Parameters} {rate : ActiveFollowerDownAcceptance.RateInput p}
    (result : ReferenceDownCutOutput p rate) : Prop :=
  result.rawComparison = some false

/-- Exact per-decision `E_false` flag: the decoder returned a unique raw word,
it differs from the current encoded word, and the ordinary DOWN parser and
local acceptance test pass. This is not a batch-wide or run-wide event. -/
def wrongUniqueAccepted {p : Parameters}
    {rate : ActiveFollowerDownAcceptance.RateInput p}
    (result : ReferenceDownCutOutput p rate) : Prop :=
  result.rawComparison = some false ∧ result.raw ≠ none ∧
    result.ordinaryAcceptance

/-- The per-decision flag has exactly the wrong-raw, returned-word, and
ordinary-local-acceptance conditions. -/
theorem wrongUniqueAccepted_iff {p : Parameters}
    {rate : ActiveFollowerDownAcceptance.RateInput p}
    (result : ReferenceDownCutOutput p rate) :
    wrongUniqueAccepted result ↔
      result.rawComparison = some false ∧ result.raw ≠ none ∧
        result.ordinaryAcceptance := Iff.rfl

/-- The reference-only selected-unoccupied receiver operation. It performs
the exact ordinary DOWN selection, pre-choice status, register, batch, and
sparse-buffer checks before evaluating `currentDecodeStep` once. Immediately
after that call it compares the flattened raw output to the derived choice
word. A mismatch is retained as ordinary diagnostic data but the reference
transition receives no word and performs no scan, recovery, installation, or
recovery-output check. -/
noncomputable def referenceDownCut (p : Parameters)
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceDownCutOutput p rate := by
  classical
  let expected := expectedDownFlatWord view i row t
  exact if hselected : ActiveFollowerDownAcceptance.downSelected p i row t then
    if hstatus : state.status = .unoccupied then
      if hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state then
        if hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch then
          if hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer then
            let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
              p i row t feedback rate state
            let flattenedRaw := decoded.2
            if hmatches : flattenedRaw = expected then
              let parsed := ordinaryParse p rate decoded.2
              let accepted := ordinaryLocalAcceptanceTest p rate t state parsed
              let afterDecode := { state with downBatch := decoded.1 }
              let outcome :=
                match parsed with
                | none =>
                    ActiveFollowerDownAcceptance.LocalDownResult.decodeOrParseRejected
                      state afterDecode decoded.2
                | some M =>
                    if haccepted : OrdinaryMessageCodec.acceptDown
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M then
                      let hstart := ActiveFollowerDownAcceptance.acceptedDownStartLE
                        p rate M t state haccepted
                      let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan
                        p rate M t hstart row
                      match ActiveFollowerDownAcceptance.checkedRecovery
                          p rate M state scan.endpoint with
                      | .error failure =>
                          ActiveFollowerDownAcceptance.LocalDownResult.outputFailure
                            state (.replay failure)
                      | .ok recovered =>
                          ActiveFollowerDownAcceptance.LocalDownResult.accepted state
                            { afterDecode with
                              lastDown := some M
                              S := recovered.registers.1
                              delta := recovered.lastService
                              backlog := recovered.registers.2
                              status := if scan.endpoint = t.val + 2 then
                                .pending else .unoccupied
                              buffer := [] }
                            decoded.2 M scan recovered.registers recovered.lastService
                    else
                      ActiveFollowerDownAcceptance.LocalDownResult.parsedButUnaccepted
                        state afterDecode decoded.2 M
              {
                outcome := outcome
                expectedWord := expected
                raw := decoded.2
                filteredRaw := decoded.2
                ordinaryParse := parsed
                ordinaryAcceptance := accepted
                rawComparison := some true
              }
            else
              let parsed := ordinaryParse p rate decoded.2
              let accepted := ordinaryLocalAcceptanceTest p rate t state parsed
              {
                outcome := .decodeOrParseRejected state
                  { state with downBatch := decoded.1 } decoded.2
                expectedWord := expected
                raw := decoded.2
                filteredRaw := none
                ordinaryParse := parsed
                ordinaryAcceptance := accepted
                rawComparison := some false
              }
          else {
            outcome := .inputFailure state .sparseBuffer
            expectedWord := expected
            raw := none
            filteredRaw := none
            ordinaryParse := none
            ordinaryAcceptance := False
            rawComparison := none
          }
        else {
          outcome := .inputFailure state .decoderBatch
          expectedWord := expected
          raw := none
          filteredRaw := none
          ordinaryParse := none
          ordinaryAcceptance := False
          rawComparison := none
        }
      else {
        outcome := .inputFailure state .registers
        expectedWord := expected
        raw := none
        filteredRaw := none
        ordinaryParse := none
        ordinaryAcceptance := False
        rawComparison := none
      }
    else {
      outcome := .skipped state .occupiedAtChoice
      expectedWord := expected
      raw := none
      filteredRaw := none
      ordinaryParse := none
      ordinaryAcceptance := False
      rawComparison := none
    }
  else {
    outcome := .skipped state .notSelectedDown
    expectedWord := expected
    raw := none
    filteredRaw := none
    ordinaryParse := none
    ordinaryAcceptance := False
    rawComparison := none
  }

/-- A `some` returned by this decoder is a unique solution of the exact batch
formed from the current follower input and the already-carried pending batch.
This is the solver's pointwise uniqueness guarantee, not an ambiguity theorem
for a batch or an awaited word. -/
theorem currentDecodeStep_raw_unique (p : Parameters) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hraw : (ActiveFollowerDownAcceptance.currentDecodeStep
      p i row t feedback rate state).2 = some word) :
    ∀ candidate,
      AffineBatchDecoder.satisfies
        (AffineBatchDecoder.samples
          (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput
                p i row t feedback rate state)) t)) candidate →
        candidate = word := by
  have hstep : AffineBatchDecoder.stepOutput p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput
          p i row t feedback rate state)) state.downBatch t = some word := by
    simpa only [ActiveFollowerDownAcceptance.currentDecodeStep,
      AffineBatchDecoder.decodeStep] using hraw
  exact (AffineBatchDecoder.stepOutput_eq_some_iff p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput
        p i row t feedback rate state)) state.downBatch t word).mp hstep |>.2.2

/-- Whenever a comparison was made, the output's retained raw word is exactly
the sole actual `currentDecodeStep` result. -/
theorem referenceDownCut_raw_eq_currentDecodeStep_of_compared
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hcompared :
      (referenceDownCut p view i row t feedback rate state).rawComparison ≠ none) :
    (referenceDownCut p view i row t feedback rate state).raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep
        p i row t feedback rate state).2 := by
  classical
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
  · by_cases hstatus : state.status = .unoccupied
    · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state
      · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch
        · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer
          · by_cases hmatches :
                (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i row t feedback rate state).2 = expectedDownFlatWord view i row t
            · simp [referenceDownCut, hselected, hstatus, hregisters,
                hbatch, hbuffer, hmatches]
            · simp [referenceDownCut, hselected, hstatus, hregisters,
                hbatch, hbuffer, hmatches]
          · simp [referenceDownCut, hselected, hstatus, hregisters, hbatch,
              hbuffer] at hcompared
        · simp [referenceDownCut, hselected, hstatus, hregisters, hbatch] at hcompared
      · simp [referenceDownCut, hselected, hstatus, hregisters] at hcompared
    · simp [referenceDownCut, hselected, hstatus] at hcompared
  · simp [referenceDownCut, hselected] at hcompared

/-- The retained `wrongUniqueAccepted` flag really names a unique decoder
return: a nonempty raw output from this solver is the sole solution to its
actual current batch. This is pointwise, not a full-batch/run event theorem. -/
theorem wrongUniqueAccepted_raw_is_unique
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hflag : wrongUniqueAccepted
      (referenceDownCut p view i row t feedback rate state)) :
    ∃ word, (referenceDownCut p view i row t feedback rate state).raw = some word ∧
      ∀ candidate,
        AffineBatchDecoder.satisfies
          (AffineBatchDecoder.samples
            (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p
                (ActiveFollowerDownAcceptance.currentRoundInput
                  p i row t feedback rate state)) t)) candidate →
          candidate = word := by
  have hraw : (referenceDownCut p view i row t feedback rate state).raw ≠ none :=
    hflag.2.1
  have hcompared :
      (referenceDownCut p view i row t feedback rate state).rawComparison ≠ none := by
    rw [hflag.1]
    decide
  have hrawEq := referenceDownCut_raw_eq_currentDecodeStep_of_compared
    view i row t feedback rate state hcompared
  have hexists : ∃ word,
      (referenceDownCut p view i row t feedback rate state).raw = some word := by
    cases hword : (referenceDownCut p view i row t feedback rate state).raw with
    | none => exact False.elim (hraw hword)
    | some word => exact ⟨word, rfl⟩
  rcases hexists with ⟨word, hword⟩
  refine ⟨word, hword, ?_⟩
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep
        p i row t feedback rate state).2 = some word := hrawEq.symm.trans hword
  exact currentDecodeStep_raw_unique p i row t feedback rate state word hdecoded

/-- The reference result equals the ordinary DOWN result whenever this call
did not observe a wrong raw word. Skipped, occupied, and invalid-input paths
have no comparison and therefore agree directly. -/
theorem referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hmatch : ¬ rawMismatch (referenceDownCut p view i row t feedback rate state)) :
    (referenceDownCut p view i row t feedback rate state).outcome =
      ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state := by
  classical
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
  · by_cases hstatus : state.status = .unoccupied
    · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state
      · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch
        · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer
          · let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
              p i row t feedback rate state
            have hflat : decoded.2 = expectedDownFlatWord view i row t := by
              by_contra hne
              have hmismatch : rawMismatch
                  (referenceDownCut p view i row t feedback rate state) := by
                simp [rawMismatch, referenceDownCut, hselected, hstatus,
                  hregisters, hbatch, hbuffer, decoded, hne]
              exact hmatch hmismatch
            simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
              hselected, hstatus, hregisters, hbatch, hbuffer, hflat,
              decoded, ordinaryParse]
            rfl
          · simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
              hselected, hstatus, hregisters, hbatch, hbuffer]
        · simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
            hselected, hstatus, hregisters, hbatch]
      · simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
          hselected, hstatus, hregisters]
    · simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
        hselected, hstatus]
  · simp [referenceDownCut, ActiveFollowerDownAcceptance.downTransition,
      hselected]

/-- Literal mismatch preservation, independent of whether a later recovery
would succeed. The reference transition is ordinary rejection, keeps the
already-logged buffer and every old register, and stores only the actual
advanced decoder batch. -/
theorem referenceDownCut_raw_mismatch_preserves
    (view : Option (ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (t : Fin p.T) (feedback : Observation p)
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer)
    (hmismatch : rawMismatch (referenceDownCut p view i row t feedback rate state)) :
    (referenceDownCut p view i row t feedback rate state).outcome =
        .decodeOrParseRejected state
          { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
            p i row t feedback rate state).1 }
          (ActiveFollowerDownAcceptance.currentDecodeStep
            p i row t feedback rate state).2 ∧
      (referenceDownCut p view i row t feedback rate state).raw =
          (ActiveFollowerDownAcceptance.currentDecodeStep
            p i row t feedback rate state).2 ∧
      (referenceDownCut p view i row t feedback rate state).filteredRaw = none ∧
      (referenceDownCut p view i row t feedback rate state).ordinaryParse =
        ordinaryParse p rate (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).2 ∧
      (referenceDownCut p view i row t feedback rate state).ordinaryAcceptance =
        ordinaryLocalAcceptanceTest p rate t state
          (ordinaryParse p rate (ActiveFollowerDownAcceptance.currentDecodeStep
            p i row t feedback rate state).2) ∧
      ({ state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.lastDown = state.lastDown ∧
       { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.S = state.S ∧
       { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.delta = state.delta ∧
       { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.backlog = state.backlog ∧
       { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.status = state.status ∧
       { state with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row t feedback rate state).1 }.buffer = state.buffer) := by
  classical
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
    p i row t feedback rate state
  have hflat : decoded.2 ≠ expectedDownFlatWord view i row t := by
    intro heq
    have hnotmismatch :
        (referenceDownCut p view i row t feedback rate state).rawComparison = some true := by
      simp [referenceDownCut, hselected, hstatus, hregisters, hbatch,
        hbuffer, decoded, heq]
    simp [rawMismatch, hnotmismatch] at hmismatch
  simp [referenceDownCut, hselected, hstatus, hregisters, hbatch,
    hbuffer, decoded, hflat]

/-- Run checked logging and then the reference-filtered DOWN operation for an
unoccupied choice snapshot. Occupied service remains delegated to the existing
declared-round owner. Release and FinishRound are outside this wrapper. -/
noncomputable def loggingThenReferenceDown (rate : ActiveFollowerDownAcceptance.RateInput p)
    (view : Option (ChoiceTimeView p rate.eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (activation : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta) :
    Except DeclaredFollowerLocalRound.RoundFailure
      (ReferencePrelaunchFollower.State p rate.eta) := by
  classical
  if hunoccupied : choiceState.status = .unoccupied then
    match ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
        choiceState with
    | .error reason => exact .error (.logging reason)
    | .ok logged =>
        exact DeclaredFollowerLocalRound.consumeDownResult rate
          (referenceDownCut p view i row t observation rate logged).outcome
  else
    exact DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t
      hactive arm observation choiceState

/-- On a successfully logged unoccupied round with no raw mismatch, the
logging/filter wrapper is exactly the accepted declared-follower logging-then-
ordinary-DOWN operation. -/
theorem loggingThenReferenceDown_eq_declared_of_matching
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (view : Option (ChoiceTimeView p rate.eta)) (i : Fin (p.m - 1))
    (row : CompleteRow p) (activation : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState logged : ReferencePrelaunchFollower.State p rate.eta)
    (hunoccupied : choiceState.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation t
      (arm, observation) choiceState = .ok logged)
    (hmatch : ¬ rawMismatch (referenceDownCut p view i row t observation rate logged)) :
    loggingThenReferenceDown rate view i row activation t hactive arm observation
        choiceState =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t
        hactive arm observation choiceState := by
  classical
  unfold loggingThenReferenceDown DeclaredFollowerLocalRound.recordOrServiceThenDown
  rw [dite_eq_left hunoccupied, dite_eq_left hunoccupied]
  simp only [hlogging]
  rw [referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
    view i row t observation rate logged hmatch]

end Bandits.Support.ReferenceDownReception

end
