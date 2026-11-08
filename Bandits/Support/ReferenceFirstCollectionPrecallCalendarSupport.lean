/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldPrefixCalendarReadout

/-!
# The original calendar before its first collection invocation

The analysis cut reads the original optional numerical slots, stopping before
the first actual invocation. Its terminal boundary is a natural number and
includes the genuine horizon. Missing observations remain absent. The queue
is the existing stopped numerical run, including the first overflow update.

Sources: `04_slow_fast_learner.tex:140-188,245-284`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:9-100,355-426`
under `sources/zip4/manuscript/`. These are deterministic internal results;
no recording law, coupling, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceFirstCollectionSamplerCall (firstCollectionCall collectionCallAt)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "R" z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "s" z:max => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h

/-- The existing first invocation's date, or the horizon if it is absent. -/
def firstCallBoundary (z : S) : ℕ :=
  match firstCollectionCall rate rewards C_star C_h z with
  | none => p.T
  | some c => c.2.1.val

/-- Strict-past cutoff at an ordinary or terminal calendar boundary. -/
def cutBoundary (n : ℕ) (z : S) : ℕ :=
  min n (firstCallBoundary rate rewards C_star C_h z)

/-- Every original suffix slot strictly before the analysis cut, without
filtering or filling any absent numerical readout. -/
def precallSlots (n : ℕ) (z : S) :
    List (Option (RecordedQueueRun.RoundInput p.K)) :=
  (List.range (cutBoundary rate rewards C_star C_h n z - s z)).map
    (fun k => ((R z)[k]?).bind (cell0 rate))

/-- Actual launch and success of every optional readout are both required. -/
def precallCells? (n : ℕ) (z : S) :
    Option (List (RecordedQueueRun.RoundInput p.K)) :=
  if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (cutBoundary rate rewards C_star C_h n z) z then
    (precallSlots rate rewards C_star C_h n z).mapM id
  else none

/-- A projection of the existing numerical run, with no fabricated state on
an absent launch or an absent prefix. -/
def precallReadout? (n : ℕ) (z : S) :
    Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) :=
  (precallCells? rate rewards C_star C_h n z).map (fun L =>
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q L))

/-- Scalar localization: an absent optional prefix contributes zero. This
does not install a physical or numerical state on the absent branch. -/
def precallBacklog (n : ℕ) (a : Fin p.K) (z : S) : ℝ :=
  match precallCells? rate rewards C_star C_h n z with
  | none => 0
  | some L => StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a

theorem firstCallBoundary_le_T (z : S) :
    firstCallBoundary rate rewards C_star C_h z ≤ p.T := by
  unfold firstCallBoundary
  split
  · exact le_rfl
  · exact Nat.le_of_lt (Fin.isLt _)

theorem cutBoundary_le (n : ℕ) (z : S) :
    cutBoundary rate rewards C_star C_h n z ≤ n := Nat.min_le_left _ _

theorem cutBoundary_horizon (z : S) :
    cutBoundary rate rewards C_star C_h p.T z =
      firstCallBoundary rate rewards C_star C_h z :=
  Nat.min_eq_right (firstCallBoundary_le_T rate rewards C_star C_h z)

theorem precallCells_no_launch (n : ℕ) (z : S)
    (hz : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (cutBoundary rate rewards C_star C_h n z) z) :
    precallCells? rate rewards C_star C_h n z = none := by
  simp only [precallCells?, ite_eq_right hz]

theorem precallCells_preserve (m n : ℕ) (z : S)
    (hm : firstCallBoundary rate rewards C_star C_h z ≤ m)
    (hn : firstCallBoundary rate rewards C_star C_h z ≤ n) :
    precallCells? rate rewards C_star C_h m z =
      precallCells? rate rewards C_star C_h n z := by
  simp only [precallCells?, precallSlots, cutBoundary,
    Nat.min_eq_right hm, Nat.min_eq_right hn]

theorem precallCells_no_call (n : ℕ) (hn : n ≤ p.T) (z : S)
    (hz : firstCollectionCall rate rewards C_star C_h z = none) :
    precallSlots rate rewards C_star C_h n z =
      (List.range (n - s z)).map (fun k => ((R z)[k]?).bind (cell0 rate)) := by
  simp only [precallSlots, cutBoundary, firstCallBoundary, hz, Nat.min_eq_left hn]

/-- The ordinary-boundary query is exactly the accepted strict-past reader
at the same cut. The definition above also makes sense at boundary `T`. -/
theorem precallCells_eq_pastCells (n : ℕ) (z : S)
    (hn : cutBoundary rate rewards C_star C_h n z < p.T) :
    precallCells? rate rewards C_star C_h n z =
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h
        ⟨cutBoundary rate rewards C_star C_h n z, hn⟩ z := rfl

private theorem record_time (z : S) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r) : r.input.time.val = s z + k :=
  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k r hr

/-- Any actual invocation bounds the first invocation, including invocations
whose subsequent checked sampler fails. -/
theorem firstCallBoundary_le_of_parameters (z : S) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r)
    (hp : (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true) :
    firstCallBoundary rate rewards C_star C_h z ≤ r.input.time.val := by
  cases hf : firstCollectionCall rate rewards C_star C_h z with
  | none =>
      have hnone := (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff
        (rate := rate) rewards C_star C_h z).mp hf r (List.mem_of_getElem? hr)
      simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hp
  | some call =>
      obtain ⟨u, t, theta⟩ := call
      obtain ⟨j, earlier, hearlier, htime, _, hprevious⟩ :=
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
          (rate := rate) rewards C_star C_h z u t theta).mp hf
      have hdate := record_time rate rewards C_star C_h z j earlier hearlier
      rw [htime] at hdate
      have hjk : j ≤ k := by
        by_contra h
        have hnone := hprevious k (by omega) r hr
        simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hp
      simp only [firstCallBoundary, hf]
      have hd := record_time rate rewards C_star C_h z k r hr
      omega

theorem parameters_none_before_cut (z : S) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r)
    (hbefore : r.input.time.val < firstCallBoundary rate rewards C_star C_h z) :
    ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
  cases hp : ReferenceLaterSamplerParameterMeasurability.parameters? r.input with
  | none => rfl
  | some theta =>
      have hb := firstCallBoundary_le_of_parameters rate rewards C_star C_h z k r hr
        (by rw [hp]; rfl)
      omega

/-- Pending-nonempty inputs have no pre-sampler parameters, directly from
the exposed physical selector. No private upstream theorem is invoked. -/
theorem parameters_none_of_pending
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload ledger saved)
    (hp : ledger.pending.Nonempty) :
    ReferenceLaterSamplerParameterMeasurability.parameters? x = none := by
  change ReferenceLaterAssignmentFibreStep.parameters? x = none
  unfold ReferenceLaterAssignmentFibreStep.parameters?
  simp only [hcoord]
  split
  · unfold ReferenceLaterAssignmentFibreStep.collectionParameters?
    split
    · rfl
    · split
      · simp only [ReferenceActivePhysicalStep.collectionInput, hp, ite_true]
      · rfl
  · rfl

private theorem selected_parameters_present
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    (LaterAssignmentStartMeasurability.selectedSamplerParameters? old
      ⟨ledger, instruction, consistent⟩).isSome = true := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  have hpair : (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
      LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction out, hrec⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hrec
  unfold LaterAssignmentStartOperation.decideReconstruction
  rw [hpair]
  rfl

private theorem collection_parameters_present
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction) (hp : x.ledger.pending = ∅)
    (out : AssignmentScoreReconstruction.ReconstructedStart
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) instruction =
        .success _ instruction out) :
    (ReferenceLaterAssignmentFibreStep.collectionParameters? x).isSome = true := by
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters?
  simp only [hstart]
  rw [dite_eq_left core]
  simp only [hp, Finset.not_nonempty_empty, ite_false, hi]
  exact selected_parameters_present x.payload _ instruction _ out hrec

/-- A produced actual empty-boundary dispatch has parameters before sampling.
This uses its reconstruction equation, without demanding sampler success or
restricting the corrected/renewed branch. -/
theorem actualNextDispatch_parameters_present
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch x payload ledger saved)
    (hbound : ∀ a c, ledger.cutoffRegisters a = some c → c.lastService ≤ c.score) :
    (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome = true := by
  obtain ⟨cutoff, hcutoff, core, started, hstart, instruction, hi, consistent,
    ht, hkind, hprep, hiff, hcases⟩ := d.classification
  rcases hcases with hbad | ⟨out, hrec, _⟩
  · obtain ⟨a, c, hc, hlt, _⟩ := hbad
    exact ((Nat.not_lt_of_ge (hbound a c hc)) hlt).elim
  · change (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true
    unfold ReferenceLaterAssignmentFibreStep.parameters?
    simp only [d.actualState]
    have hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
      have h := cutoff.isLt
      omega
    rw [dite_eq_left hcut]
    have he : (⟨ledger.cutoff - 1, by omega⟩ : Fin p.T) = cutoff := by
      apply Fin.ext
      dsimp
      omega
    rw [he]
    exact collection_parameters_present _ core started hstart
      instruction hi d.emptyPending out hrec

private theorem laterChosen_parameters_present
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.laterChosen x = true) :
    (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome = true := by
  have hp := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch x
  change ReferenceLaterAssignmentFibreStep.parameters? x =
    ReferenceLaterAssignmentFibreStep.dispatchParameters?
      (ReferenceActivePhysicalStep.prepare x).coordinator at hp
  change (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen, he,
        Bool.false_eq_true] at h
      rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
      rw [hp, he]
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
        ReferenceLaterAssignmentFibreStep.outcomeParameters?]
      exact selected_parameters_present _ _ instruction consistent
        output.reconstruction output.reconstruction_eq
  | first outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | live registers owned base outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | dagger =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h

private theorem takeWhile_lookup {α : Type*} (test : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile test).length) :
    xs[k]? = (xs.takeWhile test)[k]? := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      cases ht : test x with
      | false => simp [ht] at hk
      | true =>
          cases k with
          | zero => simp [ht]
          | succ k =>
              have hk' : k < (xs.takeWhile test).length := by simpa [ht] using hk
              simpa only [List.takeWhile, ht, List.getElem?_cons_succ] using ih k hk'

private theorem index_lt_takeWhile {α : Type*} (test : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < xs.length)
    (hall : ∀ j ≤ k, ∀ x, xs[j]? = some x → test x = true) :
    k < (xs.takeWhile test).length := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      have hx : test x = true := hall 0 (Nat.zero_le _) x rfl
      cases k with
      | zero => simp [hx]
      | succ k =>
          have hk' : k < xs.length := by simpa using hk
          have hh : ∀ j ≤ k, ∀ y, xs[j]? = some y → test y = true := by
            intro j hj y hy
            exact hall (j + 1) (by omega) y (by simpa using hy)
          simpa [hx] using ih k hk' hh

/-- A date before the first invocation cannot lie beyond the actual
collection window, even when no sampler is ever called. -/
private theorem index_lt_collectionWindow (z : S) (k w : ℕ)
    (hw : w < (R z).length) (hwk : w ≤ k) (hk : k < (R z).length)
    (hbefore : s z + k < firstCallBoundary rate rewards C_star C_h z) :
    k - w < (ReferenceCollectionPhaseHistory.collectionWindow (R z) w).length := by
  have hhead : ((R z).drop w |>.take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  rw [List.length_append, hhead]
  by_cases heq : k = w
  · omega
  · have htail : k - w - 1 < ((R z).drop (w + 1)).length := by
      simp only [List.length_drop]
      omega
    have htake := index_lt_takeWhile
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input)
      ((R z).drop (w + 1)) (k - w - 1) htail (by
        intro j hj r hr
        have hr' : (R z)[w + 1 + j]? = some r := by
          simpa only [List.getElem?_drop] using hr
        have hdate := record_time rate rewards C_star C_h z _ r hr'
        have hnone := parameters_none_before_cut rate rewards C_star C_h z _ r hr'
          (by omega)
        cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input with
        | false => rfl
        | true =>
            have hp := laterChosen_parameters_present rate r.input hb
            simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hp)
    have hi : k - w = k - w - 1 + 1 := by omega
    rw [hi]
    simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_lt_succ htake

/-- The original stream's cutoff input is LIVE and every later input has
the preceding nonempty pending ledger. All their selectors are therefore
absent, directly from the public initialized stream and literal selector. -/
theorem initializedStream_parameters_none (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc count hs).records).length < count)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) z rewards C_star C_h count hc hs hshort) (n : Fin out.ell) :
    ReferenceLaterSamplerParameterMeasurability.parameters?
      (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input = none := by
  by_cases hn : n.val = 0
  · have hr : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = out.cutoff.cut := by
      simpa only [hn] using out.cutoffIsHead
    rw [hr]
    obtain ⟨execution⟩ := out.cutoffExecution
    change ReferenceLaterAssignmentFibreStep.parameters? out.cutoff.cut.input = none
    simp only [ReferenceLaterAssignmentFibreStep.parameters?, execution.actualLive]
  · obtain ⟨j, r, incoming, cell, _, hrecord, _, hi⟩ := out.cell_at n (by omega)
    have hr : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = r :=
      (List.getElem?_eq_some_iff.mp hrecord).2
    rw [hr]
    have hp := out.pending_before_last ⟨n.val - 1, by omega⟩ (by
      change n.val - 1 + 1 < out.ell
      have h := n.isLt
      omega)
    rw [← hi] at hp
    exact parameters_none_of_pending rate r.input out.payload incoming out.saved cell.readyInput.1 hp

/-- Every actual suffix date before the first invocation has its original
LIVE or OLD observation. The crossing premise is discharged by the launched
branch in the whole-source prefix theorem below. -/
theorem original_cell_before_cut (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : ℕ) (hk : k < (R z).length)
    (hbefore : s z + k < firstCallBoundary rate rewards C_star C_h z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (c : RecordedQueueRun.RoundInput p.K),
      (R z)[k]? = some r ∧ r.input.time.val = s z + k ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none) ∨
       (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none)) ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
  let count := p.T - s z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let hsReady := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h z
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hs
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)).length
  have hW : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z) := by
    unfold W ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc]
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    rate rewards C_star C_h z hc
  by_cases hkw : k < w
  · let j : Fin W.length := ⟨k, by rw [hW]; exact hkw⟩
    obtain ⟨_, _, hcells⟩ :=
      ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
        rate rewards C_star C_h z hc
    obtain ⟨_, hdate, _, _, _, _, hread, hnone, hrows, hselected, hrewards, _⟩ := hcells j
    let r := W[j.val]
    have hlookup : (R z)[k]? = some r := by
      have hp : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z))[k]? = some r := by
        rw [← hW]
        exact List.getElem?_eq_getElem j.isLt
      exact (takeWhile_lookup
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (R z) k hkw).trans hp
    exact ⟨r, _, hlookup, hdate, hrows, hselected, hrewards, Or.inl ⟨hread, hnone⟩,
      parameters_none_before_cut rate rewards C_star C_h z k r hlookup (by
        change r.input.time.val = s z + k at hdate
        omega)⟩
  · have hcount : (R z).length = count :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc count hsReady).records).length < count := by
      rw [← hepoch]
      change w < count
      omega
    obtain ⟨_, _, d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
        hDlen, hzero, hcells⟩ :=
      ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
        rate rewards C_star C_h z hc hshort
    have hwin : k - w < d.stream.window.length := by
      rw [d.stream.windowIsActual]
      change k - w < (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc count hsReady).records _).length
      rw [← hepoch]
      exact index_lt_collectionWindow rate rewards C_star C_h z k w (by omega)
        (by omega) hk hbefore
    have hell : k - w < d.stream.ell := by
      by_contra hn
      have hshorter : d.stream.ell < d.stream.window.length := by omega
      have halign := (d.stream.alignment
        ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).2
      have hrecord : d.stream.window[d.last.val]'(by
          exact lt_of_lt_of_le d.last.isLt d.stream.withinWindow) = d.record :=
        (List.getElem?_eq_some_iff.mp d.recordAt).2
      rw [hrecord, ← hepoch] at halign
      have hlast : d.record.input.time.val + 1 = s z + w + d.stream.ell := by
        have he := d.lastIsLast
        change d.record.input.time.val + 1 = s z + w + 1 + d.last.val at halign
        omega
      cases d.outcome with
      | exhausted _ hend _ _ _ => omega
      | empty e =>
          cases e.nextBoundary with
          | terminal ht _ =>
              have hsT := d.record.input.time.isLt
              have hsbound := firstCallBoundary_le_T rate rewards C_star C_h z
              omega
          | next hb _ x _ _ htime _ _ _ _ hrun dispatch =>
              have hnext : w + d.stream.ell < (R z).length := by
                rw [hcount]
                dsimp only [count]
                omega
              let rNext := (R z)[w + d.stream.ell]'hnext
              have hlook : (R z)[w + d.stream.ell]? = some rNext :=
                List.getElem?_eq_getElem hnext
              have hx : x = rNext.input := hrun rNext (by
                rw [← hepoch]
                exact hlook)
              have hp : (ReferenceLaterSamplerParameterMeasurability.parameters?
                  rNext.input).isSome = true := by
                rw [← hx]
                exact actualNextDispatch_parameters_present rate x _ _ _ dispatch
                  (fun a c hc => (e.cutoffLastService a c hc).1)
              have hfirst := firstCallBoundary_le_of_parameters rate rewards C_star C_h
                z _ rNext hlook hp
              have hdate := record_time rate rewards C_star C_h z _ rNext hlook
              omega
    let j : Fin d.stream.ell := ⟨k - w, hell⟩
    obtain ⟨call, validCall, _, _, _, _, hrows, hselected, hrewards, hdate,
        _, _, _, _, hread, hnone, _⟩ := hcells j
    let r := d.stream.window[j.val]'(lt_of_lt_of_le j.isLt d.stream.withinWindow)
    have hlookup := (d.stream.alignment
      ⟨j.val, lt_of_lt_of_le j.isLt d.stream.withinWindow⟩).1
    rw [← hepoch] at hlookup
    have hindex : w + j.val = k := by dsimp only [j]; omega
    change (R z)[w + j.val]? = some r at hlookup
    rw [hindex] at hlookup
    refine ⟨r, _, hlookup, record_time rate rewards C_star C_h z k r hlookup,
      hrows, hselected, hrewards, Or.inr ⟨hread, hnone⟩, ?_⟩
    exact initializedStream_parameters_none rate rewards C_star C_h z hc count hsReady hshort d.stream j

private theorem mapM_id_present {α : Type*} (xs : List (Option α))
    (h : ∀ x ∈ xs, x.isSome = true) :
    ∃ L, xs.mapM id = some L ∧ xs = L.map some := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      obtain ⟨L, hL, hslots⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      cases x with
      | none => cases hx
      | some a =>
          exact ⟨a :: L, by simp [List.mapM_cons, hL], by simp only [List.map_cons, hslots]⟩

private theorem mapM_id_some {α : Type*} (xs : List (Option α)) (L : List α)
    (h : xs.mapM id = some L) : xs = L.map some := by
  induction xs generalizing L with
  | nil => simpa using h.symm
  | cons x xs ih =>
      cases x with
      | none => simp [List.mapM_cons] at h
      | some a =>
          cases ht : xs.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have hL : a :: tail = L := by simpa [List.mapM_cons, ht] using h
              rw [← hL, List.map_cons, ← ih tail ht]

private theorem mapM_some {α : Type*} (xs : List α) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- All source branch obligations are produced here. On an actual launch,
every strict-past slot succeeds, including an OLD FINISH at offset `T-1`.
No launch, missing slots, and terminal launch retain their literal options. -/
theorem precallPrefix_present (n : ℕ) (hn : n ≤ p.T) (z : S)
    (hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h n z) z) :
    ∃ L : List (RecordedQueueRun.RoundInput p.K),
      precallCells? rate rewards C_star C_h n z = some L ∧
      L.length = cutBoundary rate rewards C_star C_h n z - s z ∧
      precallSlots rate rewards C_star C_h n z = L.map some ∧
      (∀ k : Fin L.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          (R z)[k.val]? = some r ∧ r.input.time.val = s z + k.val ∧
          cell0 rate r = some L[k.val]) := by
  have hstart : s z ≤ cutBoundary rate rewards C_star C_h n z := hz.2
  have hcutT : cutBoundary rate rewards C_star C_h n z ≤ p.T :=
    (cutBoundary_le rate rewards C_star C_h n z).trans hn
  have hslot : ∀ x ∈ precallSlots rate rewards C_star C_h n z, x.isSome = true := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hkcut : k < cutBoundary rate rewards C_star C_h n z - s z := List.mem_range.mp hk
    have hkR : k < (R z).length := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
      omega
    have hbefore : s z + k < firstCallBoundary rate rewards C_star C_h z := by
      have hcut := Nat.min_le_right n (firstCallBoundary rate rewards C_star C_h z)
      change cutBoundary rate rewards C_star C_h n z ≤ _ at hcut
      omega
    obtain ⟨r, c, hr, _, _, _, _, hread, _⟩ := original_cell_before_cut
      rate rewards C_star C_h z hz.1 k hkR hbefore
    rw [hr, Option.bind_some]
    rcases hread with ⟨hlive, _⟩ | ⟨hold, hlive⟩
    · simp only [cell0, hlive, Option.some_or, Option.isSome_some]
    · simp only [cell0, hlive, Option.none_or, hold, Option.isSome_some]
  obtain ⟨L, hL, hslots⟩ := mapM_id_present _ hslot
  have hlen : L.length = cutBoundary rate rewards C_star C_h n z - s z := by
    have h := congrArg List.length hslots
    simpa only [precallSlots, List.length_map, List.length_range] using h.symm
  refine ⟨L, by simp only [precallCells?, ite_eq_left hz, hL], hlen, hslots, ?_⟩
  intro k
  have hk : k.val < cutBoundary rate rewards C_star C_h n z - s z := by
    rw [← hlen]
    exact k.isLt
  have hkR : k.val < (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    omega
  let r := (R z)[k.val]'hkR
  have hr : (R z)[k.val]? = some r := List.getElem?_eq_getElem hkR
  refine ⟨r, hr, record_time rate rewards C_star C_h z k.val r hr, ?_⟩
  have h := congrArg (fun xs => xs[k.val]?) hslots
  simp only [precallSlots, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, List.getElem?_eq_getElem k.isLt] at h
  exact Option.some.inj (by simpa only [hr, Option.bind_some] using h)

/-- Exhaustive whole-source support, with every local producer premise
discharged and absence kept distinct from the actual empty queue prefix. -/
theorem precallPrefix_support (n : ℕ) (hn : n ≤ p.T) (z : S) :
    (¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (cutBoundary rate rewards C_star C_h n z) z ∧
      precallCells? rate rewards C_star C_h n z = none) ∨
    (ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (cutBoundary rate rewards C_star C_h n z) z ∧
      ∃ L : List (RecordedQueueRun.RoundInput p.K),
        precallCells? rate rewards C_star C_h n z = some L ∧
        L.length = cutBoundary rate rewards C_star C_h n z - s z ∧
        precallSlots rate rewards C_star C_h n z = L.map some ∧
        ∀ k : Fin L.length,
          ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
            (R z)[k.val]? = some r ∧ r.input.time.val = s z + k.val ∧
            cell0 rate r = some L[k.val]) := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h n z) z
  · exact Or.inr ⟨hz, precallPrefix_present rate rewards C_star C_h n hn z hz⟩
  · exact Or.inl ⟨hz, precallCells_no_launch rate rewards C_star C_h n z hz⟩

/-- Every earlier cut is a literal take of the later optional slots. -/
theorem precallSlots_take (m n : ℕ) (hmn : m ≤ n) (z : S) :
    precallSlots rate rewards C_star C_h m z =
      (precallSlots rate rewards C_star C_h n z).take
        (cutBoundary rate rewards C_star C_h m z - s z) := by
  have hcut : cutBoundary rate rewards C_star C_h m z ≤
      cutBoundary rate rewards C_star C_h n z := min_le_min hmn le_rfl
  have hdiff := Nat.sub_le_sub_right hcut (s z)
  simp only [precallSlots, ← List.map_take, List.take_range, Nat.min_eq_left hdiff]

/-- Prefix chronology is forced by the successful original readout. Before
launch the shorter query remains absent; at launch it is exactly empty. -/
theorem precallCells_take (m n : ℕ) (hmn : m ≤ n) (z : S)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : precallCells? rate rewards C_star C_h n z = some L) :
    precallCells? rate rewards C_star C_h m z =
      if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
          (cutBoundary rate rewards C_star C_h m z) z then
        some (L.take (cutBoundary rate rewards C_star C_h m z - s z))
      else none := by
  have hslots : precallSlots rate rewards C_star C_h n z = L.map some := by
    unfold precallCells? at hL
    split at hL
    · exact mapM_id_some _ L hL
    · cases hL
  unfold precallCells?
  split
  · rw [precallSlots_take rate rewards C_star C_h m n hmn z, hslots, ← List.map_take]
    exact mapM_some _
  · rfl

theorem firstCallBoundary_on_firstCell (u t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    firstCallBoundary rate rewards C_star C_h z = t.val := by
  obtain ⟨call, hcall, heq⟩ := Option.map_eq_some_iff.mp hz
  have ht : call.2.1 = t := congrArg Prod.snd heq
  simp only [firstCallBoundary, hcall, ht]

/-- At and after the first invocation, the canonical cut is the same
accepted OLD strict-past prefix, before the invocation's current update. -/
theorem precallCells_at_or_after_firstCell (u t : Fin p.T) (n : ℕ)
    (htn : t.val ≤ n) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    precallCells? rate rewards C_star C_h n z =
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z := by
  have hcut : cutBoundary rate rewards C_star C_h n z = t.val := by
    rw [cutBoundary, firstCallBoundary_on_firstCell rate rewards C_star C_h u t z hz,
      Nat.min_eq_right htn]
  simp only [precallCells?, precallSlots, hcut,
    ReferenceFirstCollectionCurrentRetainedGate.pastCells?,
    ReferenceFirstCollectionCurrentRetainedGate.pastSlots]

/-- The terminal queue is exactly A's `run (V ++ D)` and A's incoming
`before?`/`bMinus`. The actual cutoff is included in `D` exactly once. -/
theorem precallPrefix_terminal_on_firstCell (u t : Fin p.T) (a : Fin p.K) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - s z) ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc (p.T - s z) hs).records).length < p.T - s z)
      (f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) z rewards C_star C_h (p.T - s z) hc hs hshort)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D L : List (RecordedQueueRun.RoundInput p.K)),
      let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T - s z) hs
      D.length = f.stream.ell ∧
      D[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate f.stream.cutoff.cut head rewards valid) ∧
      L = V ++ D ∧
      precallCells? rate rewards C_star C_h p.T z = some L ∧
      precallReadout? rate rewards C_star C_h p.T z =
        ReferenceFirstCollectionCurrentQueueReadout.before? rate rewards C_star C_h t z ∧
      precallBacklog rate rewards C_star C_h p.T a z =
        ReferenceFirstCollectionCurrentQueueReadout.bMinus rate rewards C_star C_h u t a z := by
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hDlen, hDzero,
      hPast, hLD, hbefore, hminus⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_before_eq_oldPrefix
      rate rewards C_star C_h u t a z hz
  have hterminal : precallCells? rate rewards C_star C_h p.T z = some L := by
    rw [precallCells_at_or_after_firstCell rate rewards C_star C_h u t p.T
      (Nat.le_of_lt t.isLt) z hz]
    exact hPast
  refine ⟨hc, hs, hshort, f, head, valid, D, L, hDlen, hDzero, hLD, hterminal, ?_, ?_⟩
  · simp only [precallReadout?, hterminal, Option.map_some, hbefore]
  · rw [precallBacklog, hterminal, hminus, hLD]

/-- Before invocation the next boundary appends the actual current slot.
The last physical round is included through boundary `T`. -/
theorem precallSlots_succ (t : Fin p.T) (z : S) (hs : s z ≤ t.val)
    (ht : t.val < firstCallBoundary rate rewards C_star C_h z) :
    precallSlots rate rewards C_star C_h (t.val + 1) z =
      precallSlots rate rewards C_star C_h t.val z ++
        [((R z)[t.val - s z]?).bind (cell0 rate)] := by
  have hcut : cutBoundary rate rewards C_star C_h t.val z = t.val :=
    Nat.min_eq_left (Nat.le_of_lt ht)
  have hcutNext : cutBoundary rate rewards C_star C_h (t.val + 1) z = t.val + 1 :=
    Nat.min_eq_left (Nat.succ_le_of_lt ht)
  have hindex : t.val + 1 - s z = (t.val - s z) + 1 := by omega
  simp only [precallSlots, hcut, hcutNext, hindex, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]

/-- The source produces both prefixes and the actual dated current cell.
The numerical successor is the existing stopped queue step, so enabled
zero-arrival service, disabled preservation, and the first detecting update
retain their original definitions. -/
theorem precallPrefix_append (t : Fin p.T) (z : S)
    (hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z)
    (ht : t.val < firstCallBoundary rate rewards C_star C_h z) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (c : RecordedQueueRun.RoundInput p.K),
      precallCells? rate rewards C_star C_h t.val z = some L ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧ cell0 rate r = some c ∧
      ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none) ∨
       (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none)) ∧
      precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      RecordedQueueRun.run Q (L ++ [c]) = RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
  have hcut : cutBoundary rate rewards C_star C_h t.val z = t.val :=
    Nat.min_eq_left (Nat.le_of_lt ht)
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h t.val z) z := by rw [hcut]; exact hz
  obtain ⟨L, hL, _, hslots, _⟩ := precallPrefix_present rate rewards C_star C_h
    t.val (Nat.le_of_lt t.isLt) z hlaunch
  have hk : t.val - s z < (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hs := hz.2
    have hT := t.isLt
    omega
  have hindex : s z + (t.val - s z) = t.val := by have hs := hz.2; omega
  obtain ⟨r, c, hr, hdate, _, _, _, hread, _⟩ := original_cell_before_cut
    rate rewards C_star C_h z hz.1 _ hk (by rw [hindex]; exact ht)
  have hcell : cell0 rate r = some c := by
    rcases hread with ⟨hlive, _⟩ | ⟨hold, hlive⟩
    · simp only [cell0, hlive, Option.some_or]
    · simp only [cell0, hlive, Option.none_or, hold]
  have hcutNext : cutBoundary rate rewards C_star C_h (t.val + 1) z = t.val + 1 :=
    Nat.min_eq_left (Nat.succ_le_of_lt ht)
  have hlaunchNext : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h (t.val + 1) z) z := by
    rw [hcutNext]
    exact ⟨hz.1, hz.2.trans (Nat.le_succ _)⟩
  have hnext : precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) := by
    unfold precallCells?
    rw [ite_eq_left hlaunchNext, precallSlots_succ rate rewards C_star C_h t z hz.2 ht,
      hslots, hr, Option.bind_some, hcell]
    rw [List.mapM_append, mapM_some]
    rfl
  refine ⟨L, r, c, hL, ?_, Fin.ext (hdate.trans hindex), hcell, hread, hnext, ?_⟩
  · simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hz.2, hr]
  · simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append, RecordedQueueRun.execute]

/-- Exhaustive one-date chronology. A date before launch retains absence or
reaches the actual empty launch prefix;
one after invocation preserves the incoming prefix; otherwise the original
current numerical cell is appended. -/
theorem precallPrefix_step_or_preserve (t : Fin p.T) (z : S) :
    (firstCallBoundary rate rewards C_star C_h z ≤ t.val ∧
      precallCells? rate rewards C_star C_h (t.val + 1) z =
        precallCells? rate rewards C_star C_h t.val z) ∨
    (t.val < firstCallBoundary rate rewards C_star C_h z ∧
      ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z ∧
      precallCells? rate rewards C_star C_h t.val z = none ∧
      (precallCells? rate rewards C_star C_h (t.val + 1) z = none ∨
        precallCells? rate rewards C_star C_h (t.val + 1) z = some [])) ∨
    (t.val < firstCallBoundary rate rewards C_star C_h z ∧
      ∃ L c, precallCells? rate rewards C_star C_h t.val z = some L ∧
        precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
        RecordedQueueRun.run Q (L ++ [c]) =
          RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c) := by
  by_cases ht : firstCallBoundary rate rewards C_star C_h z ≤ t.val
  · exact Or.inl ⟨ht, precallCells_preserve rate rewards C_star C_h
      (t.val + 1) t.val z (ht.trans (Nat.le_succ _)) ht⟩
  · have hbefore : t.val < firstCallBoundary rate rewards C_star C_h z := by omega
    by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
    · obtain ⟨L, r, c, hL, _, _, _, _, hnext, hstep⟩ :=
        precallPrefix_append rate rewards C_star C_h t z hz hbefore
      exact Or.inr (Or.inr ⟨hbefore, L, c, hL, hnext, hstep⟩)
    · have hcut : cutBoundary rate rewards C_star C_h t.val z = t.val :=
        Nat.min_eq_left (Nat.le_of_lt hbefore)
      have hnext : precallCells? rate rewards C_star C_h (t.val + 1) z = none ∨
          precallCells? rate rewards C_star C_h (t.val + 1) z = some [] := by
        by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
            (cutBoundary rate rewards C_star C_h (t.val + 1) z) z
        · right
          have hstart : t.val < s z := by
            by_contra h
            exact hz ⟨hlaunch.1, by omega⟩
          have hbound := cutBoundary_le rate rewards C_star C_h (t.val + 1) z
          have hindex : cutBoundary rate rewards C_star C_h (t.val + 1) z - s z = 0 := by omega
          simp only [precallCells?, ite_eq_left hlaunch, precallSlots, hindex,
            List.range_zero, List.map_nil, List.mapM_nil, Option.pure_def]
        · left
          exact precallCells_no_launch rate rewards C_star C_h (t.val + 1) z hlaunch
      exact Or.inr (Or.inl ⟨hbefore, hz, precallCells_no_launch
        rate rewards C_star C_h t.val z (by rw [hcut]; exact hz), hnext⟩)

theorem physicalStart_le_firstCallBoundary (z : S) :
    s z ≤ firstCallBoundary rate rewards C_star C_h z := by
  cases hf : firstCollectionCall rate rewards C_star C_h z with
  | none =>
      simpa only [firstCallBoundary, hf] using
        ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  | some call =>
      obtain ⟨u, t, theta⟩ := call
      obtain ⟨k, r, hr, htime, _⟩ :=
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
          (rate := rate) rewards C_star C_h z u t theta).mp hf
      have hdate := record_time rate rewards C_star C_h z k r hr
      rw [htime] at hdate
      simp only [firstCallBoundary, hf]
      omega

/-- The source's actual launch boundary has the empty strict prefix and the
existing zero numerical state, including a launch at the terminal horizon. -/
theorem precallPrefix_at_launch (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    precallCells? rate rewards C_star C_h (s z) z = some [] ∧
      precallReadout? rate rewards C_star C_h (s z) z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.initialState p.K)) ∧
      ∀ a : Fin p.K, precallBacklog rate rewards C_star C_h (s z) a z = 0 := by
  have hcut : cutBoundary rate rewards C_star C_h (s z) z = s z :=
    Nat.min_eq_left (physicalStart_le_firstCallBoundary rate rewards C_star C_h z)
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h (s z) z) z := by
    rw [hcut]
    exact ⟨hc, le_rfl⟩
  have hcells : precallCells? rate rewards C_star C_h (s z) z = some [] := by
    unfold precallCells?
    rw [ite_eq_left hlaunch]
    simp only [precallSlots, hcut, Nat.sub_self,
      List.range_zero, List.map_nil, List.mapM_nil, Option.pure_def]
  refine ⟨hcells, ?_, ?_⟩
  · simp only [precallReadout?, hcells, Option.map_some,
      RecordedQueueRun.run, RecordedQueueRun.execute]
  · intro a
    simp [precallBacklog, hcells, RecordedQueueRun.run, RecordedQueueRun.execute,
      RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]

/-- Genuine no-launch data remain absent. The explicit scalar localization
is zero and does not assert existence of a physical queue state. -/
theorem precallPrefix_no_launch (z : S)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) (n : ℕ) (a : Fin p.K) :
    precallCells? rate rewards C_star C_h n z = none ∧
      precallReadout? rate rewards C_star C_h n z = none ∧
      precallBacklog rate rewards C_star C_h n a z = 0 := by
  have hlaunch : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h n z) z := by
    intro h
    have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mpr h.1
    simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hc
  have hcells := precallCells_no_launch rate rewards C_star C_h n z hlaunch
  exact ⟨hcells, by simp only [precallReadout?, hcells, Option.map_none],
    by simp only [precallBacklog, hcells]⟩

/-- At a terminal launch there is no hypothetical `Fin T` next action.
Only boundary `T` reads the actual empty prefix. -/
theorem precallPrefix_terminal_launch (n : ℕ) (hn : n ≤ p.T) (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : s z = p.T) :
    precallCells? rate rewards C_star C_h n z = if n = p.T then some [] else none := by
  by_cases he : n = p.T
  · rw [ite_eq_left he, he, ← hs]
    exact (precallPrefix_at_launch rate rewards C_star C_h z hc).1
  · rw [ite_eq_right he]
    apply precallCells_no_launch
    intro hlaunch
    have hcut := cutBoundary_le rate rewards C_star C_h n z
    have hstart := hlaunch.2
    omega

/-- The exit test is exactly no invocation through the current date,
expressed using existing pre-choice calls rather than a new OLD selector. -/
theorem before_cut_iff_no_call_through (t : Fin p.T) (z : S) :
    t.val < firstCallBoundary rate rewards C_star C_h z ↔
      ∀ v : Fin p.T, v.val ≤ t.val →
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z = none := by
  constructor
  · intro ht v hv
    unfold ReferenceCalendarCollectionCallControlLaw.callAt
    by_cases hs : s z ≤ v.val
    · cases hr : (R z)[v.val - s z]? with
      | none => simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, hr,
          Option.bind_none]
      | some r =>
          have hdate := record_time rate rewards C_star C_h z _ r hr
          have hp := parameters_none_before_cut rate rewards C_star C_h z _ r hr (by omega)
          have hc := (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff r).mpr hp
          simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, hr,
            Option.bind_some, hc]
    · simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_right hs, Option.bind_none]
  · intro hnone
    cases hf : firstCollectionCall rate rewards C_star C_h z with
    | none => simpa only [firstCallBoundary, hf] using t.isLt
    | some call =>
        obtain ⟨u, v, theta⟩ := call
        obtain ⟨k, r, hr, htime, hcall, _⟩ :=
          (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
            (rate := rate) rewards C_star C_h z u v theta).mp hf
        have hdate := record_time rate rewards C_star C_h z k r hr
        rw [htime] at hdate
        have hstart : s z ≤ v.val := by omega
        have hindex : v.val - s z = k := by omega
        have hcallAt : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z =
            some (u, theta) := by
          simp only [ReferenceCalendarCollectionCallControlLaw.callAt,
            ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart, hindex, hr,
            Option.bind_some, hcall]
        have hvt : t.val < v.val := by
          by_contra h
          have he := hnone v (by omega)
          rw [hcallAt] at he
          cases he
        simpa only [firstCallBoundary, hf] using hvt

/-- A no-call terminal query reads the entire original suffix, including
its last physical update. The literal optional cells are not filtered. -/
theorem precallSlots_terminal_no_call (z : S)
    (hnone : firstCollectionCall rate rewards C_star C_h z = none) :
    precallSlots rate rewards C_star C_h p.T z = (R z).map (cell0 rate) := by
  rw [precallCells_no_call rate rewards C_star C_h p.T le_rfl z hnone,
    ← ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro k hk hk'
    have hkR : k < (R z).length := by simpa only [List.length_map] using hk'
    simp only [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hkR,
      Option.bind_some]

theorem precallCells_terminal_no_call (z : S)
    (hnone : firstCollectionCall rate rewards C_star C_h z = none) :
    precallCells? rate rewards C_star C_h p.T z =
      if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h p.T z then
        ((R z).map (cell0 rate)).mapM id else none := by
  unfold precallCells?
  rw [cutBoundary_horizon, firstCallBoundary, hnone,
    precallSlots_terminal_no_call rate rewards C_star C_h z hnone]

/-- A present OLD readout on the actual input is outside the first LIVE
window. No new OLD cell or selector schema is introduced. -/
theorem old_readout_after_firstLiveWindow (t : Fin p.T) (z : S)
    (hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hold : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true) :
    s z + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)).length ≤ t.val := by
  by_contra h
  let k := t.val - s z
  have hk : k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)).length := by
    have hs := hz.2
    dsimp only [k]
    omega
  have hR : (R z)[k]? = some r := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hz.2] using hr
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hz.1
  have hW : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hz.1 (p.T - s z)
      (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h z) =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z) := by
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← hepoch]
  let j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hz.1 (p.T - s z)
      (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h z)).length :=
    ⟨k, by rw [hW]; exact hk⟩
  obtain ⟨_, _, hcells⟩ := ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
    rate rewards C_star C_h z hz.1
  have hnone := (hcells j).2.2.2.2.2.2.2.1
  have hlookup := takeWhile_lookup
    (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (R z) k hk
  have hsame : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hz.1 (p.T - s z)
      (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h z))[j.val] = r := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem j.isLt]
    change _[k]? = some r
    rw [hW]
    exact hlookup.symm.trans hR
  rw [hsame] at hnone
  simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hold

/-- No-call survival is determined by the same source prefix as the actual
pre-choice calls. Whole current control vectors remain uninspected. -/
theorem before_cut_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : S) :
    (t.val < firstCallBoundary rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) ↔
      t.val < firstCallBoundary rate rewards C_star C_h z := by
  rw [before_cut_iff_no_call_through, before_cut_iff_no_call_through]
  have hcall (v : Fin p.T) (hv : v.val ≤ t.val) :
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) =
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 v,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 v.val t.val hv z]
    exact (ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 v z).symm
  constructor <;> intro h v hv
  · rw [← hcall v hv]
    exact h v hv
  · rw [hcall v hv]
    exact h v hv

/-- One choice of A's actual stream and lists serves every boundary. The
cutoff is the head of `D`; all later queries take the same OLD list. At the
actual launch boundary the prefix is empty. -/
theorem precallPrefix_firstCell_chronology (u t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - s z) ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc (p.T - s z) hs).records).length < p.T - s z)
      (f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) z rewards C_star C_h (p.T - s z) hc hs hshort)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D L : List (RecordedQueueRun.RoundInput p.K)),
      let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T - s z) hs
      L = V ++ D ∧ D.length = f.stream.ell ∧
      D[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate f.stream.cutoff.cut head rewards valid) ∧
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - s z ∧
      (∀ n ≤ p.T,
        precallCells? rate rewards C_star C_h n z =
          if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
              (cutBoundary rate rewards C_star C_h n z) z then
            some (L.take (cutBoundary rate rewards C_star C_h n z - s z)) else none) ∧
      (∀ v : Fin p.T, u.val ≤ v.val → v.val ≤ t.val →
        L.take (v.val - s z) = V ++ D.take (v.val - u.val)) ∧
      ∃ vStart : Fin p.T, vStart.val = s z ∧
        precallCells? rate rewards C_star C_h vStart.val z = some [] := by
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, htotal,
      hpending, hrecord, hchoice, hDlen, hDzero, hDread, hLD, hPast, hlen,
      hcoverage, hprefix, hsplit, vStart, hvStart, hzero, _⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hz
  have hterminal : precallCells? rate rewards C_star C_h p.T z = some L := by
    rw [precallCells_at_or_after_firstCell rate rewards C_star C_h u t p.T
      (Nat.le_of_lt t.isLt) z hz]
    exact hPast
  refine ⟨hc, hs, hshort, f, head, valid, D, L, hLD, hDlen, hDzero,
    hPast, hlen, ?_, hsplit, vStart, hvStart, ?_⟩
  · intro n hn
    exact precallCells_take rate rewards C_star C_h n p.T hn z L hterminal
  · rw [hvStart]
    exact (precallPrefix_at_launch rate rewards C_star C_h z hc).1

end Bandits.Support.ReferenceFirstCollectionPrecallCalendarSupport

end
