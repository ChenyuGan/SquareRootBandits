/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSReferenceFirstLiveSourceStoppedHandoverEndpoint.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverRawPrefix
public import Bandits.Support.ReferenceFirstLiveHandoverDownFeedback

/-!
# First-handover auxiliary calendar prefixes

Sources: `05_binary_transport.tex:244-281`, `06_interruptions.tex:246-299,431-440`,
and `appendix_a_local_protocol.tex:100-108,141-157` in the pinned ZIP4 manuscript.

The calendar continuation below is auxiliary analysis data. It retains the
original selected row and full DOWN affine samples, with zero reward and false
installation padding outside the finite prefix. It is not a physical run.
The decoder bank, stopped local phases, service counts and quota belong to the
subsequent `ReferenceFirstLiveHandoverPrefixReplay` consumer.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverSnapshotPrefix

local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {p : ConstructorDimensions.Parameters}

/-- The original zero-based launch boundary, including its terminal value. -/
def start (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed

/-- The exclusive calendar endpoint retains the first detecting update. -/
def stop (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) : ℕ :=
  min n (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z - 1)

/-- An actual successful installation, read from the retained choice and
ordinary output. The equality tests keep the whole current DOWN record. -/
def installationFlag {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Bool :=
  match (r.output.preparation.followers.followers i).configuration,
      (r.output.followers i).configuration with
  | .ordinary choice _, .ordinary next _ =>
      decide (choice.status = .unoccupied ∧
        next.lastDown = some (payload.downRecord i) ∧ next.status = .pending)
  | _, _ => false

theorem installationFlag_ordinary_iff {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hn : (r.output.followers i).configuration = .ordinary next nextMemory) :
    installationFlag payload r i = true ↔ choice.status = .unoccupied ∧
      next.lastDown = some (payload.downRecord i) ∧ next.status = .pending := by
  simp only [installationFlag, hc, hn, decide_eq_true_eq]

/-- The original row's controls and affine samples, with a fixed first-payload
DOWN word for the drawn follower at every calendar date. The UP word is fixed
analysis data; no UP-decoder correspondence is asserted. -/
def auxiliaryInput {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ActiveRoundActions.RoundInput payload.assignment (AffineBatchDecoder.width p) :=
  let row := z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
  let u := row.2 t
  let i := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1
  { slot := PublicDiscreteDraws.slotDraw u.1
    selected := i
    tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1
    pilots := fun player => PublicDiscreteDraws.pilotDraw (K_pos p) player u.1
    down := ⟨u.2 (0, i), CoordinatorLocalArmChoice.storedDownFlatWord payload i⟩
    up := ⟨u.2 (1, i), fun _ => 0⟩
    fast := payload.assignment.auxiliary
    fast_outside := payload.assignment.auxiliary_outside }

/-- Zero padding is a reward row in the same full arm carrier. -/
def zeroRow : ActiveRoundActions.RewardRow p.K := ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

/-- One auxiliary continuation, indexed by a proved actual first payload.
It uses actual retained installation flags only inside `[start, stop)`. -/
def auxiliaryLive (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (_hpayload : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload)
    (t : Fin p.T) : ActiveRoundActions.LiveRoundData payload.assignment (AffineBatchDecoder.width p) :=
  { input := auxiliaryInput payload z t
    rewards := if start rate rewards C_star C_h z ≤ t.val ∧
        t.val < stop rate rewards C_star C_h z n then
      ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t else zeroRow
    acceptCurrent := fun i =>
      if start rate rewards C_star C_h z ≤ t.val ∧
          t.val < stop rate rewards C_star C_h z n then
        match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
        | some r => installationFlag payload r i
        | none => false
      else false }

theorem auxiliaryLive_input (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) (t : Fin p.T) :
    (auxiliaryLive rate rewards C_star C_h z n payload hp t).input =
      auxiliaryInput payload z t := rfl

theorem auxiliaryInput_down_bit {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    (auxiliaryInput payload z t).down.bit =
      CoordinatorLocalArmChoice.currentDownHash payload
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t)
        (auxiliaryInput payload z t).selected := rfl

theorem auxiliaryLive_on_prefix (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) (t : Fin p.T)
    (hs : start rate rewards C_star C_h z ≤ t.val)
    (ht : t.val < stop rate rewards C_star C_h z n)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    (auxiliaryLive rate rewards C_star C_h z n payload hp t).rewards =
        ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t ∧
      (auxiliaryLive rate rewards C_star C_h z n payload hp t).acceptCurrent =
        installationFlag payload r := by
  simp only [auxiliaryLive, hs, ht, and_self, ite_true, hr]

theorem auxiliaryLive_padding (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) (t : Fin p.T)
    (hout : t.val < start rate rewards C_star C_h z ∨
      stop rate rewards C_star C_h z n ≤ t.val) :
    (auxiliaryLive rate rewards C_star C_h z n payload hp t).rewards = zeroRow ∧
      (auxiliaryLive rate rewards C_star C_h z n payload hp t).acceptCurrent = fun _ => false := by
  have hnot : ¬ (start rate rewards C_star C_h z ≤ t.val ∧
      t.val < stop rate rewards C_star C_h z n) := by omega
  simp only [auxiliaryLive, hnot, ite_false, and_self]

theorem feedback_zero {a : ActiveRoundActions.Assignment p.m p.K}
    (s : ActiveRoundActions.Snapshot a) (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (player : Fin p.m) : ActiveRoundActions.feedback p.two_le_m s input zeroRow player = 0 := by
  unfold ActiveRoundActions.feedback FiniteBanditModel.playerFeedback
  split <;> rfl

/-- Padding preserves any snapshot, so the fold genuinely starts at zero. -/
theorem finish_zero {a : ActiveRoundActions.Assignment p.m p.K}
    (s : ActiveRoundActions.Snapshot a) (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p)) :
    ActiveRoundActions.finishLiveRound p.two_le_m s input zeroRow (fun _ => false) = s := by
  have hc : ¬ ActiveRoundActions.confirmation p.two_le_m s input zeroRow input.selected := by
    intro h
    have hz := feedback_zero s input (ActiveRoundActions.coordinator p.two_le_m)
    exact (lt_irrefl 0) (hz ▸ h.2.2.2.2)
  have hr : ∀ j, ¬ ActiveRoundActions.releaseObservation p.two_le_m s input zeroRow j := by
    intro j h
    have hz := feedback_zero s input (PublicDiscreteDraws.followerPlayer p.two_le_m j)
    exact (lt_irrefl 0) (hz ▸ h.1)
  cases s
  simp only [ActiveRoundActions.finishLiveRound, hc, ite_false, ActiveRoundActions.statusAfterAcceptance,
    Bool.false_eq_true, and_false, hr, and_false]

/-- Every fold entry strictly before the launch is padding. -/
theorem prestart_snapshot (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload)
    (k : ℕ) (hk : k ≤ start rate rewards C_star C_h z) :
    ActiveRoundActions.liveSegment p.two_le_m
      ((List.ofFn (auxiliaryLive rate rewards C_star C_h z n payload hp)).take k) =
      ActiveRoundActions.initialSnapshot payload.assignment := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstart : start rate rewards C_star C_h z ≤ p.T := by
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      have hkT : k < p.T := by omega
      rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using hkT)]
      simp only [List.getElem_ofFn, ActiveRoundActions.liveSegment, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hpad := auxiliaryLive_padding rate rewards C_star C_h z n payload hp
        ⟨k, hkT⟩ (Or.inl (show k < start rate rewards C_star C_h z from by omega))
      rw [hpad.1, hpad.2, finish_zero]
      exact ih (by omega)

/-- Extending the cutoff leaves every earlier auxiliary entry unchanged. -/
theorem auxiliaryLive_locality (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n₁ n₂ : ℕ) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) (t : Fin p.T)
    (hcut : (t.val < stop rate rewards C_star C_h z n₁) ↔
      (t.val < stop rate rewards C_star C_h z n₂)) :
    auxiliaryLive rate rewards C_star C_h z n₁ payload hp t =
      auxiliaryLive rate rewards C_star C_h z n₂ payload hp t := by
  simp only [auxiliaryLive, hcut]

/-- Snapshot locality uses the strict earlier prefix, including all padding. -/
theorem snapshot_locality (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n₁ n₂ : ℕ) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) (t : Fin p.T)
    (hcut : ∀ u : Fin p.T, u.val < t.val →
      (u.val < stop rate rewards C_star C_h z n₁ ↔
        u.val < stop rate rewards C_star C_h z n₂)) :
    ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n₁ payload hp) t =
      ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n₂ payload hp) t := by
  unfold ActiveObservationBridge.liveSnapshotBefore
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
  · intro k h₁ _
    have hkt : k < t.val := by
      have hh : k < min t.val p.T := by
        simpa only [List.length_take, List.length_ofFn] using h₁
      exact (lt_min_iff.mp hh).1
    have hkT : k < p.T := hkt.trans t.isLt
    simp only [List.getElem_take, List.getElem_ofFn]
    exact auxiliaryLive_locality rate rewards C_star C_h z n₁ n₂ payload hp
      ⟨k, hkT⟩ (hcut ⟨k, hkT⟩ hkt)

/-- Actual incoming and prepared configurations agree throughout the original
first-live window. Ordinary configurations, current fields and the initial
statuses are produced from the corrected seed and actual start-round calls. -/
theorem actual_window_frame (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
    ∀ k : Fin W.length,
      let r := W.get k
      ∃ (selected : ReferenceActivePhysicalStep.Selection r.input)
        (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
        r.output.preparation.coordinator.selection = some selected ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z =
          some selected.view.payload ∧
        r.input.rows = z.1.2 ∧
        r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        r.input.rewards = rewards ∧
        (∀ i, r.input.state.followers i = .ordinary (states i) (memories i)) ∧
        (∀ i, (r.output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)) ∧
        (∀ i, (states i).status = .unoccupied ↔ (states i).lastDown = none) ∧
        (∀ i, (states i).status ≠ .unoccupied →
          (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
        (selected.view.pendingAtChoice.Nonempty → ∀ i, (states i).status ≠ .released) ∧
        (k.val = 0 → ∀ i, (states i).status = .unoccupied) := by
  let s := start rate rewards C_star C_h z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := seed.activeAtStart
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  let R := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hspan
  have hcomplete : R.records = ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
      rate rewards C_star C_h z := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards
      C_star C_h initial
      (ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc).1).symm
  have hwindow : W = ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [hcomplete]
  dsimp only
  rw [← hwindow]
  intro k
  let r := W.get k
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate z rewards C_star C_h hc count hspan k
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode seed.coordinatorFirst seed.followers seed.memory seed.configuration
    seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none seed.unoccupied
    seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hgeom := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode seed.coordinatorFirst k cell.selected cell.selection_actual
  obtain ⟨hsigma, htime, hgrid, hbits⟩ := hgeom
  change cell.selected.view.payload.sigma.val = s at hsigma
  change r.input.time.val = s + k.val at htime
  change r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
    cell.selected.view.payload.sigma at hgrid
  change ∀ t : Fin p.T, s ≤ t.val → t.val < r.input.time.val →
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t = false at hbits
  have hrprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation r.output_eq
  have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro j st mem hj
    obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((seed.configuration j).symm.trans hj)
    exact ⟨seed.unoccupied j, seed.lastDown_none j⟩
  have hselected : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
      some cell.selected := by
    rw [← hrprep]
    exact cell.selection_actual
  have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_no_released
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode seed.coordinatorFirst hinitial k cell.selected hselected
  have hincoming : ∀ i, r.input.state.followers i =
      .ordinary (cell.states i) (cell.memories i) ∧
      ((cell.states i).status = .unoccupied → (cell.states i).lastDown = none) ∧
      (k.val = 0 → (cell.states i).status = .unoccupied) := by
    intro i
    obtain ⟨hprefix, hprefixStates⟩ := hsafe.1 k.val k.isLt.le
    obtain ⟨before, memory, hbefore, hlocal, _, _, _, hzero, hoccupied⟩ := hprefixStates i
    obtain ⟨_, hactual, _⟩ := ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
      hmode k
    have hinputState : r.input.state = (ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val hprefix
        hmode).finalState := by
      change r = _ at hactual
      rw [hactual]
      rfl
    have hinput : r.input.state.followers i = .ordinary before memory := by
      rw [hinputState]
      exact hbefore
    have hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time before memory =
        .ok (before, memory) := by
      by_cases hu : before.status = .unoccupied
      · exact ActiveFollowerLifecycle.startRound_unoccupied rate.eta r.input.time before memory hlocal hu
      · obtain ⟨_, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := hoccupied hu
        have hcoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate M =
            cell.selected.view.payload.sigma := by
          apply Fin.ext
          have hone := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
          change cell.selected.view.payload.sigma.val = s at hsigma
          omega
        have hrecordTime : M.val.sigma ≤ r.input.time.val := by
          change r.input.time.val = s + k.val at htime
          omega
        have hrecordGrid : r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
          rw [hcoordinate]
          exact hgrid
        have hbitFalse : token.bit = false := by
          rw [hbit]
          apply hbits token.timestamp
          · omega
          · change r.input.time.val = s + k.val at htime
            omega
        have hgridNe : FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate M) ≠ r.input.time.val + 1 := by omega
        have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta
          r.input.time before memory hu hlocal M hM hrecordTime (by omega) token hread
          (by change token.timestamp.val + 1 = r.input.time.val; omega)
        simpa only [hgridNe, decide_false, hbitFalse, Bool.false_or,
          Bool.false_eq_true, ite_false] using hbranch
    have hprep : (r.output.preparation.followers.followers i).configuration =
        .ordinary (cell.states i) (cell.memories i) := cell.ordinary i
    rw [r.output.preparation.followers.followers_eq i] at hprep
    obtain ⟨actualBefore, actualMemory, _, hactualBefore, hstartActual, _⟩ :=
      ReferenceActiveDataOwnership.prepare_ordinary_choice i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i) (r.input.state.followers i)
        (cell.states i) (cell.memories i) hprep
    obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinput.symm.trans hactualBefore)
    have heq := Prod.mk.inj (Except.ok.inj (hstart.symm.trans hstartActual))
    have hstate : cell.states i = before := heq.1.symm
    have hmemory : cell.memories i = memory := heq.2.symm
    refine ⟨by rw [hstate, hmemory]; exact hinput, ?_, ?_⟩
    · rw [hstate]
      exact fun hu => (hzero hu).1
    · intro hk0
      have hseedBefore : before = seed.followers i := by
        have hb : initial.followers i = .ordinary before memory := by
          have hb := hbefore
          simp only [hk0] at hb
          rw [ReferenceActivePhysicalHorizon.run_zero_final] at hb
          exact hb
        exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          (hb.symm.trans (seed.configuration i))).1
      rw [hstate, hseedBefore]
      exact seed.unoccupied i
  have hfields : ∀ i, (cell.states i).status ≠ .unoccupied →
      (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i) := by
    intro i
    have hp : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (cell.states i) (cell.memories i) := by
      rw [← hrprep]
      exact cell.ordinary i
    exact (hcarried i (cell.states i) (cell.memories i) hp).1
  have hpayload : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some cell.selected.view.payload := by
    have hprov := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
      rate rewards C_star C_h z hc
    dsimp only at hprov
    rw [← hwindow] at hprov
    obtain hzero | ⟨hW, installed, firstSelected, _, _, _, _, hp, hrows⟩ := hprov
    · have hk := k.isLt
      omega
    · obtain ⟨selected, hsel, hsame, _⟩ := hrows k
      have heq : selected = cell.selected := Option.some.inj
        (hsel.symm.trans cell.selection_actual)
      exact hp.trans (congrArg some (hsame.symm.trans (congrArg
        (fun chosen : ReferenceActivePhysicalStep.Selection r.input => chosen.view.payload) heq)))
  obtain ⟨_, hrows, hJ, hrewards, _⟩ :=
    ReferenceFirstWindowNumericalStream.actual_first_live_source_cell
      rate z rewards C_star C_h hc count hspan k
  refine ⟨cell.selected, cell.states, cell.memories, cell.selection_actual, cell.assignment_live, hpayload,
    hrows, hJ, hrewards, fun i => (hincoming i).1, cell.ordinary, ?_, hfields, ?_, ?_⟩
  · intro i
    constructor
    · exact (hincoming i).2.1
    · intro hnone
      by_contra hu
      have hsome := hfields i hu
      rw [hnone] at hsome
      cases hsome
  · intro hnonempty i
    have hp : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (cell.states i) (cell.memories i) := by
      rw [← hrprep]
      exact cell.ordinary i
    exact (hcarried i (cell.states i) (cell.memories i) hp).2 hnonempty
  · intro hk0 i
    exact (hincoming i).2.2 hk0

/-- Retained accepted diagnostics supply the actual selection test. -/
theorem acceptedDown_selected {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (haccepted : ReferenceFirstLiveConfirmationHistory.AcceptedDown r i M) :
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hi, hd, ho⟩ := haccepted
  obtain ⟨_, _, actualLogged, _, _, _, hi', hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
  have heq : actualLogged = logged := Option.some.inj (hi'.symm.trans hi)
  subst actualLogged
  have hcutAccepted := hcut ▸ ho
  have hselected : ActiveFollowerDownAcceptance.downSelected p
      (r.output.preparation.followers.followers i).follower
      (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).time := by
    by_contra hnot
    rw [ReferenceDownReception.referenceDownCut, dite_eq_right hnot] at hcutAccepted
    cases hcutAccepted
  have halign := r.output.preparation.follower_alignment i
  simpa only [halign.1, halign.2.1, halign.2.2.1] using hselected

/-- A true computed flag is an actual retained accepted current record,
with successful ordinary output. Parse success alone is insufficient. -/
theorem installationFlag_true_accepted {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hn : (r.output.followers i).configuration = .ordinary next nextMemory)
    (hnone : choice.lastDown = none)
    (hflag : installationFlag payload r i = true) :
    ReferenceFirstLiveConfirmationHistory.AcceptedDown r i (payload.downRecord i) ∧
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  obtain ⟨hu, hcurrent, _⟩ :=
    (installationFlag_ordinary_iff payload r i choice next choiceMemory nextMemory hc hn).mp hflag
  have hn' : r.output.next.followers i = .ordinary next nextMemory := by
    rw [r.output_eq] at hn ⊢
    exact hn
  obtain ⟨choice', memory', hc', _, _, hchange⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology r i next nextMemory hn'
  have hc'' : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice' memory' := hc'
  obtain ⟨heqChoice, heqMemory⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hc''.symm.trans hc)
  subst choice'
  subst memory'
  have hne : ReferencePrelaunchFollower.acceptedStart choice ≠
      ReferencePrelaunchFollower.acceptedStart next := by
    have hz : ReferencePrelaunchFollower.acceptedStart choice = 0 := by
      simp only [ReferencePrelaunchFollower.acceptedStart, hnone]
    have hnstart : ReferencePrelaunchFollower.acceptedStart next = payload.sigma.val + 1 := by
      simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
    omega
  obtain ⟨logged, cut, after, raw, M, scan, registers, lastService, hi, hd, ho, _⟩ := hchange hne
  have heq := (ReferenceFirstLiveDownNumericalRecovery.accepted_down_release_finish_frame
    r i choice choiceMemory hc logged after cut raw M scan registers lastService hi hd ho
      next nextMemory hn).2
  obtain ⟨_, _, actualLogged, _, _, _, hi', hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
  have hl : actualLogged = logged := Option.some.inj (hi'.symm.trans hi)
  subst actualLogged
  have hlast := (ReferenceFollowerReplyChronology.referenceDownCut_accepted
    _ _ _ _ _ logged after raw M scan registers lastService (hcut ▸ ho)).2
  have hM : M = payload.downRecord i := Option.some.inj
    (hlast.symm.trans (heq ▸ hcurrent))
  subst M
  have ha : ReferenceFirstLiveConfirmationHistory.AcceptedDown r i (payload.downRecord i) :=
    ⟨logged, cut, after, raw, scan, registers, lastService, hi, hd, ho⟩
  exact ⟨ha, acceptedDown_selected r i (payload.downRecord i) ha⟩

/-- The live missing-set barrier disables release independently of unused
UP words and fast-arm analysis data. -/
theorem finish_status_while_missing {a : ActiveRoundActions.Assignment p.m p.K}
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (row : ActiveRoundActions.RewardRow p.K)
    (flags : ActiveRoundActions.Follower p.m → Bool)
    (hne : snapshot.missing.Nonempty) (i : ActiveRoundActions.Follower p.m) :
    (ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row flags).status i =
      ActiveRoundActions.statusAfterAcceptance snapshot input flags i := by
  have hno : ¬ (snapshot.status i = .pending ∧
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i) := by
    rintro ⟨hpending, hrelease⟩
    exact ActiveRoundActions.no_releaseObservation_while_missing p.two_le_m snapshot
      input row i hne.ne_empty hpending hrelease
  exact ite_eq_right hno

/-- Conditional one-round status calculation. Its configuration and field
inputs are supplied by consecutive actual supported records at application. -/
theorem physical_status_step {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (states next : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories nextMemories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : ∀ i, (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hnext : ∀ i, (r.output.followers i).configuration = .ordinary (next i) (nextMemories i))
    (hnone : ∀ i, (states i).status = .unoccupied → (states i).lastDown = none)
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hnextFields : ∀ i, (next i).status = .pending →
      (next i).lastDown = some (selected.view.payload.downRecord i))
    (hnoReleased : ∀ i, (states i).status ≠ .released)
    (hnextNoReleased : ∀ i, (next i).status ≠ .released)
    (hne : selected.view.pendingAtChoice.Nonempty)
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment (AffineBatchDecoder.width p))
    (hslot : input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1)
    (hdraw : input.selected = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1)
    (row : ActiveRoundActions.RewardRow p.K) (i : Fin (p.m - 1)) :
    (ActiveRoundActions.finishLiveRound p.two_le_m
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩ input row
      (installationFlag selected.view.payload r)).status i = (next i).status := by
  have hfinishStatus := finish_status_while_missing
    (⟨selected.view.pendingAtChoice, fun j => (states j).status⟩ :
      ActiveRoundActions.Snapshot selected.view.payload.assignment)
    input row (installationFlag selected.view.payload r) hne i
  refine hfinishStatus.trans ?_
  by_cases hu : (states i).status = .unoccupied
  · by_cases hn : (next i).status = .unoccupied
    · have hflag : installationFlag selected.view.payload r i = false := by
        simp only [installationFlag, hchoice i, hnext i, hn, reduceCtorEq, and_false, decide_false]
      simp only [ActiveRoundActions.statusAfterAcceptance, hu, hflag,
        Bool.false_eq_true, and_false, ite_false, hn]
    · have hpending : (next i).status = .pending := by
        cases h : (next i).status <;> simp_all
      have hflag : installationFlag selected.view.payload r i = true :=
        (installationFlag_ordinary_iff _ r i _ _ _ _ (hchoice i) (hnext i)).mpr
          ⟨hu, hnextFields i hpending, hpending⟩
      have hselected := (installationFlag_true_accepted selected.view.payload r i
        (states i) (next i) (memories i) (nextMemories i) (hchoice i) (hnext i)
        (hnone i hu) hflag).2
      have hs : input.slot = PublicDiscreteDraws.downSlot := hslot.trans hselected.1
      have hi : input.selected = i := hdraw.trans hselected.2
      simp only [ActiveRoundActions.statusAfterAcceptance, hu, hs, hi, hflag, hpending,
        true_and, and_true]
      exact ite_eq_left (by rfl)
  · have hpending : (states i).status = .pending := by
      cases h : (states i).status <;> simp_all
    have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r
    have hout := hnext i
    rw [hfinish] at hout
    obtain ⟨choice, memory, post, hc, hr, hf, _, _⟩ :=
      ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _
        (next i) (nextMemories i) hout
    obtain ⟨heq, hmem⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hc.symm.trans (hchoice i))
    subst choice
    subst memory
    have hn := (ReferenceActiveConfirmationRelease.pending_choice_successful_finish_preserves_status
      r.output.preparation selected hsel i (states i) (memories i) hne (hchoice i)
      hpending (hfields i hu) post hr (next i) (nextMemories i) hf).2.1
    simp [ActiveRoundActions.statusAfterAcceptance, hpending, hn]

/-- The actual confirmation erasure uses the same incoming status and
full-width DOWN bit as the auxiliary model. Only a DOWN feedback identity is
needed; no physical action identity on other branches is assumed. -/
theorem physical_confirmation_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z = some r)
    (hrW : r ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time)
    (hrow : r.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hin : ∀ i, r.input.state.followers i = .ordinary (states i) (memories i))
    (hchoice : ∀ i, (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hnoReleased : ∀ i, (states i).status ≠ .released)
    (hne : selected.view.pendingAtChoice.Nonempty) :
    ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ↔
      ActiveRoundActions.confirmation p.two_le_m
        ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
        (auxiliaryInput selected.view.payload z r.input.time)
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time)
        (auxiliaryInput selected.view.payload z r.input.time).selected := by
  let input := auxiliaryInput selected.view.payload z r.input.time
  let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
    ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
  let i : Fin (p.m - 1) := input.selected
  have hslot : input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 := by
    dsimp [input, auxiliaryInput]
    rw [hrow]
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i := by
    dsimp [i, input, auxiliaryInput]
    rw [hrow]
  have hhash : input.down.bit = CoordinatorLocalArmChoice.currentDownHash selected.view.payload
      (r.input.row.2 r.input.time) i := by
    rw [hrow]
    rfl
  have hinvariant : ActiveRoundActions.no_released_while_missing snapshot := by
    intro _ j
    exact hnoReleased j
  have hobs (hpending : (states i).status = .pending)
      (hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.downSlot)
      (hmem : i ∈ selected.view.pendingAtChoice)
      (hzero : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 r.input.time) i = 0) :
      CoordinatorLocalArmChoice.ownGridObservationValue r.output.preparation.coordinatorObservation =
        ActiveRoundActions.feedback p.two_le_m snapshot input
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time)
          (ActiveRoundActions.coordinator p.two_le_m) := by
    have hnot : (states i).status ≠ .unoccupied := by rw [hpending]; decide
    have hactual := ReferenceFirstLiveHandoverDownFeedback.actual_first_live_after_down_feedback
      rate rewards C_star C_h z r.input.time r hr hrW selected hsel i hmem hdown hdraw
      ⟨states i, memories i, hin i, hfields i hnot⟩ hzero
    have hmodel := ActiveRoundActions.pending_down_coordinator_feedback p.two_le_m snapshot input
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time)
      (hslot.trans hdown) hmem hinvariant hpending (hhash.trans hzero)
    have hnormalized :
        (r.output.preparation.feedback.observations (ActiveRoundActions.coordinator p.two_le_m)).val.val =
          CoordinatorLocalArmChoice.ownGridObservationValue r.output.preparation.coordinatorObservation :=
      r.output.preparation.feedback.observation_grid_value _
    rw [← hnormalized, hactual, hmodel]
    dsimp [input, auxiliaryInput, ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow]
    rw [hrow]
    rfl
  constructor
  · intro hevent
    obtain ⟨_, _, hdown, hmem, hzero, hpositive⟩ := hevent
    rw [hdraw] at hmem hzero
    have hpending : (states i).status = .pending := by
      have hc : (r.output.preparation.followers.followers
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1)).configuration = .ordinary (states i) (memories i) := by
        rw [hdraw]
        exact hchoice i
      have ho := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
        r.output.preparation selected hsel (states i) (memories i) hc
        (show ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected from
          ⟨hlive, hne, hdown, by simpa only [hdraw] using hmem,
            by simpa only [hdraw] using hzero, hpositive⟩)
      exact ho.resolve_right (hnoReleased i)
    refine ⟨hslot.trans hdown, rfl, hmem, hhash.trans hzero, ?_⟩
    rw [← hobs hpending hdown hmem hzero]
    exact hpositive
  · intro hconfirm
    change ActiveRoundActions.confirmation p.two_le_m snapshot input
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time) i at hconfirm
    have hpending := ActiveRoundActions.confirmation_implies_pending p.two_le_m snapshot input
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time) i hinvariant hconfirm
    obtain ⟨hdown, _, hmem, hzero, hpositive⟩ := hconfirm
    have hd : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
        PublicDiscreteDraws.downSlot := hslot.symm.trans hdown
    have hz : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 r.input.time) i = 0 := hhash.symm.trans hzero
    refine ⟨hlive, hne, hd, ?_, ?_, ?_⟩
    · rw [hdraw]
      exact hmem
    · rw [hdraw]
      exact hz
    · rw [hobs hpending hd hmem hz]
      exact hpositive

/-- The strict calendar fold advances by exactly its current entry. -/
theorem snapshot_successor {a : ActiveRoundActions.Assignment p.m p.K}
    (live : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (t u : Fin p.T) (hu : u.val = t.val + 1) :
    ActiveObservationBridge.liveSnapshotBefore p a live u =
      ActiveRoundActions.finishLiveRound p.two_le_m
        (ActiveObservationBridge.liveSnapshotBefore p a live t)
        (live t).input (live t).rewards (live t).acceptCurrent := by
  unfold ActiveObservationBridge.liveSnapshotBefore
  rw [hu, List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using t.isLt)]
  simp only [List.getElem_ofFn, ActiveRoundActions.liveSegment, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- A supported actual record supplies launch, without any supplied launch or
history invariant. The terminal and absent-launch branches are impossible here. -/
theorem crossing_of_support (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (d : ℕ)
    (hd : d ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  by_contra hnot
  have hnone : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing = none := by
    cases hv : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing with
    | none => rfl
    | some c => simp [hv] at hnot
  have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate z rewards C_star C_h).mpr hnone
  have hnil := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
    rate rewards C_star C_h z hlaunch
  obtain ⟨k, _, _, _⟩ :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff rate rewards C_star C_h z d).mp hd
  have hk := k.isLt
  simp only [hnil, List.length_nil] at hk
  omega

/-- Every earlier calendar entry of a supported window record is supported.
This retains the actual strict-past decoder and inclusive overflow endpoint. -/
theorem supported_predecessors (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k j : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (hjk : j.val ≤ k.val)
    (hk : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[k.val].input.time.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z) :
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z)[j.val].input.time.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z := by
  obtain ⟨k', hdate, hmissing, hstop⟩ :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff rate rewards C_star C_h z _).mp hk
  have heq : k' = k := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_date_injective
    rate rewards C_star C_h z k' k (by omega)
  subst k'
  have hsub := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_missing_antitone
    rate rewards C_star C_h z j k hjk
  have hjtime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z j).1
  have hktime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).1
  exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
    rate rewards C_star C_h z _).mpr ⟨j, rfl, hmissing.mono hsub, by omega⟩

/-- The actual calendar induction. The only branch selectors are launch,
actual payload lookup, supported date and the finite query cutoff. -/
theorem window_snapshot_projection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload) :
    let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
    ∀ k : Fin W.length,
      (W.get k).input.time.val + 1 ∈
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z →
      (W.get k).input.time.val < stop rate rewards C_star C_h z n →
      let snapshot := ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n payload hp) (W.get k).input.time
      snapshot.missing = ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (W.get k) ∧
        ∀ (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (W.get k).input.state.followers i = .ordinary state memory → snapshot.status i = state.status := by
  dsimp only
  intro k
  generalize hkval : k.val = j
  induction j generalizing k with
  | zero =>
      intro hd _
      have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z k).1
      have ht : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).get k).input.time.val = start rate rewards C_star C_h z := by
        change _ = start rate rewards C_star C_h z + k.val at htime
        calc
          _ = start rate rewards C_star C_h z + k.val := htime
          _ = start rate rewards C_star C_h z := by rw [hkval, Nat.add_zero]
      have hsnap : ActiveObservationBridge.liveSnapshotBefore p payload.assignment
          (auxiliaryLive rate rewards C_star C_h z n payload hp)
          ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time =
          ActiveRoundActions.initialSnapshot payload.assignment := by
        unfold ActiveObservationBridge.liveSnapshotBefore
        rw [ht]
        exact prestart_snapshot rate rewards C_star C_h z n payload hp _ le_rfl
      have hm := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_initial_missing
        rate rewards C_star C_h z (by have hh := k.isLt; omega)
      have hk0 : k = ⟨0, by have hh := k.isLt; omega⟩ := Fin.ext hkval
      have hm' : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
          ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k) = Finset.univ := by
        simpa only [hk0] using hm
      obtain ⟨_, states, memories, _, _, _, _, _, _, hin, _, _, _, _, hinit⟩ :=
        actual_window_frame rate rewards C_star C_h z hc k
      refine ⟨by rw [hsnap, hm']; rfl, ?_⟩
      intro i state memory hstate
      have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hin i).symm.trans hstate)
      rw [hsnap]
      exact (hinit hkval i).symm.trans (congrArg ReferencePrelaunchFollower.State.status heq.1)
  | succ j ih =>
      intro hd hcut
      let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
      have hkW : k.val < W.length := k.isLt
      let prev : Fin W.length := ⟨j, by omega⟩
      let a := W.get prev
      let b := W.get k
      have hprevTime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z prev).1
      have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z k).1
      have hsucc : b.input.time.val = a.input.time.val + 1 := by
        change a.input.time.val = _ at hprevTime
        change b.input.time.val = _ at htime
        dsimp only [prev] at hprevTime
        omega
      have hprevSup : a.input.time.val + 1 ∈
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z :=
        supported_predecessors rate rewards C_star C_h z k prev (by dsimp [prev]; omega) hd
      have hprevCut : a.input.time.val < stop rate rewards C_star C_h z n := by
        change b.input.time.val < _ at hcut
        omega
      obtain ⟨ihmissing, ihstatus⟩ := ih prev rfl hprevSup hprevCut
      obtain ⟨sa, states, memories, hsa, halive, hpa, harows, haJ, _, hain, hachoice,
        hanone, hafields, hanoreleased, _⟩ := actual_window_frame rate rewards C_star C_h z hc prev
      obtain ⟨sb, next, nextMemories, hsb, _, hpb, _, _, _, hbin, _, _, hbfields,
        hbnoreleased, _⟩ := actual_window_frame rate rewards C_star C_h z hc k
      change a.output.preparation.coordinator.selection = some sa at hsa
      change b.output.preparation.coordinator.selection = some sb at hsb
      change a.input.rows = z.1.2 at harows
      change a.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z at haJ
      have hpay : sa.view.payload = payload := Option.some.inj (hpa.symm.trans hp)
      have hsame : sb.view.payload = sa.view.payload := Option.some.inj (hpb.symm.trans hpa)
      subst payload
      have hma : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate a = sa.view.pendingAtChoice := by
        unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
        rw [hsa]
        rfl
      have hmb : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate b = sb.view.pendingAtChoice := by
        unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
        rw [hsb]
        rfl
      have hna : sa.view.pendingAtChoice.Nonempty := by
        rw [← hma]
        exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_date_mem_support_iff
          rate rewards C_star C_h z prev).mp hprevSup |>.1
      have hnb : sb.view.pendingAtChoice.Nonempty := by
        rw [← hmb]
        exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_date_mem_support_iff
          rate rewards C_star C_h z k).mp hd |>.1
      let live := auxiliaryLive rate rewards C_star C_h z n sa.view.payload hp
      let old := ActiveObservationBridge.liveSnapshotBefore p sa.view.payload.assignment live a.input.time
      have hstatus : old.status = fun i => (states i).status := by
        funext i
        exact ihstatus i (states i) (memories i) (hain i)
      have hsnapshot : old = ⟨sa.view.pendingAtChoice, fun i => (states i).status⟩ := by
        have hm : old.missing = sa.view.pendingAtChoice := ihmissing.trans hma
        calc
          old = ⟨old.missing, old.status⟩ := by cases old; rfl
          _ = _ := congrArg₂ ActiveRoundActions.Snapshot.mk hm hstatus
      have hlink : b.input.state = a.output.next := by
        have h := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_successor
          rate rewards C_star C_h z j (by have hh := k.isLt; omega)
        have hk' : k = ⟨j + 1, by have hh := k.isLt; omega⟩ := Fin.ext hkval
        simpa only [b, a, W, prev, hk', List.get_eq_getElem] using h
      have hnext : ∀ i, (a.output.followers i).configuration = .ordinary (next i) (nextMemories i) := by
        intro i
        have h := hbin i
        change b.input.state.followers i = _ at h
        rw [hlink, a.output_eq] at h
        simpa only [a.output_eq, ReferenceActivePhysicalStep.step] using h
      have hrow : a.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
        simp only [ReferenceActivePhysicalStep.RoundInput.row, harows, haJ]
      have hbounds : start rate rewards C_star C_h z ≤ a.input.time.val := by
        change a.input.time.val = start rate rewards C_star C_h z + prev.val at hprevTime
        omega
      have hlookup := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z prev).2
      have hentry := auxiliaryLive_on_prefix rate rewards C_star C_h z n sa.view.payload hp
        a.input.time hbounds hprevCut a hlookup
      have hadvance := snapshot_successor live a.input.time b.input.time hsucc
      change ActiveObservationBridge.liveSnapshotBefore p sa.view.payload.assignment live b.input.time = _ at hadvance
      rw [hentry.1, hentry.2] at hadvance
      have hconfirm := physical_confirmation_iff rate rewards C_star C_h z a hlookup
        (List.get_mem W prev) sa hsa halive hrow states memories hain hachoice hafields
        (hanoreleased hna) hna
      obtain ⟨sa', hsa', _, hmissingStep⟩ :=
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_missing_step
          rate rewards C_star C_h z j (by have hh := k.isLt; omega)
      have hsaEq : sa' = sa := Option.some.inj (hsa'.symm.trans hsa)
      subst sa'
      have hmissingStep' : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate b =
          if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent a sa then
            sa.view.pendingAtChoice.erase (auxiliaryInput sa.view.payload z a.input.time).selected
          else sa.view.pendingAtChoice := by
        have hk' : k = ⟨j + 1, by have hh := k.isLt; omega⟩ := Fin.ext hkval
        have hstep : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate b =
            if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent a sa then
              (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate a).erase
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (a.input.row.2 a.input.time).1)
            else ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate a := by
          simpa only [a, b, W, prev, hk', List.get_eq_getElem] using hmissingStep
        have hdraw : (auxiliaryInput sa.view.payload z a.input.time).selected =
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (a.input.row.2 a.input.time).1 := by
          dsimp [auxiliaryInput]
          rw [hrow]
        rw [hma, ← hdraw] at hstep
        exact hstep
      constructor
      · rw [hadvance]
        change (if ActiveRoundActions.confirmation p.two_le_m old
            (auxiliaryInput sa.view.payload z a.input.time)
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards a.input.time)
            (auxiliaryInput sa.view.payload z a.input.time).selected then
          old.missing.erase (auxiliaryInput sa.view.payload z a.input.time).selected else old.missing) = _
        rw [hsnapshot, ← propext hconfirm, hmissingStep']
      · intro i state memory hstate
        have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hbin i).symm.trans hstate)
        rw [hadvance]
        change (ActiveRoundActions.finishLiveRound p.two_le_m old
          (auxiliaryInput sa.view.payload z a.input.time)
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards a.input.time)
          (installationFlag sa.view.payload a)).status i = _
        rw [hsnapshot]
        have hstep := physical_status_step a sa hsa states next memories nextMemories hachoice hnext
          (fun i hu => (hanone i).mp hu) hafields
          (fun i hpending => by rw [← hsame]; exact hbfields i (by rw [hpending]; decide))
          (hanoreleased hna) (hbnoreleased hnb) hna
          (auxiliaryInput sa.view.payload z a.input.time)
          (by dsimp [auxiliaryInput]; rw [hrow])
          (by dsimp [auxiliaryInput]; rw [hrow])
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards a.input.time) i
        exact hstep.trans (congrArg ReferencePrelaunchFollower.State.status heq.1)

/-- The computed flag characterizes actual successful current-record
installation on the original first-live window, including recovery and finish. -/
theorem actual_installation_flag_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
    ∀ (k : Fin W.length) (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)),
      installationFlag payload (W.get k) i = true ↔
        ReferenceFirstLiveConfirmationHistory.AcceptedDown (W.get k) i (payload.downRecord i) := by
  let s := start rate rewards C_star C_h z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  let R := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hspan
  have hcomplete : R.records = ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
      rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h initial
      (ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc).1).symm
  have hwindow : W = ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [hcomplete]
  have hframe := actual_window_frame rate rewards C_star C_h z hc
  dsimp only at hframe ⊢
  rw [← hwindow] at hframe ⊢
  intro k payload i
  let r := W.get k
  obtain ⟨_, states, memories, _, _, _, _, _, _, _, hchoice, hanone, _⟩ := hframe k
  change (∀ i, (r.output.preparation.followers.followers i).configuration =
    .ordinary (states i) (memories i)) at hchoice
  change installationFlag payload r i = true ↔
    ReferenceFirstLiveConfirmationHistory.AcceptedDown r i (payload.downRecord i)
  constructor
  · intro hflag
    cases hn : (r.output.followers i).configuration with
    | dagger => simp only [installationFlag, hchoice i, hn, Bool.false_eq_true] at hflag
    | ordinary next nextMemory =>
      have hu := ((installationFlag_ordinary_iff payload r i (states i) next
        (memories i) nextMemory (hchoice i) hn).mp hflag).1
      exact (installationFlag_true_accepted payload r i (states i) next (memories i)
        nextMemory (hchoice i) hn ((hanone i).mp hu) hflag).1
  · intro ha
    have hnumeric := ReferenceFirstLiveDownNumericalRecovery.actual_first_live_down_numerical_recovery
      rate z rewards C_star C_h hc count hspan i k (payload.downRecord i) ha
    dsimp only at hnumeric
    obtain ⟨_, _, _, _, _, _, _, _, logged, cut, after, raw, scan, registers, lastService,
      next, nextMemory, _, hd, _, _, _, _, _, _, _, _, _, hn, _, _, hlast, _, _, _, hstatus, _⟩ := hnumeric
    obtain ⟨choice, memory, _, hc, hu, _⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
    exact (installationFlag_ordinary_iff payload r i choice next memory nextMemory hc hn).mpr
      ⟨hu, hlast, hstatus⟩

/-- A new physical acceptance cannot confirm in its own round: the receiver
was unoccupied at choice, while a confirmation requires prior occupancy. -/
theorem actual_installation_no_confirmation (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input)
    (hsel : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).output.preparation.coordinator.selection =
      some selected) (i : Fin (p.m - 1))
    (hflag : installationFlag payload
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k) i = true) :
    ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k) selected := by
  let r := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k
  have ha := (actual_installation_flag_iff rate rewards C_star C_h z hc k payload i).mp hflag
  have hdraw := (acceptedDown_selected r i (payload.downRecord i) ha).2
  obtain ⟨_, cut, _, _, _, _, _, _, hd, _⟩ := ha
  obtain ⟨choice, memory, _, hchoice, hu, _⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
  intro hevent
  have hchoice' : (r.output.preparation.followers.followers
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1)).configuration = .ordinary choice memory := by
    rw [hdraw]
    exact hchoice
  have ho := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
    r.output.preparation selected hsel choice memory hchoice' hevent
  rcases ho with h | h <;> rw [hu] at h <;> cases h

/-- The literal finite carrier shared with the next decoder/count consumer. -/
def prefixDates (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) : Finset (Fin p.T) :=
  Finset.univ.filter fun t => start rate rewards C_star C_h z ≤ t.val ∧
    t.val < stop rate rewards C_star C_h z n ∧ t.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z

/-- Original-source branch producer. A nonempty finite supported query
obtains the first actual payload once and uses its single auxiliary calendar
for every queried incoming snapshot. The empty branch creates no payload. -/
theorem actual_prefix_projection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    prefixDates rate rewards C_star C_h z n = ∅ ∨
      ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
        (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload),
      ∀ (t : Fin p.T), start rate rewards C_star C_h z ≤ t.val →
        t.val < stop rate rewards C_star C_h z n →
        t.val + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z →
        ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (selected : ReferenceActivePhysicalStep.Selection r.input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
          r.input.time = t ∧
          r.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (∀ i, r.input.state.followers i = .ordinary (states i) (memories i)) ∧
          (∀ i, (r.output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, installationFlag payload r i = true ↔
            ReferenceFirstLiveConfirmationHistory.AcceptedDown r i (payload.downRecord i)) ∧
          (∀ i, installationFlag payload r i = true →
            ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected) ∧
          let snapshot := ActiveObservationBridge.liveSnapshotBefore p payload.assignment
            (auxiliaryLive rate rewards C_star C_h z n payload hp) t
          snapshot.missing = selected.view.pendingAtChoice ∧
          snapshot.missing = ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
            rate rewards C_star C_h t.val z ∧
          ∀ i, snapshot.status i = (states i).status := by
  by_cases hempty : prefixDates rate rewards C_star C_h z n = ∅
  · exact Or.inl hempty
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨_, _, hud⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨_, _, _, firstSelected, _, hp, _⟩ :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_provenance
        rate rewards C_star C_h z (u.val + 1) hud
    refine Or.inr ⟨firstSelected.view.payload, hp, ?_⟩
    intro t _ ht hd
    have hc := crossing_of_support rate rewards C_star C_h z (t.val + 1) hd
    obtain ⟨k, hdate, _, _⟩ :=
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
        rate rewards C_star C_h z (t.val + 1)).mp hd
    let r := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k
    have htime : r.input.time = t := Fin.ext (by change r.input.time.val + 1 = t.val + 1 at hdate; omega)
    subst t
    obtain ⟨selected, states, memories, hsel, _, hpselected, _, _, _, hin, hchoice, _⟩ :=
      actual_window_frame rate rewards C_star C_h z hc k
    have hpay : selected.view.payload = firstSelected.view.payload := Option.some.inj
      (hpselected.symm.trans hp)
    have hprojection := window_snapshot_projection rate rewards C_star C_h z n hc
      firstSelected.view.payload hp k hd ht
    have hm : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r = selected.view.pendingAtChoice := by
      change r.output.preparation.coordinator.selection = some selected at hsel
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hsel]
      rfl
    refine ⟨r, selected, states, memories,
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z k).2, rfl, hsel, hpay, hin, hchoice,
        actual_installation_flag_iff rate rewards C_star C_h z hc k firstSelected.view.payload,
        actual_installation_no_confirmation rate rewards C_star C_h z hc k firstSelected.view.payload selected hsel,
        hprojection.1.trans hm, ?_, ?_⟩
    · exact hprojection.1.trans (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_eq_window_missing
        rate rewards C_star C_h z k hd).symm
    · intro i
      exact hprojection.2 i (states i) (memories i) (hin i)

/-- Empty physical correspondence gives zero for every supported sum. -/
theorem empty_prefix_sum (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (h : prefixDates rate rewards C_star C_h z n = ∅) (f : Fin p.T → ℝ) :
    (∀ t ∈ prefixDates rate rewards C_star C_h z n, False) ∧
      ∑ t ∈ prefixDates rate rewards C_star C_h z n, f t = 0 := by
  simp only [h, Finset.notMem_empty, false_implies, implies_true, Finset.sum_empty, and_self]

/-- Future queries and absent supported rounds have empty correspondence. -/
theorem prefixDates_empty_of (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (h : ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z = ∅ ∨
      n ≤ start rate rewards C_star C_h z) :
    prefixDates rate rewards C_star C_h z n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨hs, hstop, hd⟩ := (Finset.mem_filter.mp ht).2
  rcases h with h | h
  · rw [h] at hd
    exact Finset.notMem_empty _ hd
  · have hle : stop rate rewards C_star C_h z n ≤ n := min_le_left _ _
    omega

/-- No launch, empty window and launch at the horizon are explicit empty
physical branches. No launch index or payload is constructed in this result. -/
theorem exceptional_prefix_empty (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (h : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none ∨
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z = [] ∨
      start rate rewards C_star C_h z = p.T ∨ n ≤ start rate rewards C_star C_h z) :
    prefixDates rate rewards C_star C_h z n = ∅ := by
  apply prefixDates_empty_of
  rcases h with h | h | h | h
  · exact Or.inl (ReferenceFirstLiveSourceStoppedHandoverEndpoint.empty_window_endpoints
      rate rewards C_star C_h z (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z h)).1
  · exact Or.inl (ReferenceFirstLiveSourceStoppedHandoverEndpoint.empty_window_endpoints
      rate rewards C_star C_h z h).1
  · exact Or.inl (ReferenceFirstLiveSourceStoppedHandoverEndpoint.terminal_launch_endpoints
      rate rewards C_star C_h z h).1
  · exact Or.inr h

/-- Including query `t` uses the exclusive prefix `t + 1`, clipped at the
same global endpoint. Incoming acceptance still governs confirmation. -/
theorem query_included_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    t.val < stop rate rewards C_star C_h z (t.val + 1) ↔
      t.val < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h z - 1 := by
  simp only [stop, lt_min_iff, Nat.lt_succ_self, true_and]

/-- Once both query cutoffs cover `t`, their snapshots before `t` coincide. -/
theorem snapshot_locality_of_queries (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n₁ n₂ : ℕ) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload)
    (t : Fin p.T) (h₁ : t.val ≤ n₁) (h₂ : t.val ≤ n₂) :
    ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n₁ payload hp) t =
      ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n₂ payload hp) t := by
  apply snapshot_locality
  intro u hu
  simp only [stop, lt_min_iff]
  omega

/-- UP words, pilot values and fast arms cannot affect DOWN actions while
confirmations are missing, provided the actual DOWN controls and bit agree. -/
theorem down_actions_noninterference {a : ActiveRoundActions.Assignment p.m p.K}
    (snapshot : ActiveRoundActions.Snapshot a)
    (left right : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (hne : snapshot.missing.Nonempty)
    (hl : left.slot = PublicDiscreteDraws.downSlot)
    (hr : right.slot = PublicDiscreteDraws.downSlot)
    (hselected : left.selected = right.selected)
    (htuple : left.tuple = right.tuple) (hbit : left.down.bit = right.down.bit) :
    ActiveRoundActions.actions p.two_le_m snapshot left =
      ActiveRoundActions.actions p.two_le_m snapshot right := by
  have hnd : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by decide
  have hnu : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by decide
  funext player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hc | ⟨i, hi⟩
  · subst player
    rw [ActiveRoundActions.actions_coordinator, ActiveRoundActions.actions_coordinator]
    simp only [ActiveRoundActions.coordinatorAction, hne.ne_empty, hl, hr, hnd,
      ite_false, true_and, hselected, htuple, hbit]
  · subst player
    rw [ActiveRoundActions.actions_follower, ActiveRoundActions.actions_follower]
    simp only [ActiveRoundActions.followerAction, hl, hr, hnd, hnu, false_and,
      or_false, true_and, ite_false, hselected, htuple]

/-- The unused DOWN-round fields cannot affect any feedback or confirmation
identity. Together with the missing-set release barrier this covers status. -/
theorem down_feedback_noninterference {a : ActiveRoundActions.Assignment p.m p.K}
    (snapshot : ActiveRoundActions.Snapshot a)
    (left right : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (row : ActiveRoundActions.RewardRow p.K) (hne : snapshot.missing.Nonempty)
    (hl : left.slot = PublicDiscreteDraws.downSlot)
    (hr : right.slot = PublicDiscreteDraws.downSlot)
    (hselected : left.selected = right.selected)
    (htuple : left.tuple = right.tuple) (hbit : left.down.bit = right.down.bit)
    (flags : ActiveRoundActions.Follower p.m → Bool) :
    (∀ player, ActiveRoundActions.feedback p.two_le_m snapshot left row player =
      ActiveRoundActions.feedback p.two_le_m snapshot right row player) ∧
    (∀ i, ActiveRoundActions.confirmation p.two_le_m snapshot left row i ↔
      ActiveRoundActions.confirmation p.two_le_m snapshot right row i) ∧
    (∀ i, (ActiveRoundActions.finishLiveRound p.two_le_m snapshot left row flags).status i =
      (ActiveRoundActions.finishLiveRound p.two_le_m snapshot right row flags).status i) := by
  have hactions := down_actions_noninterference snapshot left right hne hl hr hselected htuple hbit
  have hf : ∀ player, ActiveRoundActions.feedback p.two_le_m snapshot left row player =
      ActiveRoundActions.feedback p.two_le_m snapshot right row player := by
    intro player
    unfold ActiveRoundActions.feedback
    rw [hactions]
  refine ⟨hf, ?_, ?_⟩
  · intro i
    simp only [ActiveRoundActions.confirmation, hl, hr, hselected, hbit, hf]
  · intro i
    rw [finish_status_while_missing _ _ _ _ hne, finish_status_while_missing _ _ _ _ hne]
    simp only [ActiveRoundActions.statusAfterAcceptance, hl, hr, hselected]

/-- With no DOWN and no installation, a nonempty live projection is unchanged
on UP, DATA and all remaining slot branches. -/
theorem finish_non_down {a : ActiveRoundActions.Assignment p.m p.K}
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (row : ActiveRoundActions.RewardRow p.K) (hne : snapshot.missing.Nonempty)
    (hslot : input.slot ≠ PublicDiscreteDraws.downSlot) :
    ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row (fun _ => false) = snapshot := by
  have hc : ¬ ActiveRoundActions.confirmation p.two_le_m snapshot input row input.selected :=
    fun h => hslot h.1
  have hm : (ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row (fun _ => false)).missing =
      snapshot.missing := ite_eq_right hc
  have hs : (ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row (fun _ => false)).status =
      snapshot.status := by
    funext i
    rw [finish_status_while_missing _ _ _ _ hne]
    simp only [ActiveRoundActions.statusAfterAcceptance, Bool.false_eq_true, and_false, ite_false]
  calc
    _ = ⟨(ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row (fun _ => false)).missing,
        (ActiveRoundActions.finishLiveRound p.two_le_m snapshot input row (fun _ => false)).status⟩ := by
      rfl
    _ = ⟨snapshot.missing, snapshot.status⟩ := congrArg₂ ActiveRoundActions.Snapshot.mk hm hs
    _ = snapshot := by cases snapshot; rfl

/-- Every actual non-DOWN first-live update has false installation flags.
This is derived from the retained physical installation characterization. -/
theorem actual_non_down_flags (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hslot : PublicDiscreteDraws.slotDraw
      (((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.row.2
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time).1 ≠
      PublicDiscreteDraws.downSlot) :
    installationFlag payload
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k) = fun _ => false := by
  funext i
  apply Bool.eq_false_iff.mpr
  intro hflag
  have ha := (actual_installation_flag_iff rate rewards C_star C_h z hc k payload i).mp hflag
  exact hslot (acceptedDown_selected _ i (payload.downRecord i) ha).1

/-- The DOWN word is the complete affine-decoder word for the same first
payload record; neither its width nor its coefficients are collapsed. -/
theorem auxiliaryInput_decoder_word {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    (auxiliaryInput payload z t).down.word = HandoverStoppedDecoderReplay.currentWord p
      (CanonicalRecordingRates.beta p rate.eta.val)
      (payload.downRecord (auxiliaryInput payload z t).selected) := rfl

/-- On an actual supported non-DOWN round, every local hypothesis of the
non-DOWN preservation calculation is produced from the original source. -/
theorem actual_non_down_projection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0 rate rewards C_star C_h z = some payload)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).length)
    (hd : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z)
    (ht : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time.val <
      stop rate rewards C_star C_h z n)
    (hslot : (auxiliaryInput payload z
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time).slot ≠
        PublicDiscreteDraws.downSlot) :
    let t := ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k).input.time
    let live := auxiliaryLive rate rewards C_star C_h z n payload hp
    let snapshot := ActiveObservationBridge.liveSnapshotBefore p payload.assignment live t
    ActiveRoundActions.finishLiveRound p.two_le_m snapshot (live t).input (live t).rewards
      (live t).acceptCurrent = snapshot := by
  dsimp only
  let r := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z).get k
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  have hprojection := window_snapshot_projection rate rewards C_star C_h z n hc payload hp k hd ht
  have hmissing : (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
      (auxiliaryLive rate rewards C_star C_h z n payload hp) r.input.time).missing.Nonempty := by
    rw [hprojection.1]
    exact ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_date_mem_support_iff
      rate rewards C_star C_h z k).mp hd).1
  obtain ⟨_, _, _, _, _, _, hrows, hJ, _⟩ := actual_window_frame rate rewards C_star C_h z hc k
  have hrow : r.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change r.input.rows = z.1.2 at hrows
    change r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z at hJ
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ]
  have hnondown : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ≠ PublicDiscreteDraws.downSlot := by
    rw [hrow]
    exact hslot
  have hflags := actual_non_down_flags rate rewards C_star C_h z hc k payload hnondown
  have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).1
  have hs : start rate rewards C_star C_h z ≤ r.input.time.val := by
    change r.input.time.val = start rate rewards C_star C_h z + k.val at htime
    omega
  have hentry := auxiliaryLive_on_prefix rate rewards C_star C_h z n payload hp r.input.time hs ht r
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar rate rewards C_star C_h z k).2
  rw [hentry.2, hflags]
  exact finish_non_down _ _ _ hmissing hslot

end Bandits.Support.ReferenceFirstLiveHandoverSnapshotPrefix

end
