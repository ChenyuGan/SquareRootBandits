/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationRun
public import Bandits.Support.ReferenceInitializationRun

/-!
# Internal actual/reference initialization comparison

The numerical input below retains the entire original published output and
private coordinates. The reference reads its selected original row. Past
histories contain accepted actual physical records, with no supplied current
actions or feedback.

Sources: `sources/zip4/manuscript/07_public_setup.tex:63-115,129-140`,
`08_main_theorem.tex:29-42`, `appendix_b_communication.tex:94-165,296-299`,
and `appendix_a_local_protocol.tex:6-14`.

These are internal deterministic lemmas, not a source-facing theorem or an
all-horizon coupling. In particular, no global initialization event is defined.

This module establishes the source initial base and the per-round physical,
own-history and declared-follower comparison seam. The remaining consumer is
the induction over `ActualInitializationRun.foldBlockAux`, carrying the
all-candidate/true-only register comparison through full gain and weight
updates, pending declarations, cumulative counters and strict crossing, and
then comparing `combinedBoundaryHandoff` with `finishBlock`. Neither that
consumer nor an equality-or-source-obstruction block theorem is claimed here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ActualReferenceInitializationBlock

open ConstructorDimensions BootstrapDimensions ActiveRoundActions
open ReferencePrelaunchFollower ActiveFollowerDownAcceptance
open scoped Classical

variable {p : Parameters}

/-- The same follower index on the accepted reference carrier. -/
abbrev refFollower (i : Fin (p.m - 1)) : Follower p.m := ⟨i.val, i.isLt⟩

/-- The existing reference input, literally projected from the original whole
published output and the original private arrays, with the same rewards,
constants and rate. No new random coordinate is introduced. -/
def referenceInput (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) : ReferenceInitializationRun.Input p where
  ids := source.1.1
  row := source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
  rewards := rewards
  coordinates := source.2
  C_star := C_star
  C_h := C_h
  eta := rate.eta

/-- A player's own entry of an accepted actual physical record. -/
def recordEntry {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin p.m) : Fin p.K × Observation p :=
  (record.result.actions i,
    ActualInitializationPhysicalStep.observationOfGrid p (record.result.feedback i))

/-- A local history is obtained by indexing the accumulated actual records;
there is no default or fabricated record. -/
def recordHistory {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (i : Fin p.m) : LocalHistory p past.length :=
  fun u => recordEntry past[u.val] i

/-- Induction data concerning only the already executed physical prefix. -/
def past_related {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (b : ReferenceInitializationRun.Boundary p) : Prop :=
  ∃ hlength : past.length = ReferenceInitializationRun.elapsed p b.completed,
    (∀ u : Fin past.length, past[u.val].time.val = u.val) ∧
    ∀ (i : Fin p.m) (u : Fin (ReferenceInitializationRun.elapsed p b.completed)),
      b.history i u = recordHistory past i (Fin.cast hlength.symm u)

/-- The follower part of the boundary induction relation. An activated
follower is in the true row, retains its exact ordinary replay state, buffer
and partial DOWN bank, and has no accepted assignment. Proposal memory is
arbitrary retained data. Dagger is excluded. -/
def follower_start_related (x : ReferenceInitializationRun.Input p)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (rate : RateInput p)
    (hRate : x.eta = rate.eta) (b : ReferenceInitializationRun.Boundary p)
    (i : Fin (p.m - 1)) (actual : ActualInitializationRun.FollowerCarry p rate) : Prop :=
  match actual with
  | .bootstrap numerators _ =>
      b.activation (refFollower i) = none ∧ numerators = b.numerators i
  | .declared row activation (.ordinary state _) =>
      row = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      b.activation (refFollower i) = some activation ∧
      state = hRate ▸ ReferenceInitializationRun.ordinary x b (refFollower i) ∧
      state.lastDown = none ∧ acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
      state.status = .unoccupied ∧ state.initializationFailure = false ∧
      state.buffer = (replay rate.eta i x.row activation
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p b.completed)).buffer ∧
      state.downBatch = (replay rate.eta i x.row activation
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p b.completed)).downBatch
  | .declared _ _ .dagger => False

/-- The block-start induction relation. All history clauses concern times
strictly before the current block. The coordinator's block-local fields are
reset by the accepted `beginBlock`, rather than constrained here. -/
def BlockStartRelated (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (s : Fin (n_boot p))
    (actual : ActualInitializationRun.BlockCarry p rate s)
    (b : ReferenceInitializationRun.Boundary p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards)) : Prop :=
  b.completed = s.val ∧ b.crossing = none ∧
  (∀ i, b.forcedFailure i = false) ∧
  actual.monitor.val.counters = b.counters ∧
  actual.C_star = C_star ∧ actual.C_h = C_h ∧
  past_related past b ∧
  ∀ i, follower_start_related (referenceInput source rewards C_star C_h rate)
    source rate rfl b i (actual.followers i)

/-- Source initial base: empty physical history, all-one weights, zero
cumulative counters, no declarations, and no launch or forced failure. -/
theorem initial_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) :
    BlockStartRelated source rewards C_star C_h rate
      (ActualInitializationRun.firstBlock p)
      (ActualInitializationRun.initialCarry p rate C_star C_h)
      (ReferenceInitializationRun.initial p) [] := by
  refine ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨by simp only [List.length_nil, ReferenceInitializationRun.initial,
      ReferenceInitializationRun.elapsed, Nat.zero_mul, Nat.min_zero], ?_, ?_⟩
    · intro u
      exact Fin.elim0 u
    · intro i u
      exact Fin.elim0 (Fin.cast (by simp only [ReferenceInitializationRun.elapsed,
        ReferenceInitializationRun.initial, Nat.zero_mul, Nat.min_zero]) u)
  · intro i
    exact ⟨rfl, rfl⟩

/-- Ordinary replay has valid carried buffer domains, derived from its actual
chronological typed observations rather than supplied as a success premise. -/
theorem replay_buffer_valid {n : ℕ} (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    ActiveFollowerLifecycle.localBufferValid (replay eta i row activation history hn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨u, _, htime, _⟩ := replay_buffer_fields eta i row activation history hn r hr
    rw [htime]
    exact ⟨Nat.succ_pos _, (Nat.succ_le_of_lt u.isLt).trans hn⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply (replay_buffer_pairwise eta i row activation history hn).imp
    intro a b hab heq
    exact (Nat.ne_of_lt hab) (congrArg Prod.fst heq)
  · intro r hr
    obtain ⟨u, _, _, _, hy, _⟩ := replay_buffer_fields eta i row activation history hn r hr
    obtain ⟨q, hq⟩ := (history u).2.property
    refine ⟨q.val, Nat.le_of_lt_succ q.isLt, ?_⟩
    rw [hy]
    exact hq

/-- Every domain checked by the unoccupied lifecycle is proved for the full
ordinary replay, including the retained partial DOWN bank. -/
theorem replay_domain_valid {n : ℕ} (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) :
    ActiveFollowerLifecycle.localStateDomainValid (replay eta i row activation history hn) := by
  obtain ⟨_, _, hS, hd, hb, _⟩ := replay_registers eta i row activation history hn
  obtain ⟨hpending, hcompleted, _⟩ := replay_batch_spec eta i row activation history hn
  refine ⟨?_, replay_buffer_valid eta i row activation history hn, hpending, hcompleted⟩
  exact ⟨hS ▸ Nat.zero_le _, hd ▸ Nat.zero_le _, hb ▸ Nat.zero_le _⟩

/-- Checked UP-offer domains follow from the lifecycle domains; no local
success or matching-word assumption is needed. -/
theorem up_domain_of_local_domain {eta : LearningRate} (state : State p eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2.1⟩

/-- A real zero-field state offers exactly the admissible source initial
record on its selected UP channel. This proves the check succeeds. -/
theorem checked_up_zero (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : Fin p.T) (state : State p eta)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hu : state.status = .unoccupied) (hs : acceptedStart state = 0)
    (hS : state.S = 0) (hd : state.delta = 0) (hb : state.backlog = 0)
    (hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation time) :
    ActiveFollowerQueueOperation.checkedUpOffer eta i row activation time state =
      .offer ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ := by
  have hfields : ActiveFollowerQueueOperation.upOfferFields state =
      OrdinaryMessageCodec.upPlaceholder := by
    simp only [ActiveFollowerQueueOperation.upOfferFields, hs, hS, hd, hb,
      OrdinaryMessageCodec.upPlaceholder]
  have hadm : OrdinaryMessageCodec.upAdmissible (codecParams p eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := hfields ▸ Or.inl rfl
  have hgate : ActiveFollowerQueueOperation.selectedUpRound i row activation time ∧
      state.status = .unoccupied := ⟨hselected, hu⟩
  simp only [ActiveFollowerQueueOperation.checkedUpOffer,
    dite_eq_left (up_domain_of_local_domain state hdomain), dite_eq_left hgate,
    dite_eq_left hadm]
  apply congrArg ActiveFollowerQueueOperation.UpOfferResult.offer
  exact Subtype.ext hfields

/-- The offered initial word is the existing reference zero word, through
the existing ordinary encoder; the unused DOWN rate cannot affect it. -/
theorem offered_zero_word (eta : LearningRate) :
    ActiveFollowerArmChoice.offeredUpWord eta
      (⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ :
        OrdinaryMessageCodec.UpRecord (codecParams p eta)) =
      BootstrapPhysicalBlock.initialUpWord p := rfl

/-- Unoccupied service is disabled: the accepted service output preserves
the entire carried state, for every latent arrival value. -/
theorem unoccupied_service_disabled (eta : LearningRate) (state : State p eta)
    (hu : state.status = .unoccupied) (n arrival : ℕ) :
    ¬ state.status.occupied ∧
    ActiveFollowerQueueOperation.serviceOutput n state arrival = state := by
  constructor
  · rw [hu]
    simp only [FollowerStatus.occupied, reduceCtorEq, or_self, not_false_eq_true]
  · exact ActiveFollowerQueueOperation.serviceOutput_unoccupied_preserves n state hu arrival

/-- Complete choice-time correspondence for an unoccupied zero-field
follower. The lifecycle and UP checks succeed for arbitrary retained memory;
the returned configuration is exactly the incoming one. -/
theorem prepare_unoccupied_zero {s : Fin (n_boot p)} (rate : RateInput p)
    (v : BootstrapPhysicalBlock.Input p s) (i : Fin (p.m - 1))
    (activation : Activation p) (time : Fin p.T) (ha : activation.val ≤ time.val + 1)
    (state : State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hu : state.status = .unoccupied) (hs : acceptedStart state = 0)
    (hS : state.S = 0) (hd : state.delta = 0) (hb : state.backlog = 0) :
    (DeclaredFollowerLocalRound.prepare rate i v.row activation time ha
      (.ordinary state memory)).configuration = .ordinary state memory ∧
    (DeclaredFollowerLocalRound.prepare rate i v.row activation time ha
      (.ordinary state memory)).arm = BootstrapPhysicalBlock.unoccupiedAction v time (refFollower i) := by
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta time state
    memory hdomain hu
  by_cases hdata : PublicDiscreteDraws.slotDraw (v.row.2 time).1 = PublicDiscreteDraws.dataSlot
  · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i v.row activation time ∧
        state.status = .unoccupied) := by
      rintro ⟨⟨_, hup, _⟩, _⟩
      rw [hdata] at hup
      exact (by decide : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot) hup
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i v.row
      activation time state (up_domain_of_local_domain state hdomain) hnot
    have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data state
      (v.row.2 time) i none hu hdata
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
      ActiveFollowerArmChoice.followerArmChoice, harm]
    exact ⟨trivial, (ite_eq_left hdata).symm⟩
  · by_cases hselected : PublicDiscreteDraws.slotDraw (v.row.2 time).1 =
        PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (v.row.2 time).1 = i
    · have hoff := checked_up_zero rate.eta i v.row activation time state hdomain hu
        hs hS hd hb ⟨ha, hselected⟩
      have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
          ActiveFollowerArmChoice.offeredUpMatchesState state
            (⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ :
              OrdinaryMessageCodec.UpRecord (codecParams p rate.eta)) := by
        constructor
        · exact hdomain.1
        · exact ⟨hs.symm, hS.symm, hd.symm, hb.symm⟩
      have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (v.row.2 time) i ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ hu
        hselected.1 hselected.2 hvalid
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, harm]
      constructor
      · trivial
      · have hselected' : PublicDiscreteDraws.slotDraw (v.row.2 time).1 =
            PublicDiscreteDraws.upSlot ∧ PublicDiscreteDraws.selectedFollowerDraw
              p.two_le_m p.m_lt_K (v.row.2 time).1 = refFollower i := hselected
        change sendArm (BootstrapPhysicalBlock.initialUpBit v time (refFollower i))
          ((BootstrapPhysicalBlock.tuple v time).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
          ((BootstrapPhysicalBlock.tuple v time).val (coordinator p.two_le_m)) = _
        unfold BootstrapPhysicalBlock.unoccupiedAction BootstrapPhysicalBlock.slot
          BootstrapPhysicalBlock.selected
        rw [ite_eq_right hdata, ite_eq_left hselected']
    · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i v.row activation time ∧
          state.status = .unoccupied) := fun h => hselected h.1.2
      have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i v.row
        activation time state (up_domain_of_local_domain state hdomain) hnot
      have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other state
        (v.row.2 time) i none hu hdata hselected
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, harm]
      constructor
      · trivial
      · have hselected' : ¬ (PublicDiscreteDraws.slotDraw (v.row.2 time).1 =
            PublicDiscreteDraws.upSlot ∧ PublicDiscreteDraws.selectedFollowerDraw
              p.two_le_m p.m_lt_K (v.row.2 time).1 = refFollower i) := hselected
        unfold BootstrapPhysicalBlock.unoccupiedAction BootstrapPhysicalBlock.slot
          BootstrapPhysicalBlock.selected
        rw [ite_eq_right hdata, ite_eq_right hselected']
        rfl

/-- Only the sampled activity/held-arm/ID fields of a startup state. Gain and
candidate registers do not enter the current arm rule, even after a save. -/
def startup_draws_related {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ v.uninformed}) (state : BootstrapObservedFollower.StartupState p s) : Prop :=
  match state.blockCase with
  | .inactive => v.active i = false
  | .active held privateID _ _ =>
      v.active i = true ∧ held = v.held i ∧ privateID = v.privateId i

/-- Local arm correspondence from the sampled fields, with all gain and
candidate data arbitrary. In particular pending saves cannot truncate play. -/
theorem startup_arm_eq {s : Fin (n_boot p)}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (v : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ v.uninformed})
    (state : BootstrapObservedFollower.StartupState p s) (time : Fin p.T)
    (hids : v.ids = source.1.1)
    (hu : v.uniform = BootstrapPhysicalInput.uniformArmMap p source.2)
    (havoid : ∀ t, (v.followerAvoid i t).val =
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (v.held i)
        (BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) t)).val)
    (h : startup_draws_related v i state) :
    BootstrapObservedFollower.localArm p s state source.1.1 time
      (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) t) =
      BootstrapPhysicalBlock.uninformedAction v time i := by
  cases hc : state.blockCase with
  | inactive =>
      simp only [startup_draws_related, hc] at h
      rw [BootstrapObservedFollower.localArm_inactive p s state source.1.1 time _ hc]
      simp only [BootstrapPhysicalBlock.uninformedAction, h, Bool.false_eq_true,
        ite_false, hu]
      rfl
  | active held privateID gain registers =>
      simp only [startup_draws_related, hc] at h
      rw [BootstrapObservedFollower.localArm_active p s state source.1.1 time _
        held privateID gain registers hc]
      rw [h.2.1, h.2.2]
      simp only [BootstrapPhysicalBlock.uninformedAction, h.1, ite_true, hids,
        havoid time]

/-- These sampled fields survive every accepted bootstrap observation. Gain
and all-candidate updates continue in the accepted operation. -/
theorem startup_draws_observe {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (i : {i // i ∈ v.uninformed})
    (state : BootstrapObservedFollower.StartupState p s)
    (rows : CompletePublicTable.CompleteRows p) (time : Fin p.T) (own : Observation p)
    (hin : time ∈ calendarBlock p s)
    (hopen : state.processed.val < BootstrapObservedFollower.blockLength p s)
    (hnext : time.val = BootstrapObservedFollower.blockStart p s + state.processed.val)
    (h : startup_draws_related v i state) :
    startup_draws_related v i
      (BootstrapObservedFollower.observeOne p s state v.ids rows time own hin hopen hnext) := by
  cases hc : state.blockCase with
  | inactive =>
      simpa only [startup_draws_related, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hc] using h
  | active held privateID gain registers =>
      simpa only [startup_draws_related, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hc] using h

/-- One follower's INTERNAL pre-round induction data. Its ordinary state is
the replay of the accumulated prior actual records, with arbitrary retained
memory. No current action, feedback, successful check or passing oracle occurs. -/
def round_follower_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (i : Fin (p.m - 1))
    (f : ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h)) : Prop :=
  let v := ReferenceInitializationRun.physical
    (referenceInput source rewards C_star C_h rate) b h
  match f with
  | .bootstrap state =>
      ∃ hi : refFollower i ∈ v.uninformed,
        state.numerators = b.numerators i ∧ startup_draws_related v ⟨refFollower i, hi⟩ state
  | .declared row activation (.ordinary state _) =>
      row = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      b.activation (refFollower i) = some activation ∧
      state = replay rate.eta i v.row activation
        (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn ∧
      state.initializationFailure = false
  | .declared _ _ .dagger => False

/-- Per-round induction data at an accepted preparation. The coordinator
state is the already processed reference prefix; follower data refer only to
past actual records and original sampled fields. -/
def round_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T)
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate
      (ReferenceInitializationRun.nextBlock b h)) : Prop :=
  prepared.source = source ∧ prepared.rewards = rewards ∧
  prepared.time.val = past.length ∧
  prepared.coordinatorInput.data.coordinator = BootstrapPhysicalBlock.run
    (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
    prepared.time.val ∧
  ∀ i, round_follower_related source rewards rate C_star C_h b h past hn i
    (prepared.followerInputs i)

/-- Physical arms and simultaneous collision feedback follow from the
INTERNAL pre-round relation. Neither vector is an incoming hypothesis. -/
theorem physical_round_correspondence
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T)
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hr : round_related source rewards rate C_star C_h b h past hn prepared) :
    let v := ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h
    ActualInitializationPhysicalStep.actionProfile prepared =
      BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v prepared.time.val)
        prepared.time ∧
    ActualInitializationPhysicalStep.physicalFeedback prepared = fun i =>
      BootstrapPhysicalBlock.observationIndex v (BootstrapPhysicalBlock.run v prepared.time.val)
        prepared.time i := by
  let v := ReferenceInitializationRun.physical
    (referenceInput source rewards C_star C_h rate) b h
  have hcoord : prepared.coordinator.arm = BootstrapPhysicalBlock.coordinatorAction v
      (BootstrapPhysicalBlock.run v prepared.time.val) prepared.time := by
    rw [ActualInitializationPhysicalStep.prepared_coordinator_arm_eq_choice,
      hr.1, hr.2.2.2.1]
    rfl
  have hfollowers : ∀ i, (prepared.followers i).arm =
      BootstrapPhysicalBlock.followerAction v prepared.time (refFollower i) := by
    intro i
    have helper (f : ActualInitializationPhysicalStep.FollowerState p rate
        (ReferenceInitializationRun.nextBlock b h))
        (hready : ActualInitializationPhysicalStep.followerAtNextCursor prepared.time f)
        (hf : round_follower_related source rewards rate C_star C_h b h past hn i f) :
        (ActualInitializationPhysicalStep.prepareFollowerValid rate
          (ReferenceInitializationRun.nextBlock b h) prepared.time prepared.source i f hready).arm =
          BootstrapPhysicalBlock.followerAction v prepared.time (refFollower i) := by
      cases f with
      | bootstrap state =>
          obtain ⟨hi, _, hdraws⟩ := hf
          rw [ActualInitializationPhysicalStep.prepareFollowerValid_bootstrap_arm]
          rw [hr.1]
          change _ = (if hj : (⟨i.val, i.isLt⟩ : Follower p.m) ∈ v.uninformed then
            BootstrapPhysicalBlock.uninformedAction v prepared.time ⟨_, hj⟩
            else BootstrapPhysicalBlock.unoccupiedAction v prepared.time _)
          rw [dite_eq_left hi]
          exact startup_arm_eq source v ⟨refFollower i, hi⟩ state prepared.time rfl rfl (fun _ => rfl) hdraws
      | declared row activation configuration =>
          cases configuration with
          | dagger => exact False.elim hf
          | ordinary state memory =>
              obtain ⟨hrow, hactivation, hstate, _⟩ := hf
              have hnot : (⟨i.val, i.isLt⟩ : Follower p.m) ∉ v.uninformed := by
                intro hmem
                have hn := (ReferenceInitializationRun.mem_uninformed b
                  (⟨i.val, i.isLt⟩ : Follower p.m)).mp hmem
                change b.activation (⟨i.val, i.isLt⟩ : Follower p.m) = some activation at hactivation
                rw [hactivation] at hn
                cases hn
              have hfields := replay_registers rate.eta i v.row activation
                (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn
              have hdomain := replay_domain_valid rate.eta i v.row activation
                (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn
              rw [← hstate] at hfields hdomain
              have hchoice := prepare_unoccupied_zero rate v i activation prepared.time hready state
                memory hdomain hfields.2.2.2.2.2 hfields.2.1 hfields.2.2.1
                hfields.2.2.2.1 hfields.2.2.2.2.1
              rw [ActualInitializationPhysicalStep.prepareFollowerValid_declared_arm]
              rw [hr.1, hrow]
              change _ = (if hj : (⟨i.val, i.isLt⟩ : Follower p.m) ∈ v.uninformed then
                BootstrapPhysicalBlock.uninformedAction v prepared.time ⟨_, hj⟩
                else BootstrapPhysicalBlock.unoccupiedAction v prepared.time _)
              rw [dite_eq_right hnot]
              exact hchoice.2
    rw [prepared.followers_eq i]
    exact helper _ (prepared.readiness.2.2.2.2.2 i) (hr.2.2.2.2 i)
  have hactions : ActualInitializationPhysicalStep.actionProfile prepared =
      BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v prepared.time.val)
        prepared.time := by
    funext i
    unfold ActualInitializationPhysicalStep.actionProfile BootstrapPhysicalBlock.actions
    split_ifs with hi
    · exact hcoord
    · exact hfollowers _
  refine ⟨hactions, ?_⟩
  funext i
  unfold ActualInitializationPhysicalStep.physicalFeedback
    ActualInitializationPhysicalStep.gridFeedback BootstrapPhysicalBlock.observationIndex
  rw [hactions, hr.2.1]
  rfl

/-- The literal successful branch of the accepted preparation operation. -/
def prepareAt (rate : RateInput p) (s : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate s time coordinator
      followers source) : ActualInitializationPhysicalStep.PreparedRound p rate s where
  time := time
  source := source
  rewards := rewards
  coordinatorInput := coordinator
  followerInputs := followers
  readiness := hready
  coordinator := BootstrapCoordinatorLocalRound.prepare p coordinator time
    (by rw [hready.1]; exact hready.2.1)
    (BootstrapPhysicalInput.playerRoundScalarAt p source.2 (ActiveRoundActions.coordinator p.two_le_m) time)
  coordinator_eq := rfl
  followers := fun i => ActualInitializationPhysicalStep.prepareFollowerValid rate s time source i
    (followers i) (hready.2.2.2.2.2 i)
  followers_eq := fun _ => rfl

theorem prepareAt_eq (rate : RateInput p) (s : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate s time coordinator
      followers source) :
    ActualInitializationPhysicalStep.prepare rate s time coordinator followers source rewards =
      .ok (prepareAt rate s time coordinator followers source rewards hready) := by
  simp only [ActualInitializationPhysicalStep.prepare, dite_eq_left hready]
  rfl

/-- The original source sampler gives exactly the reference block's incoming
activity, held arm and private ID at the actual block start. -/
theorem begin_startup_draws (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (i : {i // i ∈ (ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h).uninformed}) :
    startup_draws_related
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h) i
      (BootstrapObservedFollower.beginBlock p (ReferenceInitializationRun.nextBlock b h)
        (b.numerators i.val) (b.weight_ge_one i.val)
        (source.2.1.1 (ReferenceInitializationRun.nextBlock b h) i.val)) := by
  let scalars := source.2.1.1 (ReferenceInitializationRun.nextBlock b h) i.val
  unfold startup_draws_related
  cases ha : PrivateSourceStreams.activityScalarDraw p scalars.1 with
  | false =>
      rw [BootstrapObservedFollower.beginBlock_inactive_case p _ _ _ _ ha]
      exact ha
  | true =>
      rw [BootstrapObservedFollower.beginBlock_active_case p _ _ _ _ ha]
      exact ⟨ha, rfl, rfl⟩

/-- The accepted block start satisfies the actual next-cursor checks. Its
coordinator list/mode reset and cumulative monitor are inherited unchanged
from the accepted operations. -/
theorem begin_ready (rate : RateInput p) (s : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (actual : ActualInitializationRun.BlockCarry p rate s) :
    ActualInitializationPhysicalStep.ActualInputReady p rate s
      (ActualInitializationRun.blockTime p s 0
        (by have := BootstrapObservedFollower.blockStart_lt_blockStop p s
            unfold BootstrapObservedFollower.blockLength; omega))
      (ActualInitializationRun.beginBlock p rate s source actual).coordinator
      (ActualInitializationRun.beginBlock p rate s source actual).followers source := by
  let started := ActualInitializationRun.beginBlock p rate s source actual
  have hi := started.invariant
  refine ⟨hi.1.1, ActualInitializationRun.blockTime_mem p s 0 _, hi.1.2.1,
    hi.1.2.2.1, hi.1.2.2.2.1, ?_⟩
  intro i
  have hcursor := hi.2.2.1 i
  generalize he : started.followers i = f at hcursor ⊢
  cases f with
  | bootstrap state =>
      refine ⟨ActualInitializationRun.blockTime_mem p s 0 _, ?_, ?_⟩
      · change state.processed.val = 0 at hcursor
        rw [hcursor]
        have := BootstrapObservedFollower.blockStart_lt_blockStop p s
        unfold BootstrapObservedFollower.blockLength
        omega
      · change state.processed.val = 0 at hcursor
        change BootstrapObservedFollower.blockStart p s + 0 =
          BootstrapObservedFollower.blockStart p s + state.processed.val
        rw [hcursor]
  | declared row activation configuration => exact hcursor

/-- The physical pre-round relation has a proved base at every related block
boundary. No current-block action or history is supplied to this theorem. -/
theorem begin_round_related
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past) :
    let started := ActualInitializationRun.beginBlock p rate
      (ReferenceInitializationRun.nextBlock b h) source actual
    let time := ActualInitializationRun.blockTime p (ReferenceInitializationRun.nextBlock b h) 0
      (by have := BootstrapObservedFollower.blockStart_lt_blockStop p
            (ReferenceInitializationRun.nextBlock b h)
          unfold BootstrapObservedFollower.blockLength; omega)
    round_related source rewards rate C_star C_h b h past
      (by rw [hr.2.2.2.2.2.2.1.choose]; exact ReferenceInitializationRun.elapsed_le_T p _)
      (prepareAt rate _ time started.coordinator started.followers source rewards
        (begin_ready rate _ source actual)) := by
  obtain ⟨hlength, _, hhistory⟩ := hr.2.2.2.2.2.2.1
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · change (ReferenceInitializationRun.nextBlock b h).val * B_boot p + 0 = past.length
    rw [hlength, ReferenceInitializationRun.elapsed_eq_blockStart b h]
    exact Nat.add_zero _
  · change (BootstrapCoordinatorLocalRound.resetCoordinatorBlockState p actual.coordinator) =
      BootstrapPhysicalBlock.run _ ((ReferenceInitializationRun.nextBlock b h).val * B_boot p + 0)
    rw [Nat.add_zero, BootstrapPhysicalBlock.run_at_block_start]
    cases actual.coordinator
    rfl
  · intro i
    have hf := hr.2.2.2.2.2.2.2 i
    change round_follower_related source rewards rate C_star C_h b h past _ i
      (ActualInitializationRun.beginFollowerBlock p rate _ source i (actual.followers i))
    generalize he : actual.followers i = f at hf ⊢
    cases f with
    | bootstrap numerators lowerBound =>
        obtain ⟨ha, hn⟩ := hf
        have hmem := (ReferenceInitializationRun.mem_uninformed b
          (⟨i.val, i.isLt⟩ : Follower p.m)).mpr ha
        subst numerators
        refine ⟨hmem, BootstrapObservedFollower.beginBlock_numerators p _ _ _ _, ?_⟩
        exact begin_startup_draws source rewards rate C_star C_h b h ⟨_, hmem⟩
    | declared row activation configuration =>
        cases configuration with
        | dagger => exact False.elim hf
        | ordinary state memory =>
            obtain ⟨hrow, ha, hstate, _, _, _, _, _, _, hmarker, _⟩ := hf
            refine ⟨hrow, ha, ?_, hmarker⟩
            have hord : ReferenceInitializationRun.ordinary
                (referenceInput source rewards C_star C_h rate) b (refFollower i) =
                replay rate.eta i (source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source)) activation
                  (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p _) := by
              simp only [ReferenceInitializationRun.ordinary, hr.2.2.1 (refFollower i),
                Bool.false_eq_true, ite_false, ha, atLaunch]
              rfl
            have hh : b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) =
                fun u => recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))
                  (Fin.cast hlength.symm u) := funext (hhistory _)
            rw [hstate, hord, hh]
            exact ReferenceInitializationRun.replay_cast rate.eta i _ activation _ _ _ hlength

/-- The actual DOWN checks are consequences of the explicit lifecycle
domains, including quantization of every retained sparse observation. -/
theorem down_domain_of_local_domain (rate : RateInput p) (state : State p rate.eta)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state) :
    operationInputDomain p rate state := by
  refine ⟨hdomain.1, hdomain.2.2, ?_, hdomain.2.1.2.1⟩
  intro r hr
  obtain ⟨q, hq, hy⟩ := hdomain.2.1.2.2 r hr
  exact ⟨(hdomain.2.1.1 r hr).1, (hdomain.2.1.1 r hr).2,
    ⟨⟨q, Nat.lt_succ_of_le hq⟩, hy⟩⟩

/-- On an active unoccupied receiver, the actual current DOWN input is
literally the reference's input, on the same original follower channel. -/
theorem current_down_input_eq (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : Fin p.T) (own : Fin p.K × Observation p) (state : State p rate.eta)
    (ha : activation.val ≤ time.val + 1) (hu : state.status = .unoccupied) :
    currentRoundInput p i row time own.2 rate state = downInput i row activation time own := by
  unfold currentRoundInput downInput
  simp only [ha, hu, decide_true, true_and]

/-- Equality of actual and reference decoder operations is proved from the
literal current inputs, rather than assumed as matching decoder output. -/
theorem current_decode_eq (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : Fin p.T) (own : Fin p.K × Observation p) (state : State p rate.eta)
    (ha : activation.val ≤ time.val + 1) (hu : state.status = .unoccupied)
    (hselected : downSelected p i row time) :
    currentDecodeStep p i row time own.2 rate state =
      decodeAt i row activation time own state.downBatch := by
  have hs : (downInput i row activation time own).selected = true := by
    exact decide_eq_true ⟨ha, hselected⟩
  unfold currentDecodeStep decodeAt
  rw [ite_eq_left hs]
  have heq : currentInputExtension p (currentRoundInput p i row time own.2 rate state) =
      traceAt i row activation time own := by
    funext t
    exact current_down_input_eq rate i row activation time own state ha hu
  rw [heq]

/-- An unselected reference DOWN call leaves the exact old batch and produces
no parsed word. This does not reset an older partial batch. -/
theorem decodeAt_not_selected (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : Fin p.T) (own : Fin p.K × Observation p)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hselected : ¬ downSelected p i row time) :
    decodeAt i row activation time own batch = (batch, none) := by
  have hs : (downInput i row activation time own).selected = false := by
    apply decide_eq_false (p := activation.val ≤ time.val + 1 ∧
      PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 = i)
    intro h
    exact hselected h.2
  exact ite_eq_right (by rw [hs]; exact Bool.noConfusion)

/-- Every checked actual observation stage agrees with the suppressed
reference update in the absence of the concrete current parsed acceptance.
The inputs are INTERNAL chronological induction data; local check success,
decoder output, memory preservation and absence of dagger are conclusions. -/
theorem observe_unoccupied_eq_step (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time : Fin p.T) (ha : activation.val ≤ time.val + 1)
    (own : Fin p.K × Observation p) (state : State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hu : state.status = .unoccupied) (hs : acceptedStart state = 0)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hbefore : ∀ r ∈ state.buffer, r.calendarRound < time.val + 1)
    (hnotpassing : ¬ passing_at rate.eta i row activation time own state.downBatch) :
    DeclaredFollowerLocalRound.observeOrdinary rate i row activation time ha own.1 own.2
      state memory = .ok (step i row activation time own state, memory) := by
  let logged : State p rate.eta :=
    {state with buffer := state.buffer ++ logAt i row activation time own}
  have hbranch : ActiveFollowerLogging.loggingBranch activation time state := ⟨ha, hu⟩
  have hlogvalid : ActiveFollowerLifecycle.localBufferValid logged := by
    have h := ActiveFollowerLogging.localBufferValid_loggingUpdate_of_chronological i row
      activation time own state hdomain.2.1 hbefore hu
    exact (show ActiveFollowerLogging.loggingUpdate i row activation time own state = logged
      from ite_eq_left hbranch) ▸ h
  have hlog : ActiveFollowerLogging.checkedLogging i row activation time own state =
      .ok logged := by
    have heq : ActiveFollowerLogging.loggingUpdate i row activation time own state = logged :=
      ite_eq_left hbranch
    simp only [ActiveFollowerLogging.checkedLogging, dite_eq_left hdomain.2.1,
      heq, dite_eq_left hlogvalid]
  have hloggedDomain : ActiveFollowerLifecycle.localStateDomainValid logged :=
    ⟨hdomain.1, hlogvalid, hdomain.2.2⟩
  have hdownDomain := down_domain_of_local_domain rate logged hloggedDomain
  have hpostDomain : ActiveFollowerLifecycle.localStateDomainValid
      (step i row activation time own state) := by
    obtain ⟨h1, h2, h3, h4, _⟩ := step_registers i row activation time own state
    obtain ⟨hp, hc, _⟩ := step_batch_spec i row activation time own state hu
      hdomain.2.2.1 hdomain.2.2.2
    refine ⟨?_, ?_, hp, hc⟩
    · exact ⟨h2 ▸ hdomain.1.1, h3 ▸ hdomain.1.2.1, h4 ▸ hdomain.1.2.2⟩
    · simpa only [ActiveFollowerLifecycle.localBufferValid, step, ite_eq_left hu, logged]
        using hlogvalid
  have hpostStatus : (step i row activation time own state).status = .unoccupied :=
    (step_registers i row activation time own state).2.2.2.2.trans hu
  have hdown : DeclaredFollowerLocalRound.consumeDownResult rate
      (downTransition p i row time own.2 rate logged) =
      .ok (step i row activation time own state) := by
    by_cases hselected : downSelected p i row time
    · have hdecode := current_decode_eq rate i row activation time own logged ha hu hselected
      have hparsed : parsedCurrentOutput p i row time own.2 rate logged =
          parsedAt rate.eta i row activation time own state.downBatch := by
        unfold parsedCurrentOutput parsedAt
        rw [hdecode]
      cases hp : parsedAt rate.eta i row activation time own state.downBatch with
      | none =>
          have heq := downTransition_rejected_equation p i row time own.2 rate logged hselected
            hu hdownDomain.1 hdownDomain.2.1 hdownDomain.2.2 (hparsed.trans hp)
          rw [heq]
          simp only [DeclaredFollowerLocalRound.consumeDownResult, hdecode, step,
            ite_eq_left hu, decide_eq_false hnotpassing, Bool.or_false]
          rfl
      | some M =>
          have hnot : ¬ OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
              (acceptedStart logged) (time.val + 1) M := by
            intro haccept
            apply hnotpassing
            have hstart : acceptedStart logged = 0 := hs
            rw [hstart] at haccept
            exact ⟨M, hp, haccept⟩
          have heq := downTransition_unaccepted_equation p i row time own.2 rate logged
            hselected hu hdownDomain.1 hdownDomain.2.1 hdownDomain.2.2 M
            (hparsed.trans hp) hnot
          rw [heq]
          simp only [DeclaredFollowerLocalRound.consumeDownResult, hdecode, step,
            ite_eq_left hu, decide_eq_false hnotpassing, Bool.or_false]
          rfl
    · rw [downTransition_notSelected p i row time own.2 rate logged hselected]
      simp only [DeclaredFollowerLocalRound.consumeDownResult, step, ite_eq_left hu,
        decodeAt_not_selected i row activation time own state.downBatch hselected,
        decide_eq_false hnotpassing, Bool.or_false]
      rfl
  simp only [DeclaredFollowerLocalRound.observeOrdinary,
    DeclaredFollowerLocalRound.recordOrServiceThenDown_unoccupied rate i row activation
      time ha own.1 own.2 state hu, hlog, hdown]
  unfold DeclaredFollowerLocalRound.releaseAndFinish
  rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i time _ own.2 _ _ hu]
  simp only [ActiveFollowerLifecycle.finishRound_unoccupied rate.eta time row _ memory
    hpostDomain hpostStatus]

/-- The two existing typed-observation constructors agree on the generated
physical grid feedback, including collision zero. -/
theorem observationOfGrid_eq_ownObservation {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (i : Fin p.m) (time : Fin p.T) :
    ActualInitializationPhysicalStep.observationOfGrid p
      (BootstrapPhysicalBlock.observationIndex v (BootstrapPhysicalBlock.run v time.val) time i) =
      ReferenceInitializationRun.ownObservation v i time := by
  apply Subtype.ext
  apply Subtype.ext
  exact BootstrapPhysicalBlock.observationIndex_value v _ time i

/-- Preparation retains its input labels on every checked branch. -/
theorem prepare_metadata (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p) (time : Fin p.T)
    (ha : activation.val ≤ time.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    let q := DeclaredFollowerLocalRound.prepare rate i row activation time ha input
    q.follower = i ∧ q.row = row ∧ q.activation = activation ∧ q.time = time := by
  cases input with
  | dagger => exact ⟨rfl, rfl, rfl, rfl⟩
  | ordinary state memory =>
      dsimp only [DeclaredFollowerLocalRound.prepare]
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A complete local declared-follower round on this generated reference
block. The old buffer/batch and arbitrary old proposal memory are retained.
The sole excluded branch is a literal parsed DOWN acceptance on the generated
own entry, with accepted start zero. -/
theorem declared_round_correspondence {s : Fin (n_boot p)} (rate : RateInput p)
    (v : BootstrapPhysicalBlock.Input p s) (i : Fin (p.m - 1))
    (hinformed : refFollower i ∉ v.uninformed)
    (activation : Activation p) (time : Fin p.T) (ha : activation.val ≤ time.val + 1)
    {n : ℕ} (history : LocalHistory p n) (hn : n ≤ p.T) (hbefore : n ≤ time.val)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hnotpassing : ¬ passing_at rate.eta i v.row activation time
      (ReferenceInitializationRun.ownEntry v
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time)
      (replay rate.eta i v.row activation history hn).downBatch) :
    let state := replay rate.eta i v.row activation history hn
    let prepared := DeclaredFollowerLocalRound.prepare rate i v.row activation time ha
      (.ordinary state memory)
    prepared.arm = BootstrapPhysicalBlock.unoccupiedAction v time (refFollower i) ∧
    (DeclaredFollowerLocalRound.observe prepared
      (ReferenceInitializationRun.ownObservation v
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time)).configuration =
      .ordinary (step i v.row activation time
        (prepared.arm, ReferenceInitializationRun.ownObservation v
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state) memory := by
  let state := replay rate.eta i v.row activation history hn
  have hfields := replay_registers rate.eta i v.row activation history hn
  have hdomain := replay_domain_valid rate.eta i v.row activation history hn
  have hchoice := prepare_unoccupied_zero rate v i activation time ha state memory hdomain
    hfields.2.2.2.2.2 hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2.1
  let prepared := DeclaredFollowerLocalRound.prepare rate i v.row activation time ha
    (.ordinary state memory)
  have hstatus : state.status = .unoccupied := hfields.2.2.2.2.2
  have htimestamp : ∀ r ∈ state.buffer, r.calendarRound < time.val + 1 := by
    intro r hr
    obtain ⟨u, _, ht, _⟩ := replay_buffer_fields rate.eta i v.row activation history hn r hr
    rw [ht]
    omega
  have harm : BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v time.val)
      time (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) = prepared.arm := by
    rw [BootstrapPhysicalBlock.actions_follower]
    unfold BootstrapPhysicalBlock.followerAction
    rw [dite_eq_right hinformed]
    exact hchoice.2.symm
  have hnot : ¬ passing_at rate.eta i v.row activation time
      (prepared.arm, ReferenceInitializationRun.ownObservation v
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state.downBatch := by
    simpa only [ReferenceInitializationRun.ownEntry, harm] using hnotpassing
  have hobs := observe_unoccupied_eq_step rate i v.row activation time ha
    (prepared.arm, ReferenceInitializationRun.ownObservation v
      (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state memory
    hstatus hfields.2.1 hdomain htimestamp hnot
  refine ⟨hchoice.2, ?_⟩
  have hconfiguration : prepared.configuration = .ordinary state memory := hchoice.1
  have hmetadata := prepare_metadata rate i v.row activation time ha (.ordinary state memory)
  change prepared.follower = i ∧ prepared.row = v.row ∧ prepared.activation = activation ∧
    prepared.time = time at hmetadata
  change (DeclaredFollowerLocalRound.observe prepared _).configuration = _
  simp only [DeclaredFollowerLocalRound.observe, hconfiguration]
  simp only [hmetadata.1, hmetadata.2.1, hmetadata.2.2.1, hmetadata.2.2.2]
  rw [hobs]

/-- Appending a real physical record preserves every older own entry. -/
theorem recordHistory_append_prefix {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin p.m) (u : Fin past.length) :
    recordHistory (past ++ [record]) i
      ⟨u.val, by simp only [List.length_append, List.length_singleton]; omega⟩ =
      recordHistory past i u := by
  unfold recordHistory
  rw [List.getElem_append_left u.isLt]

/-- The last own entry is exactly the appended physical action and grid
observation; no prior buffer, batch or memory is reset by this extension. -/
theorem recordHistory_append_last {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) (i : Fin p.m) :
    recordHistory (past ++ [record]) i
      ⟨past.length, by simp only [List.length_append, List.length_singleton]; omega⟩ =
      recordEntry record i := by
  unfold recordHistory
  rw [List.getElem_append_right (Nat.le_refl past.length)]
  simp only [Nat.sub_self, List.getElem_cons_zero]

/-- One genuine accepted actual physical record. Both its preparation and its
observation continuations are the existing operations; `executed` proves the
accepted `step` equation. This is a one-round producer, not horizon recursion. -/
def executeAt (rate : RateInput p) (s : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate s time coordinator
      followers source) : ActualInitializationRun.PhysicalRoundRecord p rate source rewards := by
  let prepared := prepareAt rate s time coordinator followers source rewards hready
  let outcomes := ActualInitializationPhysicalStep.observeFollowers prepared
  let result : ActualInitializationPhysicalStep.RoundResult p rate s :=
    ⟨prepared, outcomes.val, outcomes.property⟩
  refine ⟨s, time, coordinator, followers, result, ?_, rfl⟩
  unfold ActualInitializationPhysicalStep.step
  rw [prepareAt_eq rate s time coordinator followers source rewards hready]
  rfl

/-- The produced physical record and each of its own entries agree with the
reference, as a consequence of the pre-round invariant. -/
theorem executeAt_correspondence
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate
      (ReferenceInitializationRun.nextBlock b h) time coordinator followers source)
    (hr : round_related source rewards rate C_star C_h b h past hn
      (prepareAt rate _ time coordinator followers source rewards hready)) :
    let v := ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h
    let record := executeAt rate _ time coordinator followers source rewards hready
    record.result.actions = BootstrapPhysicalBlock.actions v
      (BootstrapPhysicalBlock.run v time.val) time ∧
    record.result.feedback = (fun i => BootstrapPhysicalBlock.observationIndex v
      (BootstrapPhysicalBlock.run v time.val) time i) ∧
    ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry v i time := by
  have hc := physical_round_correspondence source rewards rate C_star C_h b h past hn
    (prepareAt rate _ time coordinator followers source rewards hready) hr
  refine ⟨hc.1, hc.2, ?_⟩
  intro i
  apply Prod.ext
  · exact congrFun hc.1 i
  · change ActualInitializationPhysicalStep.observationOfGrid p
        (ActualInitializationPhysicalStep.physicalFeedback
          (prepareAt rate _ time coordinator followers source rewards hready) i) = _
    rw [congrFun hc.2 i]
    exact observationOfGrid_eq_ownObservation _ i time

/-- Real record extension: every prior own entry is preserved and the last
entry is the generated reference action/observation. Current entry equality
is proved from the invariant and the actual simultaneous operations. -/
theorem executeAt_history_extension
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate
      (ReferenceInitializationRun.nextBlock b h) time coordinator followers source)
    (hr : round_related source rewards rate C_star C_h b h past hn
      (prepareAt rate _ time coordinator followers source rewards hready)) :
    let record := executeAt rate _ time coordinator followers source rewards hready
    let v := ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h
    (∀ (i : Fin p.m) (u : Fin past.length),
      recordHistory (past ++ [record]) i
        ⟨u.val, by simp only [List.length_append, List.length_singleton]; omega⟩ =
        recordHistory past i u) ∧
    ∀ i, recordHistory (past ++ [record]) i
      ⟨past.length, by simp only [List.length_append, List.length_singleton]; omega⟩ =
      ReferenceInitializationRun.ownEntry v i time := by
  refine ⟨fun i u => recordHistory_append_prefix past _ i u, ?_⟩
  intro i
  rw [recordHistory_append_last]
  exact (executeAt_correspondence source rewards rate C_star C_h b h past hn time coordinator
    followers hready hr).2.2 i

/-- The first accepted actual record of a related block, obtained without
assuming any current-block equality. -/
theorem begin_record_correspondence
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past) :
    let started := ActualInitializationRun.beginBlock p rate
      (ReferenceInitializationRun.nextBlock b h) source actual
    let time := ActualInitializationRun.blockTime p (ReferenceInitializationRun.nextBlock b h) 0
      (by have := BootstrapObservedFollower.blockStart_lt_blockStop p
            (ReferenceInitializationRun.nextBlock b h)
          unfold BootstrapObservedFollower.blockLength; omega)
    let record := executeAt rate _ time started.coordinator started.followers source rewards
      (begin_ready rate _ source actual)
    ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      i time := by
  exact (executeAt_correspondence source rewards rate C_star C_h b h past _ _ _ _ _
    (begin_round_related source rewards rate C_star C_h b h actual past hr)).2.2

/-- Reindexing the same already supplied local entries changes no operation
of the accepted ordinary fold. Used below only with the actual record prefix
embedding, whose entry equality is proved by list indexing. -/
theorem run_map_history {n m : ℕ} (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (small : LocalHistory p n) (large : LocalHistory p m) (hn : n ≤ p.T) (hm : m ≤ p.T)
    (embed : Fin n → Fin m) (htime : ∀ u, (embed u).val = u.val)
    (hentry : ∀ u, large (embed u) = small u) (us : List (Fin n)) (state : State p eta) :
    run i row activation large hm (us.map embed) state =
      run i row activation small hn us state := by
  induction us generalizing state with
  | nil => rfl
  | cons u us ih =>
      have hc : calendar hm (embed u) = calendar hn u := Fin.ext (htime u)
      simp only [List.map_cons, run]
      rw [hc, hentry, ih]

/-- Splitting off the last real round preserves the exact earlier log and
partial decoder bank. No boundary reset is introduced by ordinary replay. -/
theorem replay_succ {n : ℕ} (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (history : LocalHistory p (n + 1)) (hn : n + 1 ≤ p.T) :
    replay eta i row activation history hn =
      step i row activation ⟨n, by omega⟩ (history (Fin.last n))
        (replay eta i row activation (fun u => history u.castSucc) (by omega)) := by
  unfold replay
  rw [List.ofFn_succ_last, run_append]
  have heq : (List.ofFn (fun u : Fin n => u.castSucc)) =
      (List.ofFn (fun u : Fin n => u)).map Fin.castSucc := by
    rw [List.map_ofFn]
    rfl
  rw [heq]
  have hrun := run_map_history eta i row activation (fun u => history u.castSucc)
    history (by omega) hn Fin.castSucc (fun _ => rfl) (fun _ => rfl)
    (List.ofFn (fun u : Fin n => u)) (initial p eta)
  rw [hrun]
  rfl

/-- Replay of the actual extended record accumulator is exactly the old
replay followed by the new physical own entry. The appended record's calendar
time is the only chronological input. -/
theorem replay_recordHistory_append (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (hn : past.length ≤ p.T) (hm : (past ++ [record]).length ≤ p.T)
    (htime : record.time.val = past.length) :
    replay rate.eta i row activation
      (recordHistory (past ++ [record])
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hm =
      step i row activation record.time
        (recordEntry record (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (replay rate.eta i row activation
          (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn) := by
  have hlength : (past ++ [record]).length = past.length + 1 := by
    simp only [List.length_append, List.length_singleton]
  let extended : LocalHistory p (past.length + 1) := fun u =>
    recordHistory (past ++ [record])
      (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) (Fin.cast hlength.symm u)
  have hbound : past.length + 1 ≤ p.T := hlength ▸ hm
  have hcast := ReferenceInitializationRun.replay_cast rate.eta i row activation
    (recordHistory (past ++ [record])
      (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hm hbound hlength
  rw [← hcast, replay_succ]
  have hp : (fun u : Fin past.length => extended u.castSucc) =
      recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) := by
    funext u
    exact recordHistory_append_prefix past record _ u
  have hl : extended (Fin.last past.length) =
      recordEntry record (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) :=
    recordHistory_append_last past record _
  change step i row activation _ (extended (Fin.last past.length))
    (replay rate.eta i row activation (fun u => extended u.castSucc) _) = _
  rw [hp, hl]
  congr 1
  exact Fin.ext htime.symm

/-- Complete declared-follower continuation in a produced actual physical
record. The next state is replay of the extended actual own history and the
old memory is unchanged. The sole excluded local event is the actual ordinary
parsed DOWN test on this generated reference entry. -/
theorem executeAt_declared_continuation
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate
      (ReferenceInitializationRun.nextBlock b h) time coordinator followers source)
    (hr : round_related source rewards rate C_star C_h b h past hn
      (prepareAt rate _ time coordinator followers source rewards hready))
    (i : Fin (p.m - 1)) (row : Fin (M p)) (activation : Activation p)
    (state : State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : followers i = .declared row activation (.ordinary state memory))
    (hnotpassing : ¬ passing_at rate.eta i
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) activation time
      (ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state.downBatch) :
    let record := executeAt rate _ time coordinator followers source rewards hready
    (record.result.followers i).next =
      .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
        (.ordinary (replay rate.eta i
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) activation
          (recordHistory (past ++ [record])
            (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
          (by simp only [List.length_append, List.length_singleton]
              have ht : time.val = past.length := hr.2.2.1
              have _hT := time.isLt
              omega)) memory) := by
  let v := ReferenceInitializationRun.physical
    (referenceInput source rewards C_star C_h rate) b h
  let record := executeAt rate _ time coordinator followers source rewards hready
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)
  have hrel : round_follower_related source rewards rate C_star C_h b h past hn i
      (followers i) := hr.2.2.2.2 i
  rw [hf] at hrel
  obtain ⟨hrow, hactivation, hstate, _⟩ := hrel
  have ha : activation.val ≤ time.val + 1 := by
    have hc := hready.2.2.2.2.2 i
    simpa only [hf, ActualInitializationPhysicalStep.followerAtNextCursor] using hc
  have hinformed : refFollower i ∉ v.uninformed := by
    intro hmem
    have hnone := (ReferenceInitializationRun.mem_uninformed b (refFollower i)).mp hmem
    rw [hactivation] at hnone
    cases hnone
  have hc := executeAt_correspondence source rewards rate C_star C_h b h past hn time
    coordinator followers hready hr
  change state = replay rate.eta i v.row activation (recordHistory past player) hn at hstate
  have hnot : ¬ passing_at rate.eta i v.row activation time
      (ReferenceInitializationRun.ownEntry v player time)
      (replay rate.eta i v.row activation (recordHistory past player) hn).downBatch := by
    rw [← hstate]
    exact hnotpassing
  have hlocal := declared_round_correspondence rate v i hinformed activation time ha
    (recordHistory past player) hn (Nat.le_of_eq hr.2.2.1.symm) memory hnot
  rw [← hstate] at hlocal
  let q := DeclaredFollowerLocalRound.prepare rate i v.row activation time ha
    (.ordinary state memory)
  have hentry : recordEntry record player =
      (q.arm, ReferenceInitializationRun.ownObservation v player time) := by
    rw [hc.2.2 player]
    apply Prod.ext
    · change BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v time.val) time player = _
      rw [BootstrapPhysicalBlock.actions_follower]
      unfold BootstrapPhysicalBlock.followerAction
      rw [dite_eq_right hinformed]
      exact hlocal.1.symm
    · rfl
  have hq : (DeclaredFollowerLocalRound.observe q
      (ReferenceInitializationRun.ownObservation v player time)).configuration =
      .ordinary (replay rate.eta i v.row activation
        (recordHistory (past ++ [record]) player) (by
          simp only [List.length_append, List.length_singleton]
          have ht := hr.2.2.1
          have _hT := time.isLt
          omega)) memory := by
    rw [replay_recordHistory_append rate source rewards past record i v.row activation hn _
      (show record.time.val = past.length from hr.2.2.1), hentry]
    rw [← hstate]
    exact hlocal.2
  have hfeedback : ActualInitializationPhysicalStep.observationOfGrid p
      (record.result.feedback player) = ReferenceInitializationRun.ownObservation v player time := by
    rw [congrFun hc.2.1 player]
    exact observationOfGrid_eq_ownObservation v player time
  have htransition := record.result.followerTransition i
  change ActualInitializationPhysicalStep.observeFollower rate _ time source i
    (ActualInitializationPhysicalStep.prepareFollowerValid rate _ time source i (followers i)
      (hready.2.2.2.2.2 i)) (record.result.feedback player) = .ok (record.result.followers i)
    at htransition
  have hprepare := ActualInitializationRun.prepareFollowerValid_congr time source i
    (followers i) (.declared row activation (.ordinary state memory)) hf
    (hready.2.2.2.2.2 i) ha
  rw [hprepare, hrow] at htransition
  change Except.ok (ε := ActualInitializationPhysicalStep.InputFailure p
      (ReferenceInitializationRun.nextBlock b h))
    ⟨.declared _ activation q, .declared _ activation
      (DeclaredFollowerLocalRound.observe q
        (ActualInitializationPhysicalStep.observationOfGrid p (record.result.feedback player))).configuration⟩ =
      .ok (record.result.followers i) at htransition
  rw [hfeedback, hq] at htransition
  exact congrArg ActualInitializationPhysicalStep.FollowerOutcome.next (Except.ok.inj htransition).symm

/-- Extending the actual physical accumulator by its next calendar record
preserves strict chronological indexing, including its new final position. -/
theorem chronological_append {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hpast : ∀ u : Fin past.length, past[u.val].time.val = u.val)
    (htime : record.time.val = past.length) :
    ∀ u : Fin (past ++ [record]).length, (past ++ [record])[u.val].time.val = u.val := by
  intro u
  by_cases hu : u.val < past.length
  · rw [List.getElem_append_left hu]
    exact hpast ⟨u.val, hu⟩
  · have heq : u.val = past.length := by
      have hb := u.isLt
      simp only [List.length_append, List.length_singleton] at hb
      omega
    rw [List.getElem_append_right (Nat.le_of_not_gt hu)]
    simpa only [heq, Nat.sub_self, List.getElem_cons_zero] using htime

/-- The actual coordinator observation on generated feedback equals the
existing reference physical step, including the list, mode and audit log. -/
theorem coordinator_observation_eq_step {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (time : Fin p.T)
    (htime : time ∈ calendarBlock p s) :
    BootstrapCoordinatorLocalRound.observationUpdate p v.row v.ids
      (BootstrapPhysicalBlock.run v time.val) time
      (BootstrapPhysicalBlock.observationIndex v (BootstrapPhysicalBlock.run v time.val)
        time (coordinator p.two_le_m)) =
      BootstrapPhysicalBlock.step v (BootstrapPhysicalBlock.run v time.val) time := by
  unfold BootstrapCoordinatorLocalRound.observationUpdate BootstrapPhysicalBlock.step
    BootstrapPhysicalBlock.discoveryPositive
  simp only [htime, true_and]
  simp only [← BootstrapPhysicalBlock.observationIndex_pos_iff,
    BootstrapCoordinatorLocalRound.coordinatorSlot, BootstrapPhysicalBlock.slot]
  rfl

/-- The actual produced coordinator continuation, in either prelaunch or
launched phase, retains exactly the next reference physical state. -/
theorem executeAt_coordinator_extension
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (time : Fin p.T)
    (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate
      (ReferenceInitializationRun.nextBlock b h) time coord followers source)
    (hr : round_related source rewards rate C_star C_h b h past hn
      (prepareAt rate _ time coord followers source rewards hready)) :
    let record := executeAt rate _ time coord followers source rewards hready
    BootstrapCoordinatorLocalRound.Continuation.coordinatorState record.result.coordinator.next =
      BootstrapPhysicalBlock.run
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        (time.val + 1) := by
  let record := executeAt rate _ time coord followers source rewards hready
  have hc := executeAt_correspondence source rewards rate C_star C_h b h past hn time
    coord followers hready hr
  have hstate : coord.data.coordinator = BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      time.val := hr.2.2.2.1
  change BootstrapCoordinatorLocalRound.Continuation.coordinatorState
    record.result.coordinator.next = _
  rw [ActualInitializationRun.roundResult_next_eq,
    BootstrapCoordinatorLocalRound.continuationAfterObservation_coordinator_eq]
  change BootstrapCoordinatorLocalRound.observationUpdate p coord.data.row coord.data.ids
    coord.data.coordinator time (record.result.feedback (coordinator p.two_le_m)) = _
  rw [hready.2.2.1, hready.2.2.2.1, hstate, congrFun hc.2.1 (coordinator p.two_le_m)]
  rw [BootstrapPhysicalBlock.run_succ]
  exact coordinator_observation_eq_step _ time hready.2.1

/-- The produced actual bootstrap continuation cannot reject a ready cursor.
It advances once, retains its old numerator vector until the boundary, counts
the current stay gain even after a pending save, and performs the literal
all-candidate update on that same own observation. -/
theorem executeAt_bootstrap_continuation (rate : RateInput p) (s : Fin (n_boot p))
    (time : Fin p.T) (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hready : ActualInitializationPhysicalStep.ActualInputReady p rate s time coord followers source)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p s)
    (hf : followers i = .bootstrap state) :
    let record := executeAt rate s time coord followers source rewards hready
    let own := ActualInitializationPhysicalStep.observationOfGrid p
      (record.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
    ∃ next : BootstrapObservedFollower.StartupState p s,
      (record.result.followers i).next = .bootstrap next ∧
      next.processed.val = state.processed.val + 1 ∧
      next.numerators = state.numerators ∧
      next.blockCase = (match state.blockCase with
        | .inactive => .inactive
        | .active held privateID gain registers =>
            .active held privateID
              (if BootstrapObservedFollower.positiveStay source.1.1 privateID time own
                then gain + 1 else gain)
              (BootstrapObservedFollower.observationAdvance p s source.1.1 source.1.2 true
                privateID registers time own)) := by
  let record := executeAt rate s time coord followers source rewards hready
  let own := ActualInitializationPhysicalStep.observationOfGrid p
    (record.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
  have hcursor : ActualInitializationPhysicalStep.followerAtNextCursor (rate := rate) time
      (.bootstrap state) := by
    have hc := hready.2.2.2.2.2 i
    simpa only [hf] using hc
  let next := BootstrapObservedFollower.observeOne p s state source.1.1 source.1.2 time own
    hcursor.1 hcursor.2.1 hcursor.2.2
  have hprepare := ActualInitializationRun.prepareFollowerValid_congr time source i
    (followers i) (.bootstrap state) hf (hready.2.2.2.2.2 i) hcursor
  have htransition := record.result.followerTransition i
  change ActualInitializationPhysicalStep.observeFollower rate s time source i
    (ActualInitializationPhysicalStep.prepareFollowerValid rate s time source i (followers i)
      (hready.2.2.2.2.2 i))
    (record.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) =
      .ok (record.result.followers i) at htransition
  rw [hprepare] at htransition
  have hobs := BootstrapObservedFollower.observe_accepted_processed p s state source.1.1
    source.1.2 time own hcursor.1 hcursor.2.1 hcursor.2.2
  dsimp only [own] at hobs
  simp only [ActualInitializationPhysicalStep.prepareFollowerValid,
    ActualInitializationPhysicalStep.observeFollower, hobs] at htransition
  have hnext : (record.result.followers i).next = .bootstrap next :=
    congrArg ActualInitializationPhysicalStep.FollowerOutcome.next (Except.ok.inj htransition).symm
  exact ⟨next, hnext, rfl, rfl, rfl⟩

end Bandits.Support.ActualReferenceInitializationBlock

end
