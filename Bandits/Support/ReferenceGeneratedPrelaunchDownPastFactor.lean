/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownDerivedPast

/-!
# Original-source prelaunch DOWN prefix codes and completion factors

Internal deterministic support for `appendix_a_local_protocol.tex:111-138`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42`. Prefix codes retain the three actual
branches, all registers and every original saved real coordinate. Completion
is a measurable proof device with arbitrary omitted coordinates.

No probability bound, historical birth characterization or manuscript closure
is asserted here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownPastFactor

open MeasureTheory ConstructorDimensions BootstrapDimensions
open ReferenceInitializationMeasurability
open scoped Classical

-- Match the admitted initialization code spaces for countable lists/options.
-- This does not apply to lists of continuous records or to saved scalar fibres.
attribute [local instance 3000] ReferenceInitializationMeasurability.listCountableMeasurableSpace
  ReferenceInitializationMeasurability.listCountableMeasurableSingletonClass
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace
  ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass

local instance sumMeasurableSingletonClass (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inl_image (β := β)
    | inr x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inr_image (α := α)

variable {p : Parameters}

/-- Actual played arm and exact quantization index, with no padded entries. -/
abbrev HistoryCode (p : Parameters) (n : ℕ) := Fin n → Fin p.K × Fin (D p + 1)

def historyCode {n : ℕ} (history : ReferencePrelaunchFollower.LocalHistory p n) : HistoryCode p n :=
  fun u => ((history u).1, ReferenceInitializationMeasurability.observationGridIndex p (history u).2)

def decodeHistoryCode {n : ℕ} (code : HistoryCode p n) : ReferencePrelaunchFollower.LocalHistory p n :=
  fun u => ((code u).1, FollowerDownMeasurability.feedbackAtGrid p (code u).2)

theorem decode_historyCode {n : ℕ} (history : ReferencePrelaunchFollower.LocalHistory p n) :
    decodeHistoryCode (historyCode history) = history := by
  funext u
  change ((history u).1, FollowerDownMeasurability.feedbackAtGrid p
    (ReferenceInitializationMeasurability.observationGridIndex p (history u).2)) = history u
  refine Prod.ext rfl ?_
  apply Subtype.ext
  apply Subtype.ext
  exact (ReferenceInitializationMeasurability.observationGridIndex_value p (history u).2).symm

/-- The same three sums as the actual proof-erased prefix observation. -/
abbrev PrefixCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p)
    (n : ℕ) :=
  ((ReferenceInitializationRun.Boundary p × ReferencePrelaunchFollower.Activation p × HistoryCode p n × FollowerObservationStageMeasurabilityRepair.CarriedState p rate) ⊕
    (ReferenceInitializationRun.Boundary p × HistoryCode p n)) ⊕ (ReferenceInitializationRun.Boundary p × FollowerObservationStageMeasurabilityRepair.CarriedState p rate)

def encodePrefix (rate : ReferenceActivePhysicalStep.RateInput p) {i : Fin (p.m - 1)}
    {n : ℕ} : ReferenceGeneratedPrelaunchDownPrefix.PrefixObservation p rate.eta i n → PrefixCode p rate n
  | .inl (.inl v) => .inl (.inl (v.1, v.2.1, historyCode v.2.2.1,
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate v.2.2.2))
  | .inl (.inr v) => .inl (.inr (v.1, historyCode v.2))
  | .inr v => .inr (v.1, FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate v.2)

def decodePrefixCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin (p.m - 1)) {n : ℕ} : PrefixCode p rate n → ReferenceGeneratedPrelaunchDownPrefix.PrefixObservation p rate.eta i n
  | .inl (.inl v) => .inl (.inl (v.1, v.2.1, decodeHistoryCode v.2.2.1,
      FollowerDownMeasurability.followerStateOfCode rate v.2.2.2.1.1 (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer v.2.2.2)))
  | .inl (.inr v) => .inl (.inr (v.1, decodeHistoryCode v.2))
  | .inr v => .inr (v.1,
      FollowerDownMeasurability.followerStateOfCode rate v.2.1.1 (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer v.2))

theorem decode_encodePrefix (rate : ReferenceActivePhysicalStep.RateInput p)
    {i : Fin (p.m - 1)} {n : ℕ} (v : ReferenceGeneratedPrelaunchDownPrefix.PrefixObservation p rate.eta i n) :
    decodePrefixCode rate i (encodePrefix rate v) = v := by
  rcases v with (v | v) | v
  · simp only [encodePrefix, decodePrefixCode, decode_historyCode,
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct]
  · simp only [encodePrefix, decodePrefixCode, decode_historyCode]
  · simp only [encodePrefix, decodePrefixCode, FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct]

def sourcePrefixCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    PrefixCode p rate r.val :=
  encodePrefix rate (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation rate rewards C_star C_h z i r)

theorem decode_sourcePrefixCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    decodePrefixCode rate i (sourcePrefixCode rate rewards C_star C_h z i r) =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation rate rewards C_star C_h z i r :=
  decode_encodePrefix rate _

private theorem measurable_cases {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hk : Measurable key)
    (branch : β → α → γ) (hb : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hb).comp (hk.prodMk measurable_id)

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem buffer_codes_ofFn {n : ℕ} (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧ HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton values).length = n := List.length_ofFn
  constructor
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].calendarRound,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].pilot) = _
    simp only [List.getElem_ofFn]
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].observation,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].thinScalar) = _
    simp only [List.getElem_ofFn]

private theorem carriedState_eq_of_buffer {rate : ReferenceActivePhysicalStep.RateInput p}
    (s : ReferencePrelaunchFollower.State p rate.eta) {n : ℕ} (sk : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (vs : FollowerDownMeasurability.SavedScalarFamily n) (hbuf : s.buffer = FollowerDownJointMeasurability.bufferFromSkeletonAndScalars sk vs) :
    FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate s = ⟨(FollowerDownMeasurability.followerStateCode rate s, ⟨n, sk⟩), vs⟩ := by
  have hc := buffer_codes_ofFn sk vs
  have hl : s.buffer.length = n := by rw [hbuf]; exact List.length_ofFn
  have hs : HEq (FollowerDownJointMeasurability.bufferSkeletonCode s.buffer) sk := by rw [hbuf]; exact hc.1
  have hv : HEq (FollowerDownJointMeasurability.bufferScalarsCode s.buffer) vs := by rw [hbuf]; exact hc.2
  apply Sigma.ext
  · exact congrArg (Prod.mk (FollowerDownMeasurability.followerStateCode rate s)) (Sigma.ext hl hs)
  · exact hv

/-- A fixed finite history is only a local lemma input. The generated-source
theorem below constructs and partitions its own history. No joint replay
measurability is assumed. -/
theorem measurable_replay_carriedState (rate : ReferenceActivePhysicalStep.RateInput p)
    {n : ℕ} (i : Fin (p.m - 1)) (a : ReferencePrelaunchFollower.Activation p) (H : ReferencePrelaunchFollower.LocalHistory p n)
    (hn : n ≤ p.T) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferencePrelaunchFollower.replay rate.eta i row a H hn)) := by
  let state := fun row => ReferencePrelaunchFollower.replay rate.eta i row a H hn
  let mask := fun row u => decide (SparseCalendarReplay.loggingTestsPass
    (ReferencePrelaunchFollower.loggingRound i row a (ReferencePrelaunchFollower.calendar hn u) (H u)))
  have hmask : Measurable (mask : CompletePublicTable.CompleteRow p → Fin n → Bool) := by
    apply measurable_pi_iff.mpr
    intro u
    let present : ReferenceInitializationMeasurability.LoggingCode p → Bool := fun x => x.isRight
    have hpres : Measurable present := by
      exact measurable_fun_sum measurable_const measurable_const
    convert hpres.comp (ReferenceInitializationMeasurability.measurable_loggingEntryCode i a (ReferencePrelaunchFollower.calendar hn u) (H u)) using 1
    funext row
    simp only [Function.comp_apply, present, mask, ReferenceInitializationMeasurability.loggingEntryCode]
    split_ifs with h <;> simp only [h, decide_true, decide_false, Sum.isRight_inl, Sum.isRight_inr]
  have hbank := ReferenceInitializationMeasurability.measurable_replay_downBatchCode p rate.eta i a H hn
  have hfailure := ReferenceInitializationMeasurability.measurable_replay_down_projection p rate.eta i a H hn
  let code := fun row => FollowerDownMeasurability.followerStateCode rate (state row)
  have hcode : Measurable code := by
    let make : FollowerDownMeasurability.DecoderBatchCode p × Bool → FollowerDownMeasurability.FollowerStateCode p rate :=
      fun v => ⟨none, 0, 0, 0, 0, v.1, v.2⟩
    have hmake : Measurable make := .of_discrete
    have hm := hmake.comp (hbank.prodMk hfailure)
    convert hm using 1
    funext row
    obtain ⟨h1, _, h2, h3, h4, h5⟩ := ReferencePrelaunchFollower.replay_registers rate.eta i row a H hn
    simp only [code, state, FollowerDownMeasurability.followerStateCode, make, h1, h2, h3, h4, h5,
      FollowerDownMeasurability.followerStatusCode]
    rfl
  let indices := fun m : Fin n → Bool => (List.ofFn (fun u : Fin n => u)).filter m
  let skeleton := fun m : Fin n → Bool => fun j : Fin (indices m).length =>
    ((ReferencePrelaunchFollower.calendar hn ((indices m)[j])).val + 1, (H ((indices m)[j])).1)
  let values := fun (m : Fin n → Bool) (row : CompletePublicTable.CompleteRow p)
      (j : Fin (indices m).length) =>
    ((H ((indices m)[j])).2.val,
      (row.2 (ReferencePrelaunchFollower.calendar hn ((indices m)[j]))).1 ContinuousControlSlice.Label.thin)
  let branch := fun (key : FollowerDownMeasurability.FollowerStateCode p rate × (Fin n → Bool))
      (row : CompletePublicTable.CompleteRow p) =>
    (⟨(key.1, ⟨(indices key.2).length, skeleton key.2⟩), values key.2 row⟩ : FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
  have hb : ∀ key, Measurable (branch key) := by
    intro key
    change Measurable ((@Sigma.mk
      (FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
      (fun index => FollowerDownMeasurability.SavedScalarFamily index.2.1)
      ((key.1, ⟨(indices key.2).length, skeleton key.2⟩) :
        FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)) ∘ values key.2)
    apply (measurable_sigmaMk _).comp
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_const.prodMk ((measurable_pi_apply ContinuousControlSlice.Label.thin).comp
      (measurable_fst.comp ((measurable_pi_apply
        (ReferencePrelaunchFollower.calendar hn ((indices key.2)[j]))).comp measurable_snd)))
  have hm := measurable_cases (fun row => (code row, mask row))
    (hcode.prodMk hmask) branch hb
  convert hm using 1
  funext row
  apply carriedState_eq_of_buffer
  rw [ReferencePrelaunchFollower.replay_buffer]
  change (List.ofFn (fun u : Fin n => u)).flatMap
    (fun u => ReferencePrelaunchFollower.logAt i row a (ReferencePrelaunchFollower.calendar hn u) (H u)) =
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars (skeleton (mask row)) (values (mask row) row)
  have hlist (us : List (Fin n)) :
      us.flatMap (fun u => ReferencePrelaunchFollower.logAt i row a (ReferencePrelaunchFollower.calendar hn u) (H u)) =
        (us.filter (mask row)).map (fun u =>
          (⟨(ReferencePrelaunchFollower.calendar hn u).val + 1, (H u).1, (H u).2.val,
            (row.2 (ReferencePrelaunchFollower.calendar hn u)).1 ContinuousControlSlice.Label.thin⟩ :
              SparseCalendarReplay.SparseCalendarRecord p.K)) := by
    induction us with
    | nil => rfl
    | cons u us ih =>
      rw [List.flatMap_cons, List.filter_cons]
      by_cases h : SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row a (ReferencePrelaunchFollower.calendar hn u) (H u))
      · have hm : mask row u = true := by simp only [mask, h, decide_true]
        rw [hm, ite_eq_left rfl, List.map_cons, ih]
        simp only [ReferencePrelaunchFollower.logAt, h, ↓reduceIte, List.singleton_append]
        rfl
      · have hm : mask row u = false := by simp only [mask, h, decide_false]
        rw [hm, ite_eq_right Bool.false_ne_true, ih]
        simp only [ReferencePrelaunchFollower.logAt, h, ↓reduceIte, List.nil_append]
  rw [hlist]
  simp only [FollowerDownJointMeasurability.bufferFromSkeletonAndScalars, skeleton, values, indices]
  exact (List.ofFn_getElem_eq_map _ _).symm

private theorem measurable_fibres {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hk : Measurable key) (f : α → γ)
    (hf : ∀ b, Measurable (fun x : {x // key x = b} => f x.val)) : Measurable f := by
  intro S hS
  have he : f ⁻¹' S = ⋃ b : β,
      Subtype.val '' ((fun x : {x // key x = b} => f x.val) ⁻¹' S) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨key x, ⟨x, rfl⟩, hx, rfl⟩
    · intro hx
      obtain ⟨b, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      subst x
      exact hy
  rw [he]
  exact MeasurableSet.iUnion fun b =>
    (measurableSet_eq_fun hk measurable_const).subtype_image (hf b hS)

/-- Fixed-boundary history coordinates: actual boundary history below elapsed,
then the physical played arm and grid feedback at each remaining offset. -/
def fixedHistoryCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    HistoryCode p r.val := fun u =>
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m
    (ActualReferenceInitializationBlock.refFollower i)
  if h : u.val < ReferenceInitializationRun.elapsed p b.completed then
    ((b.history player ⟨u.val, h⟩).1,
      ReferenceInitializationMeasurability.observationGridIndex p (b.history player ⟨u.val, h⟩).2)
  else
    let t : Fin p.T := ⟨u.val, lt_trans u.isLt r.isLt⟩
    let physical := ReferenceInitializationRun.physical (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z) b hb
    (BootstrapPhysicalBlock.actions physical (BootstrapPhysicalBlock.run physical t.val) t player,
      BootstrapPhysicalBlock.observationIndex physical (BootstrapPhysicalBlock.run physical t.val) t player)

theorem measurable_fixedHistoryCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fixedHistoryCode rate rewards C_star C_h b hb i r) := by
  apply measurable_pi_iff.mpr
  intro u
  by_cases h : u.val < ReferenceInitializationRun.elapsed p b.completed
  · simpa only [fixedHistoryCode, h, ↓reduceDIte] using
      (measurable_const : Measurable (fun _ : BootstrapPrivateRoundStreams.SourceInput p =>
        ((b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) ⟨u.val, h⟩).1,
        ReferenceInitializationMeasurability.observationGridIndex p (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) ⟨u.val, h⟩).2)))
  · let t : Fin p.T := ⟨u.val, lt_trans u.isLt r.isLt⟩
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)
    have ha := (ReferenceInitializationMeasurability.measurable_physicalAction_at_fixedBoundary p C_star C_h rate.eta
      rewards b hb t player).comp ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
    have hy := ((measurable_pi_apply player).comp ((measurable_pi_apply t).comp
      (ReferenceInitializationMeasurability.measurable_physicalObservationIndex_at_fixedBoundary p C_star C_h rate.eta
        rewards b hb))).comp ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
    simpa only [fixedHistoryCode, h, ↓reduceDIte, t, player, Function.comp_apply,
      ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput,
      ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using ha.prodMk hy

private theorem fixedHistoryCode_eq (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hbefore : r.val ≤ ReferenceInitializationRun.elapsed p (b.completed + 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    fixedHistoryCode rate rewards C_star C_h b hb i r z = historyCode
      (ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z) b hb
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore) := by
  funext u
  simp only [fixedHistoryCode, historyCode, ReferencePrelaunchLifecycleReplay.prefixHistory,
    ReferenceInitializationRun.extendedHistory, Fin.val_castLE]
  split_ifs
  · rfl
  · rw [ReferenceInitializationRun.ownEntry, ReferenceInitializationMeasurability.observationGridIndex_ownObservation]

private theorem processed_bounds (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing = none) :
    let b := ReferenceInitializationRun.run (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r).val
    b.completed < n_boot p ∧ r.val ≤ ReferenceInitializationRun.elapsed p (b.completed + 1) := by
  dsimp only
  have he : (ReferenceInitializationRun.run (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).completed = (roundBlockIndex p r).val :=
    GeneratedBootstrapRoundLaw.processed_completed z.1.1 rewards C_star C_h rate.eta (roundBlockIndex p r)
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 hc
  rw [he]
  refine ⟨(roundBlockIndex p r).isLt, ?_⟩
  exact ((mem_calendarBlock_iff p (roundBlockIndex p r) r).mp
    (round_mem_quotient_block p r)).2.le

/-- Borel measurability of the full, lossless original-source prefix code. -/
theorem measurable_sourcePrefixCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z => sourcePrefixCode rate rewards C_star C_h z i r) := by
  let boundary := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    ReferenceInitializationRun.run (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r).val
  have hboundary : Measurable boundary :=
    (ReferenceInitializationMeasurability.measurable_run p C_star C_h rate.eta rewards (roundBlockIndex p r).val).comp
      ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
  apply measurable_fibres boundary hboundary
  intro b
  by_cases hex : ∃ z, boundary z = b
  · obtain ⟨z0, hz0⟩ := hex
    by_cases hc : b.crossing = none
    · have hb := processed_bounds rate rewards C_star C_h z0 r (by
        change (boundary z0).crossing = none; rw [hz0]; exact hc)
      change (boundary z0).completed < n_boot p ∧
        r.val ≤ ReferenceInitializationRun.elapsed p ((boundary z0).completed + 1) at hb
      rw [hz0] at hb
      let H := fixedHistoryCode rate rewards C_star C_h b hb.1 i r
      have hH : Measurable H := measurable_fixedHistoryCode rate rewards C_star C_h b hb.1 i r
      have heq (z : {z // boundary z = b}) :
          sourcePrefixCode rate rewards C_star C_h z.val i r =
          match b.activation (ActualReferenceInitializationBlock.refFollower i) with
          | none => .inl (.inr (b, H z.val))
          | some a => .inl (.inl (b, a, H z.val,
              FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferencePrelaunchFollower.replay rate.eta i
                (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z.val).2.1 a (decodeHistoryCode (H z.val))
                (Nat.le_of_lt r.isLt)))) := by
        cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z.val i r with
        | inl processed =>
          rcases processed with active | inactive
          · obtain ⟨hbefore, ha, hs, hhistory⟩ := active.property
            have hbd : active.val.1.val = b := active.val.1.property.2.2.trans z.property
            have hactivation : b.activation (ActualReferenceInitializationBlock.refFollower i) =
                some active.val.2.1 :=
              (congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                b.activation (ActualReferenceInitializationBlock.refFollower i)) hbd).symm.trans ha
            have hh : H z.val = historyCode active.val.2.2.1 := by
              have hsub : (⟨b, hb.1⟩ : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p}) =
                  ⟨active.val.1.val, active.val.1.property.1⟩ := Subtype.ext hbd.symm
              have he := congrArg (fun b : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p} =>
                fixedHistoryCode rate rewards C_star C_h b.val b.property i r z.val) hsub
              exact he.trans ((fixedHistoryCode_eq rate rewards C_star C_h _ _ i r hbefore z.val).trans
                (congrArg historyCode hhistory.symm))
            simp only [sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
              hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
              hactivation, hh]
            rw [hbd, hs, decode_historyCode]
            rfl
          · obtain ⟨hbefore, ha, hhistory⟩ := inactive.property
            have hbd : inactive.val.1.val = b := inactive.val.1.property.2.2.trans z.property
            have hactivation : b.activation (ActualReferenceInitializationBlock.refFollower i) = none := by
              rw [← hbd]; exact ha
            have hh : H z.val = historyCode inactive.val.2 := by
              have hsub : (⟨b, hb.1⟩ : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p}) =
                  ⟨inactive.val.1.val, inactive.val.1.property.1⟩ := Subtype.ext hbd.symm
              have he := congrArg (fun b : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p} =>
                fixedHistoryCode rate rewards C_star C_h b.val b.property i r z.val) hsub
              exact he.trans ((fixedHistoryCode_eq rate rewards C_star C_h _ _ i r hbefore z.val).trans
                (congrArg historyCode hhistory.symm))
            simp only [sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
              hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, hactivation, hh]
            rw [hbd]
        | inr stopped =>
          have hbd : stopped.val.1 = b := stopped.property.2.1.trans z.property
          exact (stopped.property.1 ((congrArg
            (fun b : ReferenceInitializationRun.Boundary p => b.crossing) hbd).trans hc)).elim
      have hbranch : Measurable (fun z : {z // boundary z = b} =>
          match b.activation (ActualReferenceInitializationBlock.refFollower i) with
          | none => (Sum.inl (Sum.inr (b, H z.val)) : PrefixCode p rate r.val)
          | some a => .inl (.inl (b, a, H z.val,
              FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferencePrelaunchFollower.replay rate.eta i
                (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z.val).2.1 a (decodeHistoryCode (H z.val))
                (Nat.le_of_lt r.isLt))))) := by
        cases ha : b.activation (ActualReferenceInitializationBlock.refFollower i) with
        | none => exact measurable_inl.comp (measurable_inr.comp
            (measurable_const.prodMk (hH.comp measurable_subtype_coe)))
        | some a =>
          have hstate : Measurable (fun z : {z // boundary z = b} =>
              FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferencePrelaunchFollower.replay rate.eta i
                (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z.val).2.1 a (decodeHistoryCode (H z.val))
                (Nat.le_of_lt r.isLt))) := by
            exact measurable_cases (fun z : {z // boundary z = b} => H z.val) (hH.comp measurable_subtype_coe)
              (fun code (z : {z // boundary z = b}) => FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferencePrelaunchFollower.replay rate.eta i
                (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z.val).2.1 a (decodeHistoryCode code)
                (Nat.le_of_lt r.isLt))) (fun code =>
                  (measurable_replay_carriedState rate i a (decodeHistoryCode code)
                    (Nat.le_of_lt r.isLt)).comp
                    ((measurable_fst.comp (measurable_snd.comp ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates)).comp
                      measurable_subtype_coe))
          exact measurable_inl.comp (measurable_inl.comp (measurable_const.prodMk
            (measurable_const.prodMk ((hH.comp measurable_subtype_coe).prodMk hstate))))
      convert hbranch using 1
      funext z
      exact heq z
    · have hstate : Measurable (fun z : {z // boundary z = b} =>
          FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
            (ReferenceInitializationRun.ordinary
              (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z.val)
              (boundary z.val) (ActualReferenceInitializationBlock.refFollower i))) :=
        (ReferencePrelaunchCarriedMeasurability.measurable_sourceOrdinaryCarriedState rate C_star C_h rewards
        (roundBlockIndex p r).val (ActualReferenceInitializationBlock.refFollower i)).comp
          measurable_subtype_coe
      have hm : Measurable (fun z : {z // boundary z = b} =>
          (Sum.inr (b, FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (ReferenceInitializationRun.ordinary
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z.val) (boundary z.val)
            (ActualReferenceInitializationBlock.refFollower i))) : PrefixCode p rate r.val)) :=
        measurable_inr.comp (measurable_const.prodMk hstate)
      convert hm using 1
      funext z
      simp only [sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix]
      simp only [show ReferenceInitializationRun.run (ActualReferenceInitializationBlock.referenceInput z.val rewards
        C_star C_h rate) (roundBlockIndex p r).val = b from z.property, hc, ↓reduceDIte,
        z.property]
      rfl
  · have : IsEmpty {z // boundary z = b} := ⟨fun z => hex ⟨z.val, z.property⟩⟩
    exact measurable_of_empty _

private theorem measurable_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) :
    Measurable f := by
  intro S hS
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ S}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hS

/-- Only the discrete projections of the lossless prefix code. -/
abbrev PrefixRegisters (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) (n : ℕ) :=
  ((ReferenceInitializationRun.Boundary p × ReferencePrelaunchFollower.Activation p × HistoryCode p n × FollowerDownMeasurability.FollowerStateCode p rate) ⊕
    (ReferenceInitializationRun.Boundary p × HistoryCode p n)) ⊕ (ReferenceInitializationRun.Boundary p × FollowerDownMeasurability.FollowerStateCode p rate)

def prefixRegisters {rate : ReferenceActivePhysicalStep.RateInput p} {n : ℕ} :
    PrefixCode p rate n → PrefixRegisters p rate n
  | .inl (.inl v) => .inl (.inl (v.1, v.2.1, v.2.2.1, v.2.2.2.1.1))
  | .inl (.inr v) => .inl (.inr v)
  | .inr v => .inr (v.1, v.2.1.1)

theorem measurable_prefixRegisters (rate : ReferenceActivePhysicalStep.RateInput p) (n : ℕ) :
    Measurable (prefixRegisters : PrefixCode p rate n → PrefixRegisters p rate n) := by
  have hcode : Measurable (fun s : FollowerObservationStageMeasurabilityRepair.CarriedState p rate => s.1.1) := by
    apply measurable_sigma_sections
      (β := fun index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
        FollowerDownMeasurability.SavedScalarFamily index.2.1)
    intro index
    change Measurable (fun _ : FollowerDownMeasurability.SavedScalarFamily index.2.1 => index.1)
    exact measurable_const
  apply measurable_fun_sum
  · apply measurable_fun_sum
    · exact measurable_inl.comp (measurable_inl.comp (measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
            (hcode.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))))
    · exact measurable_inl.comp (measurable_inr.comp measurable_id)
  · exact measurable_inr.comp (measurable_fst.prodMk (hcode.comp measurable_snd))

def sourcePrefixRegisters (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    PrefixRegisters p rate r.val := prefixRegisters (sourcePrefixCode rate rewards C_star C_h z i r)

theorem measurable_sourcePrefixRegisters (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z => sourcePrefixRegisters rate rewards C_star C_h z i r) :=
  (measurable_prefixRegisters rate r.val).comp
    (measurable_sourcePrefixCode rate rewards C_star C_h i r)

def bankOfRegisters {rate : ReferenceActivePhysicalStep.RateInput p} {n : ℕ} :
    PrefixRegisters p rate n → Option (FollowerDownMeasurability.DecoderBatchCode p)
  | .inl (.inl v) => some v.2.2.2.downBatch
  | .inl (.inr _) => none
  | .inr v => some v.2.downBatch

def sourceBankCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    Option (FollowerDownMeasurability.DecoderBatchCode p) :=
  bankOfRegisters (sourcePrefixRegisters rate rewards C_star C_h z i r)

theorem measurable_sourceBankCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z => sourceBankCode rate rewards C_star C_h z i r) :=
  (measurable_of_countable bankOfRegisters).comp
    (measurable_sourcePrefixRegisters rate rewards C_star C_h i r)

theorem decode_sourceBankCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    (sourceBankCode rate rewards C_star C_h z i r).map FollowerDownMeasurability.decoderBatchOfCode =
      match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inl (.inl active) => some active.val.2.2.2.downBatch
      | .inl (.inr _) => none
      | .inr stopped => some stopped.val.2.downBatch := by
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl v =>
    cases v <;> simp only [sourceBankCode, sourcePrefixRegisters, sourcePrefixCode,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
      prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState, FollowerDownMeasurability.followerStateCode, bankOfRegisters,
      Option.map_some, Option.map_none, FollowerDownMeasurability.decoderBatchOfCode_code]
  | inr v =>
    simp only [sourceBankCode, sourcePrefixRegisters, sourcePrefixCode,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
      prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState, FollowerDownMeasurability.followerStateCode, bankOfRegisters,
      Option.map_some, FollowerDownMeasurability.decoderBatchOfCode_code]

abbrev TestCode (p : Parameters) := Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p) ×
  Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))

def testCode (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) : TestCode p :=
  (test.time, test.sample, test.sent)

def decodeTestCode (test : TestCode p) : ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
  ⟨test.1, test.2.1, test.2.2⟩

def testFromRowCode (i : Fin (p.m - 1))
    (rowcode : Fin p.T → PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p))
    (a : ReferencePrelaunchFollower.Activation p) (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p) : Option (TestCode p) :=
  if (a.val ≤ t.val + 1 ∧ (rowcode t).1 = PublicDiscreteDraws.downSlot ∧
      (rowcode t).2.1 = i) ∧ 0 < own.2.val.val then some (t, (rowcode t).2.2, none)
  else none

private theorem testFromRowCode_eq (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (a : ReferencePrelaunchFollower.Activation p) (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p) :
    testFromRowCode i (ReferenceInitializationMeasurability.ordinaryRowCode p i row) a t own =
      (ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a t own).map testCode := by
  simp only [testFromRowCode, ReferenceInitializationMeasurability.ordinaryRowCode, ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, ReferencePrelaunchFollower.downInput,
    decide_eq_true_eq]
  split_ifs with h <;> simp [h, testCode] <;> rfl

def testsOfRegisters (i : Fin (p.m - 1)) (r : Fin p.T)
    (rowcode : Fin p.T → PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p))
    {rate : ReferenceActivePhysicalStep.RateInput p} : PrefixRegisters p rate r.val → List (TestCode p)
  | .inl (.inl v) => (List.ofFn (fun u : Fin r.val => u)).filterMap (fun u =>
      testFromRowCode i rowcode v.2.1 (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u)
        (decodeHistoryCode v.2.2.1 u))
  | .inl (.inr _) => []
  | .inr v =>
      if v.1.forcedFailure (ActualReferenceInitializationBlock.refFollower i) then [] else
        match v.1.activation (ActualReferenceInitializationBlock.refFollower i) with
        | none => []
        | some a => (List.ofFn (fun u : Fin (ReferenceInitializationRun.elapsed p v.1.completed) => u)).filterMap
            (fun u => testFromRowCode i rowcode a (ReferencePrelaunchFollower.calendar (ReferenceInitializationRun.elapsed_le_T p _) u)
              (v.1.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) u))

def sourceTestsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    List (TestCode p) :=
  testsOfRegisters i r (ReferenceInitializationMeasurability.ordinaryRowCode p i (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2.1)
    (sourcePrefixRegisters rate rewards C_star C_h z i r)

theorem measurable_sourceTestsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z => sourceTestsCode rate rewards C_star C_h z i r) := by
  let f : (Fin p.T → PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p)) × PrefixRegisters p rate r.val →
      List (TestCode p) := fun v => testsOfRegisters i r v.1 v.2
  have hf : Measurable f := measurable_of_countable _
  exact hf.comp
    (((ReferenceInitializationMeasurability.measurable_ordinaryRowCode p i).comp
      (measurable_fst.comp (measurable_snd.comp ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates))).prodMk
        (measurable_sourcePrefixRegisters rate rewards C_star C_h i r))

theorem sourceTestsCode_eq (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    sourceTestsCode rate rewards C_star C_h z i r =
      (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).map testCode := by
  simp only [sourceTestsCode, sourcePrefixRegisters, sourcePrefixCode,
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests]
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl v =>
    cases v with
    | inl active =>
      simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters,
        testsOfRegisters, decode_historyCode, testFromRowCode_eq, List.map_filterMap]
      rfl
    | inr inactive => rfl
  | inr v =>
    simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters, testsOfRegisters,
      ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests]
    split_ifs
    · rfl
    · cases ha : v.val.1.activation (ActualReferenceInitializationBlock.refFollower i) with
      | none => rfl
      | some a =>
        simp only [testFromRowCode_eq, List.map_filterMap]
        rfl

theorem decode_sourceTestsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    (sourceTestsCode rate rewards C_star C_h z i r).map decodeTestCode =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r := by
  rw [sourceTestsCode_eq, List.map_map]
  have hi : decodeTestCode ∘ testCode = (id : ReferenceGeneratedDownBatchCalendar.ExecutedTest p → _) := by
    funext test
    cases test
    rfl
  rw [hi, List.map_id]

/-- Boolean reflection of both ordered candidate conditions. -/
def decodeFlagCode (flag : Bool × Bool) : Prop × Prop := (flag.1 = true, flag.2 = true)

def sourceFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : List (Bool × Bool) :=
  (sourceTestsCode rate rewards C_star C_h z i r).map
    (fun (test : TestCode p) => (decide (test.2.2 ≠ some w),
      decide (AffineChannelLaw.affineHash test.2.1 w = 1)))

theorem measurable_sourceFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Measurable (fun z => sourceFlagsCode rate rewards C_star C_h z i r w) :=
  (measurable_of_countable (fun tests : List (TestCode p) => tests.map
    (fun (test : TestCode p) => (decide (test.2.2 ≠ some w),
      decide (AffineChannelLaw.affineHash test.2.1 w = 1))))).comp
        (measurable_sourceTestsCode rate rewards C_star C_h i r)

theorem decode_sourceFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    (sourceFlagsCode rate rewards C_star C_h z i r w).map decodeFlagCode =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags rate rewards C_star C_h z i r w := by
  simp only [sourceFlagsCode, sourceTestsCode_eq, List.map_map, Function.comp_def,
    decodeFlagCode, testCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags]
  apply List.map_congr_left
  intro test _
  exact Prod.ext decide_eq_true_eq decide_eq_true_eq

/-- Exact pending-cohort flags, dropping the actual number of completed banks. -/
def sourceCohortFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : List (Bool × Bool) :=
  (sourceFlagsCode rate rewards C_star C_h z i r w).drop
    (AffineBatchDecoder.quota p * ((sourceBankCode rate rewards C_star C_h z i r).map
      (fun bank => bank.2.length)).getD 0)

theorem measurable_sourceCohortFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Measurable (fun z => sourceCohortFlagsCode rate rewards C_star C_h z i r w) :=
  (measurable_of_countable (fun v : List (Bool × Bool) × Option (FollowerDownMeasurability.DecoderBatchCode p) =>
    v.1.drop (AffineBatchDecoder.quota p * (v.2.map (fun bank => bank.2.length)).getD 0))).comp
      ((measurable_sourceFlagsCode rate rewards C_star C_h i r w).prodMk
        (measurable_sourceBankCode rate rewards C_star C_h i r))

theorem decode_sourceCohortFlagsCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    (sourceCohortFlagsCode rate rewards C_star C_h z i r w).map decodeFlagCode =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i r w := by
  rw [sourceCohortFlagsCode, List.map_drop, decode_sourceFlagsCode]
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl v =>
    cases v <;> simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags, hp,
      sourceBankCode, sourcePrefixRegisters, sourcePrefixCode,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
      prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState, FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchCode,
      bankOfRegisters, Option.map_some, Option.getD_some, List.length_map,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests,
      List.map_nil, List.drop_nil]
  | inr v =>
    simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags, hp,
      sourceBankCode, sourcePrefixRegisters, sourcePrefixCode,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
      prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState, FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchCode,
      bankOfRegisters, Option.map_some, Option.getD_some, List.length_map]

def birthOfRegisters (i : Fin (p.m - 1))
    {rate : ReferenceActivePhysicalStep.RateInput p} {n : ℕ} : PrefixRegisters p rate n → Option ℕ
  | .inl (.inl v) => ReferenceGeneratedPrelaunchDownPrefix.bankBirth v.2.1 (FollowerDownMeasurability.decoderBatchOfCode v.2.2.2.downBatch)
  | .inl (.inr _) => none
  | .inr v => (v.1.activation (ActualReferenceInitializationBlock.refFollower i)).bind
      (fun a => ReferenceGeneratedPrelaunchDownPrefix.bankBirth a (FollowerDownMeasurability.decoderBatchOfCode v.2.downBatch))

private theorem birthOfRegisters_eq (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    birthOfRegisters i (sourcePrefixRegisters rate rewards C_star C_h z i r) =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r := by
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl v =>
    cases v <;> simp only [birthOfRegisters, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth,
      sourcePrefixRegisters, sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
      hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code]
  | inr v =>
    simp only [birthOfRegisters, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth,
      sourcePrefixRegisters, sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
      hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code]

theorem measurable_sourcePrefixBirth (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z => ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r) := by
  have h := (measurable_of_countable (birthOfRegisters i)).comp
    (measurable_sourcePrefixRegisters rate rewards C_star C_h i r)
  convert h using 1
  funext z
  exact (birthOfRegisters_eq rate rewards C_star C_h z i r).symm

def birthAtRegisters (i : Fin (p.m - 1)) (alpha k : ℕ)
    {rate : ReferenceActivePhysicalStep.RateInput p} {n : ℕ} : PrefixRegisters p rate n → Prop
  | .inl (.inl v) =>
      let bank := FollowerDownMeasurability.decoderBatchOfCode v.2.2.2.downBatch
      bank.completed.length = k ∧ bank.pending = [] ∧ ReferenceGeneratedPrelaunchDownPrefix.bankBirth v.2.1 bank = some alpha
  | .inl (.inr _) => False
  | .inr v =>
      let bank := FollowerDownMeasurability.decoderBatchOfCode v.2.downBatch
      ∃ a, v.1.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        bank.completed.length = k ∧ bank.pending = [] ∧ ReferenceGeneratedPrelaunchDownPrefix.bankBirth a bank = some alpha

private theorem birthAt_eq_registers (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (alpha : ℕ) (hα : alpha ≤ p.T) (k : ℕ) (h : alpha < p.T) :
    ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i alpha hα k ↔
      birthAtRegisters i alpha k (sourcePrefixRegisters rate rewards C_star C_h z i ⟨alpha, h⟩) := by
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨alpha, h⟩ with
  | inl v =>
    cases v <;> simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt, h, ↓reduceDIte, hp, birthAtRegisters,
      sourcePrefixRegisters, sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code]
  | inr v =>
    simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt, h, ↓reduceDIte, hp, birthAtRegisters,
      sourcePrefixRegisters, sourcePrefixCode, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix, prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code]

private theorem measurableSet_via_code {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] (f : α → β) (hf : Measurable f) (E : β → Prop) :
    MeasurableSet {x | E (f x)} := hf (Set.to_countable _).measurableSet

/-- Includes `alpha = T` through the actual terminal output and ordinary state. -/
theorem measurableSet_birthAt (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (alpha : ℕ) (hα : alpha ≤ p.T) (k : ℕ) :
    MeasurableSet {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i alpha hα k} := by
  by_cases h : alpha < p.T
  · have hm := measurableSet_via_code _
      (measurable_sourcePrefixRegisters rate rewards C_star C_h i ⟨alpha, h⟩)
      (birthAtRegisters i alpha k)
    exact hm.congr (Set.ext (fun z => (birthAt_eq_registers rate rewards C_star C_h z i alpha hα k h).symm))
  · let terminal := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceInitializationRun.output (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z)
    have ht : Measurable terminal := (ReferenceInitializationMeasurability.measurable_output p C_star C_h rate.eta rewards).comp
      ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
    have hc : Measurable (fun s : FollowerObservationStageMeasurabilityRepair.CarriedState p rate => s.1.1) := by
      apply measurable_sigma_sections
        (β := fun index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate => FollowerDownMeasurability.SavedScalarFamily index.2.1)
      intro index
      change Measurable (fun _ : FollowerDownMeasurability.SavedScalarFamily index.2.1 => index.1)
      exact measurable_const
    have hs := hc.comp (ReferencePrelaunchCarriedMeasurability.measurable_sourceTerminalOrdinaryCarriedState rate C_star C_h rewards
      (ActualReferenceInitializationBlock.refFollower i))
    have hm := measurableSet_via_code _ (ht.prodMk hs) (fun v =>
      ∃ a, v.1.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        (FollowerDownMeasurability.decoderBatchOfCode v.2.downBatch).completed.length = k ∧
        (FollowerDownMeasurability.decoderBatchOfCode v.2.downBatch).pending = [] ∧
        ReferenceGeneratedPrelaunchDownPrefix.bankBirth a (FollowerDownMeasurability.decoderBatchOfCode v.2.downBatch) = some alpha)
    simpa only [ReferenceGeneratedPrelaunchDownPrefix.birthAt, h, ↓reduceDIte, terminal, Function.comp_apply,
      ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code] using hm

def activeIndicatorRegisters (alpha k ell : ℕ) {rate : ReferenceActivePhysicalStep.RateInput p}
    {n : ℕ} (flags : List (Bool × Bool)) : PrefixRegisters p rate n → Prop
  | .inl (.inl v) =>
      let bank := FollowerDownMeasurability.decoderBatchOfCode v.2.2.2.downBatch
      bank.completed.length = k ∧ ReferenceGeneratedPrelaunchDownPrefix.bankBirth v.2.1 bank = some alpha ∧
        bank.pending.length = ell - 1 ∧ List.Forall (fun f => f.1 = true ∧ f.2 = true) flags
  | .inl (.inr _) => False
  | .inr _ => False

/-- Borel measurability of the complete literal strict-past indicator; current
receiver positivity and the current affine equation are separate operations. -/
theorem measurableSet_source_prelaunch_down_past_indicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hα : alpha ≤ p.T) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet {z | ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
      rate rewards C_star C_h z i alpha k ell hα r w} := by
  have hm := measurableSet_via_code _
    ((measurable_sourcePrefixRegisters rate rewards C_star C_h i r).prodMk
      (measurable_sourceCohortFlagsCode rate rewards C_star C_h i r w))
    (fun v => activeIndicatorRegisters alpha k ell v.2 v.1)
  have he (z : BootstrapPrivateRoundStreams.SourceInput p) :
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hα r w ↔
      1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧ alpha ≤ r.val ∧
        ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i alpha hα k ∧
        activeIndicatorRegisters alpha k ell (sourceCohortFlagsCode rate rewards C_star C_h z i r w)
          (sourcePrefixRegisters rate rewards C_star C_h z i r) := by
    have hf := decode_sourceCohortFlagsCode rate rewards C_star C_h z i r w
    rw [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator]
    cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl v =>
      cases v <;> simp only [sourcePrefixRegisters, sourcePrefixCode,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
        prefixRegisters, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
        FollowerDownMeasurability.followerStateCode, FollowerDownMeasurability.decoderBatchOfCode_code,
        activeIndicatorRegisters, ← hf, List.forall_map_iff, Function.comp_def, decodeFlagCode]
    | inr v =>
      simp only [sourcePrefixRegisters, sourcePrefixCode,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, hp, ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs, encodePrefix,
        prefixRegisters, activeIndicatorRegisters]
  have hall := (measurableSet_via_code (fun _ : BootstrapPrivateRoundStreams.SourceInput p => ())
    measurable_const (fun _ => 1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧ alpha ≤ r.val)).inter
      ((measurableSet_birthAt rate rewards C_star C_h i alpha hα k).inter hm)
  convert hall using 1
  ext z
  simpa only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc] using he z

/-- Insert the completed selected whole row into an arbitrary original row
array, preserving IDs, every other row, and every private field including `J`. -/
def sourceCompletion (r : Fin p.T) (rows0 : CompletePublicTable.CompleteRows p)
    (e0 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    BootstrapPrivateRoundStreams.SourceInput p :=
  let e := GeneratedBootstrapRoundLaw.complete p r e0 v.2
  ((v.1, Function.update rows0 (PrivateSourceStreams.coordinatorIndex p e.2.1.2) e.1), e.2)

/-- Completion insertion retains the entire private coordinate tuple. -/
theorem sourceCompletion_allPrivateArrays (r : Fin p.T)
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    (sourceCompletion r rows0 e0 v).2 = (GeneratedBootstrapRoundLaw.complete p r e0 v.2).2 := rfl

/-- Every original unselected row is retained literally. -/
theorem sourceCompletion_other_row (r : Fin p.T)
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) (j : Fin (M p))
    (hj : j ≠ PrivateSourceStreams.coordinatorIndex p
      (GeneratedBootstrapRoundLaw.complete p r e0 v.2).2.1.2) :
    (sourceCompletion r rows0 e0 v).1.2 j = rows0 j :=
  Function.update_of_ne hj _ _

theorem sourceCoordinates_sourceCompletion (r : Fin p.T) (rows0 : CompletePublicTable.CompleteRows p)
    (e0 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    ReferencePrelaunchCarriedMeasurability.sourceCoordinates (sourceCompletion r rows0 e0 v) = (v.1, GeneratedBootstrapRoundLaw.complete p r e0 v.2) := by
  simp only [sourceCompletion, ReferencePrelaunchCarriedMeasurability.sourceCoordinates, ActualInitializationPhysicalStep.selectedRowIndex,
    Function.update_self]

theorem measurable_sourceCompletion (r : Fin p.T) (rows0 : CompletePublicTable.CompleteRows p)
    (e0 : GeneratedBootstrapRoundLaw.Coordinates p) : Measurable (sourceCompletion r rows0 e0) := by
  let e := fun v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r => GeneratedBootstrapRoundLaw.complete p r e0 v.2
  have he : Measurable e := (GeneratedBootstrapRoundLaw.measurable_complete p r e0).comp measurable_snd
  have hi : Measurable (fun v => PrivateSourceStreams.coordinatorIndex p (e v).2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp he)))
  have hrows : Measurable (fun v => Function.update rows0
      (PrivateSourceStreams.coordinatorIndex p (e v).2.1.2) (e v).1) :=
    measurable_cases _ hi (fun j v => Function.update rows0 j (e v).1)
      (fun j => (measurable_update rows0 (a := j)).comp (measurable_fst.comp he))
  exact (measurable_fst.prodMk hrows).prodMk (measurable_snd.comp he)

theorem past_sourceCompletion (r : Fin p.T) (rows0 : CompletePublicTable.CompleteRows p)
    (e0 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates (sourceCompletion r rows0 e0 v)).2 = v.2 := by
  rw [sourceCoordinates_sourceCompletion]
  exact GeneratedBootstrapRoundLaw.past_complete p r e0 v.2

private theorem completion_reconstruct {α : Sort*} (r : Fin p.T)
    (f : BootstrapPrivateRoundStreams.SourceInput p → α)
    (hinv : ∀ z z', z.1.1 = z'.1.1 →
      GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 =
        GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z').2 →
          f z = f z')
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    f (sourceCompletion r rows0 e0 (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2)) = f z :=
  hinv _ z rfl (past_sourceCompletion r rows0 e0 _)

private theorem completion_independent {α : Sort*} (r : Fin p.T)
    (f : BootstrapPrivateRoundStreams.SourceInput p → α)
    (hinv : ∀ z z', z.1.1 = z'.1.1 →
      GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 =
        GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z').2 →
          f z = f z')
    (rows0 rows1 : CompletePublicTable.CompleteRows p) (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    f (sourceCompletion r rows0 e0 v) = f (sourceCompletion r rows1 e1 v) :=
  hinv _ _ rfl ((past_sourceCompletion r rows0 e0 v).trans
    (past_sourceCompletion r rows1 e1 v).symm)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (i : Fin (p.m - 1)) (r : Fin p.T)

/-- Lossless prefix codes are invariant under arbitrary omitted-coordinate changes. -/
theorem sourcePrefixCode_eq_of_past (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 =
      GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z').2) :
    sourcePrefixCode rate rewards C_star C_h z i r = sourcePrefixCode rate rewards C_star C_h z' i r :=
  congrArg (encodePrefix rate) (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i r hids hpast)

theorem sourceBankCode_eq_of_past (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 =
      GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z').2) :
    sourceBankCode rate rewards C_star C_h z i r = sourceBankCode rate rewards C_star C_h z' i r :=
  congrArg (fun code => bankOfRegisters (prefixRegisters code))
    (sourcePrefixCode_eq_of_past rate rewards C_star C_h i r z z' hids hpast)

theorem sourceTestsCode_eq_of_past (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2 =
      GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z').2) :
    sourceTestsCode rate rewards C_star C_h z i r = sourceTestsCode rate rewards C_star C_h z' i r := by
  rw [sourceTestsCode_eq, sourceTestsCode_eq,
    ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_prefix_tests_eq_of_past rate rewards C_star C_h z z' i r hids hpast]

def prefixCodeFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : PrefixCode p rate r.val :=
  sourcePrefixCode rate rewards C_star C_h (sourceCompletion r rows0 e0 v) i r

def bankFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : Option (FollowerDownMeasurability.DecoderBatchCode p) :=
  sourceBankCode rate rewards C_star C_h (sourceCompletion r rows0 e0 v) i r

def testsFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : List (TestCode p) :=
  sourceTestsCode rate rewards C_star C_h (sourceCompletion r rows0 e0 v) i r

def birthFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : Option ℕ :=
  ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth rate rewards C_star C_h (sourceCompletion r rows0 e0 v) i r

theorem measurable_prefixCodeFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    Measurable (prefixCodeFromPast rate rewards C_star C_h i r rows0 e0) :=
  (measurable_sourcePrefixCode rate rewards C_star C_h i r).comp (measurable_sourceCompletion r rows0 e0)

theorem measurable_bankFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    Measurable (bankFromPast rate rewards C_star C_h i r rows0 e0) :=
  (measurable_sourceBankCode rate rewards C_star C_h i r).comp (measurable_sourceCompletion r rows0 e0)

theorem measurable_testsFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    Measurable (testsFromPast rate rewards C_star C_h i r rows0 e0) :=
  (measurable_sourceTestsCode rate rewards C_star C_h i r).comp (measurable_sourceCompletion r rows0 e0)

theorem measurable_birthFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    Measurable (birthFromPast rate rewards C_star C_h i r rows0 e0) :=
  (measurable_sourcePrefixBirth rate rewards C_star C_h i r).comp (measurable_sourceCompletion r rows0 e0)

theorem prefixCodeFromPast_reconstruct (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    prefixCodeFromPast rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) = sourcePrefixCode rate rewards C_star C_h z i r :=
  completion_reconstruct r _ (sourcePrefixCode_eq_of_past rate rewards C_star C_h i r) rows0 e0 z

theorem bankFromPast_reconstruct (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    bankFromPast rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) = sourceBankCode rate rewards C_star C_h z i r :=
  completion_reconstruct r _ (sourceBankCode_eq_of_past rate rewards C_star C_h i r) rows0 e0 z

theorem testsFromPast_reconstruct (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    testsFromPast rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) = sourceTestsCode rate rewards C_star C_h z i r :=
  completion_reconstruct r _ (sourceTestsCode_eq_of_past rate rewards C_star C_h i r) rows0 e0 z

theorem birthFromPast_reconstruct (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    birthFromPast rate rewards C_star C_h i r rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r :=
  completion_reconstruct r _
    (fun z z' hids hpast => ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_prefix_birth_eq_of_past
      rate rewards C_star C_h z z' i r hids hpast) rows0 e0 z

theorem prefixCodeFromPast_independent_of_completion (rows0 rows1 : CompletePublicTable.CompleteRows p)
    (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    prefixCodeFromPast rate rewards C_star C_h i r rows0 e0 v =
      prefixCodeFromPast rate rewards C_star C_h i r rows1 e1 v :=
  completion_independent r _ (sourcePrefixCode_eq_of_past rate rewards C_star C_h i r) rows0 rows1 e0 e1 v

theorem bankFromPast_independent_of_completion (rows0 rows1 : CompletePublicTable.CompleteRows p)
    (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    bankFromPast rate rewards C_star C_h i r rows0 e0 v = bankFromPast rate rewards C_star C_h i r rows1 e1 v :=
  completion_independent r _ (sourceBankCode_eq_of_past rate rewards C_star C_h i r) rows0 rows1 e0 e1 v

theorem testsFromPast_independent_of_completion (rows0 rows1 : CompletePublicTable.CompleteRows p)
    (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    testsFromPast rate rewards C_star C_h i r rows0 e0 v = testsFromPast rate rewards C_star C_h i r rows1 e1 v :=
  completion_independent r _ (sourceTestsCode_eq_of_past rate rewards C_star C_h i r) rows0 rows1 e0 e1 v

theorem birthFromPast_independent_of_completion (rows0 rows1 : CompletePublicTable.CompleteRows p)
    (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    birthFromPast rate rewards C_star C_h i r rows0 e0 v = birthFromPast rate rewards C_star C_h i r rows1 e1 v :=
  completion_independent r _ (fun z z' hids hpast => ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_prefix_birth_eq_of_past
    rate rewards C_star C_h z z' i r hids hpast) rows0 rows1 e0 e1 v

variable (alpha k ell : ℕ) (hα : alpha ≤ p.T)
  (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))

def indicatorFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : Prop :=
  ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator rate rewards C_star C_h
    (sourceCompletion r rows0 e0 v) i alpha k ell hα r w

theorem measurableSet_indicatorFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    MeasurableSet {v | indicatorFromPast rate rewards C_star C_h i r alpha k ell hα w rows0 e0 v} :=
  (measurableSet_source_prelaunch_down_past_indicator rate rewards C_star C_h i alpha k ell hα r w).preimage
    (measurable_sourceCompletion r rows0 e0)

theorem indicatorFromPast_reconstruct (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    indicatorFromPast rate rewards C_star C_h i r alpha k ell hα w rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) ↔
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hα r w := by
  exact Iff.of_eq (completion_reconstruct r _ (fun z z' hids hpast =>
    propext (ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_past_indicator_iff_of_past
      rate rewards C_star C_h z z' i alpha k ell hα r hids hpast w)) rows0 e0 z)

theorem indicatorFromPast_independent_of_completion (rows0 rows1 : CompletePublicTable.CompleteRows p)
    (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p) (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    indicatorFromPast rate rewards C_star C_h i r alpha k ell hα w rows0 e0 v ↔
      indicatorFromPast rate rewards C_star C_h i r alpha k ell hα w rows1 e1 v := by
  exact Iff.of_eq (completion_independent r _ (fun z z' hids hpast =>
    propext (ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_past_indicator_iff_of_past
      rate rewards C_star C_h z z' i alpha k ell hα r hids hpast w)) rows0 rows1 e0 e1 v)

/-- Endpoint `T` cannot be an earlier birth in an indicator at `r < T`. -/
theorem indicatorFromPast_false_of_lt (h : r.val < alpha)
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    ¬ indicatorFromPast rate rewards C_star C_h i r alpha k ell hα w rows0 e0 v := by
  intro hi
  exact (Nat.not_le_of_lt h) hi.2.2.1

/-- Birth predicates factor only at prefixes at or after their own boundary. -/
def birthAtFromPast (alpha k : ℕ) (hα : alpha ≤ p.T)
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) : Prop :=
  ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h (sourceCompletion r rows0 e0 v) i alpha hα k

theorem measurableSet_birthAtFromPast (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p) :
    MeasurableSet {v | birthAtFromPast rate rewards C_star C_h i r alpha k hα rows0 e0 v} :=
  (measurableSet_birthAt rate rewards C_star C_h i alpha hα k).preimage
    (measurable_sourceCompletion r rows0 e0)

theorem birthAtFromPast_reconstruct (hαr : alpha ≤ r.val)
    (rows0 : CompletePublicTable.CompleteRows p) (e0 : GeneratedBootstrapRoundLaw.Coordinates p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    birthAtFromPast rate rewards C_star C_h i r alpha k hα rows0 e0
        (z.1.1, GeneratedBootstrapRoundLaw.past p r (ReferencePrelaunchCarriedMeasurability.sourceCoordinates z).2) ↔
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i alpha hα k := by
  exact Iff.of_eq (completion_reconstruct r _ (fun z z' hids hpast =>
    propext (ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_birthAt_iff_of_past
      rate rewards C_star C_h z z' i alpha hα k r hαr hids hpast)) rows0 e0 z)

theorem birthAtFromPast_independent_of_completion (hαr : alpha ≤ r.val)
    (rows0 rows1 : CompletePublicTable.CompleteRows p) (e0 e1 : GeneratedBootstrapRoundLaw.Coordinates p)
    (v : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    birthAtFromPast rate rewards C_star C_h i r alpha k hα rows0 e0 v ↔
      birthAtFromPast rate rewards C_star C_h i r alpha k hα rows1 e1 v := by
  exact Iff.of_eq (completion_independent r _ (fun z z' hids hpast =>
    propext (ReferenceGeneratedPrelaunchDownDerivedPast.source_prelaunch_down_birthAt_iff_of_past
      rate rewards C_star C_h z z' i alpha hα k r hαr hids hpast)) rows0 rows1 e0 e1 v)

end Bandits.Support.ReferenceGeneratedPrelaunchDownPastFactor
