/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.FollowerPrepareJointMeasurability
public import Bandits.Support.ActualReferenceInitializationBlock
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The complete ordinary reference follower state in its existing carried code

The actual stopped reference producer's ordinary follower state is measurable
on the original complete-row input, in the canonical carried representation
of countable registers, ordered timestamp/pilot skeleton, and the original
finite product of saved real coordinates. A finite adapter turns the accepted
calendar logging array into that representation and reconstructs its exact
buffer immediately. The source adapter selects `J` from the original private
scalar and reads the selected whole row from the original row array.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/06_interruptions.tex:192-209,235-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

These are internal deterministic measurability and reconstruction results.
They do not characterize corrected launch memory, prove a source theorem, or
close the regret argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferenceInitializationRun

namespace Bandits.Support.ReferencePrelaunchCarriedMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev LoggingCode := ReferenceInitializationMeasurability.LoggingCode
abbrev SavedScalar := FollowerDownMeasurability.SavedScalar
abbrev SavedScalarFamily := FollowerDownMeasurability.SavedScalarFamily
abbrev BufferIndex (p : Parameters) :=
  Sigma fun n : ℕ => FollowerDownJointMeasurability.BufferSkeletonCode p n
abbrev BufferCarry (p : Parameters) :=
  Sigma fun index : BufferIndex p => SavedScalarFamily index.1

/-- The accepted initialization bank code and the canonical local code use
the same literal ordered pending/completed entry encoding. -/
theorem downBatchCode_eq_decoderBatchCode {p : Parameters}
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    ReferenceInitializationMeasurability.downBatchCode batch =
      FollowerDownMeasurability.decoderBatchCode batch := rfl

/-- The canonical entry-by-entry code retains the full decoder state. -/
theorem decoderBatchCode_injective {p : Parameters} :
    Function.Injective
      (@FollowerDownMeasurability.decoderBatchCode p) := by
  intro left right h
  apply ReferenceInitializationMeasurability.downBatchCode_injective
    p.T (AffineBatchDecoder.width p)
  exact (downBatchCode_eq_decoderBatchCode left).trans
    (h.trans (downBatchCode_eq_decoderBatchCode right).symm)

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurableEmbedding_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Sigma β) := by
  classical
  refine ⟨?_, measurable_sigmaMk a, ?_⟩
  · intro x y h
    cases h
    rfl
  · intro s hs
    change MeasurableSet[
      (⨅ b, (inferInstance : MeasurableSpace (β b)).map (Sigma.mk b))]
      (Sigma.mk a '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro b
    rw [MeasurableSpace.map_def]
    by_cases h : b = a
    · subst b
      have hinj : Function.Injective (Sigma.mk a : β a → Sigma β) := by
        intro x y hxy
        cases hxy
        rfl
      simpa only [hinj.preimage_image] using hs
    · have hempty : (Sigma.mk b) ⁻¹' (Sigma.mk a '' s) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨y, _, hxy⟩
        exact h (congrArg Sigma.fst hxy).symm
      rw [hempty]
      exact MeasurableSet.empty

private theorem measurable_assembleSigmaProduct {α : Type*} [Countable α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ : Type*} [MeasurableSpace γ] :
    Measurable (fun x : (Sigma β) × γ =>
      (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) := by
  intro s hs
  have hsections (a : α) :
      MeasurableSet ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    exact (measurable_sigmaMk (β := fun b => β b × γ) a) hs
  have himages (a : α) : MeasurableSet
      ((Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s)) :=
    ((measurableEmbedding_sigmaMk a).prodMap MeasurableEmbedding.id).measurableSet_image'
      (hsections a)
  have hdecomp :
      (fun x : (Sigma β) × γ =>
        (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) ⁻¹' s =
      ⋃ a : α, (Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x.1.1, (x.1.2, x.2), hx, rfl⟩
    · intro hx
      obtain ⟨a, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      subst x
      exact hy
  rw [hdecomp]
  exact MeasurableSet.iUnion himages

private theorem measurable_by_countable_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

private def bufferCarryBuffer {p : Parameters} (carry : BufferCarry p) :
    List (SparseCalendarRecord p.K) :=
  FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
    carry.1.2 carry.2

private def bufferCarryOfBuffer {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) : BufferCarry p :=
  ⟨⟨buffer.length,
    FollowerDownJointMeasurability.bufferSkeletonCode buffer⟩,
    FollowerDownJointMeasurability.bufferScalarsCode buffer⟩

private def emptyBufferCarry (p : Parameters) : BufferCarry p :=
  ⟨⟨0, fun j => Fin.elim0 j⟩, fun j => Fin.elim0 j⟩

private abbrev BufferKey (p : Parameters) := ℕ × Fin p.K

private def appendSavedScalarFamily {n : ℕ}
    (values : SavedScalarFamily n) (last : SavedScalar) : SavedScalarFamily (n + 1) :=
  Fin.lastCases last values

private theorem measurable_appendSavedScalarFamily {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (values : Ω → SavedScalarFamily n) (last : Ω → SavedScalar)
    (hvalues : Measurable values) (hlast : Measurable last) :
    Measurable (fun ω => appendSavedScalarFamily (values ω) (last ω)) := by
  apply measurable_pi_iff.mpr
  intro j
  induction j using Fin.lastCases with
  | cast j =>
      have hvalue : Measurable (fun ω => values ω j) :=
        (measurable_pi_apply j).comp hvalues
      simpa only [appendSavedScalarFamily, Fin.lastCases_castSucc] using hvalue
  | last =>
      simpa [appendSavedScalarFamily] using hlast

private def appendBufferCarry {p : Parameters} (index : BufferIndex p)
    (values : SavedScalarFamily index.1) (key : BufferKey p) (saved : SavedScalar) :
    BufferCarry p :=
  ⟨⟨index.1 + 1, Fin.lastCases key index.2⟩,
    appendSavedScalarFamily values saved⟩

private theorem bufferCarryBuffer_append {p : Parameters} (index : BufferIndex p)
    (values : SavedScalarFamily index.1) (key : BufferKey p) (saved : SavedScalar) :
    bufferCarryBuffer (appendBufferCarry index values key saved) =
      bufferCarryBuffer ⟨index, values⟩ ++
        [⟨key.1, key.2, saved.1, saved.2⟩] := by
  change FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      (Fin.lastCases key index.2) (Fin.lastCases saved values) =
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2 values ++
      [⟨key.1, key.2, saved.1, saved.2⟩]
  simp only [FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
  rw [List.ofFn_succ']
  simp_rw [Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [List.concat_eq_append]

private def loggingBufferStep {p : Parameters} (carry : BufferCarry p)
    (code : LoggingCode p) : BufferCarry p :=
  match code with
  | .inl _ => carry
  | .inr entry =>
      appendBufferCarry carry.1 carry.2 (entry.1, entry.2.1)
        (entry.2.2.1, entry.2.2.2)

private theorem loggingBufferStep_buffer {p : Parameters} (carry : BufferCarry p)
    (code : LoggingCode p) :
    bufferCarryBuffer (loggingBufferStep carry code) =
      bufferCarryBuffer carry ++ ReferenceInitializationMeasurability.decodeLoggingCode code := by
  cases code with
  | inl _ => simp [loggingBufferStep,
      ReferenceInitializationMeasurability.decodeLoggingCode]
  | inr entry =>
      rcases entry with ⟨calendarRound, pilot, observation, thin⟩
      simpa [loggingBufferStep, ReferenceInitializationMeasurability.decodeLoggingCode]
        using bufferCarryBuffer_append carry.1 carry.2
          (calendarRound, pilot) (observation, thin)

private def loggingArrayCarriedBuffer {p : Parameters} :
    (n : ℕ) → (Fin n → LoggingCode p) → BufferCarry p
  | 0, _ => emptyBufferCarry p
  | n + 1, logs =>
      loggingBufferStep
        (loggingArrayCarriedBuffer n (fun j => logs j.castSucc))
        (logs (Fin.last n))

private theorem loggingArrayCarriedBuffer_buffer {p : Parameters} (n : ℕ)
    (logs : Fin n → LoggingCode p) :
    bufferCarryBuffer (loggingArrayCarriedBuffer n logs) =
      (List.ofFn fun j : Fin n => j).flatMap (fun j =>
        ReferenceInitializationMeasurability.decodeLoggingCode (logs j)) := by
  induction n with
  | zero => simp [loggingArrayCarriedBuffer, emptyBufferCarry, bufferCarryBuffer,
      FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
  | succ n ih =>
      rw [loggingArrayCarriedBuffer, loggingBufferStep_buffer,
        ih (fun j => logs j.castSucc), List.ofFn_succ']
      simp only [List.concat_eq_append, List.flatMap_append, List.flatMap_singleton]
      simp [ReferenceInitializationMeasurability.decodeLoggingCode,
        List.ofFn_eq_map, List.flatMap_map]

private def loggingPayloadKey {p : Parameters}
    (entry : ℕ × Fin p.K × SparseCalendarReward × SparseCalendarThinScalar) : BufferKey p :=
  (entry.1, entry.2.1)

private def loggingPayloadSaved {p : Parameters}
    (entry : ℕ × Fin p.K × SparseCalendarReward × SparseCalendarThinScalar) : SavedScalar :=
  (entry.2.2.1, entry.2.2.2)

private theorem measurable_loggingBufferStepOnFiber {p : Parameters}
    (index : BufferIndex p) :
    Measurable (fun x : SavedScalarFamily index.1 × LoggingCode p =>
      loggingBufferStep ⟨index, x.1⟩ x.2) := by
  let payload :=
    ℕ × Fin p.K × SparseCalendarReward × SparseCalendarThinScalar
  let branchLeft : SavedScalarFamily index.1 × Unit → BufferCarry p :=
    fun x => ⟨index, x.1⟩
  have hleft : Measurable branchLeft :=
    (measurable_sigmaMk index).comp measurable_fst
  let branchRight : SavedScalarFamily index.1 × payload → BufferCarry p :=
    fun x => appendBufferCarry index x.1
      (loggingPayloadKey x.2) (loggingPayloadSaved x.2)
  have hentry : Measurable (fun x : SavedScalarFamily index.1 × payload => x.2) :=
    measurable_snd
  have hkey : Measurable (fun x : SavedScalarFamily index.1 × payload =>
      loggingPayloadKey x.2) := by
    exact (measurable_fst.comp hentry).prodMk
      (measurable_fst.comp (measurable_snd.comp hentry))
  have hsaved : Measurable (fun x : SavedScalarFamily index.1 × payload =>
      loggingPayloadSaved x.2) := by
    exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hentry))).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hentry)))
  have hparts : Measurable (fun x : SavedScalarFamily index.1 × payload =>
      ((x.1, loggingPayloadSaved x.2), loggingPayloadKey x.2)) := by
    exact (measurable_fst.prodMk hsaved).prodMk hkey
  have hright : Measurable branchRight := by
    let appendAtKey : BufferKey p → SavedScalarFamily index.1 × SavedScalar →
        BufferCarry p := fun key x => appendBufferCarry index x.1 key x.2
    have hfixed : Measurable (fun x : (SavedScalarFamily index.1 × SavedScalar) ×
        BufferKey p => appendAtKey x.2 x.1) := by
      exact measurable_from_prod_countable_left
        (f := fun x : (SavedScalarFamily index.1 × SavedScalar) × BufferKey p =>
          appendAtKey x.2 x.1) fun key => by
          let appendedIndex : BufferIndex p :=
            ⟨index.1 + 1, Fin.lastCases key index.2⟩
          exact (measurable_sigmaMk appendedIndex).comp
            (measurable_appendSavedScalarFamily
              (values := fun x : SavedScalarFamily index.1 × SavedScalar => x.1)
              (last := fun x => x.2) measurable_fst measurable_snd)
    exact hfixed.comp hparts
  have hsum : Measurable (Sum.elim branchLeft branchRight) :=
    hleft.sumElim hright
  let distribute : SavedScalarFamily index.1 × LoggingCode p →
      (SavedScalarFamily index.1 × Unit) ⊕
        (SavedScalarFamily index.1 × payload) :=
    (MeasurableEquiv.prodSumDistrib (SavedScalarFamily index.1) Unit payload).toFun
  have hfactor : (fun x : SavedScalarFamily index.1 × LoggingCode p =>
      loggingBufferStep ⟨index, x.1⟩ x.2) = Sum.elim branchLeft branchRight ∘ distribute := by
    funext x
    rcases x with ⟨values, code⟩
    cases code <;> rfl
  rw [hfactor]
  exact hsum.comp ((MeasurableEquiv.prodSumDistrib
    (SavedScalarFamily index.1) Unit payload).measurable)

private theorem measurable_loggingBufferStep {p : Parameters} :
    Measurable (fun x : BufferCarry p × LoggingCode p =>
      loggingBufferStep x.1 x.2) := by
  let assemble : BufferCarry p × LoggingCode p →
      Sigma fun index : BufferIndex p => SavedScalarFamily index.1 × LoggingCode p :=
    fun x => ⟨x.1.1, (x.1.2, x.2)⟩
  have hassemble : Measurable assemble := measurable_assembleSigmaProduct
  let sectionMap : (Sigma fun index : BufferIndex p =>
      SavedScalarFamily index.1 × LoggingCode p) → BufferCarry p := fun x =>
        loggingBufferStep ⟨x.1, x.2.1⟩ x.2.2
  have hsectionMap : Measurable sectionMap := by
    apply measurable_of_sigma_sections sectionMap
    intro index
    exact measurable_loggingBufferStepOnFiber index
  have hfactor : (fun x : BufferCarry p × LoggingCode p =>
      loggingBufferStep x.1 x.2) = sectionMap ∘ assemble := by
    funext x
    rfl
  rw [hfactor]
  exact hsectionMap.comp hassemble

private theorem measurable_loggingArrayCarriedBuffer {p : Parameters} (n : ℕ) :
    Measurable (loggingArrayCarriedBuffer (p := p) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let preLogs : (Fin (n + 1) → LoggingCode p) → (Fin n → LoggingCode p) :=
        fun logs j => logs j.castSucc
      have hprefix : Measurable preLogs := by
        apply measurable_pi_iff.mpr
        intro j
        exact measurable_pi_apply j.castSucc
      exact measurable_loggingBufferStep.comp
        ((ih.comp hprefix).prodMk (measurable_pi_apply (Fin.last n)))

private theorem bufferCodes_ofFn {p : Parameters} {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧
      HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values).length = n := List.length_ofFn
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

private theorem bufferCarryOfBuffer_bufferCarryBuffer {p : Parameters}
    (carry : BufferCarry p) : bufferCarryOfBuffer (bufferCarryBuffer carry) = carry := by
  rcases carry with ⟨⟨n, skeleton⟩, values⟩
  let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
    skeleton values
  have hcodes := bufferCodes_ofFn skeleton values
  have hlength : buffer.length = n := by
    simp [buffer, FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
  have hindex : (⟨buffer.length,
      FollowerDownJointMeasurability.bufferSkeletonCode buffer⟩ : BufferIndex p) =
      ⟨n, skeleton⟩ := Sigma.ext hlength hcodes.1
  change (⟨(⟨buffer.length,
      FollowerDownJointMeasurability.bufferSkeletonCode buffer⟩ : BufferIndex p),
      FollowerDownJointMeasurability.bufferScalarsCode buffer⟩ : BufferCarry p) = _
  exact Sigma.ext hindex hcodes.2

private theorem bufferCarryOfBuffer_eq_of_buffer_eq {p : Parameters}
    (left right : BufferCarry p) (h : bufferCarryBuffer left = bufferCarryBuffer right) :
    left = right := by
  calc
    left = bufferCarryOfBuffer (bufferCarryBuffer left) :=
      (bufferCarryOfBuffer_bufferCarryBuffer left).symm
    _ = bufferCarryOfBuffer (bufferCarryBuffer right) := congrArg bufferCarryOfBuffer h
    _ = right := bufferCarryOfBuffer_bufferCarryBuffer right

private def loggingArrayPrefix {p : Parameters} {N n : ℕ} (h : n ≤ N)
    (logs : Fin N → LoggingCode p) : Fin n → LoggingCode p :=
  fun j => logs ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩

private theorem loggingArrayFlatMap_eq_prefix {p : Parameters} {N n : ℕ}
    (h : n ≤ N) (logs : Fin N → LoggingCode p)
    (hzero : ∀ t, n ≤ t.val → logs t = Sum.inl ()) :
    (List.ofFn fun t : Fin N => t).flatMap (fun t =>
        ReferenceInitializationMeasurability.decodeLoggingCode (logs t)) =
      (List.ofFn fun t : Fin n => t).flatMap (fun t =>
        ReferenceInitializationMeasurability.decodeLoggingCode
          (loggingArrayPrefix h logs t)) := by
  induction N generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      simp [loggingArrayPrefix]
  | succ N ih =>
      by_cases hlast : n = N + 1
      · subst n
        have hpref : loggingArrayPrefix (Nat.le_refl _) logs = logs := by
          funext t
          apply congrArg logs
          apply Fin.ext
          rfl
        rw [hpref]
      · have hn : n ≤ N := by omega
        have hzeroLast : logs (Fin.last N) = Sum.inl () := by
          apply hzero
          simpa using hn
        have hrestricted : ∀ t : Fin N, n ≤ t.val →
            (fun j : Fin N => logs j.castSucc) t = Sum.inl () := by
          intro t ht
          apply hzero t.castSucc
          simpa using ht
        have hpref : loggingArrayPrefix h
              logs = loggingArrayPrefix hn
                (fun t : Fin N => logs t.castSucc) := by
          funext t
          apply congrArg logs
          apply Fin.ext
          rfl
        calc
          (List.ofFn fun t : Fin (N + 1) => t).flatMap (fun t =>
              ReferenceInitializationMeasurability.decodeLoggingCode (logs t)) =
            (List.ofFn fun t : Fin N => t).flatMap (fun t =>
                ReferenceInitializationMeasurability.decodeLoggingCode (logs t.castSucc)) := by
                  rw [List.ofFn_succ']
                  rw [List.concat_eq_append, List.flatMap_append,
                    List.flatMap_singleton, hzeroLast]
                  simp only [ReferenceInitializationMeasurability.decodeLoggingCode,
                    List.append_nil]
                  simp [List.ofFn_eq_map, List.flatMap_map]
          _ = (List.ofFn fun t : Fin n => t).flatMap (fun t =>
                ReferenceInitializationMeasurability.decodeLoggingCode
                  (loggingArrayPrefix hn
                    (fun j : Fin N => logs j.castSucc) t)) := by
                  exact ih hn (fun j => logs j.castSucc) hrestricted
          _ = (List.ofFn fun t : Fin n => t).flatMap (fun t =>
                ReferenceInitializationMeasurability.decodeLoggingCode
                  (loggingArrayPrefix h logs t)) := by
                  rw [hpref]

private theorem ordinaryLogging_none_of_outside {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (t : Fin p.T)
    (ht : elapsed p b.completed ≤ t.val) :
    ReferenceInitializationMeasurability.ordinaryLogging p x b i t = Sum.inl () := by
  cases hf : b.forcedFailure i <;> cases ha : b.activation i <;>
    simp [ReferenceInitializationMeasurability.ordinaryLogging, hf, ha,
      Nat.not_lt_of_ge ht]

private theorem ordinaryLogging_fullBuffer {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) :
    (List.ofFn fun t : Fin p.T => t).flatMap (fun t =>
      ReferenceInitializationMeasurability.decodeLoggingCode
        (ReferenceInitializationMeasurability.ordinaryLogging p x b i t)) =
      (ReferenceInitializationRun.ordinary x b i).buffer := by
  let n := elapsed p b.completed
  have hfull := loggingArrayFlatMap_eq_prefix
    (p := p) (N := p.T) (n := n) (ReferenceInitializationRun.elapsed_le_T p b.completed)
    (ReferenceInitializationMeasurability.ordinaryLogging p x b i)
    (fun t ht => ordinaryLogging_none_of_outside x b i t ht)
  calc
    (List.ofFn fun t : Fin p.T => t).flatMap (fun t =>
        ReferenceInitializationMeasurability.decodeLoggingCode
          (ReferenceInitializationMeasurability.ordinaryLogging p x b i t)) =
      (List.ofFn fun t : Fin n => t).flatMap (fun t =>
        ReferenceInitializationMeasurability.decodeLoggingCode
          (loggingArrayPrefix (ReferenceInitializationRun.elapsed_le_T p b.completed)
            (ReferenceInitializationMeasurability.ordinaryLogging p x b i) t)) := hfull
    _ = (ReferenceInitializationRun.ordinary x b i).buffer := by
      simpa only [n, loggingArrayPrefix] using
        (ReferenceInitializationMeasurability.ordinaryLogging_buffer p x b i).symm

private theorem bufferCarryBuffer_bufferCarryOfBuffer {p : Parameters}
    (buffer : List (SparseCalendarRecord p.K)) :
    bufferCarryBuffer (bufferCarryOfBuffer buffer) = buffer := by
  exact FollowerDownJointMeasurability.bufferFromSkeletonAndScalars_code buffer

private theorem measurable_ordinaryFailure {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      (ReferenceInitializationRun.ordinary
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
          rewards z)
        (ReferenceInitializationRun.run
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards z) r) i).initializationFailure) := by
  let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
  let key := fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
    ReferenceInitializationRun.run (x z) r
  have hkey : Measurable key := ReferenceInitializationMeasurability.measurable_run
    p C_star C_h rate.eta rewards r
  exact measurable_by_countable_cases key hkey
    (fun b z => (ReferenceInitializationRun.ordinary (x z) b i).initializationFailure)
    (fun b => ReferenceInitializationMeasurability.measurable_ordinaryFailure_at_fixedBoundary
      p C_star C_h rate.eta rewards b i)

private theorem measurable_ordinaryStateCode {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      FollowerDownMeasurability.followerStateCode rate
        (ReferenceInitializationRun.ordinary
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards z)
          (ReferenceInitializationRun.run
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
              rewards z) r) i)) := by
  let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
  let b := fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
    ReferenceInitializationRun.run (x z) r
  let state := fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
    ReferenceInitializationRun.ordinary (x z) (b z) i
  let batch := fun z => ReferenceInitializationMeasurability.downBatchCode (state z).downBatch
  let failed := fun z => (state z).initializationFailure
  have hbatch : Measurable batch := by
    simpa only [batch, x, b, state] using
      ReferenceInitializationMeasurability.measurable_ordinary_downBatchCode
        p C_star C_h rate.eta rewards r i
  have hfailed : Measurable failed := by
    simpa only [failed, x, b, state] using
      measurable_ordinaryFailure rate C_star C_h rewards r i
  have hbatchCanonical : Measurable (fun z =>
      FollowerDownMeasurability.decoderBatchCode (state z).downBatch) := by
    have heq : (fun z => FollowerDownMeasurability.decoderBatchCode (state z).downBatch) =
        batch := by
      funext z
      exact (downBatchCode_eq_decoderBatchCode (state z).downBatch).symm
    rw [heq]
    exact hbatch
  let codeOf : FollowerDownMeasurability.DecoderBatchCode p × Bool →
      FollowerDownMeasurability.FollowerStateCode p rate := fun v =>
    ⟨none, 0, 0, 0, 0, v.1, v.2⟩
  have hcodeOf : Measurable codeOf := measurable_of_countable codeOf
  have hassembled : Measurable (fun z =>
      codeOf (FollowerDownMeasurability.decoderBatchCode (state z).downBatch,
        (state z).initializationFailure)) :=
    hcodeOf.comp (hbatchCanonical.prodMk hfailed)
  have hfields : (fun z => FollowerDownMeasurability.followerStateCode rate (state z)) =
      fun z => codeOf (FollowerDownMeasurability.decoderBatchCode (state z).downBatch,
        (state z).initializationFailure) := by
    funext z
    rcases ReferenceInitializationRun.ordinary_registers (x z) (b z) i with
      ⟨hlast, _hstart, hS, hdelta, hbacklog, hstatus⟩
    simp only [FollowerDownMeasurability.followerStateCode, codeOf,
      FollowerDownMeasurability.followerStatusCode]
    rw [hlast, hS, hdelta, hbacklog, hstatus]
    rfl
  rw [hfields]
  exact hassembled

private def assembleFollowerCarriedState {p : Parameters} {rate : RateInput p}
    (code : FollowerDownMeasurability.FollowerStateCode p rate)
    (buffer : BufferCarry p) :
    FollowerObservationStageMeasurabilityRepair.CarriedState p rate :=
  ⟨(code, buffer.1), buffer.2⟩

private theorem measurable_assembleFollowerCarriedState {p : Parameters}
    {rate : RateInput p} :
    Measurable (fun x : FollowerDownMeasurability.FollowerStateCode p rate × BufferCarry p =>
      assembleFollowerCarriedState x.1 x.2) := by
  let distribute :
      FollowerDownMeasurability.FollowerStateCode p rate × BufferCarry p →
        Sigma fun index : BufferIndex p =>
          SavedScalarFamily index.1 × FollowerDownMeasurability.FollowerStateCode p rate :=
    fun x => ⟨x.2.1, (x.2.2, x.1)⟩
  have hdistribute : Measurable distribute := by
    exact measurable_assembleSigmaProduct.comp (measurable_snd.prodMk measurable_fst)
  let sectionMap : (Sigma fun index : BufferIndex p =>
      SavedScalarFamily index.1 × FollowerDownMeasurability.FollowerStateCode p rate) →
      FollowerObservationStageMeasurabilityRepair.CarriedState p rate :=
    fun x => assembleFollowerCarriedState x.2.2 ⟨x.1, x.2.1⟩
  have hsectionMap : Measurable sectionMap := by
    apply measurable_of_sigma_sections
    intro index
    exact measurable_from_prod_countable_left (f := fun v :
        SavedScalarFamily index.1 × FollowerDownMeasurability.FollowerStateCode p rate =>
      assembleFollowerCarriedState v.2 ⟨index, v.1⟩) fun code => by
        change Measurable (fun v : SavedScalarFamily index.1 =>
            (@Sigma.mk
              (FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
              (fun index => SavedScalarFamily index.2.1) (code, index) :
              SavedScalarFamily index.1 →
              FollowerObservationStageMeasurabilityRepair.CarriedState p rate) v)
        exact (measurable_sigmaMk (α :=
          FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate)
          (β := fun index => SavedScalarFamily index.2.1) (code, index))
  have hfactor : (fun x : FollowerDownMeasurability.FollowerStateCode p rate ×
      BufferCarry p => assembleFollowerCarriedState x.1 x.2) = sectionMap ∘ distribute := by
    funext x
    rfl
  rw [hfactor]
  exact hsectionMap.comp hdistribute

theorem measurable_ordinaryCarriedState {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferenceInitializationRun.ordinary
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards z)
          (ReferenceInitializationRun.run
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
              rewards z) r) i)) := by
  let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
  let state := fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
    ReferenceInitializationRun.ordinary (x z) (ReferenceInitializationRun.run (x z) r) i
  let code := fun z => FollowerDownMeasurability.followerStateCode rate (state z)
  let logs := fun z => ReferenceInitializationMeasurability.ordinaryLogging p
    (x z) (ReferenceInitializationRun.run (x z) r) i
  let carry := fun z => loggingArrayCarriedBuffer p.T (logs z)
  have hcode : Measurable code := by
    simpa only [code, state, x] using
      measurable_ordinaryStateCode rate C_star C_h rewards r i
  have hlogs : Measurable logs := by
    simpa only [logs, x] using ReferenceInitializationMeasurability.measurable_ordinaryLogging
      p C_star C_h rate.eta rewards r i
  have hcarry : Measurable carry := by
    exact (measurable_loggingArrayCarriedBuffer p.T).comp hlogs
  let assembled := fun z => assembleFollowerCarriedState (code z) (carry z)
  have hassembled : Measurable assembled :=
    measurable_assembleFollowerCarriedState.comp (hcode.prodMk hcarry)
  have hEq : (fun z =>
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (state z)) =
      assembled := by
    funext z
    have hbuffer : bufferCarryBuffer (carry z) = (state z).buffer := by
      have hcarryBuffer := loggingArrayCarriedBuffer_buffer p.T (logs z)
      have hloggedBuffer := ordinaryLogging_fullBuffer (x z)
        (ReferenceInitializationRun.run (x z) r) i
      simpa only [carry, logs, x, state] using hcarryBuffer.trans hloggedBuffer
    have hbufferCode := bufferCarryOfBuffer_eq_of_buffer_eq (carry z)
      (bufferCarryOfBuffer (state z).buffer)
      (hbuffer.trans (bufferCarryBuffer_bufferCarryOfBuffer (state z).buffer).symm)
    change FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate (state z) =
      assembleFollowerCarriedState (code z) (carry z)
    rw [hbufferCode]
    simp [assembleFollowerCarriedState, FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      bufferCarryOfBuffer, code, state]
  rw [hEq]
  exact hassembled

/-- Original source coordinates for the reference run: the complete ID array,
the complete row selected by the original private scalar for `J`, and every
original private array and scalar. -/
def sourceCoordinates {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceInitializationMeasurability.InputCoordinates p :=
  (source.1.1,
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source), source.2))

theorem sourceCoordinates_ids {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (sourceCoordinates source).1 = source.1.1 := rfl

theorem sourceCoordinates_selectedWholeRow {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (sourceCoordinates source).2.1 =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := rfl

theorem sourceCoordinates_allPrivateArrays {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (sourceCoordinates source).2.2 = source.2 := rfl

theorem sourceCoordinates_referenceInput {p : Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) :
    ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
      rewards (sourceCoordinates source) =
    ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate := rfl

private theorem measurable_sourceSelectedWholeRow {p : Parameters} :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) := by
  have hindex : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hrows : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      source.1.2) := measurable_snd.comp measurable_fst
  exact measurable_from_prod_countable_right (f := fun v : Fin (M p) ×
      BootstrapPrivateRoundStreams.SourceInput p => v.2.1.2 v.1) (fun j =>
        (measurable_pi_apply j).comp hrows) |>.comp (hindex.prodMk measurable_id)

theorem measurable_sourceCoordinates {p : Parameters} :
    Measurable (sourceCoordinates (p := p)) := by
  have hids : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      source.1.1) := measurable_fst.comp measurable_fst
  exact hids.prodMk
    (measurable_sourceSelectedWholeRow.prodMk measurable_snd)

theorem measurable_sourceOrdinaryCarriedState {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (r : ℕ) (i : Follower p.m) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            r) i)) := by
  have h := (measurable_ordinaryCarriedState rate C_star C_h rewards r i).comp
    measurable_sourceCoordinates
  change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
    FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
      (ReferenceInitializationRun.ordinary
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
          rewards (sourceCoordinates source))
        (ReferenceInitializationRun.run
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards (sourceCoordinates source)) r) i))
  exact h

theorem sourceOrdinaryCarriedState_reconstruct {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (r : ℕ) (i : Follower p.m) :
    FollowerDownMeasurability.followerStateOfCode rate
        (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.run
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
              r) i)).1.1
      (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer
        (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.run
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
              r) i))) =
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.run
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          r) i :=
  FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct rate
    (ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i)

theorem measurable_sourceTerminalOrdinaryCarriedState {p : Parameters}
    (rate : RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (i : Follower p.m) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i)) := by
  simpa only [ReferenceInitializationRun.output] using
    measurable_sourceOrdinaryCarriedState rate C_star C_h rewards (n_boot p) i

end Bandits.Support.ReferencePrelaunchCarriedMeasurability

end
