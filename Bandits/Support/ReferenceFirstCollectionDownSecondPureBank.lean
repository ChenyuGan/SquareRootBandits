/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownBankHistory
public import Bandits.Support.ReferenceFirstCollectionUnacceptedDownReceiverPrefix

import Mathlib.Data.List.SplitLengths
import Lean.Elab.Tactic.Omega

/-!
# The second actual unaccepted DOWN batch in first collection

This module joins the actual cutoff-bank replay with the fixed-word receiver
prefix.  It keeps the cutoff bank, all prior completed batches, the original
physical calls, the current diagnostic, and the inclusive decoder update.
The stage threshold is a local conclusion under the actual positive-call count.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`.

The exported theorem is fully proved internal mathematics.  It asserts no
probability, waiting-time bound, recovery success, stopped-event membership,
predictable task, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionReadyStream (startTime actualEpoch actualWindow)
open ReferencePrelaunchFollower (acceptedStart)
open ReferenceActivePhysicalStep (Selection)

namespace Bandits.Support.ReferenceFirstCollectionDownSecondPureBank

variable {p : ConstructorDimensions.Parameters}

private theorem constant_batch_map_length
    {α : Type} (batches : List (List α)) (q : ℕ)
    (hsize : ∀ batch ∈ batches, batch.length = q) :
    batches.map List.length = List.replicate batches.length q := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      have hb := hsize batch (by simp)
      have hrest : ∀ b ∈ rest, b.length = q := by
        intro b hbmem
        exact hsize b (by simp [hbmem])
      simp only [List.map_cons, List.length_cons, hb, ih hrest]
      have hrep : List.replicate (rest.length + 1) q =
          q :: List.replicate rest.length q := by
        rw [Nat.add_one, List.replicate_succ]
      simpa [Nat.add_comm] using hrep.symm

private theorem constant_batch_flatten_length
    {α : Type} (batches : List (List α)) (q : ℕ)
    (hsize : ∀ batch ∈ batches, batch.length = q) :
    batches.flatten.length = batches.length * q := by
  induction batches with
  | nil => simp
  | cons batch rest ih =>
      have hb := hsize batch (by simp)
      have hrest : ∀ b ∈ rest, b.length = q := by
        intro b hbmem
        exact hsize b (by simp [hbmem])
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        hb, ih hrest]
      rw [Nat.add_mul]
      omega

private theorem replicate_append_length
    {α : Type} (x : α) (m n : ℕ) :
    List.replicate (m + n) x = List.replicate m x ++ List.replicate n x :=
  List.replicate_add m n x

private theorem run_chunks_exact
    (p : ConstructorDimensions.Parameters)
    (trace : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (chunks remainder : ℕ)
    (hremainder : remainder < AffineBatchDecoder.quota p)
    (hinitial : initial.pending.length < AffineBatchDecoder.quota p)
    (hcompleted : ∀ batch ∈ initial.completed,
      batch.length = AffineBatchDecoder.quota p)
    (hcount : initial.pending.length +
      (AffineBatchDecoder.positives p trace rounds).length =
        chunks * AffineBatchDecoder.quota p + remainder) :
    let final := AffineBatchDecoder.run p trace rounds initial
    final.pending =
        (initial.pending ++ AffineBatchDecoder.positives p trace rounds).drop
          (chunks * AffineBatchDecoder.quota p) ∧
      final.completed = initial.completed ++
        (List.replicate chunks (AffineBatchDecoder.quota p)).splitLengths
          ((initial.pending ++ AffineBatchDecoder.positives p trace rounds).take
            (chunks * AffineBatchDecoder.quota p)) := by
  classical
  let q := AffineBatchDecoder.quota p
  let positives := AffineBatchDecoder.positives p trace rounds
  let sourceEntries := initial.pending ++ positives
  let final := AffineBatchDecoder.run p trace rounds initial
  have hspec := AffineBatchDecoder.run_spec p trace rounds initial hinitial hcompleted
  have hfinalCompleted : ∀ batch ∈ final.completed, batch.length = q := by
    simpa only [final, q] using hspec.2.1
  have hinitialFlat := constant_batch_flatten_length initial.completed q hcompleted
  have hfinalFlat := constant_batch_flatten_length final.completed q hfinalCompleted
  have hcollected : final.completed.flatten ++ final.pending =
      initial.completed.flatten ++ sourceEntries := by
    simpa only [final, positives, sourceEntries, AffineBatchDecoder.collected,
      List.append_assoc] using hspec.2.2
  have hlength : final.completed.length * q + final.pending.length =
      initial.completed.length * q + (initial.pending.length + positives.length) := by
    have h := congrArg List.length hcollected
    simpa [sourceEntries, List.length_append, hfinalFlat, hinitialFlat] using h
  have hnormalized : final.completed.length * q + final.pending.length =
      (initial.completed.length + chunks) * q + remainder := by
    calc
      _ = initial.completed.length * q +
          (initial.pending.length + positives.length) := hlength
      _ = initial.completed.length * q + (chunks * q + remainder) := by
        rw [hcount]
      _ = (initial.completed.length + chunks) * q + remainder := by
        rw [Nat.add_mul]
        omega
  have hfinalPending : final.pending.length = remainder := by
    have hmod := congrArg (fun x : ℕ => x % q) hnormalized
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod] at hmod
    change final.pending.length % q = remainder % q at hmod
    rw [Nat.mod_eq_of_lt (by simpa only [final] using hspec.1),
      Nat.mod_eq_of_lt hremainder] at hmod
    exact hmod
  have hfinalCompletedLength : final.completed.length =
      initial.completed.length + chunks := by
    have hproducts := Nat.add_right_cancel (by
      simpa only [hfinalPending] using hnormalized)
    exact Nat.eq_of_mul_eq_mul_right (AffineBatchDecoder.quota_pos p) hproducts
  let boundary := chunks * q
  have hfinalFlatLength : final.completed.flatten.length =
      (initial.completed.length + chunks) * q := by
    rw [hfinalFlat, hfinalCompletedLength]
  have hinitialFlatLength : initial.completed.flatten.length =
      initial.completed.length * q := hinitialFlat
  have hindex : (initial.completed.length + chunks) * q =
      initial.completed.length * q + boundary := by
    dsimp [boundary]
    rw [Nat.add_mul]
  let outputChunks :=
    (List.replicate chunks q).splitLengths (sourceEntries.take boundary)
  have hsourceLength : boundary ≤ sourceEntries.length := by
    have hlengthSource : sourceEntries.length = chunks * q + remainder := by
      dsimp [sourceEntries]
      rw [List.length_append]
      simpa only [q] using hcount
    rw [hlengthSource]
    dsimp [boundary]
    omega
  have hreplicateSum : (List.replicate chunks q).sum = boundary := by
    simp [List.sum_replicate, boundary]
  have htakeLength : (sourceEntries.take boundary).length = boundary :=
    List.length_take_of_le hsourceLength
  have hchunksSum : (List.replicate chunks q).sum ≤
      (sourceEntries.take boundary).length := by
    rw [hreplicateSum, htakeLength]
  have hchunksFlat : outputChunks.flatten = sourceEntries.take boundary :=
    List.flatten_splitLengths (sourceEntries.take boundary)
      (List.replicate chunks q) (by rw [htakeLength, hreplicateSum])
  have hchunksLengths : outputChunks.map List.length = List.replicate chunks q :=
    List.map_splitLengths_length _ _ hchunksSum
  have hdrop : final.pending = sourceEntries.drop boundary := by
    have hdropAll := congrArg (fun xs : List _ => xs.drop
      ((initial.completed.length + chunks) * q)) hcollected
    have hleft : (final.completed.flatten ++ final.pending).drop
        ((initial.completed.length + chunks) * q) = final.pending := by
      rw [← hfinalFlatLength, List.drop_append_length]
    rw [hleft, List.drop_append] at hdropAll
    have hOldDrop : initial.completed.flatten.drop
        ((initial.completed.length + chunks) * q) = [] := by
      apply List.drop_eq_nil_of_le
      rw [hindex, hinitialFlatLength]
      omega
    have hdifference :
        (initial.completed.length + chunks) * q -
          initial.completed.flatten.length = boundary := by
      rw [hindex, hinitialFlatLength]
      exact Nat.add_sub_cancel_left _ _
    rw [hOldDrop, hdifference, List.nil_append] at hdropAll
    exact hdropAll
  have hsourceDecomposition : sourceEntries =
      sourceEntries.take boundary ++ sourceEntries.drop boundary :=
    (List.take_append_drop boundary sourceEntries).symm
  have hflatFinal : final.completed.flatten =
      initial.completed.flatten ++ sourceEntries.take boundary := by
    have hcollectedDrop : final.completed.flatten ++ sourceEntries.drop boundary =
        initial.completed.flatten ++ sourceEntries := by
      simpa only [hdrop] using hcollected
    have hdecomp : initial.completed.flatten ++ sourceEntries =
        (initial.completed.flatten ++ sourceEntries.take boundary) ++
          sourceEntries.drop boundary := by
      calc
        initial.completed.flatten ++ sourceEntries =
            initial.completed.flatten ++
              (sourceEntries.take boundary ++ sourceEntries.drop boundary) :=
          congrArg (List.append initial.completed.flatten) hsourceDecomposition
        _ = (initial.completed.flatten ++ sourceEntries.take boundary) ++
              sourceEntries.drop boundary := by rw [List.append_assoc]
    apply List.append_left_injective (sourceEntries.drop boundary)
    calc
      final.completed.flatten ++ sourceEntries.drop boundary =
          initial.completed.flatten ++ sourceEntries := hcollectedDrop
      _ = (initial.completed.flatten ++ sourceEntries.take boundary) ++
          sourceEntries.drop boundary := hdecomp
  have hmapFinal : final.completed.map List.length =
      (initial.completed ++ outputChunks).map List.length := by
    calc
      final.completed.map List.length = List.replicate final.completed.length q :=
        constant_batch_map_length final.completed q hfinalCompleted
      _ = List.replicate (initial.completed.length + chunks) q := by
        rw [hfinalCompletedLength]
      _ = List.replicate initial.completed.length q ++ List.replicate chunks q :=
        replicate_append_length q initial.completed.length chunks
      _ = initial.completed.map List.length ++ outputChunks.map List.length := by
        rw [constant_batch_map_length initial.completed q hcompleted, hchunksLengths]
      _ = (initial.completed ++ outputChunks).map List.length := by
        simp only [List.map_append]
  have hchunksEq : final.completed = initial.completed ++ outputChunks := by
    apply (List.eq_iff_flatten_eq).2
    refine ⟨?_, hmapFinal⟩
    simpa only [List.flatten_append, hchunksFlat] using hflatFinal
  refine ⟨?_, hchunksEq⟩
  simpa only [final, sourceEntries, positives, boundary, q] using hdrop

/-- Administrative total extension for the existing decoder API.
`actual_calls_trace_on` identifies all four fields at every consumed physical
date; the empty-list value is never used by the replay. -/
private def actualCallsTraceAux
    (p : ConstructorDimensions.Parameters) :
    List (ReferenceFollowerDownDecoderReplay.Call p) → Fin p.T →
      AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)
  | [], _ => ⟨false, false, ⟨0, 0⟩, 0⟩
  | call :: rest, time =>
      if call.1 = time then call.2 else actualCallsTraceAux p rest time

private def actualCallsTrace (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p)) :
    AffineBatchDecoder.Trace p :=
  actualCallsTraceAux p calls

private theorem actualCallsTraceAux_eq
    (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (time : Fin p.T)
    (input : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p))
    (hnodup : (calls.map Prod.fst).Nodup)
    (hmem : (time, input) ∈ calls) :
    actualCallsTraceAux p calls time = input := by
  induction calls with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        simp [actualCallsTraceAux]
      · have hheadNe : head.1 ≠ time := by
          intro heq
          apply hnodup.1
          exact List.mem_map.mpr ⟨(time, input), htail, by simp [heq]⟩
        simp only [actualCallsTraceAux, ite_eq_right hheadNe]
        exact ih hnodup.2 htail

private theorem actual_positive_entries_eq
    (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (trace : AffineBatchDecoder.Trace p)
    (htrace : ∀ call ∈ calls, trace call.1 = call.2) :
    ReferenceFollowerDownDecoderReplay.positiveCallEntries calls =
      AffineBatchDecoder.positives p trace (calls.map Prod.fst) := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
      have hcall := htrace call (by simp)
      have htail : ∀ c ∈ rest, trace c.1 = c.2 := by
        intro c hc
        exact htrace c (by simp [hc])
      have hpositive :
          AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 =
            AffineBatchDecoder.positiveAt p trace call.1 := by
        unfold AffineBatchDecoder.positiveAt AffineBatchDecoder.entry
        rw [← hcall]
        rfl
      change ReferenceFollowerDownDecoderReplay.positiveCallEntries (call :: rest) =
        AffineBatchDecoder.positives p trace (call.1 :: rest.map Prod.fst)
      rw [AffineBatchDecoder.positives_cons]
      change
        AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 ++
          ReferenceFollowerDownDecoderReplay.positiveCallEntries rest =
        AffineBatchDecoder.positiveAt p trace call.1 ++
          AffineBatchDecoder.positives p trace (rest.map Prod.fst)
      rw [hpositive, ih htail]

private theorem actual_fold_eq_run
    (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (trace : AffineBatchDecoder.Trace p)
    (htrace : ∀ call ∈ calls, trace call.1 = call.2) :
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls initial =
      AffineBatchDecoder.run p trace (calls.map Prod.fst) initial := by
  induction calls generalizing initial with
  | nil => rfl
  | cons call rest ih =>
      have hcall := htrace call (by simp)
      have htail : ∀ c ∈ rest, trace c.1 = c.2 := by
        intro c hc
        exact htrace c (by simp [hc])
      have hstep :
          ReferenceFollowerDownDecoderReplay.replayDownCall initial call =
            AffineBatchDecoder.step p trace initial call.1 := by
        unfold ReferenceFollowerDownDecoderReplay.replayDownCall
        have hdecode := ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input
          p trace (ActiveFollowerDownAcceptance.currentInputExtension p call.2)
          initial call.1 hcall
        simpa only [AffineBatchDecoder.decodeStep] using
          (congrArg Prod.fst hdecode).symm
      simp only [ReferenceFollowerDownDecoderReplay.foldDownCalls,
        List.foldl_cons, AffineBatchDecoder.run, List.map_cons, hstep]
      exact ih _ htail

private theorem actual_calendar_nodup
    (p : ConstructorDimensions.Parameters) (start count : ℕ)
    (times : List (Fin p.T))
    (htimes : times.map Fin.val = ReferenceActivePhysicalHorizon.calendar start count) :
    times.Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [htimes]
  simpa only [ReferenceActivePhysicalHorizon.calendar] using
    (List.nodup_range' : (List.range' start count 1).Nodup)

private theorem actual_calls_trace_on
    (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (start count : ℕ)
    (htimes : (calls.map Prod.fst).map Fin.val =
      ReferenceActivePhysicalHorizon.calendar start count) :
    ∀ call ∈ calls, actualCallsTrace p calls call.1 = call.2 := by
  intro call hcall
  have hnd : (calls.map Prod.fst).Nodup :=
    actual_calendar_nodup p start count (calls.map Prod.fst) htimes
  exact actualCallsTraceAux_eq p calls call.1 call.2 hnd hcall

/-- Exact positive provenance through the actual call adapter, including the
prepared-to-physical row, date, selected follower, and own observation. -/
private theorem actual_positive_hashes
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hhash : ∀ record ∈ records,
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
      0 < (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val →
      AffineChannelLaw.affineHash
        (ReferenceDownPhysicalHashRule.originalDownSample record.input) word = 1) :
    ∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records,
      AffineChannelLaw.affineHash entry.sample word = 1 := by
  classical
  intro entry hentry
  change entry ∈ (ReferenceFollowerDownDecoderReplay.actualDownCalls i records).flatMap _ at hentry
  obtain ⟨call, hcall, hpositive⟩ := List.mem_flatMap.mp hentry
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  cases hconfiguration : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
  | dagger =>
      simp only [ReferenceFollowerDownDecoderReplay.actualDownCall, hconfiguration] at hcall
      cases hcall
  | ordinary choice memory =>
      rw [ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
        record i choice memory hconfiguration] at hcall
      cases Option.some.inj hcall
      change entry ∈ (if AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice)
        then [⟨ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ((ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i).2
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)).2 (0, i)⟩]
        else []) at hpositive
      split at hpositive
      · rename_i heligible
        have hlocal := (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff
          record i choice).mp heligible
        have halign := record.output.preparation.follower_alignment i
        have hdown : ActiveFollowerDownAcceptance.downSelected p i
            record.input.row record.input.time := by
          simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
            ReferenceFollowerDownDecoderReplay.preparedChoiceTime, halign.1,
            halign.2.2.1] using hlocal.1
        have hentryEq := List.mem_singleton.mp hpositive
        rw [hentryEq]
        change AffineChannelLaw.affineHash
          (((ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i).2
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)).2 (0, i)) word = 1
        have h := hhash record hrecord hdown hlocal.2.2
        have hsample :
            ((ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i).2
              (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)).2 (0, i) =
              ReferenceDownPhysicalHashRule.originalDownSample record.input := by
          rw [ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
            ReferenceFollowerDownDecoderReplay.preparedChoiceTime, halign.1, halign.2.2.1,
            ReferenceDownPhysicalHashRule.originalDownSample,
            ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdown.2]
        exact (congrArg (fun sample => AffineChannelLaw.affineHash sample word) hsample).trans h
      · exact False.elim (List.not_mem_nil hpositive)

private theorem run_before_second
    (p : ConstructorDimensions.Parameters) (trace : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hk : initial.pending.length < AffineBatchDecoder.quota p)
    (hc : ∀ batch ∈ initial.completed, batch.length = AffineBatchDecoder.quota p)
    (hn : (AffineBatchDecoder.positives p trace rounds).length =
      AffineBatchDecoder.quota p - initial.pending.length + AffineBatchDecoder.quota p - 1) :
    let positives := AffineBatchDecoder.positives p trace rounds
    AffineBatchDecoder.run p trace rounds initial =
      ⟨positives.drop (AffineBatchDecoder.quota p - initial.pending.length),
        initial.completed ++
          [initial.pending ++ positives.take (AffineBatchDecoder.quota p - initial.pending.length)]⟩ := by
  let q := AffineBatchDecoder.quota p
  let positives := AffineBatchDecoder.positives p trace rounds
  have hq : 0 < q := AffineBatchDecoder.quota_pos p
  have hsum : initial.pending.length + positives.length = 1 * q + (q - 1) := by
    change positives.length = q - initial.pending.length + q - 1 at hn
    omega
  obtain ⟨hpen, hcomp⟩ := run_chunks_exact p trace rounds initial 1 (q - 1)
    (by omega) hk hc hsum
  have hsourceTake : (initial.pending ++ positives).take q =
      initial.pending ++ positives.take (q - initial.pending.length) := by
    rw [List.take_append, List.take_of_length_le (Nat.le_of_lt hk)]
  have hpending : (AffineBatchDecoder.run p trace rounds initial).pending =
      positives.drop (q - initial.pending.length) := by
    rw [hpen, Nat.one_mul]
    change (initial.pending ++ positives).drop q = _
    rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_of_lt hk), List.nil_append]
  have hcompleted : (AffineBatchDecoder.run p trace rounds initial).completed =
      initial.completed ++ [initial.pending ++ positives.take (q - initial.pending.length)] := by
    rw [hcomp, Nat.one_mul]
    change initial.completed ++ (List.replicate 1 q).splitLengths
      ((initial.pending ++ positives).take q) = _
    simp only [List.replicate_one, List.splitLengths_cons, List.splitLengths_nil,
      List.take_take, Nat.min_self]
    rw [hsourceTake]
  have heta : AffineBatchDecoder.run p trace rounds initial =
      ⟨(AffineBatchDecoder.run p trace rounds initial).pending,
        (AffineBatchDecoder.run p trace rounds initial).completed⟩ := rfl
  rw [hpending, hcompleted] at heta
  exact heta

/-- Regroup the existing decoder's quota update without discarding old completed
batches. Physical replay and the local count are supplied by the actual root. -/
private theorem second_bank_update
    (p : ConstructorDimensions.Parameters) (trace : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (initial bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (current : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)) (time : Fin p.T)
    (hk : initial.pending.length < AffineBatchDecoder.quota p)
    (hc : ∀ batch ∈ initial.completed, batch.length = AffineBatchDecoder.quota p)
    (hbank : bank = AffineBatchDecoder.run p trace rounds initial)
    (hn : (AffineBatchDecoder.positives p trace rounds).length =
      AffineBatchDecoder.quota p - initial.pending.length + AffineBatchDecoder.quota p - 1)
    (heligible : AffineBatchDecoder.eligible current) :
    let positives := AffineBatchDecoder.positives p trace rounds
    let nextEntry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) := ⟨time, current.sample⟩
    let first := initial.pending ++ positives.take (AffineBatchDecoder.quota p - initial.pending.length)
    let second := positives.drop (AffineBatchDecoder.quota p - initial.pending.length) ++ [nextEntry]
    first.length = AffineBatchDecoder.quota p ∧
      second.length = AffineBatchDecoder.quota p ∧
      AffineBatchDecoder.decodeStep p
        (ActiveFollowerDownAcceptance.currentInputExtension p current) bank time =
        (⟨[], initial.completed ++ [first, second]⟩, AffineBatchDecoder.batchOutput second) := by
  let q := AffineBatchDecoder.quota p
  let positives := AffineBatchDecoder.positives p trace rounds
  have hq : 0 < q := AffineBatchDecoder.quota_pos p
  change positives.length = q - initial.pending.length + q - 1 at hn
  have htake : q - initial.pending.length ≤ positives.length := by omega
  have hprefix := run_before_second p trace rounds initial hk hc hn
  rw [← hbank] at hprefix
  have hpen : bank.pending = positives.drop (q - initial.pending.length) :=
    congrArg AffineBatchDecoder.State.pending hprefix
  have hcomp : bank.completed = initial.completed ++
      [initial.pending ++ positives.take (q - initial.pending.length)] :=
    congrArg AffineBatchDecoder.State.completed hprefix
  have hquota : bank.pending.length + 1 = q := by
    rw [hpen, List.length_drop]
    omega
  have hupdate := AffineBatchDecoder.decodeStep_complete p
    (ActiveFollowerDownAcceptance.currentInputExtension p current) bank time heligible hquota
  rw [hpen, hcomp] at hupdate
  refine ⟨?_, ?_, ?_⟩
  · change (initial.pending ++ positives.take (q - initial.pending.length)).length = q
    simp only [List.length_append, List.length_take, Nat.min_eq_left htake]
    change initial.pending.length < q at hk
    omega
  · change (positives.drop (q - initial.pending.length) ++
      [(⟨time, current.sample⟩ : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))]).length = q
    simp only [List.length_append, List.length_drop, List.length_singleton]
    omega
  · simpa only [q, positives, AffineBatchDecoder.entry,
      ActiveFollowerDownAcceptance.currentInputExtension, List.append_assoc,
      List.singleton_append] using hupdate

/-- Construct the administrative trace from the physical call calendar inside
this lemma; no caller supplies a trace or a trace-matching law. -/
private theorem calls_second_bank_update
    (p : ConstructorDimensions.Parameters)
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (initial bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (current : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)) (time : Fin p.T)
    (start count : ℕ)
    (hk : initial.pending.length < AffineBatchDecoder.quota p)
    (hc : ∀ batch ∈ initial.completed, batch.length = AffineBatchDecoder.quota p)
    (hcalendar : (calls.map Prod.fst).map Fin.val =
      ReferenceActivePhysicalHorizon.calendar start count)
    (hbank : bank = ReferenceFollowerDownDecoderReplay.foldDownCalls calls initial)
    (hn : (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length =
      AffineBatchDecoder.quota p - initial.pending.length + AffineBatchDecoder.quota p - 1)
    (heligible : AffineBatchDecoder.eligible current) :
    let positives := ReferenceFollowerDownDecoderReplay.positiveCallEntries calls
    let nextEntry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) := ⟨time, current.sample⟩
    let first := initial.pending ++ positives.take (AffineBatchDecoder.quota p - initial.pending.length)
    let second := positives.drop (AffineBatchDecoder.quota p - initial.pending.length) ++ [nextEntry]
    first.length = AffineBatchDecoder.quota p ∧
      second.length = AffineBatchDecoder.quota p ∧
      AffineBatchDecoder.decodeStep p
        (ActiveFollowerDownAcceptance.currentInputExtension p current) bank time =
        (⟨[], initial.completed ++ [first, second]⟩, AffineBatchDecoder.batchOutput second) := by
  let trace := actualCallsTrace p calls
  have htrace := actual_calls_trace_on p calls start count hcalendar
  have hpositives := actual_positive_entries_eq p calls trace htrace
  have hfold := actual_fold_eq_run p calls initial trace htrace
  have hbankRun := hbank.trans hfold
  have hnRun : (AffineBatchDecoder.positives p trace (calls.map Prod.fst)).length =
      AffineBatchDecoder.quota p - initial.pending.length + AffineBatchDecoder.quota p - 1 := by
    rw [← hpositives]
    exact hn
  have hupdate := second_bank_update p trace (calls.map Prod.fst) initial bank
    current time hk hc hbankRun hnRun heligible
  dsimp only at hupdate
  rw [← hpositives] at hupdate
  exact hupdate

private theorem actual_positive_take_succ
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : Fin records.length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration records[n.val] i =
      .ordinary choice memory)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i records[n.val].input.row records[n.val].input.time)
    (hstatus : choice.status = .unoccupied)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation records[n.val] i).val.val) :
    ReferenceFollowerDownDecoderReplay.actualDownPositives i (records.take (n.val + 1)) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i (records.take n.val) ++
        [⟨ReferenceFollowerDownDecoderReplay.preparedChoiceTime records[n.val] i,
          ((ReferenceFollowerDownDecoderReplay.preparedChoiceRow records[n.val] i).2
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime records[n.val] i)).2 (0, i)⟩] := by
  classical
  let record := records[n.val]
  let input := ActiveFollowerDownAcceptance.currentRoundInput p i
    (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
    (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice
  have halign := record.output.preparation.follower_alignment i
  have heligible : AffineBatchDecoder.eligible input := by
    apply (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff record i choice).mpr
    refine ⟨?_, hstatus, hpositive⟩
    simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
      ReferenceFollowerDownDecoderReplay.preparedChoiceTime, halign.1, halign.2.2.1] using hdown
  have hstep : AffineBatchDecoder.positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p input)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i) =
      [⟨ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i, input.sample⟩] := by
    change (if AffineBatchDecoder.eligible input then [_] else []) = _
    rw [ite_eq_left heligible]
    rfl
  rw [List.take_succ_eq_append_getElem n.isLt]
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil,
    ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary records[n.val] i choice memory hconfiguration]
  change ReferenceFollowerDownDecoderReplay.positiveCallEntries
      (ReferenceFollowerDownDecoderReplay.actualDownCalls i (records.take n.val) ++
        [(ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i, input)]) = _
  simp only [ReferenceFollowerDownDecoderReplay.positiveCallEntries, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, hstep]
  rfl

/-- Consistency is established before excluding the empty-solution case. -/
private theorem batch_solution_dichotomy
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hsolves : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) word) :
    AffineBatchDecoder.batchOutput batch = some word ∨
      (AffineBatchDecoder.batchOutput batch = none ∧ ∃ other, other ≠ word ∧
        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) other) := by
  classical
  cases hraw : AffineBatchDecoder.batchOutput batch with
  | none =>
      right
      refine ⟨rfl, ?_⟩
      have hnone : AffineBatchDecoder.solve (AffineBatchDecoder.samples batch) = none := hraw
      rcases (AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous _).mp hnone with
        hempty | ⟨u, v, hu, hv, huv⟩
      · exact False.elim (hempty word hsolves)
      · by_cases heq : u = word
        · exact ⟨v, fun h => huv (heq.trans h.symm), hv⟩
        · exact ⟨u, heq, hu⟩
  | some u =>
      left
      have hsome : AffineBatchDecoder.solve (AffineBatchDecoder.samples batch) = some u := hraw
      have heq := ((AffineBatchDecoder.solve_eq_some_iff _ u).mp hsome).2 word hsolves
      simp only [heq]

/-- Transfer strict physical chronology and original samples to the pure tail
including the current positive, rather than only to a final test. -/
private theorem tail_current_provenance
    (entries : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (current : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (skip : ℕ) (row : CompletePublicTable.CompleteRow p)
    (i : Fin (p.m - 1)) (lower upper : ℕ)
    (hpair : entries.Pairwise (fun a b => a.time.val < b.time.val))
    (htimes : ∀ e ∈ entries, lower ≤ e.time.val ∧ e.time.val < upper)
    (hsamples : ∀ e ∈ entries, e.sample = (row.2 e.time).2 (0, i))
    (hdate : current.time.val = upper)
    (hsample : current.sample = (row.2 current.time).2 (0, i))
    (hspan : lower ≤ upper) :
    (entries.drop skip ++ [current]).Pairwise (fun a b => a.time.val < b.time.val) ∧
      (∀ e ∈ entries.drop skip ++ [current], lower ≤ e.time.val ∧ e.time.val ≤ upper) ∧
      (∀ e ∈ entries.drop skip ++ [current], e.sample = (row.2 e.time).2 (0, i)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hpair.drop, by simp, ?_⟩
    intro earlier hearlier later hlater
    have hlaterEq := List.mem_singleton.mp hlater
    subst later
    rw [hdate]
    exact (htimes earlier (List.mem_of_mem_drop hearlier)).2
  · intro e he
    rcases List.mem_append.mp he with hentry | hcurrent
    · have h := htimes e (List.mem_of_mem_drop hentry)
      exact ⟨h.1, Nat.le_of_lt h.2⟩
    · have heq := List.mem_singleton.mp hcurrent
      subst e
      exact ⟨hdate.symm ▸ hspan, Nat.le_of_eq hdate⟩
  · intro e he
    rcases List.mem_append.mp he with hentry | hcurrent
    · exact hsamples e (List.mem_of_mem_drop hentry)
    · exact (List.mem_singleton.mp hcurrent).symm ▸ hsample

/-- Interpret the actual raw comparison only after the same literal batch has
its fixed-word solution. The successful branch asserts local acceptance only. -/
private theorem cut_solution_dichotomy
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (time : Fin p.T) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hsolves : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch)
      (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hraw : cut.raw = AffineBatchDecoder.batchOutput batch)
    (hexpected : cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hparse : cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw)
    (hparseWord : ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) = some (payload.downRecord i))
    (hlocal : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time choice
      (some (payload.downRecord i)))
    (haccept : cut.ordinaryAcceptance ↔
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time choice cut.ordinaryParse)
    (hcomparison : cut.rawComparison = some (decide (cut.raw = cut.expectedWord))) :
    (cut.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
      cut.ordinaryParse = some (payload.downRecord i) ∧
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time choice cut.ordinaryParse ∧
      cut.ordinaryAcceptance) ∨
    (cut.raw = none ∧ ∃ other, other ≠ CoordinatorLocalArmChoice.storedDownFlatWord payload i ∧
      AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) other ∧
      cut.rawComparison = some false) := by
  classical
  rcases batch_solution_dichotomy batch _ hsolves with hsome | ⟨hnone, other, hne, hother⟩
  · left
    have hrawWord := hraw.trans hsome
    have hparsed : cut.ordinaryParse = some (payload.downRecord i) := by
      rw [hparse, hrawWord]
      exact hparseWord
    have hlocalActual :
        ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time choice cut.ordinaryParse := by
      rw [hparsed]
      exact hlocal
    exact ⟨hrawWord, hparsed, hlocalActual, haccept.mpr hlocalActual⟩
  · right
    refine ⟨hraw.trans hnone, other, hne, hother, ?_⟩
    rw [hcomparison, hraw, hnone, hexpected]
    rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (source : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (count : ℕ)
  (hcross : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
  (hspan : ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
  (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)

local notation "s" => startTime (rate := rate) source rewards C_star C_h
local notation "Q" => AffineBatchDecoder.quota p

/-- The actual unaccepted first-collection DOWN prefix has a locally selected
second pure batch, and its inclusive deciding cut is exactly the ordinary
decoder's second decision. The same dispatcher and payload retain every
checked receiver call through this input and the inherited cutoff-bank provenance. -/
theorem actual_collection_unaccepted_down_second_pure_bank :
    let w := List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records);
    let B := ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records w;
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let P0 := out.payload
      out.window = B ∧ P0.sigma.val = s ∧
      (∀ i, (P0.downRecord i).val.sigma = s + 1 ∧
        (P0.downRecord i).val.q = 0) ∧
      ∀ (n : Fin out.ell) (hn : 0 < n.val)
        (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
          .ordinary before memory →
        before.lastDown = none →
        (∀ k : Fin (n.val + 1),
          let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
            out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
              (Nat.lt_of_lt_of_le n.isLt out.withinWindow))
          ∃ prior priorMemory,
            record.input.state.followers i = .ordinary prior priorMemory ∧ prior.lastDown = none ∧
            (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
              ∃ (selected : Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P0 ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                (record.output.preparation.followers.followers i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let cut := ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView i record.input.row record.input.time own rate choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
                (record.output.followers i).downInput = some choice ∧
                (record.output.followers i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i)) = some (P0.downRecord i) ∧
                acceptedStart choice = 0 ∧ (P0.downRecord i).val.sigma = s + 1 ∧
                (P0.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (P0.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) = 1))) ∧
        ∃ hBlen : 0 < (B).length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          ((B)[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          (let W0 := cutoffState.downBatch
            let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
            before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
            AffineBatchDecoder.collected before.downBatch =
              AffineBatchDecoder.collected W0 ++ P ∧
            W0.pending.length < Q ∧
            (∀ entry ∈ W0.pending, entry.time.val < s + w) ∧
            (C.map Prod.fst).map Fin.val =
              ReferenceActivePhysicalHorizon.calendar (s + w) n.val ∧
            P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ P, s + w ≤ entry.time.val ∧ entry.time.val < s + w + n.val) ∧
            (∀ entry ∈ P, entry.sample =
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                entry.time).2 (0, i)) ∧
            (∀ completed ∈ W0.completed,
              completed.length = Q) ∧
            (AffineBatchDecoder.collected W0).Pairwise
              (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < s + w) ∧
            before.downBatch.completed =
              (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed) ∧
          let W0 := cutoffState.downBatch
          let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i ((B).take n.val)
          ∀ (hdown : ActiveFollowerDownAcceptance.downSelected p i
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.row
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time),
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
            ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
            ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              let record : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) :=
                B[n.val]'(by
                  have hwindow : out.window = B := out.windowIsActual
                  rw [← hwindow]
                  exact Nat.lt_of_lt_of_le n.isLt out.withinWindow)
              let prep := record.output.preparation.followers.followers i
              let own := record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let fixedWord := CoordinatorLocalArmChoice.storedDownFlatWord P0 i
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((B).take n.val)
              let currentEntry : AffineBatchDecoder.Entry p.T
                  (AffineBatchDecoder.width p) :=
                ⟨prep.time, (prep.row.2 prep.time).2 (0, i)⟩
              prep.configuration = .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              (record.output.followers i).downInput = some choice ∧
              (record.output.followers i).down = some cut ∧
              cut.expectedWord = some fixedWord ∧
              cut.rawComparison.isSome = true ∧
              cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
              logged = choice ∧
              logged.downBatch = before.downBatch ∧
              logged.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
              cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                p i record.input.row record.input.time own rate choice).2 ∧
              (∀ (hpositive : 0 < own.val.val),
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  ((B).take (n.val + 1))).length =
                    Q - W0.pending.length + Q →
                ∃ contaminatedFirst pureSecond :
                    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                  contaminatedFirst = W0.pending ++ P.take (Q - W0.pending.length) ∧
                  pureSecond = P.drop (Q - W0.pending.length) ++ [currentEntry] ∧
                  contaminatedFirst.length = Q ∧ pureSecond.length = Q ∧
                  (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 =
                    ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩ ∧
                  cut.raw = AffineBatchDecoder.batchOutput pureSecond ∧
                  (∀ entry ∈ pureSecond,
                    AffineChannelLaw.affineHash entry.sample fixedWord = 1) ∧
                  AffineBatchDecoder.satisfies
                    (AffineBatchDecoder.samples pureSecond) fixedWord ∧
                  pureSecond.Pairwise (fun earlier later =>
                    earlier.time.val < later.time.val) ∧
                  (∀ entry ∈ pureSecond,
                    s + w ≤ entry.time.val ∧
                    entry.time.val ≤ s + w + n.val) ∧
                  (∀ entry ∈ pureSecond,
                    entry.sample =
                      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex
                        p source)).2 entry.time).2 (0, i)) ∧
                  ((cut.raw = some fixedWord ∧
                    cut.ordinaryParse = some (P0.downRecord i) ∧
                    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                      record.input.time choice cut.ordinaryParse ∧
                    cut.ordinaryAcceptance) ∨
                   (cut.raw = none ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      cut.rawComparison = some false))) := by
  classical
  have hshortBank : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count := by
    simpa [actualEpoch] using hshort
  have hBank := ReferenceFirstCollectionDownBankHistory.actual_cutoff_retained_down_diagnostic
    rate source rewards C_star C_h count hcross hspan hshortBank
  dsimp only
  let w := List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records)
  let B := ReferenceCollectionPhaseHistory.collectionWindow
    (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records w
  let receiver :=
    ReferenceFirstCollectionUnacceptedDownReceiverPrefix.actual_collection_unaccepted_down_receiver_prefix
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨d, hReceiver⟩ := receiver
  let out := d.stream
  let P0 := out.payload
  refine ⟨d, ?_⟩
  rcases hReceiver with ⟨hwindow, hsigma, hrecords, hprefix⟩
  have hwindowCanonical : out.window = B := by
    simpa [out, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hwindow
  refine ⟨hwindowCanonical, hsigma, hrecords, ?_⟩
  intro n hn i before memory hfi hnone
  obtain ⟨_hpending, _hnoAccepted, hcalls⟩ := hprefix n hn i before memory hfi hnone
  refine ⟨hcalls, ?_⟩
  have hnWindow : n.val < out.window.length :=
    Nat.lt_of_lt_of_le n.isLt out.withinWindow
  have hwindowLength : out.window.length = B.length := congrArg List.length hwindowCanonical
  have hnB : n.val < B.length := by rw [← hwindowLength]; exact hnWindow
  let nB : Fin (B).length := ⟨n.val, hnB⟩
  have hwindow' : d.stream.window = B := by simpa [out] using hwindowCanonical
  have hrecordAtN : d.stream.window[n.val]'hnWindow = (B)[n.val]'hnB := by
    exact getElem_congr_coll hwindow'
  have hfiB : ((B)[n.val]'hnB).input.state.followers i = .ordinary before memory := by
    rw [← hrecordAtN]
    exact hfi
  have hHlocal := hBank nB i before memory hfiB
  rcases hHlocal with ⟨hBlen, cutoffState, cutoffMemory, hcutOrd,
    hbankPrefix, hprepTime, hprepRow, hendpoint, hdiagnostic⟩
  let W0 := cutoffState.downBatch
  have hbankOutput := hbankPrefix
  rcases hbankPrefix with
    ⟨hbefore, hcollected, hWk, hpendingOld, hcalendar, hpositivePair,
      hpositiveTime, hsamples, hcompletedSize, hW0Pair, hW0Times,
      hcompletedReplay⟩
  change W0.pending.length < Q at hWk
  change ∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val),
    s + w ≤ entry.time.val ∧ entry.time.val < s + w + n.val at hpositiveTime
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutOrd, hbankOutput, ?_⟩
  intro hdown
  let record := (B)[n.val]'hnB
  have hdownB : ActiveFollowerDownAcceptance.downSelected p i record.input.row
      record.input.time := by
    change ActiveFollowerDownAcceptance.downSelected p i (B[n.val]'hnB).input.row
      (B[n.val]'hnB).input.time
    rw [← hrecordAtN]
    exact hdown
  let recordAtStream := d.stream.window[n.val]'hnWindow
  have hrecordEq : recordAtStream = record := hrecordAtN
  let prep := record.output.preparation.followers.followers i
  let own := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let currentEntry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
    ⟨prep.time, (prep.row.2 prep.time).2 (0, i)⟩
  let fixedWord := CoordinatorLocalArmChoice.storedDownFlatWord P0 i
  let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i ((B).take n.val)
  let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i ((B).take n.val)
  have hcallAt := hcalls ⟨n.val, by omega⟩
  rcases hcallAt with ⟨prior, priorMemory, hprior, hpriorNone, hdownBranch⟩
  rcases hdownBranch hdown with
    ⟨selected, choice, choiceMemory, hselection, hpayload, hpendingChoice, hsent, hconfigR,
      hstatusR, hlastR, hdomainR, hloggingR, hdownInputR, hcutR,
      hregisterR, hdecoderR, hbufferR, hexpectedR, hcompSomeR, hrawR,
      hfilteredR, hparseR, hacceptIffR, hcomparisonR, houtcomeRejectR,
      houtcomeR, hparseWordR, hacceptedStartR, hsigmaR, htimeR,
      hlocalTestR, hhashCurrent⟩
  let cutAt : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) →
      ReferenceDownReception.ReferenceDownCutOutput p rate := fun physical =>
    ReferenceDownReception.referenceDownCut p
      physical.output.preparation.coordinator.downView i physical.input.row physical.input.time
      (physical.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice
  let cut := cutAt recordAtStream
  have hconfigLocal : prep.configuration = .ordinary choice choiceMemory := by
    have h : (recordAtStream.output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory := hconfigR
    rw [hrecordEq] at h
    exact h
  have hinputLocal : (record.output.followers i).downInput = some choice := by
    have h : (recordAtStream.output.followers i).downInput = some choice := hdownInputR
    rw [hrecordEq] at h
    exact h
  have hcutLocal : (record.output.followers i).down = some cut := by
    have h : (recordAtStream.output.followers i).down = some cut := hcutR
    rw [hrecordEq] at h
    exact h
  have hrawLocal : cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
      record.input.row record.input.time own rate choice).2 := by
    have h : cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
        recordAtStream.input.row recordAtStream.input.time
        (recordAtStream.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice).2 := hrawR
    rw [hrecordEq] at h
    exact h
  have hhashLocal : 0 < own.val.val → AffineChannelLaw.affineHash
      (ReferenceDownPhysicalHashRule.originalDownSample record.input) fixedWord = 1 := by
    have h : 0 < (recordAtStream.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val →
        AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample recordAtStream.input)
          fixedWord = 1 := hhashCurrent
    rw [hrecordEq] at h
    exact h
  have hlocalTest : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time
      choice (some (P0.downRecord i)) := by
    have h : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate recordAtStream.input.time
        choice (some (P0.downRecord i)) := hlocalTestR
    rw [hrecordEq] at h
    exact h
  have hacceptLocal : cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
      p rate record.input.time choice cut.ordinaryParse := by
    have h : cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
        p rate recordAtStream.input.time choice cut.ordinaryParse := hacceptIffR
    rw [hrecordEq] at h
    exact h
  have hcompSomeLocal : cut.rawComparison.isSome = true := hcompSomeR
  have hcompNe : cut.rawComparison ≠ none := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hcompSomeLocal
    rw [hb]
    simp
  have hHdiagnostic := hdiagnostic cut hcutLocal hcompNe
  rcases hHdiagnostic with
    ⟨choiceH, choiceMemoryH, logged, hprepFollowerH, hconfigH,
      hstatusH, hloggedStatusH, hdownInputH, hloggedBankH,
      hcutEqH, hsampleH, hrawH, hdecodeH, hcollectedH,
      hpositiveCollectedH, hzeroH, hpartialH, hcompleteH⟩
  have hchoiceEq : choice = choiceH := by
    have hEq := hconfigLocal.symm.trans hconfigH
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hEq).1
  subst choiceH
  have hloggedEq : logged = choice :=
    Option.some.inj (hdownInputH.symm.trans hinputLocal)
  have hloggedFold : logged.downBatch =
      ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 :=
    hloggedBankH.trans hbefore
  have htimeCurrent : prep.time.val = s + w + n.val := hprepTime
  refine ⟨choice, choiceMemory, logged, cut, ?_⟩
  refine ⟨hconfigLocal, hstatusR, hinputLocal, hcutLocal, hexpectedR,
    hcompSomeR, hcomparisonR, hloggedEq, hloggedBankH, hloggedFold, hrawLocal, ?_⟩
  intro hpositive hthreshold
  have hpositiveBank : 0 < own.val.val := hpositive
  have hpositiveThrough :
      ReferenceFollowerDownDecoderReplay.actualDownPositives i ((B).take (n.val + 1)) =
        P ++ [currentEntry] :=
    actual_positive_take_succ B nB i choice choiceMemory hconfigLocal hdownB hstatusR hpositiveBank
  have hcountCurrent : P.length = Q - W0.pending.length + Q - 1 := by
    have h := congrArg List.length hpositiveThrough
    rw [hthreshold, List.length_append, List.length_singleton] at h
    change Q - W0.pending.length + Q = P.length + 1 at h
    exact Nat.eq_sub_of_add_eq h.symm
  have hpositivePrefix : ∀ entry ∈ P,
      AffineChannelLaw.affineHash entry.sample fixedWord = 1 := by
    apply actual_positive_hashes ((B).take n.val) i fixedWord
    intro physical hphysical hdownPhysical hpositivePhysical
    obtain ⟨j, hj, hphysicalEq⟩ := List.mem_iff_getElem.mp hphysical
    have hjN : j < n.val := lt_of_lt_of_le hj (List.length_take_le _ _)
    have hjB : j < B.length := lt_trans hjN hnB
    have hphysicalB : physical = (B)[j]'hjB := by
      rw [← hphysicalEq]
      simp only [List.getElem_take]
    have hjOut : j < d.stream.window.length := by
      rw [hwindow']; exact hjB
    have hphysicalOut : d.stream.window[j]'hjOut = physical := by
      rw [hphysicalB]
      exact getElem_congr_coll hwindow'
    obtain ⟨priorJ, priorMemoryJ, hpriorJ, hnoneJ, hbranchJ⟩ := hcalls ⟨j, by omega⟩
    have hdownJ : ActiveFollowerDownAcceptance.downSelected p i
        (d.stream.window[j]'hjOut).input.row (d.stream.window[j]'hjOut).input.time := by
      rw [hphysicalOut]
      exact hdownPhysical
    obtain ⟨selectedJ, choiceJ, memoryJ, hselectionJ, hpayloadJ, hpendingJ, hsentJ,
      hconfigJ, hstatusJ, hlastJ, hdomainJ, hloggingJ, hdownInputJ, hcutJ,
      hregisterJ, hdecoderJ, hbufferJ, hexpectedJ, hcompJ, hrawJ, hfilteredJ,
      hparseJ, hacceptJ, hcomparisonJ, houtcomeJ, houtcome2J, hparseWordJ,
      hacceptedJ, hsigmaJ, htimeJ, hlocalJ, hhashJ⟩ := hbranchJ hdownJ
    have hhashAtJ :
        0 < ((d.stream.window[j]'hjOut).output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val →
        AffineChannelLaw.affineHash
          (ReferenceDownPhysicalHashRule.originalDownSample (d.stream.window[j]'hjOut).input)
          fixedWord = 1 := hhashJ
    rw [hphysicalOut] at hhashAtJ
    exact hhashAtJ hpositivePhysical
  have hpositiveAll : ∀ entry ∈ P.drop (Q - W0.pending.length) ++
      [currentEntry],
      AffineChannelLaw.affineHash entry.sample fixedWord = 1 := by
    intro entry hentry
    rcases List.mem_append.mp hentry with htail | hcurrent
    · exact hpositivePrefix entry (List.mem_of_mem_drop htail)
    · have heq := List.mem_singleton.mp hcurrent
      subst entry
      have hhash : AffineChannelLaw.affineHash
          (ReferenceDownPhysicalHashRule.originalDownSample record.input) fixedWord = 1 :=
        hhashLocal hpositive
      have hsampleCurrent : (prep.row.2 prep.time).2 (0, i) =
          ReferenceDownPhysicalHashRule.originalDownSample record.input := by
        have halign := record.output.preparation.follower_alignment i
        change (((record.output.preparation.followers.followers i).row).2
          (record.output.preparation.followers.followers i).time).2 (0, i) = _
        rw [halign.1, halign.2.2.1, ReferenceDownPhysicalHashRule.originalDownSample,
          ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdownB.2]
      change AffineChannelLaw.affineHash ((prep.row.2 prep.time).2 (0, i)) fixedWord = 1
      rw [hsampleCurrent]
      exact hhash
  have hpositiveSolve : AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples
        (P.drop (Q - W0.pending.length) ++
          [currentEntry])) fixedWord := by
    apply (AffineBatchDecoder.satisfies_iff_hashes _ _).2
    intro sample hsample
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hsample
    exact hpositiveAll entry hentry
  have hchoiceReplay : choice.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 := by
    rw [← hloggedEq]
    exact hloggedFold
  let currentAtInput := ActiveFollowerDownAcceptance.currentRoundInput p i
    record.input.row record.input.time own rate choice
  have heligibleCurrent : AffineBatchDecoder.eligible currentAtInput :=
    (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff
      p i record.input.row record.input.time own rate choice).mpr
        ⟨hdownB, hstatusR, hpositiveBank⟩
  have hentryPhysical :
      (⟨record.input.time, currentAtInput.sample⟩ :
        AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) = currentEntry := by
    dsimp only [currentAtInput, ActiveFollowerDownAcceptance.currentRoundInput, currentEntry, prep]
    have halign := record.output.preparation.follower_alignment i
    rw [halign.1, halign.2.2.1]
  have hupdate := calls_second_bank_update p C W0 choice.downBatch
    currentAtInput record.input.time (s + w) n.val hWk hcompletedSize hcalendar
    hchoiceReplay hcountCurrent heligibleCurrent
  dsimp only at hupdate
  have hpositiveEntries : ReferenceFollowerDownDecoderReplay.positiveCallEntries C = P := rfl
  rw [hpositiveEntries, hentryPhysical] at hupdate
  rcases hupdate with ⟨hfirstLength, hsecondLength, hdecoded⟩
  have hdecodeBank :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
        record.input.time own rate choice).1 =
        ⟨[], W0.completed ++
          [W0.pending ++ P.take (Q - W0.pending.length),
            P.drop (Q - W0.pending.length) ++ [currentEntry]]⟩ :=
    congrArg Prod.fst hdecoded
  have hrawBatch : cut.raw = AffineBatchDecoder.batchOutput
      (P.drop (Q - W0.pending.length) ++ [currentEntry]) :=
    hrawLocal.trans (congrArg Prod.snd hdecoded)
  have hsampleCurrent : currentEntry.sample =
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
        currentEntry.time).2 (0, i) := by
    change (prep.row.2 prep.time).2 (0, i) = _
    rw [hprepRow]
  obtain ⟨hpurePair, htimesPure, hsamplesPure⟩ := tail_current_provenance P currentEntry
    (Q - W0.pending.length) (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    i (s + w) (s + w + n.val) hpositivePair hpositiveTime hsamples htimeCurrent hsampleCurrent
    (Nat.le_add_right _ _)
  have hdecision := cut_solution_dichotomy rate P0 i record.input.time choice cut
    (P.drop (Q - W0.pending.length) ++ [currentEntry]) hpositiveSolve hrawBatch
    hexpectedR hparseR hparseWordR hlocalTest hacceptLocal hcomparisonR
  exact ⟨W0.pending ++ P.take (Q - W0.pending.length),
    P.drop (Q - W0.pending.length) ++ [currentEntry],
    rfl, rfl, hfirstLength, hsecondLength, hdecodeBank, hrawBatch,
    hpositiveAll, hpositiveSolve, hpurePair, htimesPure, hsamplesPure, hdecision⟩

end Bandits.Support.ReferenceFirstCollectionDownSecondPureBank
