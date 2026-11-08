/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments

import Lean.Elab.Tactic.Omega

/-!
# The chronological incoming prefix at the actual first renewal

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,399-423`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The prefix starts at the genuine initialization launch and ends immediately
before the first renewal call. Its live inputs and collection inputs are the
existing literal source cells. Disabled collection rounds remain in the list.
The physical replay is unstopped; the analytical run retains its first overflow
update and freezes thereafter. These are internal results, not a manuscript
filtration or a source theorem closure.

The Borel result here covers the actual live-prefix readout and the erased
source representative on the retained field. Ambient Borel measurability of
the collection readout, the whole incoming output, and the retained overflow
event remains to be supplied; none of those claims is asserted below.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw

namespace Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
local notation "Record" => ReferenceFirstCollectionSamplerCall.RoundRecord p rate

/-- The actual elapsed initialization boundary, on the whole original source. -/
abbrev start (z : Z) : ℕ :=
  ReferenceFirstCollectionReadyStream.startTime (rate := rate) z.val rewards C_star C_h

theorem start_eq_physicalStart (z : Z) :
    start rate rewards C_star C_h u t z =
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := rfl

/-- The number of physical dates strictly before the renewal call. -/
def pastLength (z : Z) : ℕ := t.val - start rate rewards C_star C_h u t z

/-- The original complete physical suffix; no rows or private arrays are erased. -/
def sourceRecords (z : Z) : List Record :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h

/-- Presence of the actual renewal call produces a genuine launch crossing. -/
theorem crossing (z : Z) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨hc, _, _⟩ :=
    ReferenceFirstCollectionRenewalNumericalServiceJoin.actual_renewal_call_numerical_reconstruction
      rate rewards C_star C_h u t z d
  exact hc

theorem full_span (z : Z) :
    start rate rewards C_star C_h u t z +
      (p.T - start rate rewards C_star C_h u t z) ≤ p.T := by
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate z.val rewards C_star C_h
  change start rate rewards C_star C_h u t z ≤ p.T at hs
  omega

private theorem epoch_records (z : Z)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true)
    (hs : start rate rewards C_star C_h u t z +
      (p.T - start rate rewards C_star C_h u t z) ≤ p.T) :
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      z.val rewards C_star C_h hc
      (p.T - start rate rewards C_star C_h u t z) hs).records =
        sourceRecords rate rewards C_star C_h u t z := by
  symm
  apply ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
  exact (Option.some_get _).symm

private theorem liveWindow_eq (z : Z)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true)
    (hs : start rate rewards C_star C_h u t z +
      (p.T - start rate rewards C_star C_h u t z) ≤ p.T) :
    ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc
      (p.T - start rate rewards C_star C_h u t z) hs =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (sourceRecords rate rewards C_star C_h u t z) := by
  change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      z.val rewards C_star C_h hc
      (p.T - start rate rewards C_star C_h u t z) hs).records = _
  rw [epoch_records rate rewards C_star C_h u t z hc hs]

/-- The actual live part, taken at the maximal original horizon count. -/
def liveCells (z : Z) : List (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z.val rewards C_star C_h (crossing rate rewards C_star C_h u t z)
    (p.T - start rate rewards C_star C_h u t z)
    (full_span rate rewards C_star C_h u t z)

/-- Both boundaries are produced by the actual first empty collection stream. -/
theorem actual_boundaries (z : Z) :
    start rate rewards C_star C_h u t z ≤ u.val ∧ u.val < t.val ∧
      start rate rewards C_star C_h u t z +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (sourceRecords rate rewards C_star C_h u t z)).length = u.val := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨hc, hs, _, g, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hcut, hend, _⟩ :=
    ReferenceFirstCollectionRenewalNumericalServiceJoin.actual_renewal_call_numerical_reconstruction
      rate rewards C_star C_h u t z d
  rw [epoch_records rate rewards C_star C_h u t z hc hs] at hcut hend
  change start rate rewards C_star C_h u t z +
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (sourceRecords rate rewards C_star C_h u t z)).length = u.val at hcut
  change start rate rewards C_star C_h u t z +
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (sourceRecords rate rewards C_star C_h u t z)).length + g.stream.ell = t.val at hend
  have hpos : 1 ≤ g.stream.ell := g.stream.positiveLength
  refine ⟨?_, ?_, hcut⟩ <;> omega

/-- The live list has exactly one input for each date from launch to cutoff. -/
theorem liveCells_length (z : Z) :
    (liveCells rate rewards C_star C_h u t z).length =
      u.val - start rate rewards C_star C_h u t z := by
  rw [liveCells, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length,
    liveWindow_eq]
  have hb := (actual_boundaries rate rewards C_star C_h u t z).2.2
  omega

/-- The original complete suffix retains every date through the horizon. -/
theorem sourceRecords_length (z : Z) :
    (sourceRecords rate rewards C_star C_h u t z).length =
      p.T - start rate rewards C_star C_h u t z :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z.val rewards C_star C_h

theorem cutoff_index_lt (z : Z) :
    u.val - start rate rewards C_star C_h u t z <
      (sourceRecords rate rewards C_star C_h u t z).length := by
  rw [sourceRecords_length]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have ht := t.isLt
  omega

theorem call_index_lt (z : Z) :
    t.val - start rate rewards C_star C_h u t z <
      (sourceRecords rate rewards C_star C_h u t z).length := by
  rw [sourceRecords_length]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have ht := t.isLt
  omega

/-- The literal complete-suffix record at the cutoff date. -/
def cutoffRecord (z : Z) : Record :=
  (sourceRecords rate rewards C_star C_h u t z)[
    u.val - start rate rewards C_star C_h u t z]'(cutoff_index_lt rate rewards C_star C_h u t z)

/-- The literal complete-suffix record at the renewal date. -/
def callRecord (z : Z) : Record :=
  (sourceRecords rate rewards C_star C_h u t z)[
    t.val - start rate rewards C_star C_h u t z]'(call_index_lt rate rewards C_star C_h u t z)

/-- Calendar uniqueness identifies every actual renewal witness's record. -/
theorem actual_call_record_eq (z : Z)
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    d.record = callRecord rate rewards C_star C_h u t z := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp d.record_mem
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h n d.record hn
  rw [d.time_eq] at ht
  have hidx : n = t.val - start rate rewards C_star C_h u t z := by
    change t.val = start rate rewards C_star C_h u t z + n at ht
    omega
  subst n
  exact (List.getElem?_eq_some_iff.mp hn).2.symm

private theorem record_at_time (z : Z) (v : Fin p.T)
    (hv : start rate rewards C_star C_h u t z ≤ v.val)
    (hn : v.val - start rate rewards C_star C_h u t z <
      (sourceRecords rate rewards C_star C_h u t z).length) :
    ((sourceRecords rate rewards C_star C_h u t z)[
      v.val - start rate rewards C_star C_h u t z]'hn).input.time = v := by
  have h := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h (v.val - start rate rewards C_star C_h u t z)
    ((sourceRecords rate rewards C_star C_h u t z)[
      v.val - start rate rewards C_star C_h u t z]'hn)
    (List.getElem?_eq_getElem hn)
  apply Fin.ext
  change _ = start rate rewards C_star C_h u t z + _ at h
  omega

theorem cutoffRecord_time (z : Z) :
    (cutoffRecord rate rewards C_star C_h u t z).input.time = u :=
  record_at_time rate rewards C_star C_h u t z u
    (actual_boundaries rate rewards C_star C_h u t z).1
    (cutoff_index_lt rate rewards C_star C_h u t z)

theorem callRecord_time (z : Z) :
    (callRecord rate rewards C_star C_h u t z).input.time = t :=
  record_at_time rate rewards C_star C_h u t z t
    (by have hb := actual_boundaries rate rewards C_star C_h u t z; omega)
    (call_index_lt rate rewards C_star C_h u t z)

private theorem stream_cutoff_eq
    (z : Z)
  {hc : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true}
  {hs : start rate rewards C_star C_h u t z +
    (p.T - start rate rewards C_star C_h u t z) ≤ p.T}
  {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z.val rewards C_star C_h
      hc (p.T - start rate rewards C_star C_h u t z) hs).records).length <
        p.T - start rate rewards C_star C_h u t z}
  (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
    z.val rewards C_star C_h (p.T - start rate rewards C_star C_h u t z) hc hs hshort) :
    out.cutoff.cut = cutoffRecord rate rewards C_star C_h u t z := by
  have hi := out.cutoff.cutIndex
  rw [epoch_records rate rewards C_star C_h u t z hc hs] at hi
  have hb := (actual_boundaries rate rewards C_star C_h u t z).2.2
  have hidx : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (sourceRecords rate rewards C_star C_h u t z)).length =
        u.val - start rate rewards C_star C_h u t z := by omega
  rw [hidx] at hi
  exact (List.getElem?_eq_some_iff.mp hi).2.symm

private theorem stream_record_lookup
    (z : Z)
  {hc : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true}
  {hs : start rate rewards C_star C_h u t z +
    (p.T - start rate rewards C_star C_h u t z) ≤ p.T}
  {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z.val rewards C_star C_h
      hc (p.T - start rate rewards C_star C_h u t z) hs).records).length <
        p.T - start rate rewards C_star C_h u t z}
  (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
    z.val rewards C_star C_h (p.T - start rate rewards C_star C_h u t z) hc hs hshort) (k : Fin out.ell) :
    (sourceRecords rate rewards C_star C_h u t z)[
      u.val - start rate rewards C_star C_h u t z + k.val]? =
        some (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)) := by
  have hi := (out.alignment ⟨k.val, lt_of_lt_of_le k.isLt out.withinWindow⟩).1
  rw [epoch_records rate rewards C_star C_h u t z hc hs] at hi
  have hb := (actual_boundaries rate rewards C_star C_h u t z).2.2
  have hidx : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (sourceRecords rate rewards C_star C_h u t z)).length =
        u.val - start rate rewards C_star C_h u t z := by omega
  simpa only [hidx] using hi

/-- The cutoff choice and its actual recorder validity are produced together. -/
theorem cutoff_choice_exists (z : Z) :
    ∃ head : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice
        (cutoffRecord rate rewards C_star C_h u t z).input = some head ∧
      CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (cutoffRecord rate rewards C_star C_h u t z).output.preparation
          head.payload head.started head.weights) := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨_, _, _, g, head, _, valid, _, hhead, _⟩ :=
    ReferenceFirstCollectionRenewalNumericalServiceJoin.actual_renewal_call_numerical_reconstruction
      rate rewards C_star C_h u t z d
  have heq := stream_cutoff_eq rate rewards C_star C_h u t z g.stream
  rw [heq] at hhead valid
  exact ⟨head, hhead, valid⟩

theorem cutoffChoice_present (z : Z) :
    (ReferenceCollectionSegmentExtraction.choice
      (cutoffRecord rate rewards C_star C_h u t z).input).isSome = true := by
  obtain ⟨head, hhead, _⟩ := cutoff_choice_exists rate rewards C_star C_h u t z
  rw [hhead]
  rfl

/-- The unique actual choice, extracted from its present option. -/
def cutoffChoice (z : Z) : ReferenceCollectionSegmentExtraction.Choice rate :=
  (ReferenceCollectionSegmentExtraction.choice
    (cutoffRecord rate rewards C_star C_h u t z).input).get
      (cutoffChoice_present rate rewards C_star C_h u t z)

theorem cutoffChoice_eq (z : Z) :
    ReferenceCollectionSegmentExtraction.choice
      (cutoffRecord rate rewards C_star C_h u t z).input =
        some (cutoffChoice rate rewards C_star C_h u t z) :=
  (Option.some_get _).symm

theorem cutoffChoice_valid (z : Z) :
    CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (cutoffRecord rate rewards C_star C_h u t z).output.preparation
        (cutoffChoice rate rewards C_star C_h u t z).payload
        (cutoffChoice rate rewards C_star C_h u t z).started
        (cutoffChoice rate rewards C_star C_h u t z).weights) := by
  obtain ⟨head, hhead, valid⟩ := cutoff_choice_exists rate rewards C_star C_h u t z
  have heq : cutoffChoice rate rewards C_star C_h u t z = head :=
    Option.some.inj ((cutoffChoice_eq rate rewards C_star C_h u t z).symm.trans hhead)
  rw [heq]
  exact valid

/-- The head is the existing numerical source cell at the actual cutoff. -/
def cutoffCell (z : Z) : RecordedQueueRun.RoundInput p.K :=
  ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate
    (cutoffRecord rate rewards C_star C_h u t z)
    (cutoffChoice rate rewards C_star C_h u t z) rewards
    (cutoffChoice_valid rate rewards C_star C_h u t z)

/-- The original physical suffix starting at the cutoff, without filtering. -/
def collectionRecords (z : Z) : List Record :=
  (sourceRecords rate rewards C_star C_h u t z).drop
    (u.val - start rate rewards C_star C_h u t z)

theorem collection_index_lt (z : Z) :
    t.val - u.val - 1 < (collectionRecords rate rewards C_star C_h u t z).length := by
  simp only [collectionRecords, List.length_drop, sourceRecords_length]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have ht := t.isLt
  omega

/-- Exactly the later collection readouts strictly before the renewal call
are present. Presence is obtained from the actual numerical stream. -/
theorem collectionReadout_present (z : Z) (k : Fin (t.val - u.val - 1)) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      (start rate rewards C_star C_h u t z)
      ((collectionRecords rate rewards C_star C_h u t z)[k.val + 1]'(by
        have h := collection_index_lt rate rewards C_star C_h u t z
        have hk := k.isLt
        omega))).isSome = true := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨_, _, _, g, _, _, _, D, _, _, _, _, hDlen, _, hCells,
    _, _, _, _, _, _, _, _, hcut, hend, _⟩ :=
    ReferenceFirstCollectionRenewalNumericalServiceJoin.actual_renewal_call_numerical_reconstruction
      rate rewards C_star C_h u t z d
  have hell : g.stream.ell = t.val - u.val := by omega
  let n : Fin g.stream.ell := ⟨k.val + 1, by have hk := k.isLt; omega⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hread⟩ := hCells n
  have hr := hread.2 (by dsimp only [n]; omega)
  have hi := stream_record_lookup rate rewards C_star C_h u t z g.stream n
  have hlookup :
      (sourceRecords rate rewards C_star C_h u t z)[
        u.val - start rate rewards C_star C_h u t z + (k.val + 1)]? =
          some ((collectionRecords rate rewards C_star C_h u t z)[k.val + 1]'(by
            have h := collection_index_lt rate rewards C_star C_h u t z
            have hk := k.isLt
            omega)) := by
    have h := List.getElem?_eq_getElem (l := collectionRecords rate rewards C_star C_h u t z)
      (i := k.val + 1) (by
        have h := collection_index_lt rate rewards C_star C_h u t z
        have hk := k.isLt
        omega)
    simpa only [collectionRecords, List.getElem?_drop] using h
  have heq := Option.some.inj (hi.symm.trans hlookup)
  rw [heq] at hr
  rw [hr]
  rfl

/-- The head and every later SOME readout, including disabled records. -/
def collectionCells (z : Z) : List (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate
    (start rate rewards C_star C_h u t z)
    (collectionRecords rate rewards C_star C_h u t z)
    ⟨t.val - u.val - 1, collection_index_lt rate rewards C_star C_h u t z⟩
    (cutoffCell rate rewards C_star C_h u t z)
    (collectionReadout_present rate rewards C_star C_h u t z)

theorem collectionCells_length (z : Z) :
    (collectionCells rate rewards C_star C_h u t z).length = t.val - u.val := by
  rw [collectionCells, ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length]
  have hb := (actual_boundaries rate rewards C_star C_h u t z).2.1
  dsimp only
  omega

theorem collection_record_index_lt (z : Z) (k : Fin (t.val - u.val)) :
    k.val < (collectionRecords rate rewards C_star C_h u t z).length := by
  simp only [collectionRecords, List.length_drop, sourceRecords_length]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have ht := t.isLt
  have hk := k.isLt
  omega

/-- The original physical record at collection offset k. -/
def collectionRecord (z : Z) (k : Fin (t.val - u.val)) : Record :=
  (collectionRecords rate rewards C_star C_h u t z)[k.val]'
    (collection_record_index_lt rate rewards C_star C_h u t z k)

/-- One original numerical input per date in the half-open interval [s,t). -/
def pastCells (z : Z) : List (RecordedQueueRun.RoundInput p.K) :=
  liveCells rate rewards C_star C_h u t z ++ collectionCells rate rewards C_star C_h u t z

theorem pastCells_length (z : Z) :
    (pastCells rate rewards C_star C_h u t z).length =
      pastLength rate rewards C_star C_h u t z := by
  rw [pastCells, List.length_append, liveCells_length, collectionCells_length]
  have hb := actual_boundaries rate rewards C_star C_h u t z
  unfold pastLength
  omega

private theorem collection_list_eq (z : Z)
    (D : List (RecordedQueueRun.RoundInput p.K))
    (hlen : D.length = t.val - u.val)
    (hzero : D[0]'(by
      rw [hlen]
      have hb := (actual_boundaries rate rewards C_star C_h u t z).2.1
      omega) = cutoffCell rate rewards C_star C_h u t z)
    (hread : ∀ k : Fin (t.val - u.val - 1),
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (start rate rewards C_star C_h u t z)
        ((collectionRecords rate rewards C_star C_h u t z)[k.val + 1]'(by
          have h := collection_index_lt rate rewards C_star C_h u t z
          have hk := k.isLt
          omega)) = some (D[k.val + 1]'(by rw [hlen]; have hk := k.isLt; omega))) :
    D = collectionCells rate rewards C_star C_h u t z := by
  apply List.ext_getElem (hlen.trans (collectionCells_length rate rewards C_star C_h u t z).symm)
  intro i hi hicol
  cases i with
  | zero => exact hzero
  | succ i =>
      let k : Fin (t.val - u.val - 1) := ⟨i, by rw [hlen] at hi; omega⟩
      have hright := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_readout rate
        (start rate rewards C_star C_h u t z)
        (collectionRecords rate rewards C_star C_h u t z)
        ⟨t.val - u.val - 1, collection_index_lt rate rewards C_star C_h u t z⟩
        (cutoffCell rate rewards C_star C_h u t z)
        (collectionReadout_present rate rewards C_star C_h u t z) k
      exact Option.some.inj ((hread k).symm.trans hright)

/-- The same actual renewal reconstruction replays the literal chronological
prefix from the single zero launch seed. No queue reset occurs at renewal. -/
theorem actual_chronological_reconstruction (z : Z) :
    ∃ d : ActualRenewalCall rate rewards C_star C_h u t z,
      d.record = callRecord rate rewards C_star C_h u t z ∧
      (∀ j : Fin p.K,
        (AssignmentScoreReconstruction.sourceScore d.out j,
          AssignmentScoreReconstruction.initialQueue d.out j) =
        QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate j
            (pastCells rate rewards C_star C_h u t z))) ∧
      ∀ k : Fin (t.val - u.val),
        ∃ (call : ReferenceCollectionSegmentExtraction.Choice rate)
          (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput
              (collectionRecord rate rewards C_star C_h u t z k).output.preparation
              call.payload call.started call.weights)),
          ReferenceCollectionSegmentExtraction.choice
            (collectionRecord rate rewards C_star C_h u t z k).input = some call ∧
          (collectionCells rate rewards C_star C_h u t z)[k.val]'(by
            rw [collectionCells_length]; exact k.isLt) =
              ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate
                (collectionRecord rate rewards C_star C_h u t z k) call rewards valid := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨_, _, _, g, head, _, valid, D, hhead, _, _, _, hDlen, hDzero, hCells,
    _, _, _, _, _, _, _, _, hcut, hend, _, _, hscore, hqueue, _⟩ :=
    ReferenceFirstCollectionRenewalNumericalServiceJoin.actual_renewal_call_numerical_reconstruction
      rate rewards C_star C_h u t z d
  have hell : g.stream.ell = t.val - u.val := by omega
  have hlen : D.length = t.val - u.val := hDlen.trans hell
  have hcuteq := stream_cutoff_eq rate rewards C_star C_h u t z g.stream
  have hhead' : head = cutoffChoice rate rewards C_star C_h u t z := by
    rw [hcuteq] at hhead
    exact Option.some.inj (hhead.symm.trans (cutoffChoice_eq rate rewards C_star C_h u t z))
  have hzero : D[0]'(by rw [hlen]; have h := g.stream.positiveLength; omega) =
      cutoffCell rate rewards C_star C_h u t z := by
    simpa only [hcuteq, hhead', cutoffCell] using hDzero
  have hread : ∀ k : Fin (t.val - u.val - 1),
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (start rate rewards C_star C_h u t z)
        ((collectionRecords rate rewards C_star C_h u t z)[k.val + 1]'(by
          have h := collection_index_lt rate rewards C_star C_h u t z
          have hk := k.isLt
          omega)) = some (D[k.val + 1]'(by rw [hlen]; have hk := k.isLt; omega)) := by
    intro k
    let n : Fin g.stream.ell := ⟨k.val + 1, by have hk := k.isLt; omega⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hread⟩ := hCells n
    have hr := hread (by dsimp only [n]; omega)
    have hi := stream_record_lookup rate rewards C_star C_h u t z g.stream n
    have hlookup :
        (sourceRecords rate rewards C_star C_h u t z)[
          u.val - start rate rewards C_star C_h u t z + (k.val + 1)]? =
            some ((collectionRecords rate rewards C_star C_h u t z)[k.val + 1]'(by
              have h := collection_index_lt rate rewards C_star C_h u t z
              have hk := k.isLt
              omega)) := by
      have h := List.getElem?_eq_getElem (l := collectionRecords rate rewards C_star C_h u t z)
        (i := k.val + 1) (by
          have h := collection_index_lt rate rewards C_star C_h u t z
          have hk := k.isLt
          omega)
      simpa only [collectionRecords, List.getElem?_drop] using h
    have heq := Option.some.inj (hi.symm.trans hlookup)
    rw [heq] at hr
    exact hr
  have hD := collection_list_eq rate rewards C_star C_h u t z D hlen hzero hread
  refine ⟨d, actual_call_record_eq rate rewards C_star C_h u t z d, ?_, ?_⟩
  · intro j
    have hp :
      (AssignmentScoreReconstruction.sourceScore d.out j,
        AssignmentScoreReconstruction.initialQueue d.out j) =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate j
          (liveCells rate rewards C_star C_h u t z ++ D)) :=
      Prod.ext (hscore j) (hqueue j)
    rw [hD] at hp
    exact hp
  · intro k
    let n : Fin g.stream.ell := ⟨k.val, by rw [hell]; exact k.isLt⟩
    obtain ⟨call, valid, hchoice, _, _, hcell, _⟩ := hCells n
    have hi := stream_record_lookup rate rewards C_star C_h u t z g.stream n
    have hlookup :
        (sourceRecords rate rewards C_star C_h u t z)[
          u.val - start rate rewards C_star C_h u t z + k.val]? =
            some (collectionRecord rate rewards C_star C_h u t z k) := by
      simpa only [collectionRecord, collectionRecords, List.getElem?_drop] using
        (List.getElem?_eq_getElem (collection_record_index_lt rate rewards C_star C_h u t z k))
    have heq := Option.some.inj (hi.symm.trans hlookup)
    rw [heq] at valid hchoice hcell
    exact ⟨call, valid, hchoice, by simpa only [hD] using hcell⟩

/-- The actual call and its unstopped numerical replay, on the canonical list. -/
theorem actual_incoming_replay (z : Z) :
    ∃ d : ActualRenewalCall rate rewards C_star C_h u t z,
      d.record = callRecord rate rewards C_star C_h u t z ∧
      ∀ j : Fin p.K,
        (AssignmentScoreReconstruction.sourceScore d.out j,
          AssignmentScoreReconstruction.initialQueue d.out j) =
        QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate j
            (pastCells rate rewards C_star C_h u t z)) := by
  obtain ⟨d, hd, hreplay, _⟩ := actual_chronological_reconstruction rate rewards C_star C_h u t z
  exact ⟨d, hd, hreplay⟩

/-- The analytical stopped queue machine on the same literal incoming list. -/
def incoming (z : Z) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (pastCells rate rewards C_star C_h u t z)

/-- The full existing countable output, with every accepted queue record. -/
def incomingReadout (z : Z) :
    (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) :=
  ((incoming rate rewards C_star C_h u t z).registers,
    (incoming rate rewards C_star C_h u t z).overflow,
    (incoming rate rewards C_star C_h u t z).records)

/-- The ordinary four numerical fields, with a distinct absent tag at every
unused position of the original finite horizon. -/
def pastReadout (z : Z) :
    Fin p.T → Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p :=
  fun k => match (pastCells rate rewards C_star C_h u t z)[k.val]? with
    | none => .inl ()
    | some cell => .inr (cell.enabled, cell.recordedArm, cell.reward, cell.rate)

/-- The same ordinary numerical coordinates for the live portion alone. -/
def liveReadout (z : Z) :
    Fin p.T → Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p :=
  fun k => match (liveCells rate rewards C_star C_h u t z)[k.val]? with
    | none => .inl ()
    | some cell => .inr (cell.enabled, cell.recordedArm, cell.reward, cell.rate)

private theorem normalized_replay
    (cells : List (RecordedQueueRun.RoundInput p.K)) (j : Fin p.K)
    (initial : ℕ × ℕ) :
    QueueReplay.replay (4 * rate.n) initial
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j) =
      QueueReplay.replay (4 * rate.n) initial
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate j cells) := by
  induction cells generalizing initial with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.map_cons, ReferenceFirstCollectionAllArmNumericalStream.arrivals,
        QueueReplay.replay, List.foldl_cons] at ih ⊢
      have hstep : QueueReplay.transition (4 * rate.n) initial
          (UnstoppedRecordedQueueComparison.unstoppedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j) =
          QueueReplay.transition (4 * rate.n) initial
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j) := by
        cases he : cell.enabled <;>
          simp [UnstoppedRecordedQueueComparison.unstoppedRecord, he, QueueReplay.transition]
      rw [hstep]
      exact ih _

/-- The incoming flag checks every earlier prefix, including a crossing
update whose queue may have drained at a later physical date. -/
theorem incoming_noOverflow_iff_firstOverflow (z : Z) :
    (incoming rate rewards C_star C_h u t z).overflow = false ↔
      pastLength rate rewards C_star C_h u t z <
        UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (pastCells rate rewards C_star C_h u t z) := by
  have h := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (pastCells rate rewards C_star C_h u t z)
    (pastCells rate rewards C_star C_h u t z).length (Nat.le_refl _)
  rw [List.take_length, pastCells_length] at h
  change (incoming rate rewards C_star C_h u t z).overflow = true ↔ _ at h
  exact Bool.eq_false_iff.trans ((not_congr h).trans not_le)

/-- The strict-past test is independent of the appended current input.
Thus it also applies to the literal actual current cell when that cell is
produced by a consumer; the first crossing update remains included. -/
theorem incoming_noOverflow_iff_appended_firstOverflow (z : Z) :
    ∀ current : RecordedQueueRun.RoundInput p.K,
      (incoming rate rewards C_star C_h u t z).overflow = false ↔
        pastLength rate rewards C_star C_h u t z <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (pastCells rate rewards C_star C_h u t z ++ [current]) := by
  intro current
  have h := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (pastCells rate rewards C_star C_h u t z ++ [current])
    (pastCells rate rewards C_star C_h u t z).length (by simp)
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, pastCells_length] at h
  change (incoming rate rewards C_star C_h u t z).overflow = true ↔ _ at h
  exact Bool.eq_false_iff.trans ((not_congr h).trans not_le)

/-- Before any past overflow the stopped registers equal the full physical
replay. The no-overflow test is an implication in the conclusion. -/
theorem incoming_registers_before_overflow (z : Z) :
    (incoming rate rewards C_star C_h u t z).overflow = false →
      ∀ j : Fin p.K,
        (incoming rate rewards C_star C_h u t z).registers j =
          QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate j
              (pastCells rate rewards C_star C_h u t z)) := by
  intro hflag j
  have hbefore := (incoming_noOverflow_iff_firstOverflow
    rate rewards C_star C_h u t z).mp hflag
  have h := UnstoppedRecordedQueueComparison.prefix_registers_eq_unstopped_replay
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (pastCells rate rewards C_star C_h u t z)
    (pastCells rate rewards C_star C_h u t z).length (Nat.le_refl _) j
  rw [pastCells_length] at h
  rw [Nat.min_eq_left (Nat.le_of_lt hbefore)] at h
  simp only [← pastCells_length rate rewards C_star C_h u t z, List.take_length,
    UnstoppedRecordedQueueComparison.unstoppedReplay] at h
  exact h.trans (normalized_replay rate (pastCells rate rewards C_star C_h u t z) j (0, 0))

/-- The strict-past test is equivalent to bounding every unstopped prefix
backlog, rather than testing only the possibly drained terminal backlog. -/
theorem incoming_noOverflow_iff_all_prefixes (z : Z) :
    (incoming rate rewards C_star C_h u t z).overflow = false ↔
      ∀ h : ℕ, h ≤ pastLength rate rewards C_star C_h u t z →
        ∀ j : Fin p.K,
          32 * (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (pastCells rate rewards C_star C_h u t z) h j).2 ≤ D p := by
  rw [incoming_noOverflow_iff_firstOverflow]
  constructor
  · intro hbefore h hh j
    by_cases hz : h = 0
    · subst h
      simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay]
    · have hnocross := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (pastCells rate rewards C_star C_h u t z) h (by omega)
        (by rw [pastCells_length]; exact hh) (by omega)
      by_contra hnot
      apply hnocross
      exact ⟨j, Nat.lt_of_not_ge hnot⟩
  · intro hbound
    by_contra hnot
    have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (pastCells rate rewards C_star C_h u t z)
      (by rw [pastCells_length]; omega)
    obtain ⟨j, hj⟩ := hcross
    have hb := hbound
      (UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (pastCells rate rewards C_star C_h u t z)) (Nat.le_of_not_gt hnot) j
    exact (Nat.not_lt_of_ge hb) hj

/-- The same actual call's reconstructed registers equal the analytical
incoming registers precisely on the strict-past no-overflow branch. -/
theorem actual_incoming_registers (z : Z) :
    ∃ d : ActualRenewalCall rate rewards C_star C_h u t z,
      d.record = callRecord rate rewards C_star C_h u t z ∧
      ((incoming rate rewards C_star C_h u t z).overflow = false →
        ∀ j : Fin p.K,
          (AssignmentScoreReconstruction.sourceScore d.out j,
            AssignmentScoreReconstruction.initialQueue d.out j) =
            (incoming rate rewards C_star C_h u t z).registers j) := by
  obtain ⟨d, hd, hreplay⟩ := actual_incoming_replay rate rewards C_star C_h u t z
  refine ⟨d, hd, ?_⟩
  intro hflag j
  exact (hreplay j).trans
    (incoming_registers_before_overflow rate rewards C_star C_h u t z hflag j).symm

/-- Erase only current and future selected-row controls using the existing
renewal subtype constructor and its proved membership. -/
def erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) : Z :=
  ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
    rate rewards C_star C_h u t z (fun _ => control0)

theorem erasedSource_val (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    (erasedSource rate rewards C_star C_h u t control0 z).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val := rfl

/-- The actual launch time survives the selected-control suffix erasure. -/
theorem start_erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    start rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 z) =
        start rate rewards C_star C_h u t z := by
  obtain ⟨_, _, _, hstart, _⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.actual_launch_of_firstCollectionCall
      rate rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z) (fun _ => control0)
      (firstCollectionCall_eq rate rewards C_star C_h u t z)
  exact hstart

theorem past_span (z : Z) :
    start rate rewards C_star C_h u t z + pastLength rate rewards C_star C_h u t z ≤ p.T := by
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have ht := t.isLt
  unfold pastLength
  omega

private theorem live_cell_input_congr
    {left right : Record} (hr : left = right)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell left)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell right) : a.input = b.input := by
  subst right
  exact ReferenceFirstLiveNumericalPrefixTemporal.actualLiveSourceCell_input_unique a b

private theorem liveCells_eq_count (z : Z) :
    liveCells rate rewards C_star C_h u t z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z.val rewards C_star C_h (crossing rate rewards C_star C_h u t z)
        (pastLength rate rewards C_star C_h u t z)
        (past_span rate rewards C_star C_h u t z) := by
  let hc := crossing rate rewards C_star C_h u t z
  let hs := full_span rate rewards C_star C_h u t z
  let hn := past_span rate rewards C_star C_h u t z
  let N := p.T - start rate rewards C_star C_h u t z
  let n := pastLength rate rewards C_star C_h u t z
  have hle : n ≤ N := by
    have ht := t.isLt
    dsimp only [n, N, pastLength]
    omega
  have hrecords := ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc)
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards
    (start rate rewards C_star C_h u t z) N hs
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h hc).activeAtStart n hle
  change (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z.val rewards C_star C_h hc N hs).records.take n =
    (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate z.val rewards C_star C_h hc n hn).records at hrecords
  have hlength : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc N hs).length ≤ n := by
    rw [liveWindow_eq]
    have hb := actual_boundaries rate rewards C_star C_h u t z
    dsimp only [n, pastLength]
    omega
  have hwindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc N hs =
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h hc n hn := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow _ =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [← hrecords]
    unfold ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    rw [← List.take_takeWhile]
    exact (List.take_of_length_le hlength).symm
  apply List.ext_getElem
  · simpa only [liveCells, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
      using congrArg List.length hwindow
  · intro i hi hj
    have hi' : i < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h hc N hs).length := by
      simpa only [liveCells, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length] using hi
    have hj' : i < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h hc n hn).length := by
      simpa only [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length] using hj
    have hrecord :
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z.val rewards C_star C_h hc N hs)[i]'hi' =
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z.val rewards C_star C_h hc n hn)[i]'hj' := by
      have h := congrArg (fun rs : List Record => rs[i]?) hwindow
      simpa only [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
        Option.some.injEq] using h
    calc
      _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate z.val rewards C_star C_h hc N hs ⟨i, hi'⟩).input := by
        exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
          rate z.val rewards C_star C_h hc N hs ⟨i, hi'⟩
      _ = (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate z.val rewards C_star C_h hc n hn ⟨i, hj'⟩).input :=
        live_cell_input_congr rate hrecord _ _
      _ = _ := (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate z.val rewards C_star C_h hc n hn ⟨i, hj'⟩).symm

/-- The live portion already factors through the original selected strict
control prefix. The broad crossing/elapsed stratum is sufficient here. -/
theorem liveCells_erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    liveCells rate rewards C_star C_h u t z =
      liveCells rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) := by
  let s := start rate rewards C_star C_h u t z
  let q := ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val
  have hs : s ≤ t.val := by
    have hb := actual_boundaries rate rewards C_star C_h u t z
    dsimp only [s]
    omega
  let index := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs
  let left : ReferenceTotalSourceDisintegration.SourceStratum
      rate rewards C_star C_h t index :=
    ⟨z.val, rfl, crossing rate rewards C_star C_h u t z, rfl⟩
  let right : ReferenceTotalSourceDisintegration.SourceStratum
      rate rewards C_star C_h t index :=
    ⟨(erasedSource rate rewards C_star C_h u t control0 z).val,
      rfl, crossing rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z),
      start_erasedSource rate rewards C_star C_h u t control0 z⟩
  have h := ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_eq_of_sourcePrefix
    rate rewards C_star C_h q t s hs control0 left right
    (erasedSource_val rate rewards C_star C_h u t control0 z)
  rw [liveCells_eq_count rate rewards C_star C_h u t z,
    liveCells_eq_count rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 z)]
  simpa only [left, right, s, pastLength, start_erasedSource] using h

/-- Ambient Borel measurability of the literal maximal live-prefix readout.
The finite partition retains the original private J and elapsed boundary. -/
theorem measurable_liveReadout (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (liveReadout rate rewards C_star C_h u t) := by
  let cover (i : ReferenceTotalSourcePairCoupling.StratumIndex t) : Set Z :=
    {z | z.val ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
      rate rewards C_star C_h t i}
  have hcover (i : ReferenceTotalSourcePairCoupling.StratumIndex t) : MeasurableSet (cover i) :=
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 i).preimage measurable_subtype_coe
  have hall (z : Z) : ∃ i, z ∈ cover i := by
    have hs : start rate rewards C_star C_h u t z ≤ t.val := by
      have hb := actual_boundaries rate rewards C_star C_h u t z
      omega
    exact ⟨(ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val,
      ⟨start rate rewards C_star C_h u t z, Nat.lt_succ_of_le hs⟩),
      rfl, crossing rate rewards C_star C_h u t z, rfl⟩
  have hlocal (i : ReferenceTotalSourcePairCoupling.StratumIndex t) :
      Measurable (fun x : cover i => liveReadout rate rewards C_star C_h u t x.val) := by
    let hs := Nat.lt_succ_iff.mp i.2.isLt
    let castSource (x : cover i) : ReferenceTotalSourceDisintegration.SourceStratum
        rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex i.1 t i.2.val hs) :=
      ⟨x.val.val, x.property⟩
    have hcast : Measurable castSource := by
      apply Measurable.subtype_mk
      exact measurable_subtype_coe.comp measurable_subtype_coe
    have hread := (ReferenceFirstLiveNumericalPrefixBorel.measurable_numericalCountPastReadout
      rate rewards C_star C_h i.1 t i.2.val hs control0).comp hcast
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k.val < t.val - i.2.val
    · have hcoordinate := (measurable_pi_apply ⟨k.val, hk⟩).comp hread
      convert hcoordinate using 1
      funext x
      have hx : start rate rewards C_star C_h u t x.val = i.2.val := x.property.2.2
      simp only [Function.comp_apply, liveReadout, liveCells_eq_count, pastLength, hx,
        ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout, castSource]
      rfl
    · have heq : (fun x : cover i => liveReadout rate rewards C_star C_h u t x.val k) =
          fun _ => (Sum.inl () : Unit ⊕ ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p) := by
        funext x
        have hx : start rate rewards C_star C_h u t x.val = i.2.val := x.property.2.2
        have hlen := liveCells_length rate rewards C_star C_h u t x.val
        have hb := (actual_boundaries rate rewards C_star C_h u t x.val).2.1
        have hk' : (liveCells rate rewards C_star C_h u t x.val).length ≤ k.val := by
          omega
        simp only [liveReadout, List.getElem?_eq_none hk']
      rw [heq]
      exact measurable_const
  intro S hS
  have heq : (liveReadout rate rewards C_star C_h u t) ⁻¹' S =
      ⋃ i : ReferenceTotalSourcePairCoupling.StratumIndex t,
        ((↑) : cover i → Z) ''
          ((fun x : cover i => liveReadout rate rewards C_star C_h u t x.val) ⁻¹' S) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := hall z
      exact Set.mem_iUnion.mpr ⟨i, ⟨⟨z, hi⟩, hz, rfl⟩⟩
    · intro hz
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
      exact hx
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (MeasurableEmbedding.subtype_coe (hcover i)).measurableSet_image' (hlocal i hS)

private theorem choice_tailArgs
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (h : ReferenceCollectionSegmentExtraction.choice x = some call) :
    ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x) =
      .inr (.inr (.inr ⟨call.payload, call.preLedger, call.started, call.weights⟩)) := by
  change ReferenceActiveDispatchTemporal.tailArgs
    (ReferenceActivePhysicalStep.prepare x).coordinator = _
  unfold ReferenceCollectionSegmentExtraction.choice at h
  generalize hd : (ReferenceActivePhysicalStep.prepare x).coordinator = cut at h ⊢
  cases cut with
  | first outcome => simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at h
  | live r q base outcome =>
      cases outcome <;> simp only [ReferenceCollectionSegmentExtraction.choiceOfCut] at h
      all_goals try { simp only [ite_self] at h; contradiction }
      all_goals
        split at h
        · contradiction
        next hn =>
          cases Option.some.inj h
          simp only [ReferenceActiveDispatchTemporal.tailArgs, dite_eq_right hn]
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionSegmentExtraction.choiceOfCut] at h
      all_goals try { simp only [ite_self] at h; contradiction }
      all_goals
        split at h
        · contradiction
        next hn =>
          cases Option.some.inj h
          simp only [ReferenceActiveDispatchTemporal.tailArgs, dite_eq_right hn]
  | invalidCollectionCutoff => simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at h
  | dagger => simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at h

private theorem choice_args_eq_of_current
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (lc rc : ReferenceCollectionSegmentExtraction.Choice rate)
    (hlc : ReferenceCollectionSegmentExtraction.choice left = some lc)
    (hrc : ReferenceCollectionSegmentExtraction.choice right = some rc)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    (⟨lc.payload, lc.preLedger, lc.started, lc.weights⟩ :
      ReferenceActiveDispatchTemporal.CollectionArgs p rate) =
        ⟨rc.payload, rc.preLedger, rc.started, rc.weights⟩ := by
  have hdata : ReferenceActiveDispatchTemporal.dispatchData left =
      ReferenceActiveDispatchTemporal.dispatchData right := by
    cases left with
    | mk state rows selected time active rewardsL =>
      cases right with
      | mk stateR rowsR selectedR timeR activeR rewardsR =>
        dsimp only at hstate hselected htime hcurrent
        subst stateR
        subst selectedR
        subst timeR
        cases hp : state.coordinator with
        | first =>
            let x : ReferenceActivePhysicalStep.RoundInput p rate :=
              ⟨state, rows, selected, time, active, rewardsL⟩
            have hprep : (ReferenceActivePhysicalStep.prepare x).coordinator =
                .first (CoordinatorRoundDispatch.dispatchFirst
                  (ReferenceActivePhysicalStep.firstInput x)) := by
              simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
                x, hp, CoordinatorRoundDispatch.dispatch]
              rfl
            change ReferenceCollectionSegmentExtraction.choice x = some lc at hlc
            unfold ReferenceCollectionSegmentExtraction.choice at hlc
            rw [hprep] at hlc
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hlc
        | dagger =>
            simp [ReferenceCollectionSegmentExtraction.choice,
              ReferenceCollectionSegmentExtraction.choiceOfCut,
              ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hp] at hlc
        | live r q base =>
            exact ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
              state rows rowsR selected time active rewardsL rewardsR r q base hp hcurrent
        | collection payload ledger saved =>
            exact ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current
              state rows rowsR selected time active rewardsL rewardsR payload ledger saved hp hcurrent
  have ht := congrArg (fun data => data.2.2) hdata
  change ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch left) =
    ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch right) at ht
  rw [choice_tailArgs rate left lc hlc, choice_tailArgs rate right rc hrc] at ht
  exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj ht))

private theorem collection_cell_eq_of_current
    (left right : Record) (lc rc : ReferenceCollectionSegmentExtraction.Choice rate)
    (lv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput left.output.preparation lc.payload lc.started lc.weights))
    (rv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput right.output.preparation rc.payload rc.started rc.weights))
    (hlc : ReferenceCollectionSegmentExtraction.choice left.input = some lc)
    (hrc : ReferenceCollectionSegmentExtraction.choice right.input = some rc)
    (hstate : left.input.state = right.input.state)
    (hselected : left.input.selected = right.input.selected)
    (htime : left.input.time = right.input.time)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time) :
    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate left lc rewards lv =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate right rc rewards rv := by
  have ha := choice_args_eq_of_current rate left.input right.input lc rc
    hlc hrc hstate hselected htime hcurrent
  rcases lc with ⟨lp, ll, ls, lw, li⟩
  rcases rc with ⟨rp, rl, rs, rw, ri⟩
  dsimp only at ha
  obtain ⟨hp, hrest⟩ := Sigma.mk.inj_iff.mp ha
  subst rp
  have he := eq_of_heq hrest
  obtain ⟨hl, hs, hw⟩ := Prod.mk.inj he
  subst_vars
  cases left with
  | mk lx lo hlo =>
    cases right with
    | mk rx ro hro =>
      cases hlo
      cases hro
      dsimp only [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell,
        ReferenceActivePhysicalStep.collectionRecordingInput,
        CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights]
      congr 1
      · exact congrArg (ReferenceActivePhysicalStep.collectionEnabled rl) htime
      · congr 1
        · exact congrArg (ReferenceActivePhysicalStep.collectionEnabled rl) htime
        · exact congrArg Prod.fst hcurrent
      · exact congrArg (fun time => fun arm =>
          ((rewards time arm).val : ℝ) / (D p : ℝ)) htime

theorem collectionRecord_lookup (z : Z) (k : Fin (t.val - u.val)) :
    (sourceRecords rate rewards C_star C_h u t z)[
      u.val - start rate rewards C_star C_h u t z + k.val]? =
        some (collectionRecord rate rewards C_star C_h u t z k) := by
  simpa only [collectionRecord, collectionRecords, List.getElem?_drop] using
    (List.getElem?_eq_getElem (collection_record_index_lt rate rewards C_star C_h u t z k))

/-- Every collection cell is tied to its original row array, selected private
index, whole reward table, and calendar date, including disabled dates. -/
theorem collectionRecord_facts (z : Z) (k : Fin (t.val - u.val)) :
    (collectionRecord rate rewards C_star C_h u t z k).input.rows = z.val.1.2 ∧
    (collectionRecord rate rewards C_star C_h u t z k).input.selected =
      ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
    (collectionRecord rate rewards C_star C_h u t z k).input.rewards = rewards ∧
    (collectionRecord rate rewards C_star C_h u t z k).input.time.val = u.val + k.val := by
  have hlookup := collectionRecord_lookup rate rewards C_star C_h u t z k
  have hmem := List.mem_of_getElem? hlookup
  rw [← epoch_records rate rewards C_star C_h u t z
    (crossing rate rewards C_star C_h u t z) (full_span rate rewards C_star C_h u t z)] at hmem
  have hi := ReferenceActivePhysicalHorizon.run_record_inputs
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z.val rewards C_star C_h
      (crossing rate rewards C_star C_h u t z))
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards
    (start rate rewards C_star C_h u t z) (p.T - start rate rewards C_star C_h u t z)
    (full_span rate rewards C_star C_h u t z)
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active rate z.val rewards
      C_star C_h (crossing rate rewards C_star C_h u t z)).1
    (collectionRecord rate rewards C_star C_h u t z k) hmem
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z.val rewards C_star C_h (u.val - start rate rewards C_star C_h u t z + k.val)
    (collectionRecord rate rewards C_star C_h u t z k) hlookup
  have hb := (actual_boundaries rate rewards C_star C_h u t z).1
  refine ⟨hi.1, hi.2.1, hi.2.2, ?_⟩
  change _ = start rate rewards C_star C_h u t z + _ at ht
  omega

/-- The same original strict-past evidence fixes the incoming state and time
of each collection record on the two complete sources. -/
theorem collectionRecord_evidence_erasedSource
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) (k : Fin (t.val - u.val)) :
    (collectionRecord rate rewards C_star C_h u t z k).evidence =
      (collectionRecord rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) k).evidence := by
  obtain ⟨n, hn, he⟩ :=
    ReferenceFirstCollectionRenewalPastLocality.strict_past_evidence_of_firstCollectionCall
      rate rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z) (fun _ => control0)
      (firstCollectionCall_eq rate rewards C_star C_h u t z)
  let offset := u.val - start rate rewards C_star C_h u t z + k.val
  have hk : offset < n := by
    have hb := actual_boundaries rate rewards C_star C_h u t z
    have hk := k.isLt
    change start rate rewards C_star C_h u t z + n = t.val at hn
    dsimp only [offset]
    omega
  have h := congrArg (fun rs : List (ReferenceActivePhysicalHorizon.RoundEvidence
      (p := p) (rate := rate)) => rs[offset]?) he
  have hl := collectionRecord_lookup rate rewards C_star C_h u t z k
  have hr := collectionRecord_lookup rate rewards C_star C_h u t
    (erasedSource rate rewards C_star C_h u t control0 z) k
  rw [start_erasedSource] at hr
  change (((sourceRecords rate rewards C_star C_h u t z).take n).map
    ReferenceActivePhysicalHorizon.RoundRecord.evidence)[offset]? =
      (((sourceRecords rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z)).take n).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence)[offset]? at h
  simp only [List.getElem?_map, List.getElem?_take_of_lt hk, offset, hl, hr,
    Option.map_some, Option.some.injEq] at h
  exact h

/-- Each collection input is unchanged by erasing controls at and after t. -/
theorem collectionCells_erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    collectionCells rate rewards C_star C_h u t z =
      collectionCells rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) := by
  obtain ⟨_, _, _, hleft⟩ := actual_chronological_reconstruction rate rewards C_star C_h u t z
  obtain ⟨_, _, _, hright⟩ := actual_chronological_reconstruction rate rewards C_star C_h u t
    (erasedSource rate rewards C_star C_h u t control0 z)
  apply List.ext_getElem
  · rw [collectionCells_length, collectionCells_length]
  · intro i hi hj
    let k : Fin (t.val - u.val) := ⟨i, by rwa [collectionCells_length] at hi⟩
    obtain ⟨lc, lv, hlc, hl⟩ := hleft k
    obtain ⟨rc, rv, hrc, hr⟩ := hright k
    rw [hl, hr]
    have he := collectionRecord_evidence_erasedSource rate rewards C_star C_h u t control0 z k
    have hf := collectionRecord_facts rate rewards C_star C_h u t z k
    have hg := collectionRecord_facts rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 z) k
    have htime : (collectionRecord rate rewards C_star C_h u t z k).input.time =
        (collectionRecord rate rewards C_star C_h u t
          (erasedSource rate rewards C_star C_h u t control0 z) k).input.time :=
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.time he
    apply collection_cell_eq_of_current rate rewards _ _ lc rc lv rv hlc hrc
      (congrArg ReferenceActivePhysicalHorizon.RoundEvidence.before he)
      (hf.2.1.trans hg.2.1.symm) htime
    dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
    rw [hf.1, hf.2.1, hg.1, hg.2.1, ← htime]
    symm
    apply ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
    have hk := k.isLt
    rw [hf.2.2.2]
    omega

/-- Equality of the complete literal incoming list under strict-past erasure. -/
theorem incoming_prefix_suffix (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    pastCells rate rewards C_star C_h u t z =
      pastCells rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) := by
  unfold pastCells
  rw [liveCells_erasedSource rate rewards C_star C_h u t control0 z,
    collectionCells_erasedSource rate rewards C_star C_h u t control0 z]

theorem incoming_erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    incoming rate rewards C_star C_h u t z =
      incoming rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) :=
  congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate))
    (incoming_prefix_suffix rate rewards C_star C_h u t control0 z)

theorem pastReadout_erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    pastReadout rate rewards C_star C_h u t z =
      pastReadout rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 z) := by
  unfold pastReadout
  rw [incoming_prefix_suffix rate rewards C_star C_h u t control0 z]

/-- The ordinary numerical readout loses no information about the finite
incoming list. No discrete measurable structure is imposed on real inputs. -/
theorem pastReadout_eq_iff (z w : Z) :
    pastReadout rate rewards C_star C_h u t z = pastReadout rate rewards C_star C_h u t w ↔
      pastCells rate rewards C_star C_h u t z = pastCells rate rewards C_star C_h u t w := by
  constructor
  · intro h
    apply ReferenceFirstLiveNumericalPrefixBorel.numericalListReadout_injective (n := p.T)
      (pastCells rate rewards C_star C_h u t z) (pastCells rate rewards C_star C_h u t w)
    · rw [pastCells_length]
      have ht := t.isLt
      unfold pastLength
      omega
    · rw [pastCells_length]
      have ht := t.isLt
      unfold pastLength
      omega
    · exact h
  · intro h
    unfold pastReadout
    rw [h]

private theorem erasedSource_put (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (v : CheckedAssignmentSample.AssignmentVector p) :
    erasedSource rate rewards C_star C_h u t control0
        (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v) =
      erasedSource rate rewards C_star C_h u t control0 z := by
  apply Subtype.ext
  rw [erasedSource_val, erasedSource_val,
    ReferenceFirstCollectionRenewalVectorInsertion.put_val,
    ReferenceFirstCollectionRenewalVectorInsertion.insert_eq_replaceSelectedControlSuffix]
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext j
    by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst j
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val <;> simp only [hv, ite_true, ite_false]
    · have hj' : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z.val t
            (ReferenceFirstCollectionRenewalVectorInsertion.suffix t z.val v)) := hj
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 t.val _ j hj',
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow z.val t _ j hj,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 t.val _ j hj]
  · rfl

local notation "B" => ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "mu" => ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
  rate rewards C_star C_h u t

/-- The retained representative depends on the erased first source only.
The second source is unrestricted on the product carrier. -/
def retainedIncoming (control0 : ContinuousLearningRows.TimeControl p) (b : B) :
    RecordedQueueRun.RunState p.K :=
  incoming rate rewards C_star C_h u t
    (erasedSource rate rewards C_star C_h u t control0 b.1.1)

/-- The no-overflow event for the retained representative. -/
def G_R (control0 : ContinuousLearningRows.TimeControl p) : Set B :=
  {b | (retainedIncoming rate rewards C_star C_h u t control0 b).overflow = false}

/-- The original erased source is a measurable subtype representative on
the exact retained comap field. No function on arbitrary retained tuples is
filled by a fallback source. -/
theorem measurable_erasedSource_retained (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p))]
      (fun b : B => erasedSource rate rewards C_star C_h u t control0 b.1.1) := by
  apply Measurable.subtype_mk
  exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).comp (comap_measurable _)

/-- Actual insertion support supplies the equality of the two source
prefixes almost everywhere on the same finite unnormalized pair law. -/
theorem ae_actual_incoming_factor (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ b : B ∂mu,
      pastCells rate rewards C_star C_h u t b.2 =
        pastCells rate rewards C_star C_h u t
          (erasedSource rate rewards C_star C_h u t control0 b.1.1) ∧
      incoming rate rewards C_star C_h u t b.2 =
        retainedIncoming rate rewards C_star C_h u t control0 b ∧
      ∃ d : ActualRenewalCall rate rewards C_star C_h u t b.2,
        d.record = callRecord rate rewards C_star C_h u t b.2 ∧
        (b ∈ G_R rate rewards C_star C_h u t control0 →
          ∀ j : Fin p.K,
            (AssignmentScoreReconstruction.sourceScore d.out j,
              AssignmentScoreReconstruction.initialQueue d.out j) =
              (incoming rate rewards C_star C_h u t b.2).registers j) := by
  have he := ReferenceFirstCollectionRenewalInstallationCoupling.pair_measurableEmbedding
    rate rewards C_star C_h u t
  have hs := MeasureTheory.ae_map_mem_range he.measurableSet_range he.measurable.aemeasurable
    (μ := ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
      rate rewards C_star C_h u t)
  change ∀ᵐ b : B ∂mu,
    b ∈ Set.range (ReferenceFirstCollectionRenewalInstallationCoupling.pair
      rate rewards C_star C_h u t) at hs
  filter_upwards [hs] with b hb
  obtain ⟨wv, rfl⟩ := hb
  have hprefix : pastCells rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2) =
      pastCells rate rewards C_star C_h u t
        (erasedSource rate rewards C_star C_h u t control0 wv.1.1) := by
    rw [incoming_prefix_suffix rate rewards C_star C_h u t control0
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2),
      erasedSource_put]
  have hrun := congrArg
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)) hprefix
  refine ⟨hprefix, hrun, ?_⟩
  obtain ⟨d, hd, hregisters⟩ := actual_incoming_registers rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2)
  refine ⟨d, hd, ?_⟩
  intro hg
  apply hregisters
  rw [show incoming rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2) =
    incoming rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 wv.1.1) from hrun]
  exact hg

/-- On actual insertion support the retained event is exactly the strict
all-prefix test for the second source's chronological incoming run. -/
theorem ae_G_R_iff_firstOverflow (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ b : B ∂mu,
      b ∈ G_R rate rewards C_star C_h u t control0 ↔
        pastLength rate rewards C_star C_h u t b.2 <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (pastCells rate rewards C_star C_h u t b.2) := by
  filter_upwards [ae_actual_incoming_factor rate rewards C_star C_h u t control0] with b hb
  change (retainedIncoming rate rewards C_star C_h u t control0 b).overflow = false ↔ _
  rw [← hb.2.1]
  exact incoming_noOverflow_iff_firstOverflow rate rewards C_star C_h u t b.2

end Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix

end
