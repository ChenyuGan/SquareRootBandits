/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
public import Bandits.Support.ReferenceCompleteObservationPrefixInformation

import Lean.Elab.Tactic.Omega

/-!
# Borel information in the actual first-renewal incoming queue

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,399-423`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The numerical observations below are projections of the existing actual cells.
Their real vectors have their ordinary product Borel structures. The raw
complete observation supplies the cutoff head; original record lookups identify
it with the canonical prefix. No new execution or probability law is defined.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceCompleteNumericalBranchObservation
open ReferenceActiveHorizonMeasurability
open ReferenceFirstCollectionCheckedSourcePrefix
open ReferenceLaterCollectionArrivalReadout
open ReferenceLaterCollectionSourceReadoutMeasurability

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
local notation "Code" => ReferenceFirstLiveNumericalPrefixBorel.NumericalCellReadout p

/-- The raw collection head is identified by its original physical index and
its actual choice, rather than by a chosen stream's length. -/
theorem cutoffReadout_zero (z : Z) :
    laterCollectionReadout 0 (cutoffRecord rate rewards C_star C_h u t z) =
      some (cutoffCell rate rewards C_star C_h u t z) := by
  let hc := crossing rate rewards C_star C_h u t z
  have hepoch := completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z.val hc
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have hw : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z.val rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z.val)).records).length =
        u.val - start rate rewards C_star C_h u t z := by
    rw [← hepoch]
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (sourceRecords rate rewards C_star C_h u t z)).length = _
    omega
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z.val rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z.val)).records).length <
        p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
    rw [hw]
    change _ < p.T - start rate rewards C_star C_h u t z
    have ht := t.isLt
    omega
  obtain ⟨_, _, d, _, _, _, D, _, _, _, _, hDlen, _, hcells⟩ :=
    actualFirstCollectionRawObservationIdentity rate rewards C_star C_h z.val hc hshort
  let n : Fin d.stream.ell := ⟨0, by have h := d.stream.positiveLength; omega⟩
  obtain ⟨call, valid, hcall, _, _, hcell, _, _, _, _, _, _, _, _, hread, _⟩ := hcells n
  have hi := (d.stream.alignment ⟨0,
    lt_of_lt_of_le n.isLt d.stream.withinWindow⟩).1
  have hw' := hw
  rw [← hepoch] at hw'
  rw [← hepoch, hw'] at hi
  have hlookup := List.getElem?_eq_getElem (cutoff_index_lt rate rewards C_star C_h u t z)
  change (sourceRecords rate rewards C_star C_h u t z)[
    u.val - start rate rewards C_star C_h u t z]? =
      some (cutoffRecord rate rewards C_star C_h u t z) at hlookup
  simp only [Nat.add_zero] at hi
  have hr := Option.some.inj (hi.symm.trans hlookup)
  dsimp only [n] at hcall hcell hread
  rw [hr] at hcall
  have hchoice : call = cutoffChoice rate rewards C_star C_h u t z :=
    Option.some.inj (hcall.symm.trans (cutoffChoice_eq rate rewards C_star C_h u t z))
  rw [hcell] at hread
  have he : sourceCell rate
      (d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow)) call rewards valid =
      cutoffCell rate rewards C_star C_h u t z := by
    unfold cutoffCell
    congr 1
  simpa only [hr] using hread.trans (congrArg some he)

private theorem readout_zero_of_some (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout s record = some cell) :
    laterCollectionReadout 0 record = some cell := by
  classical
  have hp : (laterCollectionReadout s record).isSome = true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ := (laterCollectionReadout_domain s record).mp hp
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa only [laterCollectionReadout, dite_eq_left hf, hcoord] using hread
      | _ => simp only [hcoord] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hg : s < registers.payload.sigma.val := by simpa only [hcoord] using hb
          have hg0 : 0 < registers.payload.sigma.val := by omega
          simpa only [laterCollectionReadout, dite_eq_left hf, hcoord, hg, hg0, ite_true] using hread
      | _ => simp only [hcoord] at hb
  | first outcome => cases outcome <;> simp only [hcoord] at hb
  | invalidCollectionCutoff => simp only [hcoord] at hb
  | dagger => simp only [hcoord] at hb

/-- Every canonical collection entry, including the head and disabled dates,
is the raw unmasked collection readout of its original record. -/
theorem collectionReadout_zero (z : Z) (k : Fin (t.val - u.val)) :
    laterCollectionReadout 0 (collectionRecord rate rewards C_star C_h u t z k) =
      some ((collectionCells rate rewards C_star C_h u t z)[k.val]'(by
        rw [collectionCells_length]; exact k.isLt)) := by
  by_cases hk : k.val = 0
  · have hr : collectionRecord rate rewards C_star C_h u t z k =
        cutoffRecord rate rewards C_star C_h u t z := by
      have h := collectionRecord_lookup rate rewards C_star C_h u t z k
      rw [hk, Nat.add_zero] at h
      exact Option.some.inj (h.symm.trans (List.getElem?_eq_getElem
        (cutoff_index_lt rate rewards C_star C_h u t z)))
    rw [hr]
    simpa only [hk, collectionCells, readoutPrefix, List.getElem_cons_zero] using
      cutoffReadout_zero rate rewards C_star C_h u t z
  · let q : Fin (t.val - u.val - 1) := ⟨k.val - 1, by have h := k.isLt; omega⟩
    have h := readoutPrefix_readout rate (start rate rewards C_star C_h u t z)
      (collectionRecords rate rewards C_star C_h u t z)
      ⟨t.val - u.val - 1, collection_index_lt rate rewards C_star C_h u t z⟩
      (cutoffCell rate rewards C_star C_h u t z)
      (collectionReadout_present rate rewards C_star C_h u t z) q
    have hq : q.val + 1 = k.val := by dsimp only [q]; omega
    apply readout_zero_of_some rate (start rate rewards C_star C_h u t z)
    simpa only [collectionRecord, collectionCells, hq] using h

/-- The same whole-source observation supplies the four canonical fields at
the exact complete-suffix index `u - start + k`. -/
theorem rawCollection_lookup (z : Z) (k : Fin (t.val - u.val)) :
    (rawCollectionNumericalDecoder rate
      (completeBranchObservation rate rewards C_star C_h z.val))[
        u.val - start rate rewards C_star C_h u t z + k.val]? =
      some ((collectionRecord rate rewards C_star C_h u t z k).input.time,
        some (numericalCoordinates
          ((collectionCells rate rewards C_star C_h u t z)[k.val]'(by
            rw [collectionCells_length]; exact k.isLt)))) := by
  rw [rawCollectionNumericalDecoder_completeSuffixRecords]
  simp only [List.getElem?_map]
  have hl := collectionRecord_lookup rate rewards C_star C_h u t z k
  unfold sourceRecords at hl
  rw [hl, Option.map_some, collectionReadout_zero]
  rfl

private def eraseDate : Unit ⊕ (Fin p.T × Option Code) → Unit ⊕ Code
  | .inl _ => .inl ()
  | .inr (_, none) => .inl ()
  | .inr (_, some c) => .inr c

private theorem measurable_eraseDate : Measurable (eraseDate (p := p)) := by
  have he : Measurable (Equiv.optionEquivSumPUnit Code) := comap_measurable _
  have h : Measurable (fun c : Option Code =>
      Sum.elim (fun a : Code => (Sum.inr a : Unit ⊕ Code))
        (fun _ : PUnit => Sum.inl ()) (Equiv.optionEquivSumPUnit Code c)) :=
    (measurable_inr.sumElim measurable_const).comp he
  have hi : Measurable (fun e : Fin p.T × Option Code =>
      eraseDate (Sum.inr e)) := by
    convert h.comp measurable_snd using 1
    funext e
    rcases e with ⟨v, c⟩
    cases c <;> rfl
  exact measurable_const.sumElim hi

private theorem measurable_tag_remove {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A] (f : X → A)
    (h : Measurable (fun x => (Sum.inr (f x) : Unit ⊕ A))) : Measurable f := by
  intro s hs
  convert h hs.inr_image using 1
  ext x
  simp

private theorem measurable_variable_observation {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A]
    (f : X → List A) (hf : Measurable f) (j : X → ℕ) (hj : Measurable j) :
    Measurable (fun x => listObservationAt (f x) (j x)) := by
  have ho := measurable_snd.comp (measurable_listObservationCoordinates.comp hf)
  have he : Measurable (fun v : (ℕ → Unit ⊕ A) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact he.comp (ho.prodMk hj)

/-- Borelness of an actual collection cell's complete real vectors and marker.
The domain is the original renewal source, with no assignment-sigma filter. -/
theorem measurable_collectionCellCoordinates (k : Fin (t.val - u.val)) :
    Measurable (fun z : Z => numericalCoordinates
      ((collectionCells rate rewards C_star C_h u t z)[k.val]'(by
        rw [collectionCells_length]; exact k.isLt))) := by
  have hsource : Measurable (fun z : Z => z.val) := measurable_subtype_coe
  have hraw := (measurable_rawCollectionNumericalDecoder rate).comp
    ((measurable_completeBranchObservation rate rewards C_star C_h).comp hsource)
  have hstart : Measurable (start rate rewards C_star C_h u t) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp hsource
  have hj : Measurable (fun z : Z => u.val - start rate rewards C_star C_h u t z + k.val) :=
    (measurable_of_countable (fun s : ℕ => u.val - s + k.val)).comp hstart
  have h := (measurable_eraseDate (p := p)).comp
    (measurable_variable_observation _ hraw _ hj)
  apply measurable_tag_remove
  convert h using 1
  funext z
  simp only [Function.comp_apply, listObservationAt, rawCollection_lookup, eraseDate]

private theorem measurable_collectionTag (n : ℕ) :
    Measurable (fun z : Z =>
      match (collectionCells rate rewards C_star C_h u t z)[n]? with
      | none => (Sum.inl () : Unit ⊕ Code)
      | some c => Sum.inr (numericalCoordinates c)) := by
  by_cases hn : n < t.val - u.val
  · have h := (measurable_inr (α := Unit)).comp
      (measurable_collectionCellCoordinates rate rewards C_star C_h u t ⟨n, hn⟩)
    convert h using 1
    funext z
    rw [List.getElem?_eq_getElem (by rw [collectionCells_length]; exact hn)]
    rfl
  · have heq : (fun z : Z =>
        match (collectionCells rate rewards C_star C_h u t z)[n]? with
        | none => (Sum.inl () : Unit ⊕ Code)
        | some c => Sum.inr (numericalCoordinates c)) = fun _ => Sum.inl () := by
      funext z
      rw [List.getElem?_eq_none (by rw [collectionCells_length]; omega)]
    rw [heq]
    exact measurable_const

/-- The complete four-field readout of the original chronological prefix is
Borel on the whole renewal source. Disabled cells remain present. -/
theorem measurable_pastReadout :
    Measurable (pastReadout rate rewards C_star C_h u t) := by
  classical
  have hstart : Measurable (start rate rewards C_star C_h u t) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hlen : Measurable (fun z : Z => (liveCells rate rewards C_star C_h u t z).length) := by
    simpa only [liveCells_length, Function.comp_def] using
      (measurable_of_countable (fun s : ℕ => u.val - s)).comp hstart
  have hcollection : Measurable (fun z : Z => fun n : ℕ =>
      match (collectionCells rate rewards C_star C_h u t z)[n]? with
      | none => (Sum.inl () : Unit ⊕ Code)
      | some c => Sum.inr (numericalCoordinates c)) :=
    measurable_pi_iff.mpr (measurable_collectionTag rate rewards C_star C_h u t)
  have heval : Measurable (fun v : (ℕ → Unit ⊕ Code) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  have hlive := measurable_liveReadout rate rewards C_star C_h u t
    (Classical.choice (inferInstance : Nonempty (ContinuousLearningRows.TimeControl p)))
  apply measurable_pi_iff.mpr
  intro k
  have hindex : Measurable (fun z : Z => k.val - (liveCells rate rewards C_star C_h u t z).length) :=
    (measurable_of_countable (fun n : ℕ => k.val - n)).comp hlen
  have htail := heval.comp (hcollection.prodMk hindex)
  have hhead := (measurable_pi_apply k).comp hlive
  have h : Measurable (fun z : Z =>
      if k.val < (liveCells rate rewards C_star C_h u t z).length then
        liveReadout rate rewards C_star C_h u t z k
      else match (collectionCells rate rewards C_star C_h u t z)[
          k.val - (liveCells rate rewards C_star C_h u t z).length]? with
        | none => (Sum.inl () : Unit ⊕ Code)
        | some c => Sum.inr (numericalCoordinates c)) :=
    hhead.ite (measurableSet_lt (measurable_const (a := k.val)) hlen) htail
  convert h using 1
  funext z
  unfold pastReadout pastCells liveReadout
  by_cases hk : k.val < (liveCells rate rewards C_star C_h u t z).length
  · rw [ite_eq_left hk, List.getElem?_append_left hk]
  · rw [ite_eq_right hk, List.getElem?_append_right (Nat.le_of_not_gt hk)]
    rfl

/-- A projection of the existing run state, without a measurable-space
instance on the operational state itself. -/
def stateReadout {K : ℕ} (state : RecordedQueueRun.RunState K) :
    (Fin K → ℕ × ℕ) × (Bool × (Fin K → List (Bool × ℕ))) :=
  (state.registers, state.overflow, state.records)

private instance recordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective (listObservationCoordinates (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Sum.inr.injEq] using he
    have hm := measurable_listObservationCoordinates (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton (listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_stepReadout {X : Type*} [MeasurableSpace X]
    (state : X → RecordedQueueRun.RunState p.K)
    (cell : X → RecordedQueueRun.RoundInput p.K)
    (hs : Measurable (fun x => stateReadout (state x)))
    (hc : Measurable (fun x => numericalCoordinates (cell x))) :
    Measurable (fun x => stateReadout
      (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state x) (cell x))) := by
  classical
  have hreg := measurable_fst.comp hs
  have hflag := measurable_fst.comp (measurable_snd.comp hs)
  have hrecords := measurable_snd.comp (measurable_snd.comp hs)
  have henabled := measurable_fst.comp hc
  have harrivals := measurable_snd.comp ((measurable_arrivalsFromNumerical rate).comp hc)
  have hrecs : Measurable (fun x => fun j : Fin p.K =>
      RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state x) (cell x) j) := by
    apply measurable_pi_iff.mpr
    intro j
    have h := (measurable_of_countable (fun v : Bool × (Bool × ℕ) =>
      if v.1 then (false, 0) else if v.2.1 then (true, v.2.2) else (false, 0))).comp
        (hflag.prodMk (henabled.prodMk ((measurable_pi_apply j).comp harrivals)))
    exact h
  have hnext : Measurable (fun x => fun j : Fin p.K =>
      QueueReplay.transition (4 * rate.n) ((state x).registers j)
        (RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (state x) (cell x) j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : (ℕ × ℕ) × (Bool × ℕ) =>
      QueueReplay.transition (4 * rate.n) v.1 v.2)).comp
        (((measurable_pi_apply j).comp hreg).prodMk ((measurable_pi_apply j).comp hrecs))
  have hover : Measurable (fun x => (state x).overflow ||
      decide (∃ j : Fin p.K, 32 *
        (QueueReplay.transition (4 * rate.n) ((state x).registers j)
          (RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (state x) (cell x) j)).2 > (ReferenceFirstLaunchNumericalCell.queueParameters rate).D)) :=
    (measurable_of_countable (fun v : Bool × (Fin p.K → ℕ × ℕ) =>
      v.1 || decide (∃ j, 32 * (v.2 j).2 >
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D))).comp (hflag.prodMk hnext)
  have hhistory : Measurable (fun x => fun j : Fin p.K => (state x).records j ++
      [RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (state x) (cell x) j]) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_of_countable (fun v : List (Bool × ℕ) × (Bool × ℕ) =>
      v.1 ++ [v.2])).comp
        (((measurable_pi_apply j).comp hrecords).prodMk ((measurable_pi_apply j).comp hrecs))
  exact hnext.prodMk (hover.prodMk hhistory)

private theorem execute_append {K : ℕ} (q : RecordedQueueRun.Parameters)
    (left right : List (RecordedQueueRun.RoundInput K)) (state : RecordedQueueRun.RunState K) :
    RecordedQueueRun.execute q (left ++ right) state =
      RecordedQueueRun.execute q right (RecordedQueueRun.execute q left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons cell left ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih (RecordedQueueRun.step q state cell)

private theorem run_take_succ {K : ℕ} (q : RecordedQueueRun.Parameters)
    (cells : List (RecordedQueueRun.RoundInput K)) (n : ℕ) (hn : n < cells.length) :
    RecordedQueueRun.run q (cells.take (n + 1)) =
      RecordedQueueRun.step q (RecordedQueueRun.run q (cells.take n)) cells[n] := by
  rw [← List.take_append_getElem hn, RecordedQueueRun.run, execute_append]
  rfl

private theorem measurable_pastLength :
    Measurable (pastLength rate rewards C_star C_h u t) := by
  exact (measurable_of_countable (fun s : ℕ => t.val - s)).comp
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe)

private theorem measurable_run_take (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : Z => stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((pastCells rate rewards C_star C_h u t z).take n))) := by
  classical
  induction n with
  | zero =>
      simp only [List.take_zero]
      exact measurable_const
  | succ n ih =>
      have hprev := ih (by omega)
      let present : Set Z := {z | n < (pastCells rate rewards C_star C_h u t z).length}
      have hlength : Measurable (fun z : Z => (pastCells rate rewards C_star C_h u t z).length) := by
        simpa only [pastCells_length] using measurable_pastLength rate rewards C_star C_h u t
      have hp : MeasurableSet present :=
        measurableSet_lt (measurable_const (a := n)) hlength
      apply measurable_of_restrict_of_restrict_compl hp
      · let cell (x : present) : RecordedQueueRun.RoundInput p.K :=
          (pastCells rate rewards C_star C_h u t x.val)[n]'x.property
        have hc : Measurable (fun x : present => numericalCoordinates (cell x)) := by
          apply measurable_tag_remove
          have hsource : Measurable (fun x : present => x.val) := measurable_subtype_coe
          have h := ((measurable_pi_apply (⟨n, by omega⟩ : Fin p.T)).comp
            (measurable_pastReadout rate rewards C_star C_h u t)).comp hsource
          convert h using 1
          funext x
          simp only [Function.comp_apply, pastReadout,
            List.getElem?_eq_getElem x.property]
          rfl
        have h := measurable_stepReadout rate
          (fun x : present => RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((pastCells rate rewards C_star C_h u t x.val).take n)) cell
          (hprev.comp measurable_subtype_coe) hc
        convert h using 1
        funext x
        exact congrArg stateReadout (run_take_succ
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (pastCells rate rewards C_star C_h u t x.val) n x.property)
      · have hsource : Measurable (fun x : (presentᶜ : Set Z) => x.val) := measurable_subtype_coe
        convert hprev.comp hsource using 1
        funext x
        have hx : (pastCells rate rewards C_star C_h u t x.val).length ≤ n := by
          have h : ¬ n < (pastCells rate rewards C_star C_h u t x.val).length := x.property
          exact Nat.le_of_not_gt h
        change stateReadout (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((pastCells rate rewards C_star C_h u t x.val).take (n + 1))) =
          stateReadout (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            ((pastCells rate rewards C_star C_h u t x.val).take n))
        rw [List.take_of_length_le (by omega :
          (pastCells rate rewards C_star C_h u t x.val).length ≤ n + 1),
          List.take_of_length_le hx]

/-- The original stopped run's registers, overflow flag and all accepted
records are jointly Borel. This uses the literal update, including its first
overflow update, on actual source cells only. -/
theorem measurable_incomingReadout :
    Measurable (incomingReadout rate rewards C_star C_h u t) := by
  have h := measurable_run_take rate rewards C_star C_h u t p.T (Nat.le_refl _)
  convert h using 1
  funext z
  have hlen : (pastCells rate rewards C_star C_h u t z).length ≤ p.T := by
    rw [pastCells_length]
    unfold pastLength
    have ht := t.isLt
    omega
  rw [List.take_of_length_le hlen]
  rfl

/-- The existing injective readout determines the existing queue output. -/
theorem incomingReadout_eq_of_pastReadout_eq (z w : Z)
    (h : pastReadout rate rewards C_star C_h u t z =
      pastReadout rate rewards C_star C_h u t w) :
    incomingReadout rate rewards C_star C_h u t z =
      incomingReadout rate rewards C_star C_h u t w := by
  have hc := (pastReadout_eq_iff rate rewards C_star C_h u t z w).mp h
  unfold incomingReadout incoming
  rw [hc]

local notation "B" => ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "F_R" control0 => MeasurableSpace.comap
  (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0)
  (inferInstance : MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p))

/-- Borelness on the exact retained comap field, using its original
source-valued representative. The arbitrary second source is not factored
pointwise through that field. -/
theorem measurable_retainedIncomingReadout (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[F_R control0] (fun b : B => incomingReadout rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 b.1.1)) :=
  (measurable_incomingReadout rate rewards C_star C_h u t).comp
    (measurable_erasedSource_retained rate rewards C_star C_h u t control0)

/-- The exact existing retained registers, with no measurable space on RunState. -/
theorem measurable_retainedIncoming_registers (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[F_R control0] (fun b : B =>
      (retainedIncoming rate rewards C_star C_h u t control0 b).registers) :=
  measurable_fst.comp (measurable_retainedIncomingReadout rate rewards C_star C_h u t control0)

/-- The exact existing retained overflow flag. -/
theorem measurable_retainedIncoming_overflow (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[F_R control0] (fun b : B =>
      (retainedIncoming rate rewards C_star C_h u t control0 b).overflow) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_retainedIncomingReadout rate rewards C_star C_h u t control0))

/-- The exact existing retained accepted-record histories. -/
theorem measurable_retainedIncoming_records (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable[F_R control0] (fun b : B =>
      (retainedIncoming rate rewards C_star C_h u t control0 b).records) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_retainedIncomingReadout rate rewards C_star C_h u t control0))

/-- The retained no-past-overflow event is Borel on the exact retained field. -/
theorem measurableSet_G_R (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet[F_R control0] (G_R rate rewards C_star C_h u t control0) :=
  (measurable_retainedIncoming_overflow rate rewards C_star C_h u t control0)
    (MeasurableSet.singleton false)

/-- The accepted producer's actual-insertion factor transports the full
readout on the same finite unnormalized pair law, including zero-mass strata. -/
theorem ae_incomingReadout_eq_retained (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ b : B ∂ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t,
      incomingReadout rate rewards C_star C_h u t b.2 =
        incomingReadout rate rewards C_star C_h u t
          (erasedSource rate rewards C_star C_h u t control0 b.1.1) := by
  filter_upwards [ae_actual_incoming_factor rate rewards C_star C_h u t control0] with b hb
  exact congrArg stateReadout hb.2.1

end Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability

end
