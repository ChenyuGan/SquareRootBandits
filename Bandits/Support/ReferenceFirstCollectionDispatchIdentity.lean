/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownAmbiguityDetector

import Lean.Elab.Tactic.Omega

/-!
# Observable identity of actual initialized collection dispatches

Two independently constructed dispatch witnesses on the same source inputs
have the same observable collection window, payload, saved value, length, and
ledger at every shared index.  This does not identify the dispatch structures
or their proof fields.

Source context: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionDispatchIdentity

/-- Observable uniqueness for any two actual initialized dispatch witnesses
on the same original source, complete rewards, epoch, and rate. -/
theorem actual_initialized_collection_dispatch_observables
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : Real) (count : Nat)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count <= p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d1 d2 : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    d1.stream.window = d2.stream.window ∧
    d1.stream.payload = d2.stream.payload ∧
    d1.stream.saved = d2.stream.saved ∧
    d1.stream.ell = d2.stream.ell ∧
    (∀ n1 : Fin d1.stream.ell, ∀ n2 : Fin d2.stream.ell,
      n1.val = n2.val → d1.stream.ledgers n1 = d2.stream.ledgers n2) ∧
    d1.stream.cutoff.cut = d2.stream.cutoff.cut ∧
    d1.stream.cutoff.payload = d2.stream.cutoff.payload ∧
    d1.stream.cutoff.ledger = d2.stream.cutoff.ledger ∧
    d1.stream.cutoff.saved = d2.stream.cutoff.saved ∧
    d1.last.val = d2.last.val ∧
    d1.ledger = d2.ledger ∧
    d1.record = d2.record := by
  classical
  let o1 := d1.stream
  let o2 := d2.stream

  have hwindow : o1.window = o2.window :=
    o1.windowIsActual.trans o2.windowIsActual.symm

  have hcut : o1.cutoff.cut = o2.cutoff.cut :=
    Option.some.inj (o1.cutoff.cutIndex.symm.trans o2.cutoff.cutIndex)

  have hcutCoordinator :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          o1.cutoff.payload o1.cutoff.ledger o1.cutoff.saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          o2.cutoff.payload o2.cutoff.ledger o2.cutoff.saved := by
    calc
      _ = o1.cutoff.cut.output.next.coordinator := o1.cutoff.outputCoordinator.symm
      _ = o2.cutoff.cut.output.next.coordinator := by rw [hcut]
      _ = _ := o2.cutoff.outputCoordinator

  injection hcutCoordinator with hcutPayload hcutLedger hcutSaved

  have hpayload : o1.payload = o2.payload := by
    calc
      o1.payload = o1.cutoff.payload := o1.payloadMatchesCutoff
      _ = o2.cutoff.payload := hcutPayload
      _ = o2.payload := o2.payloadMatchesCutoff.symm

  have hsaved : o1.saved = o2.saved := by
    calc
      o1.saved = o1.cutoff.saved := o1.savedMatchesCutoff
      _ = o2.cutoff.saved := hcutSaved
      _ = o2.saved := o2.savedMatchesCutoff.symm

  have hledgerAtSameIndex : ∀ (n1 : Fin o1.ell) (n2 : Fin o2.ell),
      n1.val = n2.val → o1.ledgers n1 = o2.ledgers n2 := by
    intro n1 n2 hval
    by_cases hzero : n1.val = 0
    · have hzero2 : n2.val = 0 := by omega
      have hfirst1 : o1.ledgers n1 = o1.cutoff.ledger := by
        rw [o1.ledgers_are_outputs]
        simp only [hzero, List.getElem_cons_zero]
      have hfirst2 : o2.ledgers n2 = o2.cutoff.ledger := by
        rw [o2.ledgers_are_outputs]
        simp only [hzero2, List.getElem_cons_zero]
      calc
        o1.ledgers n1 = o1.cutoff.ledger := hfirst1
        _ = o2.cutoff.ledger := hcutLedger
        _ = o2.ledgers n2 := hfirst2.symm
    · obtain ⟨r1, hget1, _hfailure1, hnext1, _hvalid1, _hphase1,
        _hcursor1, _hgamma1, _hservice1, _hincrement1⟩ :=
          o1.output_properties n1
      obtain ⟨r2, hget2, _hfailure2, hnext2, _hvalid2, _hphase2,
        _hcursor2, _hgamma2, _hservice2, _hincrement2⟩ :=
          o2.output_properties n2
      have hget1' : o2.window[n2.val]? = some r1 := by
        rw [← hval, ← hwindow]
        exact hget1
      have hr : r1 = r2 := Option.some.inj (hget1'.symm.trans hget2)
      have hnext :
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
              o1.payload (o1.ledgers n1) o1.saved =
            ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
              o2.payload (o2.ledgers n2) o2.saved := by
        calc
          _ = r1.output.next.coordinator := hnext1.symm
          _ = r2.output.next.coordinator := by rw [hr]
          _ = _ := hnext2
      injection hnext with _ hledger _

  have hell : o1.ell = o2.ell := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : o2.ell < o1.ell := by omega
      have hshorterWindow : o2.ell < o1.window.length :=
        lt_of_lt_of_le hlt o1.withinWindow
      have hshorterWindow' : o2.ell < o2.window.length := by
        rw [← hwindow]
        exact hshorterWindow
      let n1 : Fin o1.ell := ⟨o2.ell - 1, by omega⟩
      let n2 : Fin o2.ell := ⟨o2.ell - 1, by have hp := o2.positiveLength; omega⟩
      have hempty : (o2.ledgers n2).pending = ∅ := by
        simpa [n2] using o2.last_empty_of_not_exhausted hshorterWindow'
      have hbefore : n1.val + 1 < o1.ell := by
        change o2.ell - 1 + 1 < o1.ell
        rw [Nat.sub_add_cancel o2.positiveLength]
        exact hlt
      have hpending : (o1.ledgers n1).pending.Nonempty :=
        o1.pending_before_last n1 hbefore
      have hsame := hledgerAtSameIndex n1 n2 (by simp [n1, n2])
      rw [← hsame] at hempty
      simp [hempty] at hpending
    · by_contra hnot
      have hlt : o1.ell < o2.ell := by omega
      have hshorterWindow : o1.ell < o2.window.length :=
        lt_of_lt_of_le hlt o2.withinWindow
      have hshorterWindow' : o1.ell < o1.window.length := by
        rw [hwindow]
        exact hshorterWindow
      let n1 : Fin o1.ell := ⟨o1.ell - 1, by have hp := o1.positiveLength; omega⟩
      let n2 : Fin o2.ell := ⟨o1.ell - 1, by omega⟩
      have hempty : (o1.ledgers n1).pending = ∅ := by
        simpa [n1] using o1.last_empty_of_not_exhausted hshorterWindow'
      have hbefore : n2.val + 1 < o2.ell := by
        change o1.ell - 1 + 1 < o2.ell
        rw [Nat.sub_add_cancel o1.positiveLength]
        exact hlt
      have hpending : (o2.ledgers n2).pending.Nonempty :=
        o2.pending_before_last n2 hbefore
      have hsame := hledgerAtSameIndex n1 n2 (by simp [n1, n2])
      rw [hsame] at hempty
      simp [hempty] at hpending

  have hlastVal : d1.last.val = d2.last.val := by
    have h1 := d1.lastIsLast
    have h2 := d2.lastIsLast
    dsimp [o1, o2] at hell
    omega

  have hterminalLedger : d1.ledger = d2.ledger := by
    calc
      d1.ledger = o1.ledgers d1.last := d1.ledgerIsLast
      _ = o2.ledgers d2.last := hledgerAtSameIndex d1.last d2.last hlastVal
      _ = d2.ledger := d2.ledgerIsLast.symm

  have hterminalRecord : d1.record = d2.record := by
    have hget1' : o2.window[d2.last.val]? = some d1.record := by
      rw [← hlastVal, ← hwindow]
      exact d1.recordAt
    exact Option.some.inj (hget1'.symm.trans d2.recordAt)

  exact ⟨hwindow, hpayload, hsaved, hell, hledgerAtSameIndex,
    hcut, hcutPayload, hcutLedger, hcutSaved, hlastVal,
    hterminalLedger, hterminalRecord⟩

end Bandits.Support.ReferenceFirstCollectionDispatchIdentity
