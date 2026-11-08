/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNumericalStartReconstruction
public import Bandits.Support.ReferenceFirstCollectionRenewalInstalledServiceTail

/-!
# Numerical replay at the actual first renewal installation and service

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,399-423`
and `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

The canonical numerical reconstruction and the actual renewal call use the
same first empty collection boundary. Their reconstruction results are
identified through the literal operation ledger and successful operation.
The resulting numerical registers initialize the same installed assignment
and its first actual complement service on the original finite pair law.
This is internal numerical service evidence, not a manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionStreamEmptyDispatch

namespace Bandits.Support.ReferenceFirstCollectionRenewalNumericalServiceJoin

variable {p : ConstructorDimensions.Parameters}

section StreamAlignment

variable {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}
    {hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T}
    {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count}

private theorem shared_stream_output
    (f g : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      source rewards C_star C_h count hcross hspan hshort)
    (i : Fin f.ell) (j : Fin g.ell) (hij : i.val = j.val) :
    f.payload = g.payload ∧ f.ledgers i = g.ledgers j ∧ f.saved = g.saved := by
  obtain ⟨r, hr, _, hc, _⟩ := f.output_properties i
  obtain ⟨r', hr', _, hc', _⟩ := g.output_properties j
  have hw : f.window = g.window := f.windowIsActual.trans g.windowIsActual.symm
  rw [hw, hij, hr'] at hr
  have hrecord : r = r' := Option.some.inj hr.symm
  rw [hrecord] at hc
  exact ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
    (hc.symm.trans hc')

/-- Two produced streams on the same original window have the same endpoint
when one ends with empty pending. No equality of dispatch witnesses is used. -/
private theorem first_empty_stream_alignment
    (f g : ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort)
    (hf : f.ledger.pending = ∅) :
    g.stream.ell = f.stream.ell ∧ g.record = f.record ∧
      g.stream.payload = f.stream.payload ∧ g.ledger = f.ledger ∧
      g.stream.saved = f.stream.saved := by
  have hw : f.stream.window = g.stream.window :=
    f.stream.windowIsActual.trans g.stream.windowIsActual.symm
  have hlength : g.stream.ell = f.stream.ell := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : f.stream.ell < g.stream.ell := by omega
      let j : Fin g.stream.ell := ⟨f.last.val, by have h := f.lastIsLast; omega⟩
      have heq := (shared_stream_output f.stream g.stream f.last j rfl).2.1
      have hn := g.allEarlierNonempty j (by
        have h := f.lastIsLast
        change f.last.val + 1 < g.stream.ell
        omega)
      rw [← heq, ← f.ledgerIsLast, hf] at hn
      exact Finset.not_nonempty_empty hn
    · by_contra hnot
      have hlt : g.stream.ell < f.stream.ell := by omega
      cases g.outcome with
      | exhausted _ hex _ _ _ =>
          have hfwindow := f.stream.withinWindow
          rw [hw, ← hex] at hfwindow
          omega
      | empty e =>
          let i : Fin f.stream.ell := ⟨g.last.val, by have h := g.lastIsLast; omega⟩
          have heq := (shared_stream_output f.stream g.stream i g.last rfl).2.1
          have hn := f.allEarlierNonempty i (by
            have h := g.lastIsLast
            change g.last.val + 1 < f.stream.ell
            omega)
          rw [heq, ← g.ledgerIsLast, e.pendingEmpty] at hn
          exact Finset.not_nonempty_empty hn
  have hlast : g.last.val = f.last.val := by
    have hg := g.lastIsLast
    have hf := f.lastIsLast
    omega
  have hrecord : g.record = f.record := by
    have hr := g.recordAt
    rw [← hw, hlast, f.recordAt] at hr
    exact Option.some.inj hr.symm
  obtain ⟨hp, hl, hs⟩ := shared_stream_output g.stream f.stream g.last f.last hlast
  exact ⟨hlength, hrecord, hp, g.ledgerIsLast.trans (hl.trans f.ledgerIsLast.symm), hs⟩

end StreamAlignment

private theorem roundInput_eq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- A canonical dispatch at the actual input reconstructs the actual call's
output. The literal ledger equation is essential: an arbitrary dispatch's
operation ledger has no such identification. -/
private theorem canonical_dispatch_actual_call_alignment
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (k : ActualNextDispatch x payload l saved)
    (hliteral : k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved k.cutoffTime) k.cutoffTime)
      k.core.payload_n_eq)
    (hx : x = d.record.input) :
    payload = d.old ∧ l = d.ledger ∧ saved = d.saved ∧
      k.cutoffTime = u ∧ k.started = d.started ∧
      k.instruction = d.instruction ∧ HEq k.reconstructed d.out := by
  rcases k with ⟨hstate, hvalid, hready, hsigma, horder, hcutcursor, hcursor,
    hfreeze, hassign, hempty, hunit, hmass, hspan, hbank, hclass,
    cutoff, hcut, core, started, hstart, instruction, hi, ledger, consistent,
    ht, hkind, hprep, hiff, hfailure, out, hrec⟩
  change ledger = CoordinatorRoundDispatch.collectionOperationLedger
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
    core.payload_n_eq at hliteral
  change payload = d.old ∧ l = d.ledger ∧ saved = d.saved ∧
    cutoff = u ∧ started = d.started ∧ instruction = d.instruction ∧ HEq out d.out
  subst ledger
  subst x
  have hcoord := hstate.symm.trans d.coordinator_eq
  obtain ⟨hp, hl, hs⟩ := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hcoord
  subst payload
  subst l
  subst saved
  have hc : cutoff = u := by
    apply Fin.ext
    rw [d.cutoff_eq] at hcut
    omega
  subst cutoff
  have hstarted : started = d.started := Except.ok.inj (hstart.symm.trans d.clock_eq)
  subst started
  have hinstruction : instruction = d.instruction := Option.some.inj (hi.symm.trans d.instruction_eq)
  subst instruction
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have heq := hrec.symm.trans d.reconstruction_eq
  injection heq with _ _ hout
  exact heq_of_eq hout

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z)

local notation "source" => z.val
local notation "count" => p.T - ReferenceFirstCollectionReadyStream.startTime
  (rate := rate) z.val rewards C_star C_h

local notation "s" => ReferenceFirstCollectionReadyStream.startTime (rate := rate)
  z.val rewards C_star C_h

/-- Reconstruct the actual call's registers from the same original numerical
prefix. The call data are internal observations supplied by the AE consumer;
no numerical truth or witness equality is assumed. -/
theorem actual_renewal_call_numerical_reconstruction :
    ∃ hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true,
    ∃ hspan : s + count ≤ p.T,
    let L := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z.val rewards C_star C_h hcross count hspan).records
    ∃ hshort : L.length < count,
    let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate z.val rewards C_star C_h hcross count hspan
    let V := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)
    let Vpre := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells.take (L.length - 1)))
    let Rprefix := fun (D : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) (h : ℕ) =>
      QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D.take h))
    let Rwhole := fun (D : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) =>
      QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))
    ∃ g : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let out := g.stream
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧
      head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      (∀ n : Fin out.ell,
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = out.payload ∧
          CollectionBufferProvenance.collectionContext call.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
          (∀ a : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
          (0 < n.val →
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
      (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
        (out.window.take h).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
            ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take h)) ∧
      (∀ n : Fin out.ell,
        let l := out.ledgers n
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        record.output.coordinator.failure = none ∧
        record.output.next.coordinator = .collection out.payload l out.saved ∧
        l.cursor = s + (L).length + 1 + n.val + 1 ∧
        CollectionBufferProvenance.collectionContext l =
          CollectionBufferProvenance.collectionContext head.preLedger ∧
        ∀ a : Fin p.K, l.gammaLoc a = 0 ∧
          (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (¬ CoordinatorCollectionLedger.armPending l a →
            l.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
            l.currentRegisters a = some ⟨(Rprefix D a (n.val + 1)).2,
              (Rprefix D a (n.val + 1)).1 - (Rprefix D a n.val).1⟩ ∧
            l.increment a =
              (QueueReplay.replay (4 * rate.n) (0, (V a).2)
                (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take (n.val + 1)))).1 ∧
            (V a).1 + l.increment a = (Rprefix D a (n.val + 1)).1)) ∧
      (g.ledger.pending = ∅ → ∀ a : Fin p.K,
        g.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
        g.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
          (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
        g.ledger.increment a =
          (QueueReplay.replay (4 * rate.n) (0, (V a).2)
            (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
        (V a).1 + g.ledger.increment a = (Rwhole D a).1) ∧
      (∀ a : Fin p.K, (Vpre a).1 ≤ (V a).1) ∧
      (∀ e, g.outcome = .empty e →
        g.ledger.pending = ∅ ∧
        g.record.output.next.coordinator = .collection g.stream.payload g.ledger g.stream.saved ∧
        (∀ a : Fin p.K,
          g.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
          g.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
            (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
          g.ledger.increment a =
            (QueueReplay.replay (4 * rate.n) (0, (V a).2)
              (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
          (V a).1 + g.ledger.increment a = (Rwhole D a).1) ∧
        (match e.nextBoundary with
        | .terminal _ _ =>
            g.record.input.time.val + 1 = p.T ∧ g.ledger.cursor = p.T + 1
        | .next beforeHorizon _ x _ _ _ _ _ _ _ _ _ =>
            g.record.input.time.val + 1 < p.T ∧
            ReferenceFirstCollectionReadyStream.startTime (rate := rate)
              source rewards C_star C_h ≤ g.record.input.time.val ∧
            x = ReferenceActivePhysicalHorizon.roundInputAt
              (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
                C_star C_h hcross)
              source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                source rewards C_star C_h)
              (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
                rate source rewards C_star C_h hcross).1
              e.prefixRun ⟨g.record.input.time.val + 1, by
                exact ⟨by omega, beforeHorizon⟩⟩ ∧
            x.state = g.record.output.next ∧
            x.time.val = g.record.input.time.val + 1 ∧
            x.rows = source.1.2 ∧
            x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            x.rewards = rewards ∧
            x.time.val = s + (L).length + out.ell ∧
            ∃ k : ActualNextDispatch x out.payload g.ledger out.saved,
              (k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x out.payload g.ledger
                  (ReferenceActivePhysicalStep.collectionClock out.payload g.ledger out.saved
                    k.cutoffTime)
                  k.cutoffTime) k.core.payload_n_eq ∧
              (k.operationLedger.assignment = g.ledger.assignment ∧
                k.operationLedger.sigma = g.ledger.sigma ∧
                k.operationLedger.cutoff = g.ledger.cutoff ∧
                k.operationLedger.freezeAt = g.ledger.freezeAt ∧
                k.operationLedger.baseScore = g.ledger.baseScore ∧
                k.operationLedger.pending = g.ledger.pending ∧
                k.operationLedger.cutoffRegisters = g.ledger.cutoffRegisters ∧
                k.operationLedger.currentRegisters = g.ledger.currentRegisters ∧
                k.operationLedger.increment = g.ledger.increment ∧
                k.operationLedger.gammaLoc = g.ledger.gammaLoc ∧
                k.operationLedger.rawBuffer = g.ledger.rawBuffer ∧
                k.operationLedger.enabledHistory = g.ledger.enabledHistory ∧
                k.operationLedger.cursor = g.ledger.cursor ∧
                k.operationLedger.phase = g.ledger.phase) ∧
              AssignmentScoreReconstruction.reconstructLaterStart k.operationLedger k.instruction =
                .success k.operationLedger k.instruction k.reconstructed ∧
              (CoordinatorCollectionLedger.validLedgerCheck k.operationLedger = true ∧
                k.operationLedger.phase = .ready ∧
                k.operationLedger.cursor = k.instruction.time.val + 1 ∧
                k.operationLedger.pending = ∅ ∧
                k.instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
                  k.operationLedger.freezeAt k.instruction.time ∧
                AssignmentScoreReconstruction.currentOutputDomainsCheck k.operationLedger = true ∧
                AssignmentScoreReconstruction.previousOutputDomainsCheck
                  k.operationLedger k.instruction = true) ∧
              (∀ a, g.ledger.cutoffRegisters a = some (k.reconstructed.registers.cutoff a)) ∧
              (∀ a, g.ledger.currentRegisters a = some (k.reconstructed.registers.current a)) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a =
                (k.reconstructed.registers.cutoff a).score + g.ledger.increment a) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a =
                (k.reconstructed.registers.current a).queue) ∧
              (∀ a, AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  AssignmentScoreReconstruction.sourceScore k.reconstructed a) ∧
              (∀ a, AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  (k.reconstructed.registers.cutoff a).score) ∧
              (∀ a, 0 < AssignmentScoreReconstruction.currentWeight k.reconstructed a) ∧
              (∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight k.reconstructed a) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a ≤
                p.T * ConstructorDimensions.D p) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a ≤
                p.T * ConstructorDimensions.D p) ∧
              (k.instruction.kind = .corrected ↔
                x.time.val + 1 < g.ledger.freezeAt) ∧
              (k.instruction.kind = .renewal ↔
                g.ledger.freezeAt ≤ x.time.val + 1) ∧
              (k.instruction.kind = .corrected →
                AssignmentScoreReconstruction.previousScore k.reconstructed =
                  some (fun a : Fin p.K => (k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService) ∧
                (∀ a, (k.reconstructed.registers.cutoff a).score =
                  ((k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService) +
                  (k.reconstructed.registers.cutoff a).lastService) ∧
                (∃ weights, AssignmentScoreReconstruction.previousWeight k.reconstructed =
                    some weights ∧
                  ∀ a, weights a = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                    ((k.reconstructed.registers.cutoff a).score -
                      (k.reconstructed.registers.cutoff a).lastService)) ∧
                (∀ a, 0 < (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  ((k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService))) ∧
              (k.instruction.kind = .renewal →
                AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed = none)) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.sourceScore k.reconstructed a = (Rwhole D a).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.initialQueue k.reconstructed a = (Rwhole D a).2) ∧
              (∀ a : Fin p.K,
                (k.reconstructed.registers.cutoff a).score = (V a).1 ∧
                (k.reconstructed.registers.cutoff a).queue = (V a).2 ∧
                (k.reconstructed.registers.cutoff a).lastService = (V a).1 - (Vpre a).1) ∧
              (∀ a : Fin p.K,
                (k.reconstructed.registers.current a).queue = (Rwhole D a).2 ∧
                (k.reconstructed.registers.current a).lastService =
                  (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                  (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                  (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1) ∧
              (k.instruction.time.val + 1 < k.operationLedger.freezeAt →
                AssignmentScoreReconstruction.previousScore k.reconstructed =
                  some (fun a : Fin p.K => (Vpre a).1) ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed =
                  some (fun a : Fin p.K =>
                    (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1)) ∧
              (k.operationLedger.freezeAt ≤ k.instruction.time.val + 1 →
                AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed = none))) ∧
      g.stream.payload = d.old ∧ g.ledger = d.ledger ∧ g.stream.saved = d.saved ∧
      s + L.length = u.val ∧ s + L.length + out.ell = t.val ∧
      g.record.input.time.val + 1 = t.val ∧
      (∃ e : EmptyPendingBoundary z.val rewards C_star C_h count hcross hspan hshort
          g.stream g.last g.ledger g.record,
        g.outcome = .empty e ∧
        ∃ (x : ReferenceActivePhysicalStep.RoundInput p rate)
          (k : ActualNextDispatch x g.stream.payload g.ledger g.stream.saved),
          x = d.record.input ∧ x.state = g.record.output.next ∧
          k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceActivePhysicalStep.collectionInput x g.stream.payload g.ledger
              (ReferenceActivePhysicalStep.collectionClock g.stream.payload g.ledger
                g.stream.saved k.cutoffTime) k.cutoffTime) k.core.payload_n_eq ∧
          k.cutoffTime = u ∧ k.started = d.started ∧ k.instruction = d.instruction ∧
          HEq k.reconstructed d.out) ∧
      (∀ a : Fin p.K, AssignmentScoreReconstruction.sourceScore d.out a = (Rwhole D a).1) ∧
      (∀ a : Fin p.K, AssignmentScoreReconstruction.initialQueue d.out a = (Rwhole D a).2) ∧
      (∀ a : Fin p.K,
        (d.out.registers.cutoff a).score = (V a).1 ∧
        (d.out.registers.cutoff a).queue = (V a).2 ∧
        (d.out.registers.cutoff a).lastService = (V a).1 - (Vpre a).1) ∧
      (∀ a : Fin p.K,
        (d.out.registers.current a).queue = (Rwhole D a).2 ∧
        (d.out.registers.current a).lastService =
          (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1) ∧
      (∀ a : Fin p.K, AssignmentScoreReconstruction.currentWeight d.out a =
        (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
      (∀ a : Fin p.K, AssignmentScoreReconstruction.cutoffWeight d.out a =
        (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1) ∧
      (d.instruction.time.val + 1 < d.ledger.freezeAt →
        AssignmentScoreReconstruction.previousScore d.out = some (fun a : Fin p.K => (Vpre a).1) ∧
        AssignmentScoreReconstruction.previousWeight d.out = some (fun a : Fin p.K =>
          (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1)) ∧
      (d.ledger.freezeAt ≤ d.instruction.time.val + 1 →
        AssignmentScoreReconstruction.previousScore d.out = none ∧
        AssignmentScoreReconstruction.previousWeight d.out = none) ∧
      AssignmentScoreReconstruction.previousScore d.out = none ∧
      AssignmentScoreReconstruction.previousWeight d.out = none ∧
      (∀ a : Fin p.K, Rwhole D a = Rprefix D a D.length) := by
  classical
  obtain ⟨hc, hs, hk, f, e, _, hnext, hpayload, hledger, hsaved, htime⟩ :=
    ReferenceFirstCollectionRenewalCallFirstEmptyBoundary.actual_renewal_call_first_empty_boundary
      rate rewards C_star C_h u t z d
  obtain ⟨g, head, initializer, valid, D, hhead, hp, hi, hchecked,
    hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, hBoundary⟩ :=
    ReferenceFirstCollectionNumericalStartReconstruction.actual_first_collection_numerical_next_start_reconstruction
      rate z.val rewards C_star C_h (p.T - s) hc hs hk
  obtain ⟨hlen, hrecord, hgp, hgl, hgs⟩ := first_empty_stream_alignment f g e.pendingEmpty
  have hgp' := hgp.trans hpayload
  have hgl' := hgl.trans hledger
  have hgs' := hgs.trans hsaved
  have hempty : g.ledger.pending = ∅ := by rw [hgl]; exact e.pendingEmpty
  obtain ⟨before, after, xf, hinput, hstate, hnextTime, hrows, hselected,
    hrewards, hwindow, hrun, kf, _, hxf, _⟩ := hnext
  have hfinalTime : g.record.input.time.val + 1 = t.val := by
    rw [hrecord, ← hnextTime, hxf, d.time_eq]
  have hcutoffTime : s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z.val rewards C_star C_h hc (p.T - s) hs).records).length = u.val := by
    have hcxt := (g.stream.context g.last).2.1
    rw [← g.ledgerIsLast, hgl', d.cutoff_eq, g.stream.cutoff.ledgerCutoff] at hcxt
    omega
  have hcanonicalBoundary :
      ∃ eg : EmptyPendingBoundary z.val rewards C_star C_h (p.T - s) hc hs hk
          g.stream g.last g.ledger g.record,
        g.outcome = .empty eg ∧
        ∃ (x : ReferenceActivePhysicalStep.RoundInput p rate)
          (k : ActualNextDispatch x g.stream.payload g.ledger g.stream.saved),
          x = d.record.input ∧ x.state = g.record.output.next ∧
          k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceActivePhysicalStep.collectionInput x g.stream.payload g.ledger
              (ReferenceActivePhysicalStep.collectionClock g.stream.payload g.ledger
                g.stream.saved k.cutoffTime) k.cutoffTime) k.core.payload_n_eq ∧
          k.cutoffTime = u ∧ k.started = d.started ∧ k.instruction = d.instruction ∧
          HEq k.reconstructed d.out := by
    cases houtcome : g.outcome with
    | exhausted hn _ _ _ _ =>
        rw [hempty] at hn
        exact (Finset.not_nonempty_empty hn).elim
    | empty eg =>
        have hnum := hBoundary eg houtcome
        rcases hnum with ⟨_, _, _, hb⟩
        cases hnextG : eg.nextBoundary with
        | terminal hT _ =>
            have ht := t.isLt
            omega
        | next beforeG afterG x original stateG timeG rowsG selectedG rewardsG windowG runG old =>
            rw [hnextG] at hb
            obtain ⟨_, _, _, _, _, _, _, _, _, k, hKdata, _⟩ := hb
            have hcanonical := hKdata.1
            have hx : x = d.record.input := by
              have hstateEq : x.state = xf.state := by rw [stateG, hrecord, ← hstate]
              have htimeEq : x.time = xf.time := by
                apply Fin.ext
                rw [timeG, hrecord, ← hnextTime]
              exact (roundInput_eq x xf hstateEq (rowsG.trans hrows.symm)
                (selectedG.trans hselected.symm) htimeEq
                (rewardsG.trans hrewards.symm)).trans hxf
            obtain ⟨_, _, _, hcut, hstarted, hinstruction, hout⟩ :=
              canonical_dispatch_actual_call_alignment rate rewards C_star C_h u t z d
                x g.stream.payload g.ledger g.stream.saved k hcanonical hx
            exact ⟨eg, rfl, x, k, hx, stateG, hcanonical,
              hcut, hstarted, hinstruction, hout⟩
  have hnum := hEndpoint hempty
  rw [hgl'] at hnum
  have hcut (a : Fin p.K) : d.out.registers.cutoff a =
      ⟨_, _, _⟩ := Option.some.inj ((d.out.registers.cutoff_eq a).symm.trans (hnum a).1)
  have hcur (a : Fin p.K) : d.out.registers.current a =
      ⟨_, _⟩ := Option.some.inj ((d.out.registers.current_eq a).symm.trans (hnum a).2.1)
  let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z.val rewards C_star C_h hc (p.T - s) hs
  let R := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))
  have hscore (a : Fin p.K) : AssignmentScoreReconstruction.sourceScore d.out a = (R a).1 := by
    change (d.out.registers.cutoff a).score + d.ledger.increment a = _
    rw [hcut a]
    exact (hnum a).2.2.2
  have hqueue (a : Fin p.K) : AssignmentScoreReconstruction.initialQueue d.out a = (R a).2 := by
    change (d.out.registers.current a).queue = _
    rw [hcur a]
  have hnone := AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
    _ d.instruction d.out d.reconstruction_eq d.renewal
  refine ⟨hc, hs, hk, g, head, initializer, valid, D, hhead, hp, hi, hchecked,
    hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, ?_,
    hgp', hgl', hgs', hcutoffTime, ?_, hfinalTime, hcanonicalBoundary,
    hscore, hqueue, ?_, ?_, ?_, ?_, ?_, ?_, hnone.1, hnone.2, ?_⟩
  · intro eg hEg
    have hb := hBoundary eg hEg
    cases hnextG : eg.nextBoundary <;> simpa only [hnextG] using hb
  · rw [hlen]
    exact htime
  · intro a
    rw [hcut a]
    exact ⟨rfl, rfl, rfl⟩
  · intro a
    rw [hcur a]
    exact ⟨rfl, rfl⟩
  · intro a
    change (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
      AssignmentScoreReconstruction.sourceScore d.out a = _
    rw [hscore a]
  · intro a
    change (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
      (d.out.registers.cutoff a).score = _
    rw [hcut a]
  · intro hstrict
    have hfreeze := d.freeze_le
    rw [d.instruction_time, d.time_eq] at hstrict
    omega
  · intro _
    exact hnone
  · intro a
    simp only [List.take_length]

end Actual

/-- On the original unnormalized pair law, the same installed renewal
assignment has the numerical replay queues and scores and performs its first
actual enabled complement update, including the first overflow update. -/
theorem ae_pairLaw_actual_numerical_service_join
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalInstallationCoupling.Source
        rate rewards C_star C_h u t ∂
        ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t,
    let z := b.1.1
    let a := b.1.2
    let z' := b.2
    let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) z'.val rewards C_star C_h
    let count := p.T - s
    let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z a
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z',
      let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved
      let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
        CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
      let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
        x.payload ell d.instruction d.out d.reconstruction_eq
      let v := LaterAssignmentStartOperation.ownAssignmentVector
        d.record.input.row d.instruction.time
      let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart
          x.payload ell d.instruction x.row,
          ∃ hlocal : output.localConsistency = consistent,
            LaterAssignmentStartOperation.laterAssignmentStart
                x.payload ell d.instruction x.row consistent =
              .success output hlocal ∧
            v = output.assignmentVector ∧
            output.reconstruction = d.out ∧
            AssignmentParameterFibreKernel.successfulSlowSet p par v =
              some output.slowSet ∧
            output.slowSet = U ∧
            output.payload.slowSet = U ∧
            let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                output := {
              priorClock := x.clock
              pending := x.ledger.pending
              proposalParameterValid := d.core.clock_parameter_valid
              priorClockValid := d.core.clock_registers_valid
              startTimeValid := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  d.instruction_time] using d.core.clock_start_time_valid
              result := d.started
              startRound_eq := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  ReferenceActivePhysicalStep.collectionClock,
                  d.instruction_time] using d.clock_eq
              assignmentStart_eq := d.instruction_eq
              priorSigma_eq := d.core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                calc
                  x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                  _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                  _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
            let installed := CoordinatorAssignmentRegisterInstall.installLater
              output clockData
            installed.registers.payload = output.payload ∧
            output.assignmentVector = installed.assignmentVector ∧
            installed.reconstruction = d.out ∧
            installed.registers.payload.anchor =
              AssignmentScoreReconstruction.currentWeight d.out ∧
            (∀ arm, installed.registers.payload.queues arm =
              AssignmentScoreReconstruction.initialQueue d.out arm) ∧
            (∀ i, installed.retainedBaseScore i =
              AssignmentScoreReconstruction.sourceScore d.out
                (output.payload.assignment.assigned i)) ∧
            installed.registers.payload.slowSet = U ∧
            ∃ selection : CoordinatorRoundDispatch.ArmSelection
                installed.registers.payload d.started d.instruction.time
                installed.registers.complementWeights d.record.input.row,
              CoordinatorLocalArmChoice.coordinatorArmChoice
                  installed.registers.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.instruction.time installed.registers.complementWeights d.record.input.row =
                some selection.arm ∧
              CoordinatorRoundDispatch.dispatchCollection x =
                .laterChosen d.core consistent d.started d.clock_eq d.instruction
                  d.instruction_eq output hlocal clockData installed selection ∧
              d.record.output.preparation =
                ReferenceActivePhysicalStep.prepare d.record.input ∧
              d.record.output.preparation.coordinator =
                .collection d.old d.ledger clock u
                  (CoordinatorRoundDispatch.dispatchCollection x) ∧
              d.record.output.preparation.coordinator.arm = selection.arm ∧
              d.record.output.coordinator =
                ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started ∧
              d.record.output.next.coordinator =
                (ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started).configuration ∧
              let r := installed.registers
              let q := installed.ownedRegisters
              let base := installed.retainedBaseScore
              let P := ReferenceActivePhysicalStep.prepare d.record.input
              ∃ recording : CoordinatorRecordingOperation.Output p,
              ∃ serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                  r q,
              ∃ pending : Finset (Fin (p.m - 1)),
              ∃ finished : CoordinatorPhaseClock.FinishRoundResult p,
                CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.liveRecordingInput
                      P r d.started) = some recording ∧
                CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
                CoordinatorLocalArmChoice.confirmationUpdate
                  r.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.record.input.time d.record.input.row
                  P.coordinatorObservation = some pending ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val d.record.input.time
                  d.started.clock pending d.record.input.row = .ok finished ∧
                d.record.output.coordinator =
                  ReferenceActivePhysicalStep.livePostChoice P r q base d.started ∧
                d.record.output.coordinator.failure = none ∧
                d.record.output.coordinator.recording = some recording ∧
                d.record.output.coordinator.up = none ∧
                d.record.output.coordinator.configuration =
                  .live { payload := r.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := d.record.input.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                    { queue := serviced.queue
                      previousService := serviced.previousService }
                    base ∧
                d.record.output.next.coordinator =
                  .live { payload := r.payload
                          priorClock := finished.clock
                          pendingAtChoice := finished.pending
                          time := d.record.input.time
                          gridBoundary := finished.clock.g
                          complementScores := serviced.score }
                    { queue := serviced.queue
                      previousService := serviced.previousService }
                    base ∧
                (∀ j : CanonicalFastSampling.FastArm
                    r.payload.slowSet,
                  serviced.score j + serviced.queue j ≤
                    (t.val - ReferenceFirstCollectionReadyStream.startTime
                      (rate := rate) b.2.val rewards C_star C_h + 1) *
                      ConstructorDimensions.D p) ∧
                (t.val - ReferenceFirstCollectionReadyStream.startTime
                    (rate := rate) b.2.val rewards C_star C_h + 1) *
                    ConstructorDimensions.D p ≤ p.T * ConstructorDimensions.D p ∧
                ∃ hcross : (ReferenceInitializationRun.output
                  (ActualReferenceInitializationBlock.referenceInput z'.val rewards C_star C_h rate)).crossing.isSome = true,
                ∃ hspan : s + count ≤ p.T,
                let L := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                  (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                    z'.val rewards C_star C_h hcross count hspan).records
                ∃ hshort : L.length < count,
                let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                  rate z'.val rewards C_star C_h hcross count hspan
                let V := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
                  (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)
                let Vpre := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
                  (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells.take (L.length - 1)))
                let Rprefix := fun (D : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) (h : ℕ) =>
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D.take h))
                let Rwhole := fun (D : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) =>
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))
                ∃ g : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                  (p := p) (rate := rate) z'.val rewards C_star C_h count hcross hspan hshort,
                let out := g.stream
                ∃ (head : Choice rate) (initializer : Initializer p)
                  (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
                    (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
                      head.payload head.started head.weights))
                  (D : List (RecordedQueueRun.RoundInput p.K)),
                  choice out.cutoff.cut.input = some head ∧
                  head.payload = out.payload ∧
                  head.initializer = some initializer ∧
                  initializer.checkedStart rate = .success head.preLedger ∧
                  ∃ hDlen : D.length = out.ell,
                  D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
                    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
                  (∀ n : Fin out.ell,
                    let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
                    let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
                    ∃ (call : Choice rate)
                      (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                          call.payload call.started call.weights)),
                      choice record.input = some call ∧ call.payload = out.payload ∧
                      CollectionBufferProvenance.collectionContext call.preLedger =
                        CollectionBufferProvenance.collectionContext head.preLedger ∧
                      cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
                      record.input.rows = z'.val.1.2 ∧
                      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z'.val ∧
                      record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
                      cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
                      cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
                        (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
                      (∀ a : Fin p.K,
                        ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
                          (cell.enabled, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
                      (0 < n.val →
                        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
                  (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
                    (out.window.take h).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
                        ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take h)) ∧
                  (∀ n : Fin out.ell,
                    let l := out.ledgers n
                    let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
                    record.output.coordinator.failure = none ∧
                    record.output.next.coordinator = .collection out.payload l out.saved ∧
                    l.cursor = s + (L).length + 1 + n.val + 1 ∧
                    CollectionBufferProvenance.collectionContext l =
                      CollectionBufferProvenance.collectionContext head.preLedger ∧
                    ∀ a : Fin p.K, l.gammaLoc a = 0 ∧
                      (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
                      (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
                      (¬ CoordinatorCollectionLedger.armPending l a →
                        l.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
                        l.currentRegisters a = some ⟨(Rprefix D a (n.val + 1)).2,
                          (Rprefix D a (n.val + 1)).1 - (Rprefix D a n.val).1⟩ ∧
                        l.increment a =
                          (QueueReplay.replay (4 * rate.n) (0, (V a).2)
                            (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take (n.val + 1)))).1 ∧
                        (V a).1 + l.increment a = (Rprefix D a (n.val + 1)).1)) ∧
                  (g.ledger.pending = ∅ → ∀ a : Fin p.K,
                    g.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
                    g.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
                      (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
                    g.ledger.increment a =
                      (QueueReplay.replay (4 * rate.n) (0, (V a).2)
                        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
                    (V a).1 + g.ledger.increment a = (Rwhole D a).1) ∧
                  (∀ a : Fin p.K, (Vpre a).1 ≤ (V a).1) ∧
                  (∀ e, g.outcome = .empty e →
                    g.ledger.pending = ∅ ∧
                    g.record.output.next.coordinator = .collection g.stream.payload g.ledger g.stream.saved ∧
                    (∀ a : Fin p.K,
                      g.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
                      g.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
                        (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
                      g.ledger.increment a =
                        (QueueReplay.replay (4 * rate.n) (0, (V a).2)
                          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
                      (V a).1 + g.ledger.increment a = (Rwhole D a).1) ∧
                    (match e.nextBoundary with
                    | .terminal _ _ =>
                        g.record.input.time.val + 1 = p.T ∧ g.ledger.cursor = p.T + 1
                    | .next beforeHorizon _ x _ _ _ _ _ _ _ _ _ =>
                        g.record.input.time.val + 1 < p.T ∧
                        ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                          z'.val rewards C_star C_h ≤ g.record.input.time.val ∧
                        x = ReferenceActivePhysicalHorizon.roundInputAt
                          (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z'.val rewards
                            C_star C_h hcross)
                          z'.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'.val) rewards
                          (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                            z'.val rewards C_star C_h)
                          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
                            rate z'.val rewards C_star C_h hcross).1
                          e.prefixRun ⟨g.record.input.time.val + 1, by
                            exact ⟨by omega, beforeHorizon⟩⟩ ∧
                        x.state = g.record.output.next ∧
                        x.time.val = g.record.input.time.val + 1 ∧
                        x.rows = z'.val.1.2 ∧
                        x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z'.val ∧
                        x.rewards = rewards ∧
                        x.time.val = s + (L).length + out.ell ∧
                        ∃ k : ActualNextDispatch x out.payload g.ledger out.saved,
                          (k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                            (ReferenceActivePhysicalStep.collectionInput x out.payload g.ledger
                              (ReferenceActivePhysicalStep.collectionClock out.payload g.ledger out.saved
                                k.cutoffTime)
                              k.cutoffTime) k.core.payload_n_eq ∧
                          (k.operationLedger.assignment = g.ledger.assignment ∧
                            k.operationLedger.sigma = g.ledger.sigma ∧
                            k.operationLedger.cutoff = g.ledger.cutoff ∧
                            k.operationLedger.freezeAt = g.ledger.freezeAt ∧
                            k.operationLedger.baseScore = g.ledger.baseScore ∧
                            k.operationLedger.pending = g.ledger.pending ∧
                            k.operationLedger.cutoffRegisters = g.ledger.cutoffRegisters ∧
                            k.operationLedger.currentRegisters = g.ledger.currentRegisters ∧
                            k.operationLedger.increment = g.ledger.increment ∧
                            k.operationLedger.gammaLoc = g.ledger.gammaLoc ∧
                            k.operationLedger.rawBuffer = g.ledger.rawBuffer ∧
                            k.operationLedger.enabledHistory = g.ledger.enabledHistory ∧
                            k.operationLedger.cursor = g.ledger.cursor ∧
                            k.operationLedger.phase = g.ledger.phase) ∧
                          AssignmentScoreReconstruction.reconstructLaterStart k.operationLedger k.instruction =
                            .success k.operationLedger k.instruction k.reconstructed ∧
                          (CoordinatorCollectionLedger.validLedgerCheck k.operationLedger = true ∧
                            k.operationLedger.phase = .ready ∧
                            k.operationLedger.cursor = k.instruction.time.val + 1 ∧
                            k.operationLedger.pending = ∅ ∧
                            k.instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
                              k.operationLedger.freezeAt k.instruction.time ∧
                            AssignmentScoreReconstruction.currentOutputDomainsCheck k.operationLedger = true ∧
                            AssignmentScoreReconstruction.previousOutputDomainsCheck
                              k.operationLedger k.instruction = true) ∧
                          (∀ a, g.ledger.cutoffRegisters a = some (k.reconstructed.registers.cutoff a)) ∧
                          (∀ a, g.ledger.currentRegisters a = some (k.reconstructed.registers.current a)) ∧
                          (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a =
                            (k.reconstructed.registers.cutoff a).score + g.ledger.increment a) ∧
                          (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a =
                            (k.reconstructed.registers.current a).queue) ∧
                          (∀ a, AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                            (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                              AssignmentScoreReconstruction.sourceScore k.reconstructed a) ∧
                          (∀ a, AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                            (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                              (k.reconstructed.registers.cutoff a).score) ∧
                          (∀ a, 0 < AssignmentScoreReconstruction.currentWeight k.reconstructed a) ∧
                          (∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight k.reconstructed a) ∧
                          (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a ≤
                            p.T * ConstructorDimensions.D p) ∧
                          (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a ≤
                            p.T * ConstructorDimensions.D p) ∧
                          (k.instruction.kind = .corrected ↔
                            x.time.val + 1 < g.ledger.freezeAt) ∧
                          (k.instruction.kind = .renewal ↔
                            g.ledger.freezeAt ≤ x.time.val + 1) ∧
                          (k.instruction.kind = .corrected →
                            AssignmentScoreReconstruction.previousScore k.reconstructed =
                              some (fun a : Fin p.K => (k.reconstructed.registers.cutoff a).score -
                                (k.reconstructed.registers.cutoff a).lastService) ∧
                            (∀ a, (k.reconstructed.registers.cutoff a).score =
                              ((k.reconstructed.registers.cutoff a).score -
                                (k.reconstructed.registers.cutoff a).lastService) +
                              (k.reconstructed.registers.cutoff a).lastService) ∧
                            (∃ weights, AssignmentScoreReconstruction.previousWeight k.reconstructed =
                                some weights ∧
                              ∀ a, weights a = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                                ((k.reconstructed.registers.cutoff a).score -
                                  (k.reconstructed.registers.cutoff a).lastService)) ∧
                            (∀ a, 0 < (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                              ((k.reconstructed.registers.cutoff a).score -
                                (k.reconstructed.registers.cutoff a).lastService))) ∧
                          (k.instruction.kind = .renewal →
                            AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                            AssignmentScoreReconstruction.previousWeight k.reconstructed = none)) ∧
                          (∀ a : Fin p.K,
                            AssignmentScoreReconstruction.sourceScore k.reconstructed a = (Rwhole D a).1) ∧
                          (∀ a : Fin p.K,
                            AssignmentScoreReconstruction.initialQueue k.reconstructed a = (Rwhole D a).2) ∧
                          (∀ a : Fin p.K,
                            (k.reconstructed.registers.cutoff a).score = (V a).1 ∧
                            (k.reconstructed.registers.cutoff a).queue = (V a).2 ∧
                            (k.reconstructed.registers.cutoff a).lastService = (V a).1 - (Vpre a).1) ∧
                          (∀ a : Fin p.K,
                            (k.reconstructed.registers.current a).queue = (Rwhole D a).2 ∧
                            (k.reconstructed.registers.current a).lastService =
                              (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1) ∧
                          (∀ a : Fin p.K,
                            AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                              (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
                          (∀ a : Fin p.K,
                            AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                              (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1) ∧
                          (k.instruction.time.val + 1 < k.operationLedger.freezeAt →
                            AssignmentScoreReconstruction.previousScore k.reconstructed =
                              some (fun a : Fin p.K => (Vpre a).1) ∧
                            AssignmentScoreReconstruction.previousWeight k.reconstructed =
                              some (fun a : Fin p.K =>
                                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1)) ∧
                          (k.operationLedger.freezeAt ≤ k.instruction.time.val + 1 →
                            AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                            AssignmentScoreReconstruction.previousWeight k.reconstructed = none))) ∧
                  g.stream.payload = d.old ∧ g.ledger = d.ledger ∧ g.stream.saved = d.saved ∧
                  s + L.length = u.val ∧ s + L.length + out.ell = t.val ∧
                  g.record.input.time.val + 1 = t.val ∧
                  (∃ e : EmptyPendingBoundary z'.val rewards C_star C_h count hcross hspan hshort
                      g.stream g.last g.ledger g.record,
                    g.outcome = .empty e ∧
                    ∃ (x : ReferenceActivePhysicalStep.RoundInput p rate)
                      (k : ActualNextDispatch x g.stream.payload g.ledger g.stream.saved),
                      x = d.record.input ∧ x.state = g.record.output.next ∧
                      k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                        (ReferenceActivePhysicalStep.collectionInput x g.stream.payload g.ledger
                          (ReferenceActivePhysicalStep.collectionClock g.stream.payload g.ledger
                            g.stream.saved k.cutoffTime) k.cutoffTime) k.core.payload_n_eq ∧
                      k.cutoffTime = u ∧ k.started = d.started ∧ k.instruction = d.instruction ∧
                      HEq k.reconstructed d.out) ∧
                  (∀ a : Fin p.K, AssignmentScoreReconstruction.sourceScore d.out a = (Rwhole D a).1) ∧
                  (∀ a : Fin p.K, AssignmentScoreReconstruction.initialQueue d.out a = (Rwhole D a).2) ∧
                  (∀ a : Fin p.K,
                    (d.out.registers.cutoff a).score = (V a).1 ∧
                    (d.out.registers.cutoff a).queue = (V a).2 ∧
                    (d.out.registers.cutoff a).lastService = (V a).1 - (Vpre a).1) ∧
                  (∀ a : Fin p.K,
                    (d.out.registers.current a).queue = (Rwhole D a).2 ∧
                    (d.out.registers.current a).lastService =
                      (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1) ∧
                  (∀ a : Fin p.K, AssignmentScoreReconstruction.currentWeight d.out a =
                    (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
                  (∀ a : Fin p.K, AssignmentScoreReconstruction.cutoffWeight d.out a =
                    (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1) ∧
                  (d.instruction.time.val + 1 < d.ledger.freezeAt →
                    AssignmentScoreReconstruction.previousScore d.out = some (fun a : Fin p.K => (Vpre a).1) ∧
                    AssignmentScoreReconstruction.previousWeight d.out = some (fun a : Fin p.K =>
                      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1)) ∧
                  (d.ledger.freezeAt ≤ d.instruction.time.val + 1 →
                    AssignmentScoreReconstruction.previousScore d.out = none ∧
                    AssignmentScoreReconstruction.previousWeight d.out = none) ∧
                  AssignmentScoreReconstruction.previousScore d.out = none ∧
                  AssignmentScoreReconstruction.previousWeight d.out = none ∧
                  (∀ a : Fin p.K, Rwhole D a = Rprefix D a D.length) ∧
                      (∀ a : Fin p.K, r.payload.anchor a =
                        (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
                      (∀ a : Fin p.K, r.payload.queues a = (Rwhole D a).2) ∧
                      (∀ i : Fin (p.m - 1), base i =
                        (Rwhole D (output.payload.assignment.assigned i)).1) ∧
                      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                        r.complementScores j = (Rwhole D j.val).1 ∧
                        q.queue j = (Rwhole D j.val).2 ∧
                        q.previousService j = (Rprefix D j.val out.ell).1 -
                          (Rprefix D j.val (out.ell - 1)).1) ∧
                      r.payload.sigma = t ∧
                      (∀ i : ActiveRoundActions.Follower p.m,
                        (r.payload.downRecord i).val =
                          ⟨t.val + 1, (r.payload.assignment.assigned i).val + 1,
                            r.payload.assignment.auxiliary.val + 1,
                            r.payload.exponent (r.payload.assignment.assigned i),
                            (Rwhole D (r.payload.assignment.assigned i)).2⟩) ∧
                      (∀ i : ActiveRoundActions.Follower p.m,
                        OrdinaryMessageCodec.dyadicRate (r.payload.downRecord i).val.h =
                          CanonicalRecordingRates.xi p rate.eta.val
                            (fun a => (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1)
                            (r.payload.assignment.assigned i)) ∧
                      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                        QueueReplay.transition (4 * rate.n) (Rwhole D j.val)
                          (true, serviced.arrival j) = (serviced.score j, serviced.queue j)) := by
  classical
  filter_upwards
    [ReferenceFirstCollectionRenewalInstalledServiceTail.ae_pairLaw_actual_service_tail
      rate rewards C_star C_h u t] with b hb
  dsimp only at hb
  rcases hb with ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction,
    hsample, hslow, hpayloadSlow, htail⟩
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
    CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
    x.payload ell d.instruction d.out d.reconstruction_eq
  let v := LaterAssignmentStartOperation.ownAssignmentVector
    d.record.input.row d.instruction.time
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  let r := installed.registers
  let q := installed.ownedRegisters
  let base := installed.retainedBaseScore
  rcases htail with ⟨hinstalledPayload, hinstalledVector, hinstalledReconstruction,
    hanchor, hqueues, hbase, hinstalledSlow, selection, hselection, hdispatch,
    hpreparation, hpreparationCoordinator, hselectedArm, hpostChoice, hnextChoice,
    recording, serviced, pending, finished, hrecord, hservice, hconfirmation, hfinish,
    hcoordinator, hfailure, hrecordingField, hupField, hconfiguration, hnextConfiguration,
    hserviceBudget, htotalHorizon⟩
  obtain ⟨hc, hs, hk, g, head, initializer, valid, D, hhead, hp, hi, hchecked,
    hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, hBoundary,
    hgp, hgl, hgs, hcutoffTime, htime, hfinalTime, hcanonicalBoundary,
    hscore, hqueue, hcut, hcur, hweight, hcutWeight, hpreviousStrict,
    hpreviousRenewal, hnoneScore, hnoneWeight, hwholePrefix⟩ :=
    actual_renewal_call_numerical_reconstruction rate rewards C_star C_h u t b.2 d
  let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate b.2.val rewards C_star C_h hc
      (p.T - ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        b.2.val rewards C_star C_h) hs
  let R := fun a : Fin p.K => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))
  have hanchorNum (a : Fin p.K) : r.payload.anchor a =
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (R a).1 := by
    rw [hanchor]
    exact hweight a
  have hqueuesNum (a : Fin p.K) : r.payload.queues a = (R a).2 :=
    (hqueues a).trans (hqueue a)
  have hbaseNum (i : Fin (p.m - 1)) : base i =
      (R (output.payload.assignment.assigned i)).1 :=
    (hbase i).trans (hscore _)
  have hcomplementNum (j : CanonicalFastSampling.FastArm r.payload.slowSet) :
      r.complementScores j = (R j.val).1 := by
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementScores j = _
    rw [CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
      output clockData j, hreconstruction]
    exact hscore j.val
  have hownedNum (j : CanonicalFastSampling.FastArm r.payload.slowSet) :
      q.queue j = (R j.val).2 := by
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters.queue j = _
    rw [CoordinatorAssignmentRegisterInstall.later_owned_queue_eq_initial_queue
      output clockData j, hreconstruction]
    exact hqueue j.val
  have hsigma : r.payload.sigma = t :=
    output.payload_start.trans (d.instruction_time.trans d.time_eq)
  have hanchorFunction : r.payload.anchor = fun a =>
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (R a).1 := funext hanchorNum
  refine ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction, hsample,
    hslow, hpayloadSlow, ?_⟩
  refine ⟨hinstalledPayload, hinstalledVector, hinstalledReconstruction, hanchor,
    hqueues, hbase, hinstalledSlow, selection, hselection, hdispatch, hpreparation,
    hpreparationCoordinator, hselectedArm, hpostChoice, hnextChoice,
    recording, serviced, pending, finished, hrecord, hservice, hconfirmation, hfinish,
    hcoordinator, hfailure, hrecordingField, hupField, hconfiguration, hnextConfiguration,
    hserviceBudget, htotalHorizon, ?_⟩
  refine ⟨hc, hs, hk, g, head, initializer, valid, D, hhead, hp, hi, hchecked,
    hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, ?_,
    hgp, hgl, hgs, hcutoffTime, htime, hfinalTime, hcanonicalBoundary,
    hscore, hqueue, hcut, hcur, hweight, hcutWeight, hpreviousStrict,
    hpreviousRenewal, hnoneScore, hnoneWeight, hwholePrefix, hanchorNum, hqueuesNum, hbaseNum,
    ?_, hsigma, ?_, ?_, ?_⟩
  · intro eg hEg
    have hb := hBoundary eg hEg
    cases hnextG : eg.nextBoundary <;> simpa only [hnextG] using hb
  · intro j
    refine ⟨hcomplementNum j, hownedNum j, ?_⟩
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters.previousService j = _
    rw [CoordinatorAssignmentRegisterInstall.later_owned_previous_service_eq_current_register
      output clockData j, hreconstruction]
    exact (hcur j.val).2
  · intro i
    have hfields := LaterAssignmentStartOperation.successful_downRecord_fields output i
    rw [hreconstruction, d.instruction_time, d.time_eq, hqueue] at hfields
    exact hfields
  · intro i
    have hrate := LaterAssignmentStartOperation.successful_downRecord_rate output i
    change OrdinaryMessageCodec.dyadicRate (r.payload.downRecord i).val.h =
      CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor
        (r.payload.assignment.assigned i) at hrate
    rw [hanchorFunction] at hrate
    exact hrate
  · intro j
    have htransition := CoordinatorLiveServiceFinish.serviced_queueReplay_transition r q serviced j
    rw [ReferenceActivePhysicalStep.payload_n_eq r.payload,
      hcomplementNum j, hownedNum j] at htransition
    exact htransition

end Bandits.Support.ReferenceFirstCollectionRenewalNumericalServiceJoin

end
