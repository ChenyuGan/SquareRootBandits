/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAssignmentPayloadPersistence

/-!
# Actual later dispatcher installation provenance

The literal later StartRound branch installs the successful reconstruction's
payload before making its arm choice. Sources:
`sources/zip4/manuscript/05_binary_transport.tex:60-68` and
`sources/zip4/manuscript/06_interruptions.tex:41-70,273-282,327-348`.

These are local constructor and physical-record facts. The reconstructed
initial queue is not yet identified with the physical queue, and no run-wide
chronology, successor-placement, or manuscript closure is claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceLaterInstallationProvenance

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

/-- Invert the computed dispatcher itself. Both post-reconstruction choice
outcomes carry the literal installation; a choice failure is not a birth. -/
theorem dispatchCollection_installation (x : CoordinatorRoundDispatch.CollectionInput p) :
    match CoordinatorRoundDispatch.dispatchCollection x with
    | .laterChosen _ _ _ _ _ _ output _ clockData installed _ =>
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | .laterChoiceFailure _ _ _ _ _ _ output _ clockData installed _ =>
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | _ => True := by
  classical
  generalize hcomputed : CoordinatorRoundDispatch.dispatchCollection x = outcome
  unfold CoordinatorRoundDispatch.dispatchCollection at hcomputed
  repeat' first
    | (split at hcomputed)
    | (extract_lets at hcomputed)
    | (subst outcome; trivial)
  · rename_i started hstart core operationLedger weights cutoff selected consistent
      hpending hscores hchoice hframe hcutoff hchoiceActual hnonempty hboundary hinputs
    dsimp only [selected] at hcomputed
    split at hcomputed
    · contradiction
    · subst outcome
      trivial
  · rename_i hclockEquations hfreeze
    rcases hclockEquations with ⟨htime, hkind, hsigma, hcutoff, hgrid, hproposal, hpending, hcommand⟩
    dsimp only at hcomputed
    repeat' first
      | (split at hcomputed)
      | (extract_lets at hcomputed)
      | (subst outcome; trivial)

/-- The physical dispatch retains the same literal installation. All other
physical cuts, including malformed collection cutoffs, impose no condition. -/
theorem dispatch_installation (x : RoundInput p rate) :
    match dispatch x with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ clockData installed _) =>
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | .collection _ _ _ _ (.laterChoiceFailure _ _ _ _ _ _ output _ clockData installed _) =>
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | _ => True := by
  classical
  unfold dispatch
  cases x.state.coordinator with
  | first => trivial
  | live registers owned base => trivial
  | collection payload ledger savedProposal =>
    by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      have hsource := dispatchCollection_installation
        (collectionInput x payload ledger (collectionClock payload ledger savedProposal cutoff) cutoff)
      generalize hresult : CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x payload ledger (collectionClock payload ledger savedProposal cutoff) cutoff) =
          outcome at *
      cases outcome <;> exact hsource
    · simp only [dite_eq_right hcutoff]
  | dagger => trivial

/-- Specialize the constructor producer to the actual physical dispatcher.
The whole payload, its physical timestamp, and every follower's immutable
DOWN q come from this same successful local reconstruction. No assertion
that reconstruction equals the physical queue is used or concluded. -/
theorem dispatch_laterChosen_provenance (x : RoundInput p rate) :
    match dispatch x with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ clockData installed _) =>
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload = output.payload ∧
        installed.registers.payload.sigma.val = x.time.val ∧
        ∀ i : ActiveRoundActions.Follower p.m,
          (installed.registers.payload.downRecord i).val.q =
            AssignmentScoreReconstruction.initialQueue output.reconstruction
              (installed.registers.payload.assignment.assigned i)
    | _ => True := by
  cases hcut : dispatch x with
  | first outcome => trivial
  | live registers owned base outcome => trivial
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> try trivial
    rename_i core consistent started hstart instruction hinstruction output hlocal
      clockData installed selected
    have hinstalled := dispatch_installation x
    rw [hcut] at hinstalled
    refine ⟨hinstalled,
      ReferenceAssignmentPayloadPersistence.laterPayload_eq_successfulStart
        output clockData installed hinstalled,
      ReferenceAssignmentPayloadPersistence.laterPayload_time_of_actual_installation
        x payload ledger clock cutoff core started instruction hstart hinstruction
        output clockData installed hinstalled, ?_⟩
    intro i
    exact (installed.registers.payload.downRecord_initialQueue i).trans
      (ReferenceAssignmentPayloadPersistence.laterPayload_down_queue_reconstruction
        output clockData installed hinstalled (installed.registers.payload.assignment.assigned i))
  | invalidCollectionCutoff => trivial
  | dagger => trivial

/-- A later chosen branch in the actual record is an existing
`InstallationBirth`. The output equality and preparation equality recover
the executed dispatch; the outcome is never supplied independently. This
remains a birth even if the subsequent post-choice tail fails. -/
theorem record_laterChosen_birth
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    match record.output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ReferenceAssignmentPayloadPersistence.InstallationBirth record installed.registers.payload
    | _ => True := by
  have hactual : record.output.preparation.coordinator = dispatch record.input := by
    rw [record.output_eq]
    exact (prepare record.input).coordinator_eq
  have hprovenance := dispatch_laterChosen_provenance record.input
  rw [← hactual] at hprovenance
  cases hcut : record.output.preparation.coordinator with
  | first outcome => trivial
  | live registers owned base outcome => trivial
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> try trivial
    rename_i core consistent started hstart instruction hinstruction output hlocal
      clockData installed selected
    rw [hcut] at hprovenance
    unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
    rw [hcut]
    exact ⟨rfl, hprovenance.2.2.1⟩
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceLaterInstallationProvenance
