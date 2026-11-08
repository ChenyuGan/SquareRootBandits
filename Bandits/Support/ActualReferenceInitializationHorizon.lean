/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationPrefix
public import Bandits.Support.ActualInitializationLaunchState
public import Bandits.Support.GeneratedCandidateControllerBridge
public import Bandits.Support.GeneratedFalseForwardEvent

/-!
# Deterministic actual/reference initialization horizon assembly

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-156`,
`sources/zip4/manuscript/appendix_b_communication.tex:101-126,294-326`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`.

Internal mathematics for the existing source run, original full published
output and private coordinates, actual grid rewards, and shared constants.
The only global exclusions are the literal operational initialization failure
and the existing all-block virtual false-forward event. Incoming relations,
parser exclusions, clean prefixes and post-pending force complements are
proved from these inputs. No probability estimate, approved source anchor,
postlaunch physical transition or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActualReferenceInitializationBlock
open scoped Classical

namespace Bandits.Support.ActualReferenceInitializationHorizon

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters}

/-- The input used by the physical comparison is exactly the selected-output
input used by the existing virtual false-forward event. -/
theorem referenceInput_eq_publishedOutput
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) :
    referenceInput source rewards C_star C_h rate =
      GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h rate.eta rewards
        (ActualInitializationPhysicalStep.selectedRowIndex p source) source := rfl

/-- A genuine noncrossed run opportunity has completed exactly its index. -/
theorem run_completed_eq_of_no_crossing (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none) :
    (ReferenceInitializationRun.run x r).completed = r := by
  rcases ReferenceInitializationRun.run_progress x r hr with hcross | hcompleted
  · rw [hc] at hcross
    cases hcross
  · exact hcompleted

/-- Every offending generated parser decision is the literal suppressed-DOWN
cause, with its carried partial bank and strict prelaunch physical endpoint. -/
theorem generatedBlockDown_false_of_no_initialization_failure
    (x : ReferenceInitializationRun.Input p)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure x)
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none)
    (h : (ReferenceInitializationRun.run x r).completed < n_boot p)
    (i : Follower p.m) :
    ¬ InitializationFailureProvenance.generatedBlockDown x
      (ReferenceInitializationRun.run x r) h i := by
  intro hbad
  have hcompleted := run_completed_eq_of_no_crossing x r (Nat.le_of_lt hr) hc
  have hsuppressed := (InitializationFailureProvenance.generatedBlockDown_current_iff
    x r hr h hc hcompleted i).mp hbad
  exact hinit (Or.inr ⟨i, ⟨r, hr⟩, hsuppressed⟩)

private theorem cleanPrefix_of_inactive {s : Fin (n_boot p)}
    (phys : BootstrapPhysicalBlock.Input p s) (rows : CompletePublicTable.CompleteRows p)
    (j : {i // i ∈ phys.uninformed}) (J : Fin (M p))
    (ha : phys.active j = false) :
    BootstrapAllCandidateController.cleanPrefix phys rows j J p.T := by
  intro k _ v _ hpass
  have hempty : BootstrapAllCandidateController.eligiblePrefix phys rows j v k = ∅ := by
    simp only [BootstrapAllCandidateController.eligiblePrefix,
      BootstrapAllCandidateController.candidateEligible,
      BootstrapAllCandidateController.positiveRound, ha, Bool.false_eq_true,
      and_false, false_and, Finset.filter_false]
  have hquota := hpass.1
  rw [hempty, Finset.card_empty] at hquota
  exact (Nat.not_le_of_gt (BootstrapAllCandidateController.q_dec_pos p)) hquota

private theorem actualPhysicalBlock_eq_of_boundary
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (s : Fin (n_boot p))
    (hp : GeneratedForwardPrefixTests.processesBlock x s)
    (hb : GeneratedForwardPrefixTests.actualBoundary x s = b)
    (hs : ReferenceInitializationRun.nextBlock b h = s) :
    GeneratedForwardPrefixTests.actualPhysicalBlock x s hp =
      hs ▸ ReferenceInitializationRun.physical x b h := by
  cases hb
  rfl

private theorem cleanPrefix_of_physical_eq {s : Fin (n_boot p)}
    (left right : BootstrapPhysicalBlock.Input p s) (heq : left = right)
    (rows : CompletePublicTable.CompleteRows p)
    (i : {i // i ∈ left.uninformed}) (j : {j // j ∈ right.uninformed})
    (hij : i.val = j.val) (J : Fin (M p))
    (hclean : BootstrapAllCandidateController.cleanPrefix left rows i J p.T) :
    BootstrapAllCandidateController.cleanPrefix right rows j J p.T := by
  cases heq
  have hj : i = j := Subtype.ext hij
  cases hj
  exact hclean

/-- Literal all-block virtual-event exclusion gives the generated controller's
clean prefix. Inactive followers cannot reach the positive quota. The
`actualPhysicalBlock` index transport is proved against this same run. -/
theorem cleanPrefix_of_no_actual_false_forward
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p)
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run
      (referenceInput source rewards C_star C_h rate) r).crossing = none)
    (h : (ReferenceInitializationRun.run
      (referenceInput source rewards C_star C_h rate) r).completed < n_boot p)
    (i : Fin (p.m - 1))
    (hi : refFollower i ∈ (ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.run (referenceInput source rewards C_star C_h rate) r) h).uninformed) :
    BootstrapAllCandidateController.cleanPrefix
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.run (referenceInput source rewards C_star C_h rate) r) h)
      source.1.2 ⟨refFollower i, hi⟩
      (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T := by
  let x := referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.run x r
  let s := ReferenceInitializationRun.nextBlock b h
  have hcompleted : b.completed = r :=
    run_completed_eq_of_no_crossing x r (Nat.le_of_lt hr) hc
  have hsval : s.val = r := hcompleted
  have hprocess : GeneratedForwardPrefixTests.processesBlock x s := by
    change (ReferenceInitializationRun.run x s.val).crossing = none ∧
      (ReferenceInitializationRun.run x s.val).completed = s.val
    rw [hsval]
    exact ⟨hc, hcompleted⟩
  have hphysical : GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess =
      ReferenceInitializationRun.physical x b h := by
    exact actualPhysicalBlock_eq_of_boundary x b h s hprocess
      (congrArg (ReferenceInitializationRun.run x) hsval) rfl
  have hi' : refFollower i ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).uninformed := by
    rw [hphysical]
    exact hi
  let j : {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).uninformed} :=
    ⟨refFollower i, hi'⟩
  have hclean : BootstrapAllCandidateController.cleanPrefix
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess) source.1.2 j
      (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T := by
    cases ha : (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).active j with
    | false => exact cleanPrefix_of_inactive _ _ j _ ha
    | true =>
        let active : GeneratedForwardPrefixTests.ActiveIncomingFollower x s hprocess := ⟨j, ha⟩
        apply GeneratedCandidateControllerBridge.cleanPrefix_of_no_virtual_failure
          x s hprocess active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        intro hbad
        have hmem : source ∈ GeneratedFalseForwardEvent.actualFalseForwardPrefixPassSet
            C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source)
            s (refFollower i) := by
          exact ⟨hprocess, active, rfl, hbad⟩
        exact hfalse (Set.mem_iUnion_of_mem s (Set.mem_iUnion_of_mem (refFollower i) hmem))
  exact cleanPrefix_of_physical_eq _ _ hphysical source.1.2 j
    ⟨refFollower i, hi⟩ rfl _ hclean

/-- The source complement forbids correction after pending declarations have
already been applied. Prior forced-failure and incoming-index facts come from
the genuine incoming relation, rather than from a pre-pending substitute. -/
theorem forced_false_of_no_initialization_failure
    (x : ReferenceInitializationRun.Input p)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure x)
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none)
    (hcompleted : (ReferenceInitializationRun.run x r).completed = r)
    (h : (ReferenceInitializationRun.run x r).completed < n_boot p)
    (hprior : ∀ i, (ReferenceInitializationRun.run x r).forcedFailure i = false) :
    ∀ i, ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x r) h i = false := by
  intro i
  cases hf : ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x r) h i with
  | false => rfl
  | true =>
      exact False.elim (hinit (Or.inl ⟨i, ⟨r, hr⟩,
        (InitializationFailureProvenance.forcedCorrectionAt_current_iff
          x r hr hc hcompleted i (hprior i)).mpr hf⟩))

/-- Continued incoming and successor relations for the original source run,
including actual gain numerators/weights and effective declaration data in
the existing relation. Both global hypotheses are literal event complements. -/
theorem sourceInitializedRun_continued_related
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source)) :
    let x := referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    ∀ execution ∈ result.continuedBlocks,
      BlockStartRelated source rewards C_star C_h rate execution.block execution.carry
        (ReferenceInitializationRun.run x execution.block.val)
        (result.records.take (BootstrapObservedFollower.blockStart p execution.block)) ∧
      ∃ h : (ReferenceInitializationRun.run x execution.block.val).completed < n_boot p,
        execution.next.val = execution.block.val + 1 ∧
        BlockStartRelated source rewards C_star C_h rate execution.next execution.nextCarry
          (ReferenceInitializationRun.finishBlock x
            (ReferenceInitializationRun.run x execution.block.val) h)
          (result.records.take (BootstrapObservedFollower.blockStart p execution.next)) := by
  exact ActualReferenceInitializationPrefix.sourceInitializedRun_continued_prefix_related
    p rate source rewards C_star C_h
    (fun r hr hc h => generatedBlockDown_false_of_no_initialization_failure _ hinit r hr hc h)
    (fun r hr hc h => cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate
      hfalse r hr hc h)


/-- The accepted prefix witness at the actual terminal block, with its real
incoming carry, original/result constants, stored-fold HEq and whole record
split. The final conjunct discharges the post-pending correction obligation. -/
theorem sourceInitializedRun_terminal_incoming
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source)) :
    let x := referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    ∃ actual : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
      ∃ h : (ReferenceInitializationRun.run x result.terminalBlock.val).completed < n_boot p,
        BlockStartRelated source rewards C_star C_h rate result.terminalBlock actual
          (ReferenceInitializationRun.run x result.terminalBlock.val)
          (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
        actual.C_star = C_star ∧ actual.C_h = C_h ∧
        actual.C_star = result.terminalC_star ∧ actual.C_h = result.terminalC_h ∧
        HEq result.terminalFold
          (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards actual) ∧
        result.records = result.records.take
          (BootstrapObservedFollower.blockStart p result.terminalBlock) ++ result.terminalFold.records ∧
        ∀ i, ReferenceInitializationRun.forced x
          (ReferenceInitializationRun.run x result.terminalBlock.val) h i = false := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, hr, hstar, hch, hresultStar, hresultCH, hfold, hrecords⟩ :=
    ActualReferenceInitializationPrefix.sourceInitializedRun_terminal_incoming_prefix
      p rate source rewards C_star C_h
      (fun r hr hc h => generatedBlockDown_false_of_no_initialization_failure x hinit r hr hc h)
      (fun r hr hc h => cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate
        hfalse r hr hc h)
  have h : (ReferenceInitializationRun.run x result.terminalBlock.val).completed < n_boot p := by
    rw [hr.1]
    exact result.terminalBlock.isLt
  exact ⟨actual, h, hr, hstar, hch, hresultStar, hresultCH, hfold, hrecords,
    forced_false_of_no_initialization_failure x hinit result.terminalBlock.val
      result.terminalBlock.isLt hr.2.1 hr.1 h hr.2.2.1⟩

/-- Local assembly only: the incoming relation, generated event complements,
stored fold and its constants are explicit inputs. Global source-run exports
below obtain every one of them from the two literal event complements. -/
private theorem terminal_fold_output_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate s)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate s actual b past)
    (hb : b = ReferenceInitializationRun.run (referenceInput source rewards C_star C_h rate) s.val)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (referenceInput source rewards C_star C_h rate) b h i = false)
    (C_star' C_h' : ℝ)
    (folded : ActualInitializationRun.BlockFoldOutput p rate s source rewards C_star' C_h' 0)
    (hstar : actual.C_star = C_star') (hch : actual.C_h = C_h')
    (hfold : HEq folded (ActualInitializationRun.foldBlock p rate s source rewards actual))
    (hstopped : ∀ next carry,
      (ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
        C_star' C_h' folded).disposition ≠ .continueNext next carry) :
    let x := referenceInput source rewards C_star C_h rate
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded
    ReferenceInitializationRun.output x = ReferenceInitializationRun.finishBlock x b h ∧
      past_related (past ++ folded.records) (ReferenceInitializationRun.output x) ∧
      folded.phase.monitorState.counters = (ReferenceInitializationRun.output x).counters ∧
      (∀ i, (ReferenceInitializationRun.output x).forcedFailure i = false) ∧
      ∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i)) := by
  have hs : s = ReferenceInitializationRun.nextBlock b h := Fin.ext hr.1.symm
  subst s
  subst C_star'
  subst C_h'
  have hfoldEq := eq_of_heq hfold
  subst folded
  let x := referenceInput source rewards C_star C_h rate
  change b = ReferenceInitializationRun.run x b.completed at hb
  have hstep : ReferenceInitializationRun.run x (b.completed + 1) =
      ReferenceInitializationRun.finishBlock x b h := by
    rw [ReferenceInitializationRun.run_succ, ← hb]
    exact ReferenceInitializationRun.advance_of_no_crossing x b hr.2.1 h
  cases hd : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition with
  | continueNext next carry =>
      exact False.elim (hstopped next carry hd)
  | launched launch seed =>
      obtain ⟨_, _, _, _, _, _, hcross, _, _, _, _, _, _⟩ :=
        ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_crossing
          source rewards rate C_star C_h b h actual past hr hdown launch seed hd
      have hsome : (ReferenceInitializationRun.run x (b.completed + 1)).crossing.isSome = true := by
        rw [hstep, hcross]
        rfl
      have hout : ReferenceInitializationRun.output x = ReferenceInitializationRun.finishBlock x b h :=
        (ReferenceInitializationRun.output_eq_of_crossing x (b.completed + 1)
          (Nat.succ_le_of_lt h) hsome).trans hstep
      obtain ⟨_, hpast, hforced, hfollowers, _⟩ :=
        ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch seed hd
      refine ⟨hout, ?_, ?_, ?_, ?_⟩
      · rw [hout]
        exact hpast
      · rw [hout]
        exact ActualReferenceInitializationBoundary.foldBlock_updatedCounters_eq
          source rewards rate C_star C_h b h actual past hr hdown
      · rw [hout]
        exact hforced
      · rw [hout]
        exact hfollowers
  | exhausted live =>
      obtain ⟨hlast, _, _, hcounters, _, hforced, hpast, hfollowers, _⟩ :=
        ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_exhausted_related
          source rewards rate C_star C_h b h actual past hr hdown hclean live hd
      have hout : ReferenceInitializationRun.output x = ReferenceInitializationRun.finishBlock x b h := by
        change ReferenceInitializationRun.run x (n_boot p) = _
        rw [← hlast]
        exact hstep
      refine ⟨hout, ?_, ?_, ?_, ?_⟩
      · rw [hout]
        exact hpast
      · rw [hout]
        exact hcounters
      · rw [hout]
        exact hforced
      · rw [hout]
        exact hfollowers

private theorem terminalDisposition_ne_continue
    {rate : RateInput p} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {startBlock : Fin (n_boot p)}
    {startCarry : ActualInitializationRun.BlockCarry p rate startBlock}
    (result : ActualInitializationHorizon.RunSuffix p rate source rewards startBlock startCarry)
    (next : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate next) :
    result.terminalDisposition ≠ .continueNext next carry := by
  rcases result with ⟨block, cs, ch, folded, handoff, heq, disposition, hdisposition,
    hstopped, hcs, hch, records, continued, hindices, hterminal, hbefore, hchron⟩
  cases disposition with
  | continueNext next' carry' => exact fun _ => hstopped
  | launched launch seed => intro hd; cases hd
  | exhausted live => intro hd; cases hd

/-- The complete actual record list is the chronological reference output
history, with every player's actual actions and own normalized observations.
The terminal updated counter vector and actual boundary follower carries are
also those of this same reference output. -/
theorem sourceInitializedRun_output_related
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source)) :
    let x := referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (∃ h : (ReferenceInitializationRun.run x result.terminalBlock.val).completed < n_boot p,
      ReferenceInitializationRun.output x = ReferenceInitializationRun.finishBlock x
        (ReferenceInitializationRun.run x result.terminalBlock.val) h) ∧
      past_related result.records (ReferenceInitializationRun.output x) ∧
      result.terminalFold.phase.monitorState.counters = (ReferenceInitializationRun.output x).counters ∧
      (∀ i, (ReferenceInitializationRun.output x).forcedFailure i = false) ∧
      ∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (result.terminalHandoff.followers i)) := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, h, hr, _, _, hstar, hch, hfold, hrecords, hforce⟩ :=
    sourceInitializedRun_terminal_incoming p rate source rewards C_star C_h hinit hfalse
  have hstopped : ∀ next carry,
      (ActualInitializationRun.combinedBoundaryHandoff p rate result.terminalBlock
        source rewards result.terminalC_star result.terminalC_h result.terminalFold).disposition ≠
          .continueNext next carry := by
    rw [← result.terminalHandoff_eq, ← result.terminalDisposition_eq]
    exact terminalDisposition_ne_continue result
  have houtput := terminal_fold_output_related source rewards rate C_star C_h result.terminalBlock
    (ReferenceInitializationRun.run x result.terminalBlock.val) h actual
    (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) hr rfl
    (generatedBlockDown_false_of_no_initialization_failure x hinit result.terminalBlock.val
      result.terminalBlock.isLt hr.2.1 h)
    (cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate hfalse
      result.terminalBlock.val result.terminalBlock.isLt hr.2.1 h)
    hforce result.terminalC_star result.terminalC_h result.terminalFold hstar hch hfold hstopped
  refine ⟨⟨h, houtput.1⟩, ?_, houtput.2.2.1, houtput.2.2.2.1, ?_⟩
  · rw [hrecords]
    exact houtput.2.1
  · rw [result.terminalHandoff_eq]
    exact houtput.2.2.2.2


private theorem terminal_fold_launched_endpoint
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate s)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate s actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hout : ReferenceInitializationRun.output (referenceInput source rewards C_star C_h rate) =
      ReferenceInitializationRun.finishBlock (referenceInput source rewards C_star C_h rate) b h)
    (C_star' C_h' : ℝ)
    (folded : ActualInitializationRun.BlockFoldOutput p rate s source rewards C_star' C_h' 0)
    (hstar : actual.C_star = C_star') (hch : actual.C_h = C_h')
    (hfold : HEq folded (ActualInitializationRun.foldBlock p rate s source rewards actual))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded).disposition = .launched launch seed) :
    let x := referenceInput source rewards C_star C_h rate
    (ReferenceInitializationRun.output x).crossing = some s ∧
      ReferenceInitializationRun.launchRound x = launch.monitor.launchPosition + 1 ∧
      launch.data.block = s ∧
      launch.triggerRound.val + 1 = BootstrapObservedFollower.blockStop p s ∧
      launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p s ∧
      launch.data.C_star = C_star ∧ launch.data.C_h = C_h ∧
      BootstrapLaunchMonitor.monitorValue p launch.monitor.counters >
        4 * BootstrapStartupCostScale.Q C_star C_h p ∧
      (∀ arm, seed.baseScores arm = 0 ∧ seed.queues arm = 0) ∧
      (BootstrapObservedFollower.blockStop p s = p.T →
        ReferenceInitializationRun.launchRound x = p.T + 1) := by
  have hs : s = ReferenceInitializationRun.nextBlock b h := Fin.ext hr.1.symm
  subst s
  subst C_star'
  subst C_h'
  have hfoldEq := eq_of_heq hfold
  subst folded
  obtain ⟨_, hblock, _, hcs, hch, _, hcross, htrigger, hposition, hactivation, hzero, _, _⟩ :=
    ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_crossing
      source rewards rate C_star C_h b h actual past hr hdown launch seed hlaunched
  let x := referenceInput source rewards C_star C_h rate
  have hround : ReferenceInitializationRun.launchRound x = launch.monitor.launchPosition + 1 := by
    unfold ReferenceInitializationRun.launchRound
    rw [hout, hcross]
    exact hactivation
  refine ⟨?_, hround, hblock, htrigger, hposition, hcs, hch, ?_, hzero, ?_⟩
  · rw [hout]
    exact hcross
  · simpa only [hcs, hch] using launch.strictThreshold
  · intro hstop
    rw [hround, hposition, hstop]

/-- Any actual terminal launch has the reference strict-crossing endpoint,
shared constants and the actual learner seed's zero scores and queues.
A crossing at the final elapsed round still has crossing `some block` and
launch round `T + 1`. -/
theorem sourceInitializedRun_launched_endpoint
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed) :
    let x := referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (ReferenceInitializationRun.output x).crossing = some result.terminalBlock ∧
      ReferenceInitializationRun.launchRound x = launch.monitor.launchPosition + 1 ∧
      launch.data.block = result.terminalBlock ∧
      launch.triggerRound.val + 1 = BootstrapObservedFollower.blockStop p result.terminalBlock ∧
      launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p result.terminalBlock ∧
      launch.data.C_star = C_star ∧ launch.data.C_h = C_h ∧
      BootstrapLaunchMonitor.monitorValue p launch.monitor.counters >
        4 * BootstrapStartupCostScale.Q C_star C_h p ∧
      (∀ arm, seed.baseScores arm = 0 ∧ seed.queues arm = 0) ∧
      (BootstrapObservedFollower.blockStop p result.terminalBlock = p.T →
        ReferenceInitializationRun.launchRound x = p.T + 1) := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, h, hr, _, _, hstar, hch, hfold, _, _⟩ :=
    sourceInitializedRun_terminal_incoming p rate source rewards C_star C_h hinit hfalse
  obtain ⟨h', hout⟩ :=
    (sourceInitializedRun_output_related p rate source rewards C_star C_h hinit hfalse).1
  have hdisposition : (ActualInitializationRun.combinedBoundaryHandoff p rate result.terminalBlock
      source rewards result.terminalC_star result.terminalC_h result.terminalFold).disposition =
        .launched launch seed := by
    rw [← result.terminalHandoff_eq, ← result.terminalDisposition_eq]
    exact hlaunched
  exact terminal_fold_launched_endpoint source rewards rate C_star C_h result.terminalBlock
    (ReferenceInitializationRun.run x result.terminalBlock.val) h actual
    (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) hr
    (generatedBlockDown_false_of_no_initialization_failure x hinit result.terminalBlock.val
      result.terminalBlock.isLt hr.2.1 h)
    hout result.terminalC_star result.terminalC_h result.terminalFold hstar hch hfold
    launch seed hdisposition

private theorem combinedBoundaryHandoff_firstDeclaration_initial
    {rate : RateInput p} {s : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p} {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate s source rewards C_star C_h 0)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : (ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star C_h folded).followers i = .firstDeclaration row activation state memory) :
    state = ReferencePrelaunchFollower.initial p rate.eta ∧
      memory = ActiveFollowerLifecycle.initialMemory p := by
  change ActualInitializationRun.boundaryOutputFromFollower p rate s (folded.followers i) =
    .firstDeclaration row activation state memory at hfirst
  cases hf : folded.followers i with
  | bootstrap startup =>
      rw [hf] at hfirst
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp only [ActualInitializationRun.boundaryOutputFromFollower, hpending,
            Option.elim_none] at hfirst
          cases hfirst
      | some saved =>
          simp only [ActualInitializationRun.boundaryOutputFromFollower, hpending,
            Option.elim_some] at hfirst
          cases hfirst
          exact ⟨rfl, rfl⟩
  | declared oldRow oldActivation configuration =>
      rw [hf] at hfirst
      cases hfirst

/-- Only the actual first-declaration boundary constructor installs initial
ordinary state and initial proposal memory. Existing declarations use their
preserved memory, as exposed by the launched-state theorem below. -/
theorem sourceInitializedRun_firstDeclaration_initial
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalHandoff.followers i = .firstDeclaration row activation state memory) :
    state = ReferencePrelaunchFollower.initial p rate.eta ∧
      memory = ActiveFollowerLifecycle.initialMemory p := by
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hfirst' := hfirst
  change result.terminalHandoff.followers i = .firstDeclaration row activation state memory at hfirst'
  rw [result.terminalHandoff_eq] at hfirst'
  exact combinedBoundaryHandoff_firstDeclaration_initial result.terminalFold
    i row activation state memory hfirst'


open Bandits.Support.ActualInitializationLaunchState

private theorem terminal_fold_launched_state
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate s)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate s actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (referenceInput source rewards C_star C_h rate) b h i = false)
    (hout : ReferenceInitializationRun.output (referenceInput source rewards C_star C_h rate) =
      ReferenceInitializationRun.finishBlock (referenceInput source rewards C_star C_h rate) b h)
    (C_star' C_h' : ℝ)
    (folded : ActualInitializationRun.BlockFoldOutput p rate s source rewards C_star' C_h' 0)
    (hstar : actual.C_star = C_star') (hch : actual.C_h = C_h')
    (hfold : HEq folded (ActualInitializationRun.foldBlock p rate s source rewards actual))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded).disposition = .launched launch seed) :
    let x := referenceInput source rewards C_star C_h rate
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      active.coordinator = .first ∧
      active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      (∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
        .declared J (active.activations i) (active.followers i)) ∧
      (∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
        (.declared J (active.activations i) (active.followers i))) ∧
      (∀ i, ∃ state memory,
        active.followers i = .ordinary state memory ∧
        state = ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) (refFollower i) ∧
        state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
        state.status = .unoccupied ∧ state.initializationFailure = false) ∧
      (∀ i, (active.activations i).val ≤ launch.monitor.launchPosition + 1) ∧
      (∀ time : Fin p.T, launch.monitor.launchPosition ≤ time.val →
        ∀ i, (active.activations i).val ≤ time.val + 1) ∧
      ∀ i row activation state memory,
        actual.followers i = .declared row activation (.ordinary state memory) →
        handoff.followers i = .preserveDeclared J activation
          (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
            (refFollower i)) memory) ∧
        active.followers i = .ordinary (ReferenceInitializationRun.ordinary x
          (ReferenceInitializationRun.output x) (refFollower i)) memory := by
  have hs : s = ReferenceInitializationRun.nextBlock b h := Fin.ext hr.1.symm
  subst s
  subst C_star'
  subst C_h'
  have hfoldEq := eq_of_heq hfold
  subst folded
  let active := ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past
    hr hdown hclean hforce launch seed hlaunched
  refine ⟨active,
    ofActualLaunchedBoundary_coordinator source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch seed hlaunched,
    ofActualLaunchedBoundary_upDecoderBank source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch seed hlaunched, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ofActualLaunchedBoundary_followerCarry source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch seed hlaunched i
  · intro i
    have hrelated :=
      (ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch seed hlaunched).2.2.2.1 i
    rw [ofActualLaunchedBoundary_followerCarry source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch seed hlaunched i, ← hout] at hrelated
    exact hrelated
  · intro i
    have hreplay := ofActualLaunchedBoundary_follower_replay source rewards rate C_star C_h b h
      actual past hr hdown hclean hforce launch seed hlaunched i
    rw [← hout] at hreplay
    exact hreplay
  · intro i
    exact ofActualLaunchedBoundary_activation_le_launchPosition source rewards rate C_star C_h b h
      actual past hr hdown hclean hforce launch seed hlaunched i
  · intro time htime i
    have hposition := ofActualLaunchedBoundary_launchPosition_eq_blockStop source rewards rate
      C_star C_h b h actual past hr hdown launch seed hlaunched
    exact ofActualLaunchedBoundary_activeAtTime source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch seed hlaunched time (by rw [← hposition]; exact htime) i
  · intro i row activation state memory hactual
    have hpreserved := ofActualLaunchedBoundary_preserveDeclared source rewards rate C_star C_h b h
      actual past hr hdown i row activation state memory hactual
    have hconfiguration := ofActualLaunchedBoundary_preservedConfiguration source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch seed hlaunched
      i row activation state memory hactual
    rw [← hout] at hpreserved hconfiguration
    exact ⟨hpreserved, hconfiguration⟩

/-- Existential canonical active state at any actual terminal launch. Its
follower configurations and activations are the actual handoff carries in the
true selected row. The existing relation retains whole ordinary replay,
chronological local history, buffer and partial DOWN bank. Old declarations
retain their proposal memory; no new state conversion or run is introduced. -/
theorem sourceInitializedRun_launched_state
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed) :
    let x := referenceInput source rewards C_star C_h rate
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    ∃ actual : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
      BlockStartRelated source rewards C_star C_h rate result.terminalBlock actual
        (ReferenceInitializationRun.run x result.terminalBlock.val)
        (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
      HEq result.terminalFold
        (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards actual) ∧
      ∃ active : ReferenceActivePhysicalStep.State p rate,
        active.coordinator = .first ∧
        active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
        (∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
          (result.terminalHandoff.followers i) = .declared J (active.activations i) (active.followers i)) ∧
        (∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
          (.declared J (active.activations i) (active.followers i))) ∧
        (∀ i, ∃ state memory,
          active.followers i = .ordinary state memory ∧
          state = ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) (refFollower i) ∧
          state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
          state.status = .unoccupied ∧ state.initializationFailure = false) ∧
        (∀ i, (active.activations i).val ≤ launch.monitor.launchPosition + 1) ∧
        (∀ time : Fin p.T, launch.monitor.launchPosition ≤ time.val →
          ∀ i, (active.activations i).val ≤ time.val + 1) ∧
        ∀ i row activation state memory,
          actual.followers i = .declared row activation (.ordinary state memory) →
          result.terminalHandoff.followers i = .preserveDeclared J activation
            (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (refFollower i)) memory) ∧
          active.followers i = .ordinary (ReferenceInitializationRun.ordinary x
            (ReferenceInitializationRun.output x) (refFollower i)) memory := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, h, hr, _, _, hstar, hch, hfold, _, hforce⟩ :=
    sourceInitializedRun_terminal_incoming p rate source rewards C_star C_h hinit hfalse
  obtain ⟨h', hout⟩ :=
    (sourceInitializedRun_output_related p rate source rewards C_star C_h hinit hfalse).1
  have hdisposition : (ActualInitializationRun.combinedBoundaryHandoff p rate result.terminalBlock
      source rewards result.terminalC_star result.terminalC_h result.terminalFold).disposition =
        .launched launch seed := by
    rw [← result.terminalHandoff_eq, ← result.terminalDisposition_eq]
    exact hlaunched
  refine ⟨actual, hr, hfold, ?_⟩
  rw [result.terminalHandoff_eq]
  exact terminal_fold_launched_state source rewards rate C_star C_h result.terminalBlock
    (ReferenceInitializationRun.run x result.terminalBlock.val) h actual
    (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) hr
    (generatedBlockDown_false_of_no_initialization_failure x hinit result.terminalBlock.val
      result.terminalBlock.isLt hr.2.1 h)
    (cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate hfalse
      result.terminalBlock.val result.terminalBlock.isLt hr.2.1 h)
    hforce hout result.terminalC_star result.terminalC_h result.terminalFold hstar hch hfold
    launch seed hdisposition


private theorem terminal_fold_exhausted_endpoint
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate s)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate s actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hout : ReferenceInitializationRun.output (referenceInput source rewards C_star C_h rate) =
      ReferenceInitializationRun.finishBlock (referenceInput source rewards C_star C_h rate) b h)
    (C_star' C_h' : ℝ)
    (folded : ActualInitializationRun.BlockFoldOutput p rate s source rewards C_star' C_h' 0)
    (hstar : actual.C_star = C_star') (hch : actual.C_h = C_h')
    (hfold : HEq folded (ActualInitializationRun.foldBlock p rate s source rewards actual))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded).disposition = .exhausted live) :
    let x := referenceInput source rewards C_star C_h rate
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate s source rewards
      C_star' C_h' folded
    s.val + 1 = n_boot p ∧
      (ReferenceInitializationRun.output x).crossing = none ∧
      ReferenceInitializationRun.launchRound x = p.T + 1 ∧
      BootstrapObservedFollower.blockStop p s = p.T ∧
      (ReferenceInitializationRun.boundaryActivation b).val = p.T + 1 ∧
      (∀ i, match handoff.followers i with
        | .continueBootstrap _ _ activation => activation.val = p.T + 1
        | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
        | .preserveDeclared _ _ _ => True) ∧
      ∀ i row activation state memory,
        actual.followers i = .declared row activation (.ordinary state memory) →
        handoff.followers i = .preserveDeclared
          (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
          (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
            (refFollower i)) memory) := by
  have hs : s = ReferenceInitializationRun.nextBlock b h := Fin.ext hr.1.symm
  subst s
  subst C_star'
  subst C_h'
  have hfoldEq := eq_of_heq hfold
  subst folded
  obtain ⟨hlast, _, hnone, _, _, _, _, _, hstop, hactivation, _, hfollowers⟩ :=
    ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_exhausted_related
      source rewards rate C_star C_h b h actual past hr hdown hclean live hexhausted
  have houtputNone : (ReferenceInitializationRun.output
      (referenceInput source rewards C_star C_h rate)).crossing = none := by
    rw [hout]
    exact hnone
  refine ⟨hlast, houtputNone, ?_, hstop, hactivation, hfollowers, ?_⟩
  · simp only [ReferenceInitializationRun.launchRound, houtputNone,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  · intro i row activation state memory hactual
    have hpreserved :=
      ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_preserveDeclared
        source rewards rate C_star C_h b h actual past hr hdown
        i row activation state memory hactual
    dsimp only at hpreserved
    rw [← hout] at hpreserved
    exact hpreserved

/-- Exhaustion has no reference crossing, launch sentinel `T + 1`, the true
last block and complete actual records through `T`. Actual terminal follower
correspondence allows pending first activation at `T + 1`, bootstrap
continuation without a save, and earlier declarations with retained memory. -/
theorem sourceInitializedRun_exhausted_related
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .exhausted live) :
    let x := referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (ReferenceInitializationRun.output x).crossing = none ∧
      ReferenceInitializationRun.launchRound x = p.T + 1 ∧
      result.terminalBlock.val + 1 = n_boot p ∧
      BootstrapObservedFollower.blockStop p result.terminalBlock = p.T ∧
      result.records.length = p.T ∧
      (ActualInitializationRun.PhysicalRoundRecord.actions result.records).length = p.T ∧
      (ActualInitializationRun.PhysicalRoundRecord.feedback result.records).length = p.T ∧
      past_related result.records (ReferenceInitializationRun.output x) ∧
      result.terminalFold.phase.monitorState.counters = (ReferenceInitializationRun.output x).counters ∧
      (∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (result.terminalHandoff.followers i))) ∧
      (ReferenceInitializationRun.boundaryActivation
        (ReferenceInitializationRun.run x result.terminalBlock.val)).val = p.T + 1 ∧
      (∀ i, match result.terminalHandoff.followers i with
        | .continueBootstrap _ _ activation => activation.val = p.T + 1
        | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
        | .preserveDeclared _ _ _ => True) ∧
      (∀ record ∈ result.records, record.time.val < p.T) ∧
      ∃ actual : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
        BlockStartRelated source rewards C_star C_h rate result.terminalBlock actual
          (ReferenceInitializationRun.run x result.terminalBlock.val)
          (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
        HEq result.terminalFold
          (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards actual) ∧
        ∀ i row activation state memory,
          actual.followers i = .declared row activation (.ordinary state memory) →
          result.terminalHandoff.followers i = .preserveDeclared
            (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
            (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (refFollower i)) memory) := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, h, hr, _, _, hstar, hch, hfold, _, _⟩ :=
    sourceInitializedRun_terminal_incoming p rate source rewards C_star C_h hinit hfalse
  have hcommon := sourceInitializedRun_output_related p rate source rewards C_star C_h hinit hfalse
  obtain ⟨h', hout⟩ := hcommon.1
  have hdisposition : (ActualInitializationRun.combinedBoundaryHandoff p rate result.terminalBlock
      source rewards result.terminalC_star result.terminalC_h result.terminalFold).disposition =
        .exhausted live := by
    rw [← result.terminalHandoff_eq, ← result.terminalDisposition_eq]
    exact hexhausted
  have hendpoint := terminal_fold_exhausted_endpoint source rewards rate C_star C_h result.terminalBlock
    (ReferenceInitializationRun.run x result.terminalBlock.val) h actual
    (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) hr
    (generatedBlockDown_false_of_no_initialization_failure x hinit result.terminalBlock.val
      result.terminalBlock.isLt hr.2.1 h)
    (cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate hfalse
      result.terminalBlock.val result.terminalBlock.isLt hr.2.1 h)
    hout result.terminalC_star result.terminalC_h result.terminalFold hstar hch hfold live hdisposition
  obtain ⟨hlast, hnone, hround, hstop, hactivation, hfollowers, hpreserve⟩ := hendpoint
  have hrecords : result.records.length = p.T :=
    hcommon.2.1.choose.trans (ReferenceInitializationRun.output_elapsed_of_no_crossing x hnone)
  have hlengths := ActualInitializationHorizon.sourceInitializedRun_history_lengths
    p rate source rewards C_star C_h
  change (ActualInitializationRun.PhysicalRoundRecord.actions result.records).length = _ ∧
    (ActualInitializationRun.PhysicalRoundRecord.feedback result.records).length = _ at hlengths
  rw [hstop] at hlengths
  refine ⟨hnone, hround, hlast, hstop, hrecords, hlengths.1, hlengths.2,
    hcommon.2.1, hcommon.2.2.1, hcommon.2.2.2.2, hactivation, ?_, ?_, actual, hr, hfold, ?_⟩
  · rw [result.terminalHandoff_eq]
    exact hfollowers
  · intro record _
    exact record.time.isLt
  · rw [result.terminalHandoff_eq]
    exact hpreserve

end Bandits.Support.ActualReferenceInitializationHorizon

end
